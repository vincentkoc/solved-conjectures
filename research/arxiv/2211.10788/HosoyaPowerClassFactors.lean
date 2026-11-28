import HosoyaPowerClassIntervals

/-! The exponent residues on a finite set of primes give finitely many power classes. -/
namespace Arxiv.«2211.10788».PowerGaps
open Finset
open scoped Classical

private noncomputable def classes (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  univ.image (fun a : ↥S → Fin k => ∏ p : ↥S, (p:ℕ)^(a p).val)

private lemma class_count (S : Finset ℕ) (k : ℕ) : (classes S k).card ≤ k^S.card := by
  unfold classes
  apply card_image_le.trans
  simp

private lemma classify {n k : ℕ} (nz : n≠0) (kp : 0<k) (S : Finset ℕ)
    (div : ∀ p∈n.primeFactors, p∉S → k∣n.factorization p) :
    ∃ d∈classes S k, ∃ y, n=d*y^k := by
  let w (p : ℕ) := p^(n.factorization p%k)
  let b (p : ↥S) : Fin k := ⟨n.factorization p.val%k,Nat.mod_lt _ kp⟩
  let d := ∏ p∈S,w p
  have mem : d∈classes S k := by
    refine mem_image.mpr ⟨b,mem_univ _,?_⟩
    change (∏ p : ↥S, w p.val)=∏ p∈S,w p
    exact prod_attach S w
  have eq : (∏ p∈S,w p)=∏ p∈n.primeFactors,w p := by
    let I := S∩n.primeFactors
    have left : (∏ p∈I,w p)=∏ p∈S,w p := by
      apply prod_subset inter_subset_left
      intro p hs miss
      have no : p∉n.factorization.support := fun h => miss (mem_inter.mpr ⟨hs,h⟩)
      simp [w,Finsupp.notMem_support_iff.mp no]
    rw [←left]
    apply prod_subset inter_subset_right
    intro p hf miss
    have no : p∉S := fun h => miss (mem_inter.mpr ⟨h,hf⟩)
    simp [w,Nat.mod_eq_zero_of_dvd (div p hf no)]
  refine ⟨d,mem,∏ p∈n.primeFactors, p^(n.factorization p/k),?_⟩
  dsimp only [d]
  rw [eq,←Finset.prod_pow,←prod_mul_distrib]
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization nz]
  apply prod_congr rfl
  intro p _
  unfold w
  rw [←pow_mul,←pow_add,Nat.mul_comm (n.factorization p/k) k,Nat.mod_add_div]

/-- If every prime outside a prescribed set occurs to multiplicity divisible
by k, the term belongs to one of at most k^|S| power classes. -/
theorem exceptional_factor_orders (s : HosoyaNeighbor) (S : Finset ℕ) (a r : ℕ) {k : ℕ} (hk : 2≤k) :
    ((Ico a (a+16*2^r)).filter (fun n => ∀ p∈(s.value n).primeFactors,
      p∉S → k∣(s.value n).factorization p)).card ≤ k^S.card*(16+32*k*r) := by
  let T (d : ℕ) := (Ico a (a+16*2^r)).filter (fun n => ∃ y, s.value n=d*y^k)
  apply le_trans _ ((Nat.mul_le_mul_right (16+32*k*r) (class_count S k)))
  calc
    _ ≤ ((classes S k).biUnion T).card := by
      apply card_le_card
      intro n hn
      obtain ⟨inRange,div⟩ := mem_filter.mp hn
      have nz : s.value n≠0 := by
        intro z
        have h := s.supportBounds.lower n
        simp [z] at h
      obtain ⟨d,dm,y,eq⟩ := classify nz (by omega) S div
      exact mem_biUnion.mpr ⟨d,dm,mem_filter.mpr ⟨inRange,y,eq⟩⟩
    _ ≤ ∑ d∈classes S k,(T d).card := card_biUnion_le
    _ ≤ ∑ _∈classes S k, (16+32*k*r) := sum_le_sum fun d _ => power_class_block_bound s d a r hk
    _ = _ := by simp

#print axioms exceptional_factor_orders
end Arxiv.«2211.10788».PowerGaps
