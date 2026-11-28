import CunninghamSelbergSieve

/-! Count prime returns in selected offset sets after parametrizing a
single reduced progression of seeds. -/

namespace CunninghamChain.OrbitIsolation
open Finset Real

private abbrev affineSite (b : Bool) := if b then firstKindTerm else secondKindTerm

noncomputable def affinePairs (b : Bool) (A W i X : ℕ) : Finset ℕ :=
  (range X).filter fun t => (A+W*t).Prime ∧ (affineSite b (A+W*t) (i+1)).Prime

private noncomputable abbrev factor (p : ℕ) := ((1-1/(p:ℝ))⁻¹)^2
private noncomputable def smallFactor := ∏ p∈(4:ℕ).primesLE, factor p
noncomputable def collisionPrimes (z W : ℕ) := (z.primesLE\(4:ℕ).primesLE).filter fun q => ¬q∣W

lemma collisionPrimes_prime_gt_two {z W q : ℕ} (hq : q∈collisionPrimes z W) : q.Prime ∧ 2<q := by
  obtain ⟨mem,_⟩ := mem_filter.mp hq
  obtain ⟨zp,np⟩ := mem_sdiff.mp mem
  have pr := Nat.prime_of_mem_primesLE zp
  exact ⟨pr,by by_contra! small; exact np (Nat.mem_primesLE.mpr ⟨by omega,pr⟩)⟩

private lemma one_le_factor {p : ℕ} (pr : p.Prime) : 1≤factor p := by
  have hp : (1:ℝ)<p := by exact_mod_cast pr.one_lt
  have pp : 0<1-1/(p:ℝ) := sub_pos.mpr ((div_lt_one (by positivity)).mpr hp)
  apply one_le_pow₀
  apply (one_le_inv₀ pp).mpr
  linarith [show 0≤1/(p:ℝ) by positivity]

theorem affine_offset_bound (b : Bool) (A i : ℕ) {W X z : ℕ} (wp : 0<W) (hz : 4≤z)
    (cut : (z^8)^4≤X) :
    ((affinePairs b A W i X).card:ℝ)*(log ((z:ℝ)+1))^2 ≤ (z+1:ℕ)*(log ((z:ℝ)+1))^2+
      54*(∏ q∈W.primeFactors, factor q)*
        (∏ q∈(collisionPrimes z W).filter (fun q => orderOf (2:ZMod q)∣i+1), factor q)*X := by
  classical
  let P := (4:ℕ).primesLE
  let G := (z.primesLE\P).filter (·∣W)
  let Q := collisionPrimes z W
  let D := Q.filter (fun q => orderOf (2:ZMod q)∣i+1)
  let E := (P∪G)∪D
  let I : Finset ℕ := {0,i+1}
  have sz : I.card=2 := by simp [I]
  have pz : P⊆z.primesLE := fun l hl => Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hl).trans hz,Nat.prime_of_mem_primesLE hl⟩
  have gz : G⊆z.primesLE := fun l hl => (mem_sdiff.mp (mem_filter.mp hl).1).1
  have dz : D⊆z.primesLE := fun l hl => (mem_sdiff.mp (mem_filter.mp (mem_filter.mp hl).1).1).1
  have ez : E⊆z.primesLE := union_subset (union_subset pz gz) dz
  have regular {q : ℕ} (hq : q∈z.primesLE\E) : 4<q ∧ ¬q∣W ∧ ¬orderOf (2:ZMod q)∣i+1 := by
    obtain ⟨mem,notE⟩ := mem_sdiff.mp hq
    have np : q∉P := fun h => notE (mem_union_left _ (mem_union_left _ h))
    have nw : ¬q∣W := fun d => notE (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem,np⟩,d⟩)))
    refine ⟨?_,nw,fun d => notE (mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem,np⟩,nw⟩,d⟩))⟩
    by_contra! small
    exact np (Nat.mem_primesLE.mpr ⟨small,Nat.prime_of_mem_primesLE mem⟩)
  have reg : ∀ q∈z.primesLE\E, 2*2<q ∧ Set.InjOn (fun j : ℕ => (2:ZMod q)^j) I := by
    intro q hq
    have h := regular hq
    refine ⟨h.1,?_⟩
    have neq : (2:ZMod q)^(i+1)≠1 := fun eq => h.2.2 (orderOf_dvd_of_pow_eq_one eq)
    intro j hj k hk eq
    simp only [I,Finset.coe_insert,Finset.coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hj hk
    rcases hj with rfl|rfl <;> rcases hk with rfl|rfl <;> simp_all
  have sieve := finite_affine_iterate_sieve_bound b I E A W sz (by decide) (by omega) ez
    (fun _ hq => (regular hq).2.1) reg cut
  let H := (affinePairs b A W i X).filter fun t => z<A+W*t
  have zeroSite (p : ℕ) : affineSite b p 0=p := by cases b <;> rfl
  have eq : ((range X).filter fun t => z<A+W*t ∧ ∀ j∈I, (affineSite b (A+W*t) j).Prime)=H := by
    ext t
    simp [I,H,affinePairs,zeroSite,and_comm,and_left_comm]
  change (((range X).filter fun t => z<A+W*t ∧ ∀ j∈I, (affineSite b (A+W*t) j).Prime).card:ℝ)*_≤_ at sieve
  rw [eq,←prod_pow] at sieve
  have pg : Disjoint P G := disjoint_left.mpr fun q hp hg => (mem_sdiff.mp (mem_filter.mp hg).1).2 hp
  have dis : Disjoint (P∪G) D := by
    apply disjoint_left.mpr
    intro q hpg hD
    obtain ⟨mem,nw⟩ := mem_filter.mp (mem_filter.mp hD).1
    rcases mem_union.mp hpg with hp|hg
    · exact (mem_sdiff.mp mem).2 hp
    · exact nw (mem_filter.mp hg).2
  have gw : G⊆W.primeFactors := fun q h => (Nat.prime_of_mem_primesLE (gz h)).mem_primeFactors (mem_filter.mp h).2 wp.ne'
  have cost := prod_le_prod_of_subset_of_one_le (f:=factor) gw (fun _ _ => sq_nonneg _)
    (fun _ h _ => one_le_factor (Nat.prime_of_mem_primeFactors h))
  change (H.card:ℝ)*_ ≤ 6*(∏ q∈(P∪G)∪D,factor q)*X at sieve
  rw [prod_union dis,prod_union pg] at sieve
  have main : (H.card:ℝ)*(log ((z:ℝ)+1))^2≤
      6*smallFactor*(∏ q∈W.primeFactors,factor q)*(∏ q∈D,factor q)*X := by
    apply sieve.trans
    change 6*((smallFactor*_)*_)*_≤_
    have small : 0 ≤ smallFactor := prod_nonneg fun _ _ => sq_nonneg _
    have nonneg : 0≤∏ q∈D,factor q := prod_nonneg fun _ _ => sq_nonneg _
    have eq := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left cost (show (0:ℝ)≤6*smallFactor by positivity)) nonneg) (Nat.cast_nonneg X)
    simpa only [mul_assoc] using eq
  have sub : affinePairs b A W i X ⊆ range (z+1)∪H := by
    intro t ht
    by_cases big : z<A+W*t
    · exact mem_union_right _ (mem_filter.mpr ⟨ht,big⟩)
    · have td := Nat.le_mul_of_pos_left t wp
      exact mem_union_left _ (mem_range.mpr (by omega))
  have card := (card_le_card sub).trans (card_union_le ..)
  rw [card_range] at card
  have cb : ((affinePairs b A W i X).card:ℝ)≤((z+1:ℕ):ℝ)+H.card := by exact_mod_cast card
  have c : smallFactor=9 := by
    rw [smallFactor,show (4:ℕ).primesLE={2,3} by decide]
    norm_num [factor]
  rw [c,show 6*(9:ℝ)=54 by norm_num] at main
  exact (mul_le_mul_of_nonneg_right cb (sq_nonneg _)).trans (by rw [add_mul]; exact add_le_add le_rfl main)

#print axioms affine_offset_bound

end CunninghamChain.OrbitIsolation
