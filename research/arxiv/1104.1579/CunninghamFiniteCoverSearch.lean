import CunninghamOrbitCoverWindow

/-! Finite candidates for prime covering systems of the two Cunningham recurrences. -/

namespace CunninghamChain.OrbitCover
open Finset SquarefreeSeeds

private lemma two_misses (b : Bool) {p j : ℕ} (pp : 0<p) (jp : 0<j) :
    ¬2∣term b p j := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero jp.ne'
  have pos := (term_bounds b pp i).1
  cases b <;> simp only [term,Bool.false_eq_true,if_false,if_true] at pos ⊢
  · rw [secondKindTerm]
    omega
  · rw [firstKindTerm]
    omega

private lemma odd_subcover (b : Bool) {p : ℕ} (pp : 0<p) (S : Finset ℕ)
    (prime : ∀ q∈S,q.Prime) (cover : Covers b p S) :
    Covers b p (S.filter (2<·)) := by
  intro j jp
  obtain ⟨q,hq,hit⟩ := cover j jp
  have lb := (prime q hq).two_le
  refine ⟨q,mem_filter.mpr ⟨hq,?_⟩,hit⟩
  by_contra! small
  have eq : q=2 := by omega
  exact two_misses b pp jp (eq ▸ hit)

theorem covers_iff_block (b : Bool) {p : ℕ} (pp : 0<p) (S : Finset ℕ)
    (prime : ∀ q∈S,q.Prime ∧ 2<q) {k : ℕ} (size : S.card≤k) :
    Covers b p S ↔ ∀ i<2^k, ∃ q∈S,q∣term b p (1+i) := by
  refine ⟨fun h i _ => h _ (by omega),?_⟩
  intro block
  by_contra h
  unfold Covers at h
  push Not at h
  obtain ⟨u,_,miss⟩ := h
  obtain ⟨j,bound,free⟩ := escape_every_block b pp S prime miss 1
  obtain ⟨q,hq,hit⟩ := block j (bound.trans_le (Nat.pow_le_pow_right (by decide) size))
  exact free q hq hit

/-- Divisors available to any irredundant cover using at most k primes. -/
def mersenneProduct (D : ℕ) : ℕ := ∏ i∈range D, (2^(i+1)-1)

def candidates (k : ℕ) := (mersenneProduct (2^(k-1))).primeFactors

private theorem mersenneProduct_pos (D : ℕ) : 0 < mersenneProduct D := by
  apply Finset.prod_pos
  intro i _
  have h : 1<(2:ℕ)^(i+1) := one_lt_pow₀ (by decide) (by omega)
  omega

private theorem order_mem {k q : ℕ} (hp : q.Prime) (odd : 2<q)
    (le : orderOf (2:ZMod q) ≤ 2^(k-1)) : q∈candidates k := by
  let d := orderOf (2:ZMod q)
  have dp : 0<d := two_order_pos hp odd
  have mod : 2^d ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff ..).mp (by
    push_cast
    exact pow_orderOf_eq_one _)
  have fac : q∣2^d-1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp mod.symm
  apply Nat.mem_primeFactors.mpr
  refine ⟨hp,fac.trans ?_,(mersenneProduct_pos _).ne'⟩
  have h : d-1 ∈ range (2^(k-1)) := mem_range.mpr (by change d≤_ at le; omega)
  simpa [mersenneProduct,Nat.sub_add_cancel dp] using
    (Finset.dvd_prod_of_mem (fun i : ℕ => (2^(i+1)-1:ℕ)) h)

/-- All primes in a minimal subcover belong to the same finite candidate
set, independently of the seed and the choice of sign. -/
theorem reduce_cover (b : Bool) {p k : ℕ} (pp : 0<p) (S : Finset ℕ)
    (prime : ∀ q∈S,q.Prime) (size : S.card≤k) (cover : Covers b p S) :
    ∃ T⊆S, T⊆candidates k ∧ (∀ q∈T,2<q) ∧ Covers b p T := by
  classical
  let A := S.filter (2<·)
  let F := A.powerset.filter (Covers b p)
  have memA : A∈F := mem_filter.mpr ⟨mem_powerset.mpr (Subset.rfl),odd_subcover b pp S prime cover⟩
  obtain ⟨T,ht,minimal⟩ := F.exists_min_image Finset.card ⟨A,memA⟩
  obtain ⟨ta,ct⟩ := mem_filter.mp ht
  have sub : T⊆A := mem_powerset.mp ta
  have ts : T⊆S := sub.trans (filter_subset _ _)
  have odd (q) (hq : q∈T) : 2<q := (mem_filter.mp (sub hq)).2
  refine ⟨T,ts,?_,odd,ct⟩
  intro q hq
  have need : ¬ Covers b p (T.erase q) := by
    intro hh
    have he : T.erase q∈F := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset _ _).trans sub),hh⟩
    exact (Nat.not_le_of_lt (card_erase_lt_of_mem hq)) (minimal _ he)
  have ord := indispensable_order b pp T (fun l hl => ⟨prime l (ts hl),odd l hl⟩) hq ct need
  apply order_mem (prime q (ts hq)) (odd q hq)
  exact ord.trans (Nat.pow_le_pow_right (by decide)
    (Nat.sub_le_sub_right ((card_le_card ts).trans size) 1))

theorem seed_mem_of_cover (b : Bool) {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (prime : ∀ q∈S,q.Prime ∧ 2<q) (cover : Covers b p S) : p∈S := by
  by_contra absent
  have miss (q) (hq : q∈S) : ¬q∣term b p 0 := by
    have zero : term b p 0=p := by cases b <;> rfl
    intro hit
    obtain unit|eq := (Nat.dvd_prime hp).mp (zero ▸ hit)
    · exact (prime q hq).1.ne_one unit
    · exact absent (eq ▸ hq)
  obtain ⟨j,_,free⟩ := escape_every_block b hp.pos S prime miss 1
  obtain ⟨q,hq,hit⟩ := cover (1+j) (by omega)
  exact free q hq hit

theorem finite_cover_iff (b : Bool) {p k : ℕ} (hp : p.Prime) :
    (∃ S : Finset ℕ, (∀ q∈S,q.Prime) ∧ S.card≤k ∧ Covers b p S) ↔
    ∃ T⊆candidates k, p∈T ∧ T.card≤k ∧ (∀ q∈T,2<q) ∧
      ∀ i<2^k, ∃ q∈T,q∣term b p (1+i) := by
  constructor
  · rintro ⟨S,pr,size,cover⟩
    obtain ⟨T,ts,sub,odd,ct⟩ := reduce_cover b hp.pos S pr size cover
    have prime (q) (hq : q∈T) := And.intro (pr q (ts hq)) (odd q hq)
    have bound := (card_le_card ts).trans size
    exact ⟨T,sub,seed_mem_of_cover b hp T prime ct,bound,odd,(covers_iff_block b hp.pos T prime bound).mp ct⟩
  · rintro ⟨T,sub,_,size,odd,block⟩
    have pr (q) (h : q∈T) := Nat.prime_of_mem_primeFactors (sub h)
    exact ⟨T,pr,size,(covers_iff_block b hp.pos T (fun q h => ⟨pr q h,odd q h⟩) size).mpr block⟩

#print axioms finite_cover_iff

end CunninghamChain.OrbitCover
