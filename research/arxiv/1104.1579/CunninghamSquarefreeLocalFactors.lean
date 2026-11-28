import research.arxiv.«1104.1579».CunninghamSquarefreePrimeSeeds

/-! # Local square obstructions in a Cunningham prefix product -/

namespace CunninghamChain.SquarefreeDensity
open Finset

private theorem square_dvd_mul {q a b : ℕ} (hq : q.Prime) :
    q^2 ∣ a*b ↔ q^2 ∣ a ∨ q^2 ∣ b ∨ q ∣ a ∧ q ∣ b := by
  constructor
  · intro hd
    by_cases ha : q ∣ a
    · by_cases hb : q ∣ b
      · exact Or.inr (Or.inr ⟨ha,hb⟩)
      · exact Or.inl (((hq.coprime_iff_not_dvd.mpr hb).pow_left 2).dvd_of_dvd_mul_right hd)
    · exact Or.inr (Or.inl (((hq.coprime_iff_not_dvd.mpr ha).pow_left 2).dvd_of_dvd_mul_left hd))
  · rintro (h|h|⟨ha,hb⟩)
    · exact dvd_mul_of_dvd_left h b
    · exact dvd_mul_of_dvd_right h a
    · simpa [sq] using Nat.mul_dvd_mul ha hb

/-- A prime square in the product comes from a square at a single site or
from first powers at two distinct sites. Zero term values are allowed. -/
theorem square_dvd_prefix_iff {q : ℕ} (hq : q.Prime) (f : ℕ → ℕ) (k : ℕ) :
    q^2 ∣ ∏ i ∈ range k, f i ↔
      (∃ i < k, q^2 ∣ f i) ∨ ∃ i j, i < j ∧ j < k ∧ q ∣ f i ∧ q ∣ f j := by
  induction k with
  | zero => simp [show ¬q^2 ∣ 1 from fun h =>
      hq.not_dvd_one ((dvd_pow_self q (by decide : 2≠0)).trans h)]
  | succ k ih =>
    rw [prod_range_succ,square_dvd_mul hq,ih]
    constructor
    · rintro ((⟨i,hi,h⟩|⟨i,j,hij,hj,h₁,h₂⟩)|h|⟨ht,hk⟩)
      · exact Or.inl ⟨i,by omega,h⟩
      · exact Or.inr ⟨i,j,hij,by omega,h₁,h₂⟩
      · exact Or.inl ⟨k,by omega,h⟩
      · obtain ⟨i,hi,hd⟩ := (hq.prime.dvd_finsetProd_iff f).mp ht
        exact Or.inr ⟨i,k,mem_range.mp hi,by omega,hd,hk⟩
    · rintro (⟨i,hi,h⟩|⟨i,j,hij,hj,h₁,h₂⟩)
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi|rfl
        · exact Or.inl (Or.inl ⟨i,hi,h⟩)
        · exact Or.inr (Or.inl h)
      · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hj|rfl
        · exact Or.inl (Or.inr ⟨i,j,hij,hj,h₁,h₂⟩)
        · exact Or.inr (Or.inr ⟨(hq.prime.dvd_finsetProd_iff f).mpr ⟨i,mem_range.mpr hij,h₁⟩,h₂⟩)

/-- Once prime-divisible sites form a single residue class modulo d, it suffices
to check the first representative. A second visit makes every lift bad. -/
theorem square_dvd_periodic_prefix_iff {q d : ℕ} (hq : q.Prime) (hd : 0 < d) (f : ℕ → ℕ)
    (hhit : ∀ i j, q ∣ f i → (q ∣ f j ↔ j ≡ i [MOD d])) (k : ℕ) :
    q^2 ∣ ∏ i ∈ range k, f i ↔ ∃ i < min k d,
      q ∣ f i ∧ (i+d < k ∨ q^2 ∣ f i) := by
  rw [square_dvd_prefix_iff hq]
  have hmod (j : ℕ) : j%d ≡ j [MOD d] := Nat.mod_modEq j d
  constructor
  · rintro (⟨j,hj,hsq⟩|⟨j,n,hjn,hn,hj,hn'⟩)
    · have hqj := (dvd_pow_self q (by decide : 2≠0)).trans hsq
      have hqi := (hhit j (j%d) hqj).mpr (hmod j)
      refine ⟨j%d,lt_min ((Nat.mod_le j d).trans_lt hj) (Nat.mod_lt _ hd),hqi,?_⟩
      by_cases small : j < d
      · exact Or.inr (by rwa [Nat.mod_eq_of_lt small])
      · have h := Nat.mod_add_div j d
        have hm := Nat.mul_le_mul_left d (Nat.div_pos (by omega : d ≤ j) hd)
        exact Or.inl (by omega)
    · have he := (hhit j n hj).mp hn'
      have hl : d ≤ n-j := Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' hjn.le).mp he.symm)
      refine ⟨j%d,lt_min ((Nat.mod_le j d).trans_lt (hjn.trans hn)) (Nat.mod_lt _ hd),
        (hhit j (j%d) hj).mpr (hmod j),Or.inl ?_⟩
      have := Nat.mod_le j d
      omega
  · rintro ⟨i,hi,hqi,hs|hs⟩
    · refine Or.inr ⟨i,i+d,by omega,hs,hqi,(hhit i (i+d) hqi).mpr ?_⟩
      simp [Nat.ModEq]
    · exact Or.inl ⟨i,lt_of_lt_of_le hi (min_le_left ..),hs⟩

open SquarefreeSeeds

private theorem two_finite_order {q : ℕ} [Fact q.Prime] (hq : 2 < q) :
    IsOfFinOrder (2 : ZMod q) := by
  have h : (2 : ZMod q) ≠ 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨q-1,by omega,ZMod.pow_card_sub_one_eq_one h⟩

/-- For either recurrence, the indices divisible by an odd prime are empty or
one entire congruence class modulo the order of two. -/
theorem term_dvd_at_iff (first : Bool) {q p i : ℕ} [Fact q.Prime] (hq : 2 < q)
    (hp : 0 < p) (hi : q ∣ term first p i) (j : ℕ) :
    q ∣ term first p j ↔ j ≡ i [MOD orderOf (2 : ZMod q)] := by
  have ht (n : ℕ) : q ∣ term first p n ↔
      (2 : ZMod q)^n * (p - fixed first (ZMod q)) + fixed first (ZMod q) = 0 := by
    rw [← ZMod.natCast_eq_zero_iff, cast_term first hp]
    rfl
  have he := (ht i).mp hi
  have hc : (p : ZMod q) - fixed first (ZMod q) ≠ 0 := by
    intro h
    rw [h,mul_zero,zero_add] at he
    cases first <;> simp [fixed] at he
  rw [ht, ← (two_finite_order hq).pow_eq_pow_iff_modEq]
  constructor
  · intro hj
    apply mul_right_cancel₀ hc
    linear_combination hj - he
  · intro hj
    simpa only [hj] using he

/-- Exact square divisibility of the canonical prefix product at each odd
prime. Only the first visit and the possible first return need inspection. -/
theorem square_dvd_chain_prefix_iff (first : Bool) {q p : ℕ} [Fact q.Prime]
    (hq : 2 < q) (hp : 0 < p) (k : ℕ) :
    q^2 ∣ ∏ i ∈ range k, (if first then firstKindTerm else secondKindTerm) p i ↔
      ∃ i < min k (orderOf (2 : ZMod q)), q ∣ term first p i ∧
        (i + orderOf (2 : ZMod q) < k ∨ q^2 ∣ term first p i) :=
  square_dvd_periodic_prefix_iff (Fact.out : q.Prime) (two_finite_order hq).orderOf_pos
    (term first p) (fun _ j hi => term_dvd_at_iff first hq hp hi j) k

private theorem odd_coprime {q : ℕ} [h : Fact q.Prime] (hq : 2 < q) : Nat.Coprime 2 q :=
  (Nat.coprime_primes Nat.prime_two h.out).mpr (by omega)

private theorem root_lt (first : Bool) {m : ℕ} [NeZero m] (i : ℕ) : root first m i < m :=
  ZMod.val_lt _

private theorem root_zero (first : Bool) (m : ℕ) : root first m 0 = 0 := by
  simp [root]

private theorem same_root_iff (first : Bool) {q : ℕ} [Fact q.Prime] (hq : 2 < q) (i j : ℕ) :
    root first q j = root first q i ↔ j ≡ i [MOD orderOf (2 : ZMod q)] := by
  let a := root first q i + q
  have ha : 0 < a := by dsimp [a]; omega
  have hbase : a ≡ root first q i [MOD q] := by simp [a,Nat.ModEq]
  have hi := (root_iff first ha (odd_coprime hq) i).mpr hbase
  rw [← term_dvd_at_iff first hq ha hi j, root_iff first ha (odd_coprime hq)]
  constructor
  · intro h
    rwa [h]
  · intro h
    exact (h.symm.trans hbase).eq_of_lt_of_lt (root_lt ..) (root_lt ..)

private theorem reduce_root_square (first : Bool) {q : ℕ} [Fact q.Prime] (hq : 2 < q) (i : ℕ) :
    root first (q^2) i ≡ root first q i [MOD q] := by
  let a := root first (q^2) i + q^2
  have ha : 0 < a := by dsimp [a]; positivity
  have hbase : a ≡ root first (q^2) i [MOD q^2] := by simp [a,Nat.ModEq]
  have hd := (root_iff first ha ((odd_coprime hq).pow_right 2) i).mpr hbase
  have hdiv : q ∣ q^2 := dvd_pow_self q (by decide)
  exact (hbase.of_dvd hdiv).symm.trans ((root_iff first ha (odd_coprime hq) i).mp (hdiv.trans hd))

private def lifts (q r : ℕ) : Finset ℕ := (range q).image (fun j => r+q*j)

private theorem mem_lifts {q r x : ℕ} (hq : 0 < q) (hr : r < q) :
    x ∈ lifts q r ↔ x < q^2 ∧ x ≡ r [MOD q] := by
  rw [lifts,mem_image]
  constructor
  · rintro ⟨j,hj,rfl⟩
    have hm := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (mem_range.mp hj))
    rw [Nat.mul_succ] at hm
    exact ⟨by rw [sq]; omega,by simp [Nat.ModEq]⟩
  · rintro ⟨hx,h⟩
    have hm : x%q = r := Eq.trans h (Nat.mod_eq_of_lt hr)
    refine ⟨x/q,mem_range.mpr ((Nat.div_lt_iff_lt_mul hq).mpr (by simpa [sq] using hx)),?_⟩
    rw [←hm,Nat.mod_add_div]

private theorem card_lifts (q r : ℕ) (hq : 0 < q) : (lifts q r).card = q := by
  rw [lifts,card_image_of_injective,card_range]
  intro i j h
  simpa [hq.ne'] using h

private noncomputable def siteLifts (first : Bool) (q k i : ℕ) : Finset ℕ :=
  if i+orderOf (2 : ZMod q) < k then lifts q (root first q i) else {root first (q^2) i}

private theorem mem_siteLifts (first : Bool) {q : ℕ} [Fact q.Prime] (hq : 2 < q) (k i x : ℕ) :
    x ∈ siteLifts first q k i ↔ x < q^2 ∧ x ≡ root first q i [MOD q] ∧
      (i+orderOf (2 : ZMod q) < k ∨ x ≡ root first (q^2) i [MOD q^2]) := by
  by_cases rep : i+orderOf (2 : ZMod q) < k
  · simp [siteLifts,rep,mem_lifts (by omega : 0<q) (root_lt first i)]
  · simp only [siteLifts,rep,if_false,mem_singleton,false_or]
    constructor
    · rintro rfl
      exact ⟨root_lt ..,reduce_root_square first hq i,.rfl⟩
    · rintro ⟨hx,_,h⟩
      exact h.eq_of_lt_of_lt hx (root_lt ..)

/-- Reduced residues modulo q² whose canonical prefix product contains q². -/
def badResidues (first : Bool) (q k : ℕ) : Finset ℕ :=
  (range (q^2)).filter fun x => ¬q ∣ x ∧ q^2 ∣ ∏ i ∈ range k, term first x i

private theorem badResidues_eq (first : Bool) {q : ℕ} [Fact q.Prime] (hq : 2 < q) (k : ℕ) :
    badResidues first q k =
      (Ico 1 (min k (orderOf (2 : ZMod q)))).biUnion (siteLifts first q k) := by
  let d := orderOf (2 : ZMod q)
  have hd : 0 < d := (two_finite_order hq).orderOf_pos
  ext x
  simp only [badResidues,mem_filter,mem_range,mem_biUnion,mem_Ico]
  constructor
  · rintro ⟨hx,hunit,hsq⟩
    have hp : 0 < x := Nat.pos_of_ne_zero (fun h => hunit (h ▸ dvd_zero q))
    obtain ⟨i,hi,hh,hrep⟩ := (square_dvd_chain_prefix_iff first hq hp k).mp hsq
    have hpos : 1 ≤ i := by
      by_contra! h
      obtain rfl : i=0 := by omega
      cases first <;> simp [term,firstKindTerm,secondKindTerm] at hh <;> contradiction
    exact ⟨i,⟨hpos,hi⟩,(mem_siteLifts first hq k i x).mpr ⟨hx,
      (root_iff first hp (odd_coprime hq) i).mp hh,
      hrep.imp_right ((root_iff first hp ((odd_coprime hq).pow_right 2) i).mp)⟩⟩
  · rintro ⟨i,⟨hi,hik⟩,hs⟩
    obtain ⟨hx,hr,hsq⟩ := (mem_siteLifts first hq k i x).mp hs
    have hunit : ¬q ∣ x := by
      intro hz
      have he : root first q i ≡ 0 [MOD q] := hr.symm.trans (Nat.modEq_zero_iff_dvd.mpr hz)
      have he' : root first q i = root first q 0 := by
        rw [root_zero]
        exact he.eq_of_lt_of_lt (root_lt ..) (by omega)
      have he'' := (same_root_iff first hq 0 i).mp he'
      have hi' := hik.trans_le (min_le_right ..)
      exact (by omega : i≠0) (he''.eq_of_lt_of_lt hi' hd)
    have hp : 0 < x := Nat.pos_of_ne_zero (fun h => hunit (h ▸ dvd_zero q))
    refine ⟨hx,hunit,(square_dvd_chain_prefix_iff first hq hp k).mpr ⟨i,hik,
      (root_iff first hp (odd_coprime hq) i).mpr hr,?_⟩⟩
    exact hsq.imp_right ((root_iff first hp ((odd_coprime hq).pow_right 2) i).mpr)

/-- Exact number of reduced bad residues at every odd prime. Each positive
first visit contributes one lift, and each repeated site contributes q−1 extra. -/
theorem card_badResidues_odd (first : Bool) {q : ℕ} [Fact q.Prime] (hq : 2 < q) (k : ℕ) :
    (badResidues first q k).card =
      (min k (orderOf (2 : ZMod q)) - 1) +
      (q-1) * (min (orderOf (2 : ZMod q)) (k-orderOf (2 : ZMod q)) - 1) := by
  classical
  let d := orderOf (2 : ZMod q)
  let S := Ico 1 (min k d)
  have disj : (S : Set ℕ).PairwiseDisjoint (siteLifts first q k) := by
    intro i hi j hj hij
    apply disjoint_left.mpr
    intro x hx hy
    have he := ((mem_siteLifts first hq k i x).mp hx).2.1.symm.trans
      ((mem_siteLifts first hq k j x).mp hy).2.1
    have hr := he.eq_of_lt_of_lt (root_lt ..) (root_lt ..)
    have hm := (same_root_iff first hq j i).mp hr
    exact hij (hm.eq_of_lt_of_lt ((mem_Ico.mp hi).2.trans_le (min_le_right ..))
      ((mem_Ico.mp hj).2.trans_le (min_le_right ..)))
  rw [badResidues_eq first hq,card_biUnion disj]
  have count (i : ℕ) : (siteLifts first q k i).card =
      1 + (q-1) * (if i+d<k then 1 else 0) := by
    change (if i+d<k then lifts q (root first q i) else {root first (q^2) i}).card = _
    by_cases h : i+d<k
    · simp [h,card_lifts _ _ (by omega : 0<q)]
      omega
    · simp [h]
  simp_rw [count]
  rw [sum_add_distrib,← mul_sum,← card_filter]
  have filter_eq : S.filter (fun i => i+d<k) = Ico 1 (min d (k-d)) := by
    ext i
    simp only [mem_filter,S,mem_Ico,lt_min_iff]
    omega
  rw [filter_eq]
  simp [S,d]

/-- The reduced classes at two contain no square obstruction. -/
theorem badResidues_two (first : Bool) (k : ℕ) : badResidues first 2 k = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hm
  obtain ⟨_,hx,hs⟩ := mem_filter.mp hm
  have ho (i : ℕ) : ¬2 ∣ term first x i := by
    cases first
    · induction i with
      | zero => simpa [term,secondKindTerm] using hx
      | succ i ih =>
        simp only [term,Bool.false_eq_true,if_false,secondKindTerm] at ih ⊢
        omega
    · cases i with
      | zero => simpa [term,firstKindTerm] using hx
      | succ i => simp [term,firstKindTerm]
  obtain ⟨i,_,hi⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff (term first x)).mp
    ((by decide : 2 ∣ 2^2).trans hs)
  exact ho i hi

#print axioms card_badResidues_odd
#print axioms badResidues_two
#print axioms term_dvd_at_iff
#print axioms square_dvd_chain_prefix_iff
#print axioms square_dvd_periodic_prefix_iff

#print axioms square_dvd_prefix_iff

end CunninghamChain.SquarefreeDensity
