import Mathlib
import research.arxiv.«1104.1579».CunninghamBrunSieve
import research.arxiv.«1104.1579».CunninghamSelbergSieve

/-!
# Almost-prime values in Cunningham prefixes

The block form of Brun's lower sieve gives a linear bound on the number of
prime factors of each of a fixed collection of admissible linear forms. The
Cunningham application imposes a common proper divisor on the following term.
-/

namespace CunninghamChain

open Finset

/-- Even Bonferroni truncation for a block with `n` forbidden prime hits. -/
private def evenWeight (r n : ℕ) : ℝ :=
  ((∑ i ∈ range (2*r+1), (-1:ℤ)^i * (n.choose i : ℤ) : ℤ) : ℝ)

private lemma evenWeight_zero (r : ℕ) : evenWeight r 0 = 1 := by
  unfold evenWeight
  rw [sum_eq_single 0]
  · norm_num
  · intro j _ hj
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
  · simp

private lemma evenWeight_succ (r n : ℕ) : evenWeight r (n+1) = n.choose (2*r) := by
  simp [evenWeight, Int.alternating_sum_range_choose_eq_choose, pow_mul]

private lemma evenWeight_nonneg (r n : ℕ) : 0 ≤ evenWeight r n := by
  cases n with
  | zero => rw [evenWeight_zero]; norm_num
  | succ n => rw [evenWeight_succ]; positivity

/-- Brun's product lower bound. A missed block is detected by its first omitted
odd intersection count. All the other even truncations are nonnegative. -/
private lemma brun_product_lower {ι : Type*} [DecidableEq ι] (I : Finset ι) (r n : ι → ℕ) :
    (∏ i ∈ I, evenWeight (r i) (n i)) -
      (∑ i ∈ I, ((n i).choose (2*r i+1) : ℝ) *
        ∏ j ∈ I.erase i, evenWeight (r j) (n j)) ≤
      if ∀ i ∈ I, n i = 0 then 1 else 0 := by
  classical
  split_ifs with hall
  · have hp : (∏ i ∈ I, evenWeight (r i) (n i)) = 1 :=
      prod_eq_one fun i hi => by rw [hall i hi, evenWeight_zero]
    rw [hp, sum_eq_zero (fun i hi => by rw [hall i hi]; simp)]
    simp
  · push Not at hall
    obtain ⟨i, hi, hhit⟩ := hall
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hhit
    let W (j : ι) := evenWeight (r j) (n j)
    let E (j : ι) := ((n j).choose (2*r j+1) : ℝ) * ∏ l ∈ I.erase j, W l
    have hdiff : W i ≤ ((n i).choose (2*r i+1) : ℝ) := by
      dsimp [W]; rw [hm, evenWeight_succ, Nat.choose_succ_succ]
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) (m.choose (2*r i+1))]
    have hrest {j : ι} : 0 ≤ ∏ l ∈ I.erase j, W l := prod_nonneg (fun l _ => evenWeight_nonneg _ _)
    have hsum := single_le_sum (s := I) (f := E) (fun j _ => mul_nonneg (Nat.cast_nonneg _) hrest) hi
    have hprod : (∏ j ∈ I, W j) ≤ E i := by
      rw [← mul_prod_erase _ _ hi]
      exact mul_le_mul_of_nonneg_right hdiff hrest
    exact sub_nonpos.mpr (hprod.trans hsum)

/-- To estimate the mean lower polynomial, it suffices to bound the total
relative cost of the omitted odd intersection counts. -/
private lemma brun_product_mass {ι : Type*} [DecidableEq ι] (I : Finset ι) (U E ε : ι → ℝ)
    (hU : ∀ i ∈ I, 0 ≤ U i) (hE : ∀ i ∈ I, E i ≤ ε i * U i) :
    (1 - ∑ i ∈ I, ε i) * (∏ i ∈ I, U i) ≤
      (∏ i ∈ I, U i) - ∑ i ∈ I, E i * ∏ j ∈ I.erase i, U j := by
  rw [sub_mul, one_mul]
  apply sub_le_sub_left
  rw [sum_mul]
  refine sum_le_sum fun i hi => ?_
  rw [← mul_prod_erase I U hi, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hE i hi)
    (prod_nonneg fun j hj => hU j (mem_of_mem_erase hj))

/-- A product of finite linear combinations has interval error bounded by the
product of the local error budgets, provided each choice of one term per block
has the corresponding product error. -/
private lemma block_product_error {ι α : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (F : ι → Finset α) (c μ e : ι → α → ℝ) (v : ι → α → ℕ → ℝ)
    (h : ∀ g ∈ Fintype.piFinset F,
      |(∑ n ∈ range N, ∏ i, v i (g i) n) - N * ∏ i, μ i (g i)| ≤ ∏ i, e i (g i)) :
    |(∑ n ∈ range N, ∏ i, ∑ a ∈ F i, c i a * v i a n) -
      N * (∏ i, ∑ a ∈ F i, c i a * μ i a)| ≤ ∏ i, ∑ a ∈ F i, |c i a| * e i a := by
  classical
  simp_rw [prod_univ_sum]
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun g hg => ?_)
  simp_rw [prod_mul_distrib]
  rw [← mul_sum, mul_left_comm (N : ℝ), ← mul_sub, abs_mul, ← abs_prod]
  exact mul_le_mul_of_nonneg_left (h g hg) (abs_nonneg _)

private noncomputable def intersection (T : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) (n : ℕ) : ℝ :=
  if ∀ q ∈ T, (n : ZMod q) ∈ B q then 1 else 0

private noncomputable def density (B : (q : ℕ) → Finset (ZMod q)) (q : ℕ) : ℝ :=
  ((B q).card : ℝ)/q

private lemma intersection_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) (n : ℕ) :
    (∏ i, intersection (g i) B n) = intersection (univ.biUnion g) B n := by
  classical
  by_cases ha : ∀ i, ∀ q ∈ g i, (n : ZMod q) ∈ B q
  · have hb : ∀ q ∈ univ.biUnion g, (n : ZMod q) ∈ B q := by
      intro q hq
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hq
      exact ha i q hi
    rw [show intersection (univ.biUnion g) B n = 1 from if_pos hb]
    exact prod_eq_one fun i _ => if_pos (ha i)
  · push Not at ha
    obtain ⟨i, q, hq, hn⟩ := ha
    have hi : ¬∀ q ∈ g i, (n : ZMod q) ∈ B q := fun h => hn (h _ hq)
    have hu : ¬∀ q ∈ univ.biUnion g, (n : ZMod q) ∈ B q :=
      fun h => hn (h _ (mem_biUnion.mpr ⟨i, mem_univ _, hq⟩))
    rw [show intersection (univ.biUnion g) B n = 0 from if_neg hu]
    exact prod_eq_zero (mem_univ i) (if_neg hi)

private lemma sum_intersection (N : ℕ) (T : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) :
    ∑ n ∈ range N, intersection T B n =
      (((range N).filter fun n => ∀ q ∈ T, (n : ZMod q) ∈ B q).card : ℝ) := by
  classical simp [intersection, sum_boole]

private lemma mixed_block_error {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (Q : ι → Finset ℕ) (hd : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hp : ∀ i, ∀ q ∈ Q i, q.Prime)
    (F : ι → Finset (Finset ℕ)) (hF : ∀ i, ∀ T ∈ F i, T ⊆ Q i)
    (B : (q : ℕ) → Finset (ZMod q)) (c : ι → Finset ℕ → ℝ) :
    |(∑ n ∈ range N, ∏ i, ∑ T ∈ F i, c i T * intersection T B n) -
      N * (∏ i, ∑ T ∈ F i, c i T * ∏ q ∈ T, density B q)| ≤
      ∏ i, ∑ T ∈ F i, |c i T| * ∏ q ∈ T, ((B q).card : ℝ) := by
  classical
  refine block_product_error N F c _ _ _ (fun g hg => ?_)
  have hs (i : ι) := hF i (g i) (Fintype.mem_piFinset.mp hg i)
  have hd' : (↑(univ : Finset ι) : Set ι).PairwiseDisjoint g :=
    fun i _ j _ hij => (hd hij).mono (hs i) (hs j)
  have hP (q : ℕ) (hq : q ∈ univ.biUnion g) : q.Prime := by
    obtain ⟨i, _, h⟩ := mem_biUnion.mp hq
    exact hp i q (hs i h)
  change |(∑ n ∈ range N, ∏ i, intersection (g i) B n) - _| ≤ _
  simp_rw [intersection_union, sum_intersection]
  rw [← prod_biUnion hd', ← prod_biUnion hd']
  exact (sieve_residue_intersection_count N _ hP B).1

private def selected (Q : Finset ℕ) (r : ℕ) (odd : Bool) : Finset (Finset ℕ) :=
  if odd then Q.powersetCard (2*r+1) else (range (2*r+1)).biUnion fun j => Q.powersetCard j

private def sign (odd : Bool) (T : Finset ℕ) : ℝ := if odd then 1 else (-1)^T.card

private lemma selected_spec {Q T : Finset ℕ} {r : ℕ} {odd : Bool} (hT : T ∈ selected Q r odd) :
    T ⊆ Q ∧ T.card ≤ 2*r+1 := by
  cases odd with
  | false =>
    obtain ⟨j,hj,h⟩ := mem_biUnion.mp hT
    obtain ⟨hs,he⟩ := mem_powersetCard.mp h
    exact ⟨hs, he ▸ (mem_range.mp hj).le⟩
  | true =>
    obtain ⟨h,he⟩ := mem_powersetCard.mp hT
    exact ⟨h,he.le⟩

private noncomputable def loc (Q : Finset ℕ) (r : ℕ) (odd : Bool) (u : Finset ℕ → ℝ) : ℝ :=
  ∑ T ∈ selected Q r odd, sign odd T * u T

private noncomputable def hits (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) (n : ℕ) :=
  Q.filter fun q => (n : ZMod q) ∈ B q

private lemma choose_hits (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) (j n : ℕ) :
    ∑ T ∈ Q.powersetCard j, intersection T B n = ((hits Q B n).card.choose j : ℝ) := by
  classical
  have hf : (Q.powersetCard j).filter (fun T => ∀ q ∈ T, (n : ZMod q) ∈ B q) =
      (hits Q B n).powersetCard j := by
    ext T
    simp only [mem_filter, mem_powersetCard, hits, subset_iff]
    grind
  unfold intersection
  rw [sum_boole, hf, card_powersetCard]

private lemma local_hit_weight (Q : Finset ℕ) (r : ℕ) (odd : Bool)
    (B : (q : ℕ) → Finset (ZMod q)) (n : ℕ) :
    loc Q r odd (fun T => intersection T B n) =
      if odd then ((hits Q B n).card.choose (2*r+1) : ℝ) else evenWeight r (hits Q B n).card := by
  classical
  cases odd with
  | true => simpa [loc, selected, sign] using choose_hits Q B (2*r+1) n
  | false =>
    simp only [loc, selected, sign, Bool.false_eq_true, if_false, evenWeight, Int.cast_sum,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
    rw [sum_biUnion (Q.pairwise_disjoint_powersetCard.set_pairwise _)]
    refine sum_congr rfl fun j hj => ?_
    rw [← choose_hits Q B j n, mul_sum]
    exact sum_congr rfl (fun T hT => by rw [(mem_powersetCard.mp hT).2])

private noncomputable def binMean (Q : Finset ℕ) (r : ℕ) (odd : Bool)
    (B : (q : ℕ) → Finset (ZMod q)) :=
  loc Q r odd (fun T => ∏ q ∈ T, density B q)

private lemma local_error_budget (Q : Finset ℕ) (r z : ℕ) (hz : 0 < z) (odd : Bool)
    (hp : ∀ q ∈ Q, q.Prime ∧ q ≤ z) (B : (q : ℕ) → Finset (ZMod q)) :
    (∑ T ∈ selected Q r odd, |sign odd T| * ∏ q ∈ T, ((B q).card : ℝ)) ≤
      ((z^(2*r+1) : ℕ) : ℝ)^2 := by
  classical
  let S := selected Q r odd
  let Y := z^(2*r+1)
  let m (T : Finset ℕ) := ∏ q ∈ T, q
  have hbound {T : Finset ℕ} (hT : T ∈ S) : m T ≤ Y := by
    obtain ⟨h₁,h₂⟩ := selected_spec hT
    calc
      _ ≤ ∏ _q ∈ T, z := prod_le_prod' fun q hq => (hp q (h₁ hq)).2
      _ = z^T.card := prod_const _
      _ ≤ Y := Nat.pow_le_pow_right hz h₂
  have he {T : Finset ℕ} (hT : T ∈ S) : (m T).primeFactors = T :=
    Nat.primeFactors_prod fun q hq => (hp q ((selected_spec hT).1 hq)).1
  have hcard : S.card ≤ Y := by
    have h := card_le_card_of_injOn m (s := S) (t := Icc 1 Y) (fun T hT => mem_Icc.mpr
      ⟨prod_pos (fun q hq => (hp q ((selected_spec hT).1 hq)).1.pos), hbound hT⟩)
      (fun T hT U hU h => (he hT).symm.trans ((congrArg Nat.primeFactors h).trans (he hU)))
    simpa using h
  have hlocal {T : Finset ℕ} (hT : T ∈ S) :
      (∏ q ∈ T, (B q).card) ≤ Y := by
    refine (prod_le_prod' (s := T) (fun q hq => ?_ : ∀ q ∈ T, (B q).card ≤ q)).trans (hbound hT)
    let : NeZero q := ⟨(hp q ((selected_spec hT).1 hq)).1.ne_zero⟩
    simpa only [ZMod.card] using (B q).card_le_univ
  change (∑ T ∈ S, _) ≤ (Y:ℝ)^2
  calc
    _ ≤ ∑ _T ∈ S, (Y:ℝ) := by
      apply sum_le_sum
      intro T hT
      have hw : |sign odd T| = 1 := by cases odd <;> simp [sign, abs_pow]
      rw [hw, one_mul]
      exact_mod_cast hlocal hT
    _ ≤ _ := by simpa only [sum_const, nsmul_eq_mul, sq] using
                   mul_le_mul_of_nonneg_right (show (S.card:ℝ) ≤ Y by exact_mod_cast hcard) (Nat.cast_nonneg (α := ℝ) Y)

private lemma truncated_interval_error {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (Q : ι → Finset ℕ) (r z : ι → ℕ) (hz : ∀ i, 0 < z i)
    (hd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hp : ∀ i, ∀ q ∈ Q i, q.Prime ∧ q ≤ z i)
    (B : (q : ℕ) → Finset (ZMod q)) (o : ι → Bool) :
    |(∑ n ∈ range N, ∏ i, loc (Q i) (r i) (o i) (fun T => intersection T B n)) -
      N * (∏ i, binMean (Q i) (r i) (o i) B)| ≤
      ∏ i, (((z i)^(2*r i+1) : ℕ) : ℝ)^2 := by
  classical
  have h := mixed_block_error N Q hd (fun i q hq => (hp i q hq).1)
    (fun i => selected (Q i) (r i) (o i)) (fun _ _ hT => (selected_spec hT).1) B (fun i => sign (o i))
  refine h.trans (prod_le_prod (fun i _ => sum_nonneg fun T _ => mul_nonneg (abs_nonneg _) (by positivity))
    (fun i _ => local_error_budget (Q i) (r i) (z i) (hz i) (o i) (hp i) B))

private lemma full_bin_mean (Q : Finset ℕ) (r : ℕ) (odd : Bool)
    (hp : ∀ q ∈ Q, q.Prime) (B : (q : ℕ) → Finset (ZMod q)) :
    let M := ∏ q ∈ Q, q
    (∑ n ∈ range M, loc Q r odd (fun T => intersection T B n)) = M * binMean Q r odd B := by
  classical
  dsimp only
  let M := ∏ q ∈ Q, q
  unfold loc binMean
  simp only [loc]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun T hT => ?_
  obtain ⟨hs,_⟩ := selected_spec hT
  have hm : (∏ q ∈ T, q) ∣ M := Finset.prod_dvd_prod_of_subset T Q id hs
  rw [← mul_sum, sum_intersection, (sieve_residue_intersection_count M T (fun q hq => hp q (hs hq)) B).2 hm]
  dsimp [density]; ring

private lemma survival_le_mean (Q : Finset ℕ) (r : ℕ) (hp : ∀ q ∈ Q, q.Prime)
    (B : (q : ℕ) → Finset (ZMod q)) :
    (∏ q ∈ Q, (1-density B q)) ≤ binMean Q r false B := by
  classical
  let M := ∏ q ∈ Q, q
  let C (q : ℕ) : Finset (ZMod q) := if h : q = 0 then ∅ else
    let : NeZero q := ⟨h⟩
    (B q)ᶜ
  have hC {q : ℕ} (hq : q ∈ Q) (x : ZMod q) : x ∈ C q ↔ x ∉ B q := by
    have hn := (hp q hq).ne_zero
    simp [C, hn]
  have hc {q : ℕ} (hq : q ∈ Q) : ((C q).card:ℝ)/q = 1-density B q := by
    have hn := (hp q hq).ne_zero
    let : NeZero q := ⟨hn⟩
    have hle : (B q).card ≤ q := by simpa [ZMod.card] using (B q).card_le_univ
    simp only [C, dif_neg hn, card_compl, ZMod.card, Nat.cast_sub hle, density]
    field_simp
  have hs (n : ℕ) : intersection Q C n ≤ loc Q r false (fun T => intersection T B n) := by
    rw [local_hit_weight]; simp only [Bool.false_eq_true, if_false]
    by_cases h : ∀ q ∈ Q, (n : ZMod q) ∈ C q
    · have he : hits Q B n = ∅ := filter_eq_empty_iff.mpr fun q hq => (hC hq _).mp (h q hq)
      rw [he, card_empty, evenWeight_zero]; exact (if_pos h).le
    · exact (if_neg h).le.trans (evenWeight_nonneg _ _)
  have hh := sum_le_sum (s := range M) (fun n _ => hs n)
  rw [full_bin_mean Q r false hp B, sum_intersection,
    (sieve_residue_intersection_count M Q hp C).2 (dvd_refl _)] at hh
  rw [prod_congr rfl fun q hq => hc hq] at hh
  exact le_of_mul_le_mul_left hh (by exact_mod_cast prod_pos (fun q hq => (hp q hq).pos) : 0 < (M:ℝ))

private lemma euler_lower {α : Type*} (Q : Finset α) (u : α → ℝ) (K : ℝ)
    (hu : ∀ q ∈ Q, 0 ≤ u q ∧ u q ≤ 1/2) (hs : ∑ q ∈ Q, u q ≤ K) :
    Real.exp (-2*K) ≤ ∏ q ∈ Q, (1-u q) := by
  have hl (q : α) (hq : q ∈ Q) : Real.exp (-(2*u q)) ≤ 1-u q := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have ⟨h₁,h₂⟩ := hu q hq
    have hx := Real.add_one_le_exp (2*u q)
    nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 1-u q by linarith),
      mul_nonneg h₁ (show 0 ≤ 1-2*u q by linarith)]
  calc
    _ ≤ Real.exp (∑ q ∈ Q, -(2*u q)) := by rw [sum_neg_distrib, ← mul_sum]; exact Real.exp_le_exp.mpr (by linarith)
    _ = ∏ q ∈ Q, Real.exp (-(2*u q)) := Real.exp_sum _ _
    _ ≤ _ := prod_le_prod (fun q _ => (Real.exp_pos _).le) hl

private lemma odd_bin_error (Q : Finset ℕ) (r : ℕ) (B : (q : ℕ) → Finset (ZMod q))
    (hp : ∀ q ∈ Q, q.Prime) (K : ℝ) (hu : ∀ q ∈ Q, 0 ≤ density B q ∧ density B q ≤ 1/2)
    (hs : ∑ q ∈ Q, density B q ≤ K) :
    binMean Q r true B ≤ (Real.exp (6*K) / 2^(2*r+1)) * binMean Q r false B := by
  let W := ∏ q ∈ Q, (1-density B q)
  have hW : Real.exp (-2*K) ≤ W := euler_lower Q _ K hu hs
  have hpW : 0 < W := lt_of_lt_of_le (Real.exp_pos _) hW
  have hU : W ≤ binMean Q r false B := survival_le_mean Q r hp B
  have htail := sieve_symmetric_tail_bound Q (density B) (2*r+1)
    (fun q hq => ⟨(hu _ hq).1, (by linarith [(hu _ hq).2])⟩)
  have hE : binMean Q r true B = ∑ T ∈ Q.powersetCard (2*r+1), ∏ q ∈ T, density B q := by
    simp [binMean, loc, selected, sign]
  rw [← hE] at htail
  change 2^(2*r+1)*binMean Q r true B*W^2 ≤ 1 at htail
  have hone : 1 ≤ Real.exp (6*K)*W^3 := by
    calc
      (1:ℝ) = Real.exp (6*K)*Real.exp (-2*K)^3 := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) hW 3) (Real.exp_nonneg _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hU (by positivity))
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  apply le_of_mul_le_mul_right (a := W^2) _ (pow_pos hpW _)
  nlinarith only [htail, hone]

private lemma flagged_product {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Bool → ℝ) (i : ι) :
    (∏ j, A j (decide (j=i))) = A i true * ∏ j ∈ univ.erase i, A j false := by
  rw [← mul_prod_erase _ _ (mem_univ i)]
  simp only [decide_true]
  congr 1
  exact prod_congr rfl (fun j hj => by simp [ne_of_mem_erase hj])

private lemma finite_brun_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ℕ) (Q : ι → Finset ℕ) (r z : ι → ℕ) (hz : ∀ i, 0 < z i)
    (hd : Pairwise fun i j => Disjoint (Q i) (Q j)) (hp : ∀ i, ∀ q ∈ Q i, q.Prime ∧ q ≤ z i)
    (B : (q : ℕ) → Finset (ZMod q)) (ε : ι → ℝ)
    (hU : ∀ i, 0 ≤ binMean (Q i) (r i) false B)
    (hE : ∀ i, binMean (Q i) (r i) true B ≤ ε i * binMean (Q i) (r i) false B) :
    let S := (range N).filter fun n => ∀ i, (hits (Q i) B n).card = 0
    let D := ∏ i, (((z i)^(2*r i+1) : ℕ) : ℝ)^2
    N * ((1 - ∑ i, ε i) * ∏ i, binMean (Q i) (r i) false B) ≤
      (S.card:ℝ) + (Fintype.card ι + 1 : ℝ)*D := by
  classical
  let V (n : ℕ) (i : ι) (o : Bool) := loc (Q i) (r i) o (fun T => intersection T B n)
  let U (i : ι) (o : Bool) := binMean (Q i) (r i) o B
  let D := ∏ i, (((z i)^(2*r i+1) : ℕ) : ℝ)^2
  let up (n : ℕ) := ∏ i, V n i false
  let odd (i : ι) (n : ℕ) := ∏ j, V n j (decide (j=i))
  let main := ∏ i, U i false
  let loss (i : ι) := ∏ j, U j (decide (j=i))
  have hmain : N * main - D ≤ ∑ n ∈ range N, up n := by
    have h := (abs_le.mp (truncated_interval_error N Q r z hz hd hp B (fun _ => false))).1
    change -D ≤ (∑ n ∈ range N, up n) - N * main at h
    linarith
  have hloss (i : ι) : (∑ n ∈ range N, odd i n) ≤ N*loss i + D := by
    have h := (abs_le.mp (truncated_interval_error N Q r z hz hd hp B (fun j => decide (j=i)))).2
    change (∑ n ∈ range N, odd i n) - N*loss i ≤ D at h
    linarith
  have hsum := sum_le_sum (s := univ) (fun i _ => hloss i)
  rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hpoint (n : ℕ) : up n - ∑ i, odd i n ≤ if ∀ i, (hits (Q i) B n).card = 0 then 1 else 0 := by
    dsimp only [up, odd]
    simp_rw [flagged_product (V n), V, local_hit_weight]
    simpa using brun_product_lower univ r (fun i => (hits (Q i) B n).card)
  have hs := sum_le_sum (s := range N) (fun n _ => hpoint n)
  rw [sum_sub_distrib, sum_comm (t := univ), sum_boole] at hs
  have hb := brun_product_mass univ (fun i => U i false) (fun i => U i true) ε (fun i _ => hU i) (fun i _ => hE i)
  have he (i : ι) := flagged_product U i
  change ∀ i, loss i = _ at he
  simp_rw [← he] at hb
  change (1-∑ i, ε i)*main ≤ main-∑ i, loss i at hb
  dsimp only
  change _ ≤ _ + (_+1)*D
  nlinarith only [hmain, hsum, hs, mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) N)]

private def level (H i : ℕ) := H^(2^i)

private lemma level_step (H i : ℕ) : level H (i+1) = (level H i)^2 := by
  simp [level, pow_succ (n := i), pow_mul]

private lemma level_mono {H : ℕ} (hH : 0 < H) : Monotone (level H) :=
  fun _ _ h => Nat.pow_le_pow_right hH (Nat.pow_le_pow_right (by decide) h)

private def band (H i : ℕ) := (level H (i+1)).primesLE \ (level H i).primesLE

private lemma mem_band {H i q : ℕ} :
    q ∈ band H i ↔ q.Prime ∧ level H i < q ∧ q ≤ level H (i+1) := by
  simp only [band, mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hu,hp⟩,hl⟩
    exact ⟨hp,lt_of_not_ge (fun h => hl ⟨h,hp⟩),hu⟩
  · rintro ⟨hp,hl,hu⟩
    exact ⟨⟨hu,hp⟩,fun h => hl.not_ge h.1⟩

private lemma band_cover {H J q : ℕ} (hp : q.Prime) (hlo : H < q) (hhi : q ≤ level H J) :
    ∃ i : Fin J, q ∈ band H i := by
  induction J with
  | zero => simp [level] at hhi; omega
  | succ J ih =>
    by_cases h : level H J < q
    · exact ⟨Fin.last J, mem_band.mpr ⟨hp,h,hhi⟩⟩
    · obtain ⟨i, hi⟩ := ih (by omega)
      exact ⟨i.castSucc, hi⟩

private lemma band_disjoint {H J : ℕ} (hH : 0 < H) :
    Pairwise fun i j : Fin J => Disjoint (band H i) (band H j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro q h₁ h₂
  obtain ⟨_,hl₁,hu₁⟩ := mem_band.mp h₁
  obtain ⟨_,hl₂,hu₂⟩ := mem_band.mp h₂
  rcases lt_or_gt_of_ne hij with h | h
  · exact hl₂.not_ge (hu₁.trans (level_mono hH (show i.val+1 ≤ j.val from h)))
  · exact hl₁.not_ge (hu₂.trans (level_mono hH (show j.val+1 ≤ i.val from h)))

private lemma band_density (H i k : ℕ) (hH : 1 < H) (hkH : 2*k ≤ H)
    (B : (q : ℕ) → Finset (ZMod q)) (hB : ∀ q, q.Prime → H < q → (B q).card ≤ k) :
    (∀ q ∈ band H i, 0 ≤ density B q ∧ density B q ≤ 1/2) ∧
      (∑ q ∈ band H i, density B q) ≤ 4*k := by
  let w := level H i
  let Q := band H i
  have hw : H ≤ w := by simpa [w,level] using level_mono (H := H) (by omega) (Nat.zero_le i)
  have hq {q : ℕ} (hm : q ∈ Q) : q.Prime ∧ w < q ∧ q ≤ w^2 := by
    simpa only [level_step] using mem_band.mp hm
  have hb {q : ℕ} (hm : q ∈ Q) : ((B q).card : ℝ) ≤ k := by
    exact_mod_cast hB q (hq hm).1 (hw.trans_lt (hq hm).2.1)
  have hq0 {q : ℕ} (hm : q ∈ Q) : (0 : ℝ) < q := by exact_mod_cast (hq hm).1.pos
  constructor
  · intro q hm
    have ha := hb hm
    have hq' : (2:ℝ)*k ≤ q := by exact_mod_cast hkH.trans (hw.trans (hq hm).2.1.le)
    exact ⟨div_nonneg (Nat.cast_nonneg _) (hq0 hm).le, (div_le_iff₀ (hq0 hm)).mpr (by linarith)⟩
  · have hwl : 0 < Real.log (w:ℝ) := Real.log_pos (by exact_mod_cast lt_of_lt_of_le hH hw)
    have hl := sieve_sum_log_div_prime_le (w^2) (Nat.pow_pos (Nat.zero_lt_of_lt (hH.trans_le hw))) Q
      (fun q h => ⟨(hq h).1,(hq h).2.2⟩)
    rw [Nat.cast_pow, Real.log_pow] at hl
    have hs : Real.log (w:ℝ) * (∑ q ∈ Q, density B q) ≤
        (k:ℝ) * ∑ q ∈ Q, Real.log q / q := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro q hm
      have hlq := Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hH).trans_le hw : (0:ℝ)<w)
        (by exact_mod_cast (hq hm).2.1.le : (w:ℝ) ≤ q)
      dsimp [density]
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ (hq0 hm).le
      nlinarith only [mul_le_mul hlq (hb hm) (Nat.cast_nonneg _) (hwl.le.trans hlq)]
    apply le_of_mul_le_mul_left (a := Real.log (w:ℝ)) _ hwl
    nlinarith only [hs, mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) k)]

/-- The heavier truncations occur at smaller primes. Summing their log-modulus
budgets costs a constant multiple of the logarithm of the largest sieving prime. -/
private lemma band_degree_sum (R J : ℕ) :
    (∑ i : Fin J, 2^(i.val+1) * (4*(R+i.rev.val+2)+2)) ≤ 2^J*(8*R+28) := by
  induction J generalizing R with
  | zero => simp
  | succ J ih =>
    rw [Fin.sum_univ_castSucc]
    have he (i : Fin J) : (i.castSucc.rev : Fin (J+1)).val = i.rev.val+1 := by
      simp [Fin.rev]; omega
    simp only [Fin.val_castSucc, he, Fin.rev_last, Fin.val_zero, Fin.val_last, add_zero]
    have h := ih (R+1)
    simp_rw [show ∀ i : Fin J, R+(i.rev.val+1)+2 = R+1+i.rev.val+2 by intro i; omega]
    rw [pow_succ]
    nlinarith only [h]

private lemma band_cost (H J R : ℕ) (hH : 0 < H) :
    (∏ i : Fin J, (((level H (i.val+1))^(2*(R+i.rev.val+2)+1) : ℕ) : ℝ)^2) ≤
      ((level H J : ℕ) : ℝ)^(8*R+28) := by
  exact_mod_cast (show (∏ i : Fin J, (level H (i.val+1)^(2*(R+i.rev.val+2)+1))^2) ≤
      (level H J)^(8*R+28) by
    simp only [level, ← pow_mul]
    rw [prod_pow_eq_pow_sum]
    apply Nat.pow_le_pow_right hH
    convert! band_degree_sum R J using 1
    apply sum_congr rfl
    intro i _
    ring)

private lemma geometric_errors (J : ℕ) :
    (∑ i : Fin J, (1:ℝ)/2^(i.rev.val+2)) ≤ 1/2 := by
  have he : (∑ i : Fin J, (1:ℝ)/2^(i.rev.val+2)) = ∑ i : Fin J, (1:ℝ)/2^(i.val+2) :=
    Equiv.sum_comp Fin.revPerm (fun i : Fin J => (1:ℝ)/2^(i.val+2))
  rw [he]
  have h (L : ℕ) : (∑ i ∈ range L, (1:ℝ)/2^(i+2)) = 1/2 - 1/2^(L+1) := by
    induction L with
    | zero => norm_num
    | succ L ih => rw [sum_range_succ, ih, show L+2 = (L+1)+1 by omega, pow_succ]; ring
  rw [Fin.sum_univ_eq_sum_range (fun i => (1:ℝ)/2^(i+2)), h]
  linarith [show 0 ≤ (1:ℝ)/2^(J+1) by positivity]

private lemma sufficient_depth (k : ℕ) : Real.exp (24*k) ≤ (2:ℝ)^(36*k) := by
  apply (Real.log_le_log_iff (Real.exp_pos _) (by positivity)).mp
  rw [Real.log_exp, Real.log_pow]
  push_cast
  have h : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith only [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) k)]

/-- Avoid the forbidden residues of every sieving prime from H through z at a
seed between z and a fixed power of z. The exponent depends only on the number
of forbidden classes allowed at a prime. -/
private lemma rough_parameters (k : ℕ) :
    ∀ H : ℕ, 1 < H → 2*k ≤ H → ∀ B : (q : ℕ) → Finset (ZMod q),
      (∀ q, q.Prime → H < q → (B q).card ≤ k) →
      ∀ X : ℕ, ∃ z n : ℕ, X < z ∧ z < n ∧ n ≤ z^(324*k+32) ∧
        ∀ q : ℕ, q.Prime → H < q → q ≤ z → (n : ZMod q) ∉ B q := by
  classical
  let R := 36*k
  have hR : Real.exp (24*k) ≤ (2:ℝ)^R := sufficient_depth k
  let A := 8*R+28
  intro H hH hkH B hB X
  let J := X+1
  let Z := level H J
  let Q (i : Fin J) := band H i
  let r (i : Fin J) := R+i.rev.val+2
  let z (i : Fin J) := level H (i.val+1)
  let U (i : Fin J) := binMean (Q i) (r i) false B
  let E (i : Fin J) := binMean (Q i) (r i) true B
  let ε (i : Fin J) := (1:ℝ)/2^(i.rev.val+2)
  let N := 8 * Z^R * Z * Z^A
  let S := (range N).filter fun n => ∀ i : Fin J, (hits (Q i) B n).card = 0
  have hZ : 2 ≤ Z := by
    have h := level_mono (H := H) (by omega) (Nat.zero_le J)
    simpa [level, Z] using (le_trans (show 2 ≤ level H 0 by simpa [level] using (show 2 ≤ H by omega)) h)
  have hzJ : 2^J ≤ Z := (Nat.lt_two_pow_self (n := 2^J)).le.trans
    (Nat.pow_le_pow_left hH _)
  have hJZ : J+1 ≤ Z := (show J+1 ≤ 2^J from Nat.lt_two_pow_self).trans hzJ
  have hd := band_disjoint (J := J) (show 0 < H by omega)
  have hhp (i : Fin J) (q : ℕ) (hq : q ∈ Q i) := (mem_band.mp hq).1
  have hb (i : Fin J) := band_density H i k hH hkH B hB
  have hU (i : Fin J) : 1/(2:ℝ)^R ≤ U i := by
    have hp := (euler_lower (Q i) (density B) (4*k) (hb i).1 (hb i).2).trans
      (survival_le_mean (Q i) (r i) (hhp i) B)
    have hR' : Real.exp (2*(4*k)) ≤ (2:ℝ)^R := (Real.exp_le_exp.mpr (by
      linarith [Nat.cast_nonneg (α := ℝ) k])).trans hR
    have h := (one_div_le_one_div_of_le (Real.exp_pos _) hR')
    rw [one_div (Real.exp _), ← Real.exp_neg] at h
    exact h.trans (by simpa only [neg_mul] using hp)
  have hpos (i : Fin J) : 0 ≤ U i := (by positivity : (0:ℝ) ≤ 1/2^R).trans (hU i)
  have hE (i : Fin J) : E i ≤ ε i * U i := by
    refine (odd_bin_error (Q i) (r i) B (hhp i) (4*k) (hb i).1 (hb i).2).trans
      (mul_le_mul_of_nonneg_right ?_ (hpos i))
    dsimp [ε]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc
      _ ≤ 2^R * (2:ℝ)^(i.rev.val+2) := mul_le_mul_of_nonneg_right
        (by rw [show (6:ℝ)*(4*k)=24*k by ring]; exact hR) (by positivity)
      _ ≤ _ := by rw [← pow_add, one_mul]; exact pow_le_pow_right₀ (by norm_num) (by dsimp [r]; omega)
  have hs := finite_brun_lower N Q r z (fun i => by dsimp [z,level]; positivity)
    hd (fun i q hq => ⟨hhp i q hq, (mem_band.mp hq).2.2⟩) B ε hpos hE
  have hcost := band_cost H J R (by omega)
  have hmass : 1/(Z:ℝ)^R ≤ ∏ i, U i := by
    have hb' := prod_le_prod (s := (univ : Finset (Fin J))) (fun _ _ => (by positivity : (0:ℝ)≤1/2^R)) (fun i _ => hU i)
    rw [prod_const, card_univ, Fintype.card_fin, one_div, inv_pow, ← pow_mul, Nat.mul_comm R J, pow_mul] at hb'
    refine le_trans ?_ hb'
    have hZ₀ : 0 < (Z:ℝ) := by exact_mod_cast (by omega : 0<Z)
    rw [one_div, inv_le_inv₀ (pow_pos hZ₀ _) (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hzJ) _
  have hmain : (N:ℝ)*(1/2 * (1/(Z:ℝ)^R)) ≤
      N*((1-∑ i, ε i)*∏ i, U i) := mul_le_mul_of_nonneg_left
    (mul_le_mul (by linarith [geometric_errors J] : (1:ℝ)/2 ≤ 1-∑ i, ε i)
      hmass (by positivity) (by have := geometric_errors J; change 0 ≤ 1-∑ i : Fin J, (1:ℝ)/2^(i.rev.val+2); linarith))
    (Nat.cast_nonneg _)
  dsimp only at hs
  have hs' : (N:ℝ)*((1-∑ i, ε i)*∏ i, U i) ≤ (S.card:ℝ) +
      ((Fintype.card (Fin J):ℝ)+1)*(∏ i : Fin J, (((z i)^(2*r i+1):ℕ):ℝ)^2) := by
    convert! hs using 1
    dsimp only [S]; congr 2
    congr 1
    ext n
    simp only [mem_filter, Q]
  have herr : ((Fintype.card (Fin J):ℝ)+1)*(∏ i : Fin J, (((z i)^(2*r i+1):ℕ):ℝ)^2) ≤
      (Z:ℝ)*(Z:ℝ)^A := by
    exact mul_le_mul (by simpa using (show (J:ℝ)+1 ≤ Z by exact_mod_cast hJZ)) hcost
      (by positivity) (by positivity)
  have hN0 : (N:ℝ)*(1/2 * (1/(Z:ℝ)^R)) = 4*(Z:ℝ)*Z^A := by
    dsimp [N]; push_cast; field_simp; ring
  have hcard : Z+1 < S.card := by
    have h1 : (1:ℝ) ≤ (Z:ℝ)^A := one_le_pow₀ (by exact_mod_cast (by omega : 1≤Z))
    have h2 : (2:ℝ) ≤ Z := by exact_mod_cast hZ
    have h := hmain.trans hs'
    rw [hN0] at h
    exact_mod_cast (by nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) Z)] :
      (Z:ℝ)+1 < S.card)
  obtain ⟨n, hn, hnZ⟩ : ∃ n ∈ S, Z < n := by
    by_contra! h
    have hsub : S ⊆ range (Z+1) := fun n hn => mem_range.mpr (Nat.lt_succ_of_le (h n hn))
    simpa using (not_le_of_gt hcard (by simpa using card_le_card hsub))
  obtain ⟨hnN, hnQ⟩ := mem_filter.mp hn
  have hNL : N ≤ Z^(R+1+A+3) := by
    have h8 : 8 ≤ Z^3 := by simpa using Nat.pow_le_pow_left hZ 3
    simp only [pow_add, pow_one]
    dsimp [N]
    nlinarith only [Nat.mul_le_mul_left (Z^R * Z * Z^A) h8]
  rw [show 324*k+32 = R+1+A+3 by dsimp [A,R]; ring]
  refine ⟨Z,n,by dsimp [J] at hJZ; omega, hnZ, (mem_range.mp hnN).le.trans hNL, ?_⟩
  intro q hp hHq hq hbad
  obtain ⟨i,hi⟩ := band_cover hp hHq hq
  have he := card_eq_zero.mp (hnQ i)
  have hmem : q ∈ hits (Q i) B n := mem_filter.mpr ⟨hi,hbad⟩
  simp [he] at hmem

private lemma rough_factor_count {Z y L : ℕ} (hZ : 1 < Z) (hy : y ≠ 0) (hle : y ≤ Z^L)
    (hrough : ∀ p, p.Prime → p ∣ y → Z < p) : Nat.IsAtMostAlmostPrime L y := by
  refine ⟨hy, ?_⟩
  rw [ArithmeticFunction.cardFactors_apply]
  apply (Nat.pow_le_pow_iff_right hZ).mp
  refine le_trans ?_ hle
  have hl (l : List ℕ) (h : ∀ p ∈ l, Z ≤ p) : Z^l.length ≤ l.prod := by
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.length_cons, List.prod_cons, pow_succ]
      rw [Nat.mul_comm p l.prod]
      exact Nat.mul_le_mul (ih (fun q hq => h q (by simp [hq]))) (h p (by simp))
  refine (hl y.primeFactorsList ?_).trans_eq (Nat.prod_primeFactorsList hy)
  intro p hp
  exact (hrough p (Nat.prime_of_mem_primeFactorsList hp) ((Nat.mem_primeFactorsList_iff_dvd hy
    (Nat.prime_of_mem_primeFactorsList hp)).mp hp)).le

/-- A qualitative Brun sieve for admissible positive-slope linear forms. The factor bound
depends only on the number of forms. Every prescribed finite prime cutoff can be avoided. -/
theorem almostPrime_linear_forms (k : ℕ) :
    ∀ a c : Fin k → ℕ, (∀ i, 0 < a i) →
      (∀ q : ℕ, q.Prime → ∃ t : ℕ, ∀ i, ¬q ∣ a i*t + c i) → ∀ B : ℕ,
      {t : ℕ | ∀ i, Nat.IsAtMostAlmostPrime (324*k+33) (a i*t + c i) ∧
        ∀ p : ℕ, p.Prime → p ∣ a i*t+c i → B < p}.Infinite := by
  classical
  let L := 324*k+32
  have hL := rough_parameters k
  intro a c ha hadm cutoff
  let H := 2*k + 2 + ∑ i, a i
  let P := H.primesLE
  let W := ∏ q ∈ P, q
  have hH : 1 < H := by dsimp [H]; omega
  have hkH : 2*k ≤ H := by dsimp [H]; omega
  have haH (i : Fin k) : a i ≤ H := (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans
    (by dsimp [H]; omega)
  have hP {q} (hq : q ∈ P) : Nat.Prime q := Nat.prime_of_mem_primesLE hq
  have hW : 0 < W := prod_pos fun _ hq => (hP hq).pos
  let g (q : ℕ) := if h : q.Prime then (hadm q h).choose else 0
  have hg {q : ℕ} (hq : q.Prime) : ∀ i, ¬q ∣ a i*g q+c i := by simpa [g,hq] using (hadm q hq).choose_spec
  let b := Nat.chineseRemainderOfFinset g id P (fun _ hq => (hP hq).ne_zero)
    (fun _ hx _ hy hxy => (Nat.coprime_primes (hP hx) (hP hy)).mpr hxy)
  let t (n : ℕ) := W*n + b.val
  have hsmall {q : ℕ} (hq : q.Prime) (hl : q ≤ H) (n : ℕ) (i : Fin k) : ¬q ∣ a i*t n + c i := by
    have hm : q ∈ P := Nat.mem_primesLE.mpr ⟨hl,hq⟩
    have hd : q ∣ W := dvd_prod_of_mem id hm
    have ht : t n ≡ g q [MOD q] := calc
      _ ≡ 0 + b.val [MOD q] := (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hd n)).add_right _
      _ ≡ g q [MOD q] := by simpa using b.property q hm
    exact fun h => hg hq i ((((ht.mul_left (a i)).add_right (c i)).dvd_iff (dvd_refl _)).mp h)
  let bad (q : ℕ) : Finset (ZMod q) :=
    if h : q.Prime then
      letI : Fact q.Prime := ⟨h⟩
      univ.image fun i : Fin k => -((a i*b.val+c i : ℕ) : ZMod q) / ((a i*W : ℕ) : ZMod q)
    else ∅
  have hbad {q : ℕ} (hq : q.Prime) : (bad q).card ≤ k := by
    dsimp only [bad]
    split
    · exact card_image_le.trans_eq (by simp)
    · rename_i h
      exact (h hq).elim
  have hhit {q : ℕ} (hq : q.Prime) (hl : H < q) (i : Fin k) (n : ℕ)
      (hf : q ∣ a i*t n + c i) : (n : ZMod q) ∈ bad q := by
    let : Fact q.Prime := ⟨hq⟩
    have hqW : ¬q ∣ W := hq.prime.not_dvd_finsetProd fun l hl' hdiv =>
      hl.not_ge ((Nat.prime_dvd_prime_iff_eq hq (hP hl')).mp hdiv ▸ Nat.le_of_mem_primesLE hl')
    have hqn : ((a i*W : ℕ) : ZMod q) ≠ 0 :=
      fun h => ((hq.dvd_mul.mp ((ZMod.natCast_eq_zero_iff _ _).mp h)).elim
        (Nat.not_dvd_of_pos_of_lt (ha i) ((haH i).trans_lt hl)) hqW)
    have he : (((a i*W : ℕ) : ZMod q))*n + ((a i*b.val+c i : ℕ) : ZMod q) = 0 := by
      have hh := (ZMod.natCast_eq_zero_iff _ _).mpr hf
      dsimp [t] at hh
      push_cast at hh ⊢; linear_combination hh
    dsimp only [bad]
    split
    case isFalse h => exact (h hq).elim
    refine mem_image.mpr ⟨i,mem_univ _, (div_eq_iff hqn).mpr ?_⟩
    linear_combination -he
  let D := ∑ i, (a i*W + (a i*b.val+c i))
  apply Set.infinite_of_forall_exists_gt
  intro x
  obtain ⟨Z,n,hZ,hn,hnL,hfree⟩ := hL H hH hkH bad (fun _ h _ => hbad h) (x+cutoff+D+2)
  have hZ₁ : 1 < Z := by omega
  have hn₁ : 1 ≤ n := by omega
  have ht₁ : n ≤ t n := (Nat.le_mul_of_pos_left n hW).trans (Nat.le_add_right _ _)
  refine ⟨t n, ?_, by omega⟩
  intro i
  have he : a i*t n + c i = a i*W*n + (a i*b.val + c i) := by dsimp [t]; ring
  have hval : a i*t n + c i ≤ Z^(L+1) := calc
    _ ≤ (a i*W+(a i*b.val+c i))*n := by
      rw [he, Nat.add_mul]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (by omega)) _
    _ ≤ Z*n := Nat.mul_le_mul_right _ (by
      have : a i*W+(a i*b.val+c i) ≤ D := single_le_sum (f := fun j => a j*W+(a j*b.val+c j)) (fun _ _ => Nat.zero_le _) (mem_univ i)
      omega)
    _ ≤ Z^(L+1) := by rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_right _ hnL
  have hr (q : ℕ) (hq : q.Prime) (hd : q ∣ a i*t n+c i) : Z < q := by
    by_contra! hz
    by_cases h : q ≤ H
    · exact hsmall hq h n i hd
    · exact hfree q hq (by omega) hz (hhit hq (by omega) i n hd)
  have ht₀ : 0 < t n := by omega
  exact ⟨rough_factor_count hZ₁ (by have := ha i; positivity) hval hr, fun q hq hd => by
    have := hr q hq hd
    omega⟩

private def chain (b : Bool) : ℕ → ℕ → ℕ := if b then firstKindTerm else secondKindTerm

private lemma chain_ge_two (b : Bool) {p : ℕ} (hp : 2 ≤ p) (i : ℕ) : 2 ≤ chain b p i := by
  cases b <;> induction i with
  | zero => exact hp
  | succ i ih =>
    simp only [chain, Bool.false_eq_true, if_false, if_true, secondKindTerm, firstKindTerm] at ih ⊢
    omega

private lemma chain_grows (b : Bool) {p : ℕ} (hp : 2 ≤ p) : StrictMono (chain b p) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have h := chain_ge_two b hp i
  cases b <;> simp only [chain, Bool.false_eq_true, if_false, if_true, secondKindTerm, firstKindTerm] at h ⊢ <;> omega

private lemma chain_shift (b : Bool) (x p : ℕ) (hp : 2 ≤ p) (i : ℕ) :
    chain b (x+p) i = 2^i*x + chain b p i := by
  induction i with
  | zero => cases b <;> simp [chain, firstKindTerm, secondKindTerm]
  | succ i ih =>
    have hg := chain_ge_two b hp i
    have he : 2^(i+1)*x = 2*(2^i*x) := by rw [pow_succ]; ring
    cases b <;> simp only [chain, Bool.false_eq_true, if_false, if_true] at ih hg ⊢
    · rw [secondKindTerm, secondKindTerm, ih, he]; omega
    · rw [firstKindTerm, firstKindTerm, ih, he]; omega

private def fixedResidue (b : Bool) (q : ℕ) : ZMod q := if b then -1 else 1

private lemma chain_fixed (b : Bool) (q p : ℕ) (hp : 2 ≤ p)
    (h : (p : ZMod q) = fixedResidue b q) (i : ℕ) :
    (chain b p i : ZMod q) = fixedResidue b q := by
  induction i with
  | zero => cases b <;> exact h
  | succ i ih =>
    have hg := chain_ge_two b hp i
    cases b <;> simp only [chain, fixedResidue, Bool.false_eq_true, if_false, if_true] at ih hg ⊢
    · rw [secondKindTerm, Nat.cast_sub (by omega : 1 ≤ 2*secondKindTerm p i)]
      push_cast; rw [ih]; ring
    · rw [firstKindTerm]; push_cast; rw [ih]; ring

/-- A prime at position k can be prescribed as a common divisor of the successor
on one admissible progression of seeds. Only this single linear form uses Dirichlet. -/
private lemma prime_at_length (b : Bool) {k : ℕ} (hk : 0 < k) :
    ∃ p : ℕ, 2 ≤ p ∧ (chain b p k).Prime := by
  have ho : Odd (chain b 2 k) := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have hg := chain_ge_two b (p := 2) (by decide) i
    cases b
    · refine ⟨secondKindTerm 2 i - 1, ?_⟩
      change 2 ≤ secondKindTerm 2 i at hg
      change 2*secondKindTerm 2 i-1 = _
      omega
    · exact ⟨firstKindTerm 2 i, rfl⟩
  obtain ⟨q, hq, hprime, hclass⟩ := Nat.forall_exists_prime_gt_and_modEq (chain b 2 k)
    (pow_ne_zero k (by decide : 2 ≠ 0)) (ho.coprime_two_right.pow_right k)
  obtain ⟨t,ht⟩ := (Nat.modEq_iff_exists_eq_add hq.le).mp hclass.symm
  exact ⟨t+2, by omega, (by rw [chain_shift b _ _ (by decide), Nat.add_comm, ← ht]; exact hprime)⟩

/-- For each fixed positive length, the first k terms can simultaneously avoid every prime
up to an arbitrary cutoff and have boundedly many prime factors, counted with multiplicity.
A fixed prime divides the composite successor on infinitely many such seeds for either kind. -/
theorem infinitely_many_rough_almostPrime_prefixes_with_composite_next (k : ℕ) (hk : 0 < k) :
    ∀ b : Bool, ∃ q : ℕ, q.Prime ∧ ∀ B : ℕ,
      {p : ℕ | 2 ≤ p ∧
        (∀ i < k, let y := (if b then firstKindTerm else secondKindTerm) p i
                  Nat.IsAtMostAlmostPrime (324*k+33) y ∧ ∀ l : ℕ, l.Prime → l ∣ y → B < l) ∧
        q ∣ (if b then firstKindTerm else secondKindTerm) p k ∧
        ¬((if b then firstKindTerm else secondKindTerm) p k).Prime}.Infinite := by
  have hL := almostPrime_linear_forms k
  intro b
  obtain ⟨v,hv,hq⟩ := prime_at_length b hk
  let q := chain b v k
  let a (i : Fin k) := 2^i.val*q
  let c (i : Fin k) := chain b v i.val
  have hq' : q.Prime := hq
  have ha (i : Fin k) : 0 < a i := Nat.mul_pos (by positivity) hq'.pos
  have he (n : ℕ) (i : Fin k) : a i*n+c i = chain b (q*n+v) i := by
    rw [chain_shift b _ _ hv]; dsimp [a,c]; ring
  have hadm (l : ℕ) (hl : l.Prime) : ∃ n : ℕ, ∀ i, ¬l ∣ a i*n + c i := by
    by_cases heq : l = q
    · subst l
      refine ⟨0, fun i => ?_⟩
      simp only [Nat.mul_zero, Nat.zero_add]
      exact Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_of_lt (chain_ge_two b hv i)) (chain_grows b hv i.isLt)
    · let : Fact l.Prime := ⟨hl⟩
      have hunit : (q : ZMod l) ≠ 0 := fun hz => heq ((Nat.prime_dvd_prime_iff_eq hl hq').mp
        ((ZMod.natCast_eq_zero_iff _ _).mp hz))
      obtain ⟨n,hn⟩ := ZMod.natCast_zmod_surjective ((fixedResidue b l - (v : ZMod l)) / (q : ZMod l))
      have hfix : ((q*n+v : ℕ) : ZMod l) = fixedResidue b l := by
        push_cast; rw [hn]; field_simp; ring
      refine ⟨n, ?_⟩
      intro i hdvd
      have hz := (ZMod.natCast_eq_zero_iff _ _).mpr (he n i ▸ hdvd : l ∣ chain b (q*n+v) i)
      rw [chain_fixed b _ _ (by omega) hfix] at hz
      cases b <;> simp [fixedResidue] at hz
  refine ⟨q,hq', ?_⟩
  intro B
  apply Set.infinite_of_forall_exists_gt
  intro x
  obtain ⟨n,hn,hnx⟩ := Set.infinite_iff_exists_gt.mp (hL a c ha hadm B) x
  have hstop : chain b (q*n+v) k = q*(2^k*n+1) := by rw [chain_shift b _ _ hv]; dsimp [q]; ring
  have hn' : 0 < 2^k*n := Nat.mul_pos (by positivity) (by omega)
  refine ⟨q*n+v, ⟨by omega, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    change Nat.IsAtMostAlmostPrime (324*k+33) (chain b (q*n+v) i) ∧ _
    have hi' := hn ⟨i,hi⟩
    change Nat.IsAtMostAlmostPrime (324*k+33) (a ⟨i,hi⟩*n+c ⟨i,hi⟩) ∧
      (∀ l : ℕ, l.Prime → l ∣ a ⟨i,hi⟩*n+c ⟨i,hi⟩ → B < l) at hi'
    rw [he] at hi'
    exact hi'
  · change q ∣ chain b _ k
    rw [hstop]; exact dvd_mul_right _ _
  · change ¬(chain b _ k).Prime
    rw [hstop]; exact Nat.not_prime_mul hq'.ne_one (by omega)
  · have := Nat.le_mul_of_pos_left n hq'.pos
    omega

#print axioms almostPrime_linear_forms
#print axioms infinitely_many_rough_almostPrime_prefixes_with_composite_next

end CunninghamChain
