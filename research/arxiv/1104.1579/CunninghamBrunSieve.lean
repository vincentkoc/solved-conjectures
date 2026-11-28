import Mathlib
import FormalConjectures.Arxiv.«1104.1579».CunninghamChain

/-! Brun's sieve and the reciprocal series of Cunningham chain seeds, for both kinds. -/

namespace CunninghamChain

open Finset

/-- Truncating the inclusion–exclusion sum after an even number of forbidden
conditions gives an upper bound. The next term gives a lower bound. -/
private lemma brun_truncation (n r : ℕ) :
    let S (m : ℕ) := ∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * (n.choose j : ℤ)
    S (2 * r + 1) ≤ (if n = 0 then 1 else 0) ∧
    (if n = 0 then 1 else 0) ≤ S (2 * r) := by
  dsimp only
  cases n with
  | zero =>
    have h (m : ℕ) : (∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * (0 : ℕ).choose j) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
      · simp
    simp [h]
  | succ n =>
    simp only [Int.alternating_sum_range_choose_eq_choose, Nat.succ_ne_zero, if_false]
    simp [pow_add, pow_mul]

private lemma brun_intersections {α : Type*} [DecidableEq α]
    (A Q : Finset α) (h : A ⊆ Q) (j : ℕ) :
    (∑ T ∈ Q.powersetCard j, if T ⊆ A then (1 : ℤ) else 0) = A.card.choose j := by
  have he : (Q.powersetCard j).filter (· ⊆ A) = A.powersetCard j := by
    ext T
    simp only [mem_filter, mem_powersetCard]
    grind [Subset.trans]
  rw [← sum_filter, he]
  simp

private lemma brun_sum_intersections {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset β) (Q : Finset α) (hits : β → Finset α)
    (h : ∀ x ∈ X, hits x ⊆ Q) (m : ℕ) :
    (∑ x ∈ X, ∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * ((hits x).card.choose j : ℤ)) =
      ∑ j ∈ range (m + 1), (-1 : ℤ) ^ j *
        ∑ T ∈ Q.powersetCard j, ((X.filter fun x => T ⊆ hits x).card : ℤ) := by
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum]
  congr 1
  calc
    _ = ∑ x ∈ X, ∑ T ∈ Q.powersetCard j, if T ⊆ hits x then (1 : ℤ) else 0 := by
      exact sum_congr rfl fun x hx => (brun_intersections _ _ (h x hx) j).symm
    _ = _ := by rw [sum_comm]; simp

private lemma single_residue_count (N M : ℕ) [NeZero M] (a : ZMod M) :
    ((range N).filter fun x : ℕ => (x : ZMod M) = a).card =
      N / M + if a.val % M < N % M then 1 else 0 := by
  have h (x : ℕ) : ((x : ZMod M) = a) ↔ x ≡ a.val [MOD M] := by
    simpa using (ZMod.natCast_eq_natCast_iff x a.val M)
  simp_rw [h]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (Nat.pos_of_ne_zero (NeZero.ne M))]

private lemma residue_count_error (N M : ℕ) [NeZero M] (B : Finset (ZMod M)) :
    |(((range N).filter fun x : ℕ => (x : ZMod M) ∈ B).card : ℝ) -
      (N : ℝ) / M * B.card| ≤ B.card := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter (range N) B (fun x : ℕ => (x : ZMod M)), Nat.cast_sum]
  rw [← nsmul_eq_mul', ← sum_const]
  rw [← sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ _ ∈ B, (1 : ℝ) := by
      apply sum_le_sum
      intro a _
      rw [single_residue_count]
      have lower := Nat.cast_div_le (α := ℝ) (m := N) (n := M)
      have upper : (N : ℝ) / M < ((N / M : ℕ) : ℝ) + 1 := by
        apply (div_lt_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M))).2
        have h := Nat.lt_div_mul_add (a := N) (b := M) (Nat.pos_of_ne_zero (NeZero.ne M))
        exact_mod_cast (show N < (N / M + 1) * M by nlinarith)
      split <;> push_cast <;> rw [abs_le] <;> constructor <;> linarith
    _ = _ := by simp

private lemma residue_count_exact (N M : ℕ) [NeZero M] (B : Finset (ZMod M)) (h : M ∣ N) :
    (((range N).filter fun x : ℕ => (x : ZMod M) ∈ B).card : ℝ) = (N : ℝ) / M * B.card := by
  classical
  rw [← sum_card_fiberwise_eq_card_filter (range N) B (fun x : ℕ => (x : ZMod M)), Nat.cast_sum]
  simp_rw [single_residue_count, Nat.mod_eq_zero_of_dvd h, Nat.not_lt_zero, if_false, add_zero]
  simp [Nat.cast_div h (by exact_mod_cast (NeZero.ne M) : (M : ℝ) ≠ 0), mul_comm]

/-- Simultaneous congruence conditions at distinct primes are independent over
one full period, and have discrepancy at most one per allowed residue on a prefix. -/
private lemma crt_count (N : ℕ) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime)
    (B : (q : ℕ) → Finset (ZMod q)) :
    |(((range N).filter fun x => ∀ q ∈ T, (x : ZMod q) ∈ B q).card : ℝ) -
      (N : ℝ) * ∏ q ∈ T, ((B q).card : ℝ) / q| ≤ ∏ q ∈ T, ((B q).card : ℝ) ∧
    ((∏ q ∈ T, q) ∣ N → (((range N).filter fun x => ∀ q ∈ T, (x : ZMod q) ∈ B q).card : ℝ) =
      (N : ℝ) * ∏ q ∈ T, ((B q).card : ℝ) / q) := by
  classical
  let M := ∏ q : T, (q : ℕ)
  have hp : ∀ q : T, 0 < (q : ℕ) := fun q => (hT _ q.2).pos
  have hm : 0 < M := Finset.prod_pos (fun q _ => hp q)
  let : NeZero M := ⟨hm.ne'⟩
  let e := ZMod.prodEquivPi (fun q : T => (q : ℕ)) (fun a b hab =>
    (Nat.coprime_primes (hT _ a.2) (hT _ b.2)).2 fun he => hab (Subtype.ext he))
  let S : Finset (ZMod M) := (Fintype.piFinset (fun q : T => B q)).map e.symm.toEquiv.toEmbedding
  have hS : S.card = ∏ q ∈ T, (B q).card := by
    change (Finset.map _ _).card = _
    rw [Finset.card_map, Fintype.card_piFinset, Finset.prod_coe_sort T (fun i => (B i).card)]
  have hmem (x : ℕ) : (x : ZMod M) ∈ S ↔ ∀ q ∈ T, (x : ZMod q) ∈ B q := by
    change (x : ZMod M) ∈ (Fintype.piFinset _).map e.symm.toEquiv.toEmbedding ↔ _
    rw [Finset.mem_map_equiv]
    change e (x : ZMod M) ∈ Fintype.piFinset _ ↔ _
    rw [Fintype.mem_piFinset, map_natCast]
    exact Subtype.forall
  have hm' : M = ∏ q ∈ T, q := Finset.prod_coe_sort T (fun i => i)
  constructor
  · have H := residue_count_error N M S
    simp_rw [hmem] at H
    rw [hS] at H
    simpa [hm', Finset.prod_div_distrib, div_mul_eq_mul_div, mul_div_assoc, Nat.cast_prod] using H
  · intro h
    have H := residue_count_exact N M S (hm' ▸ h)
    simp_rw [hmem] at H
    rw [hS] at H
    simpa [hm', Finset.prod_div_distrib, div_mul_eq_mul_div, mul_div_assoc, Nat.cast_prod] using H

private noncomputable def hitCount (N : ℕ) (T : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) : ℕ := by
  classical exact ((range N).filter fun x => ∀ q ∈ T, (x : ZMod q) ∈ B q).card

private noncomputable def survivorCount (N : ℕ) (Q : Finset ℕ)
    (B : (q : ℕ) → Finset (ZMod q)) : ℕ := by
  classical exact ((range N).filter fun x => ∀ q ∈ Q, (x : ZMod q) ∉ B q).card

private noncomputable def truncCount (N : ℕ) (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q))
    (m : ℕ) : ℝ := ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j *
      ∑ T ∈ Q.powersetCard j, (hitCount N T B : ℝ)

private lemma count_sandwich (N : ℕ) (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) (r : ℕ) :
    truncCount N Q B (2*r+1) ≤ survivorCount N Q B ∧
      (survivorCount N Q B : ℝ) ≤ truncCount N Q B (2*r) := by
  classical
  let hits (x : ℕ) := Q.filter fun q => (x : ZMod q) ∈ B q
  let S (m x : ℕ) := ∑ j ∈ range (m + 1), (-1 : ℤ) ^ j * ((hits x).card.choose j : ℤ)
  have hsum (m : ℕ) : (∑ x ∈ range N, S m x : ℤ) = truncCount N Q B m := by
    unfold S
    rw [brun_sum_intersections _ _ hits (fun x _ => filter_subset ..)]
    have ht {j : ℕ} {T : Finset ℕ} (hT : T ∈ Q.powersetCard j) :
        ((range N).filter fun x => T ⊆ hits x).card = hitCount N T B := by
      unfold hitCount
      congr 1
      apply filter_congr
      intro x _
      have hsub := (mem_powersetCard.mp hT).1
      exact ⟨fun h q hq => (mem_filter.mp (h hq)).2,
        fun h q hq => mem_filter.mpr ⟨hsub hq, h q hq⟩⟩
    unfold truncCount
    push_cast
    exact sum_congr rfl fun j _ => congrArg _ (sum_congr rfl fun T hT => by rw [ht hT])
  have hmid : (∑ x ∈ range N, (if (hits x).card = 0 then (1 : ℤ) else 0)) = survivorCount N Q B := by
    unfold survivorCount
    simp only [Finset.card_eq_zero, hits, filter_eq_empty_iff]
    rw [← sum_filter]
    simp
  rw [← hsum, ← hsum, ← Int.cast_natCast (R := ℝ) (survivorCount ..), ← hmid]
  exact_mod_cast And.intro
    (sum_le_sum (s := range N) fun x _ => (brun_truncation (hits x).card r).1)
    (sum_le_sum (s := range N) fun x _ => (brun_truncation (hits x).card r).2)

private noncomputable def hitMass (T : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q)) : ℝ :=
  ∏ q ∈ T, ((B q).card : ℝ) / q

private noncomputable def truncMass (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q))
    (m : ℕ) : ℝ := ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j *
      ∑ T ∈ Q.powersetCard j, hitMass T B

private noncomputable def truncError (Q : Finset ℕ) (B : (q : ℕ) → Finset (ZMod q))
    (m : ℕ) : ℝ := ∑ j ∈ range (m + 1), ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, ((B q).card : ℝ)

private lemma trunc_comparison (N : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (B : (q : ℕ) → Finset (ZMod q)) (m : ℕ) :
    |truncCount N Q B m - N * truncMass Q B m| ≤ truncError Q B m ∧
      ((∏ q ∈ Q, q) ∣ N → truncCount N Q B m = N * truncMass Q B m) := by
  classical
  have hcrt {j : ℕ} (T : Finset ℕ) (hT : T ∈ Q.powersetCard j) := crt_count N T
    (fun q hq => hQ q ((mem_powersetCard.mp hT).1 hq)) B
  have rearrange : truncCount N Q B m - N * truncMass Q B m =
      ∑ j ∈ range (m+1), (-1 : ℝ)^j * ∑ T ∈ Q.powersetCard j,
        ((hitCount N T B : ℝ) - N * hitMass T B) := by
    unfold truncCount truncMass
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    rw [mul_left_comm, ← mul_sub, mul_sum, ← sum_sub_distrib]
  rw [rearrange]
  constructor
  · refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun T hT => (hcrt T hT).1)
  · intro h
    apply sub_eq_zero.mp
    rw [rearrange]
    apply sum_eq_zero
    intro j _
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro T hT
    exact sub_eq_zero.mpr ((hcrt T hT).2 ((prod_dvd_prod_of_subset T Q id
      (mem_powersetCard.mp hT).1).trans h))

private lemma exact_survivors (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (B : (q : ℕ) → Finset (ZMod q)) :
    (survivorCount (∏ q ∈ Q, q) Q B : ℝ) = (∏ q ∈ Q, q : ℕ) *
      ∏ q ∈ Q, (1 - ((B q).card : ℝ) / q) := by
  classical
  let C (q : ℕ) : Finset (ZMod q) := ((range q).image fun a : ℕ => (a : ZMod q)) \ B q
  have full (q : ℕ) [NeZero q] : ((range q).image fun a : ℕ => (a : ZMod q)) = univ := by
    refine eq_univ_of_forall fun a => mem_image.mpr ⟨a.val, mem_range.mpr a.val_lt, ?_⟩
    simp
  have hc {q : ℕ} (hq : q ∈ Q) :
      ((C q).card : ℝ) / q = 1 - ((B q).card : ℝ) / q := by
    let : NeZero q := ⟨(hQ q hq).ne_zero⟩
    have hle : (B q).card ≤ q := by simpa [ZMod.card] using (B q).card_le_univ
    simp only [C, full, card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card,
      Nat.cast_sub hle]
    field_simp [(by exact_mod_cast (hQ q hq).ne_zero : (q : ℝ) ≠ 0)]
  have H := (crt_count (∏ q ∈ Q, q) Q hQ C).2 dvd_rfl
  rw [prod_congr rfl fun q hq => hc hq] at H
  convert H using 2
  unfold survivorCount
  congr 1
  apply filter_congr
  intro x _
  apply forall_congr' fun q => forall_congr' fun (hq : q ∈ Q) => ?_
  let : NeZero q := ⟨(hQ q hq).ne_zero⟩
  simp [C, full]


private lemma finite_brun_bound (N : ℕ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (B : (q : ℕ) → Finset (ZMod q)) (r : ℕ) :
    (survivorCount N Q B : ℝ) ≤ N * ((∏ q ∈ Q, (1 - ((B q).card : ℝ) / q)) +
      ∑ T ∈ Q.powersetCard (2*r+1), hitMass T B) + truncError Q B (2*r) := by
  let M := ∏ q ∈ Q, q
  have hM : (0 : ℝ) < M := by exact_mod_cast (Finset.prod_pos (fun q hq => (hQ q hq).pos))
  have hlow := (count_sandwich M Q B r).1
  rw [(trunc_comparison M Q hQ B (2*r+1)).2 dvd_rfl, exact_survivors Q hQ B] at hlow
  have hmain := (le_of_mul_le_mul_left hlow hM)
  have hstep : truncMass Q B (2*r) = truncMass Q B (2*r+1) +
      ∑ T ∈ Q.powersetCard (2*r+1), hitMass T B := by
    simp [truncMass, sum_range_succ, pow_add, pow_mul]
  have hactual := (count_sandwich N Q B r).2
  have herr := (abs_le.mp (trunc_comparison N Q hQ B (2*r)).1).2
  calc
    _ ≤ truncCount N Q B (2*r) := hactual
    _ ≤ N * truncMass Q B (2*r) + truncError Q B (2*r) := by linarith
    _ ≤ _ := by rw [hstep]; gcongr

private lemma euler_harmonic_bound (z : ℕ) :
    (harmonic z : ℝ) * ∏ q ∈ (z+1).primesBelow, (1 - (q : ℝ)⁻¹) ≤ 1 := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n : ℕ => (n : ℝ)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_comm] }
  have hlocal {q : ℕ} (hq : q.Prime) : ‖f q‖ < 1 := by
    change ‖(q : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)
  let emb : Fin z ↪ (z+1).smoothNumbers :=
    ⟨fun i => ⟨(i : ℕ)+1, Nat.mem_smoothNumbers_of_lt (by omega) (by have := i.isLt; omega)⟩,
      fun i j h => Fin.ext (by have := congrArg Subtype.val h; simpa using this)⟩
  have H := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := f) hlocal (z+1)).2
  have h := sum_le_hasSum (univ.map emb) (fun _ _ => (by dsimp [f]; positivity)) H
  have hs : (∑ i ∈ univ.map emb, f (i : ℕ)) = (harmonic z : ℝ) := by
    rw [sum_map]
    change (∑ i : Fin z, (((i : ℕ) + 1 : ℕ) : ℝ)⁻¹) = _
    rw [Finset.sum_fin_eq_sum_range, harmonic]
    push_cast
    exact sum_congr rfl fun i hi => dif_pos (mem_range.mp hi)
  rw [hs] at h
  change _ ≤ ∏ q ∈ (z+1).primesBelow, (1 - (q : ℝ)⁻¹)⁻¹ at h
  rw [Finset.prod_inv_distrib] at h
  have hpos : 0 < ∏ q ∈ (z+1).primesBelow, (1 - (q : ℝ)⁻¹) := by
    apply Finset.prod_pos
    intro q hq
    exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Nat.prime_of_mem_primesBelow hq).one_lt))
  apply (le_div_iff₀ hpos).mp
  simpa [one_div] using h

private lemma odd_local_density (z : ℕ) (hz : 2 ≤ z) :
    (Real.log ((z : ℝ)+1)) ^ 2 *
      ∏ q ∈ (z+1).primesBelow.erase 2, (1 - 2 / (q : ℝ)) ≤ 4 := by
  let Q := (z+1).primesBelow.erase 2
  have hq {q : ℕ} (ha : q ∈ Q) : 2 < q := by
    obtain ⟨hne, hmem⟩ := mem_erase.mp ha
    have := (Nat.prime_of_mem_primesBelow hmem).two_le
    omega
  have htwo : 2 ∈ (z+1).primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, by decide⟩
  have hfac {q : ℕ} (ha : q ∈ Q) : (0 : ℝ) ≤ 1 - 2 / q := by
    have h : (2 : ℝ) < q := by exact_mod_cast hq ha
    have h' : 0 < (q : ℝ) := by linarith
    exact sub_nonneg.mpr ((div_le_one h').mpr h.le)
  have hprod : (∏ q ∈ Q, (1 - 2 / (q : ℝ))) ≤ (∏ q ∈ Q, (1 - (q : ℝ)⁻¹)) ^ 2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod (fun q ha => hfac ha)
    intro q _
    nlinarith [sq_nonneg ((q : ℝ)⁻¹), show 2 / (q : ℝ) = 2 * (q : ℝ)⁻¹ by ring]
  have h := euler_harmonic_bound z
  rw [← Finset.mul_prod_erase _ _ htwo] at h
  change (harmonic z : ℝ) * ((1 - (2 : ℝ)⁻¹) * ∏ q ∈ Q, (1 - (q : ℝ)⁻¹)) ≤ 1 at h
  have hpos : 0 ≤ ∏ q ∈ Q, (1 - (q : ℝ)⁻¹) := by
    apply Finset.prod_nonneg
    intro q ha
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (by exact_mod_cast (hq ha).le.trans' (by decide : 1 ≤ 2)))
  have hl := log_add_one_le_harmonic z
  push_cast at hl
  have hlpos : 0 ≤ Real.log ((z : ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) z])
  calc
    _ ≤ (Real.log ((z : ℝ)+1) * ∏ q ∈ Q, (1 - (q : ℝ)⁻¹)) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hprod (sq_nonneg _)
    _ ≤ 4 := by
      have hh := mul_le_mul_of_nonneg_right hl hpos
      have hu : Real.log ((z : ℝ)+1) * (∏ q ∈ Q, (1 - (q : ℝ)⁻¹)) ≤ 2 := by nlinarith
      nlinarith [mul_nonneg hlpos hpos, mul_nonneg (sub_nonneg.mpr hu)
        (add_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hlpos hpos))]

private lemma select_product {α : Type*} (s : Finset α) (f : α → ℝ) {L : ℝ} (hl : L ≤ 1)
    (hf : ∀ a ∈ s, 1 / 3 ≤ f a) (hs : ∏ a ∈ s, f a ≤ L) :
    ∃ t ⊆ s, L / 3 ≤ ∏ a ∈ t, f a ∧ ∏ a ∈ t, f a ≤ L := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨∅, by simp, by simp; linarith, hs⟩
  | insert a s ha ih =>
    by_cases h : ∏ i ∈ s, f i ≤ L
    · obtain ⟨t, ht, h₁, h₂⟩ := ih (fun i hi => hf i (mem_insert_of_mem hi)) h
      exact ⟨t, ht.trans (subset_insert ..), h₁, h₂⟩
    · refine ⟨insert a s, Subset.rfl, ?_, hs⟩
      rw [prod_insert ha]
      have hpos : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi =>
        (by norm_num : (0 : ℝ) ≤ 1 / 3).trans (hf i (mem_insert_of_mem hi))
      have hh := mul_le_mul_of_nonneg_right (hf a (mem_insert_self ..)) hpos
      linarith [lt_of_not_ge h]

private lemma symmetric_tail {α : Type*} (Q : Finset α) (u : α → ℝ) (j : ℕ)
    (hu : ∀ q ∈ Q, 0 ≤ u q ∧ u q ≤ 1) :
    ((2 : ℝ)^j * (∑ T ∈ Q.powersetCard j, ∏ q ∈ T, u q)) *
      (∏ q ∈ Q, (1-u q))^2 ≤ 1 := by
  classical
  have htail : (2 : ℝ)^j * (∑ T ∈ Q.powersetCard j, ∏ q ∈ T, u q) ≤ ∏ q ∈ Q, (1+2*u q) := by
    rw [prod_one_add, mul_sum]
    calc
      _ = ∑ T ∈ Q.powersetCard j, ∏ q ∈ T, (2 * u q) := by
        apply sum_congr rfl
        intro T hT
        rw [prod_mul_distrib, prod_const, (mem_powersetCard.mp hT).2]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (fun t ht => mem_powerset.mpr (mem_powersetCard.mp ht).1)
        intro T hT _
        exact prod_nonneg fun q hq => mul_nonneg (by norm_num) (hu q (mem_powerset.mp hT hq)).1
  refine (mul_le_mul_of_nonneg_right htail (sq_nonneg _)).trans ?_
  rw [← prod_pow, ← prod_mul_distrib]
  calc
    _ ≤ ∏ _q ∈ Q, (1 : ℝ) := by
      apply prod_le_prod
      · intro q hq
        exact mul_nonneg (by linarith [(hu q hq).1]) (sq_nonneg _)
      · intro q hq
        nlinarith [sq_nonneg (u q), mul_nonneg (sq_nonneg (u q)) (sub_nonneg.mpr (hu q hq).2)]
    _ = _ := by simp

/-- Forbidden seed residues for the first two terms. With `plus = true`
the second term is `2p+1`; otherwise it is `2p-1`. -/
private noncomputable def pairResidues (plus : Bool) (q : ℕ) : Finset (ZMod q) := by
  classical exact {0, if plus then -(2 : ZMod q)⁻¹ else (2 : ZMod q)⁻¹}

private lemma two_nonzero (q : ℕ) (hq : 2 < q) : (2 : ZMod q) ≠ 0 := by
  exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)

private lemma pairResidues_card (b : Bool) {q : ℕ} (hp : q.Prime) (hq : 2 < q) :
    (pairResidues b q).card = 2 := by
  let : Fact q.Prime := ⟨hp⟩
  apply Finset.card_pair
  cases b
  · exact (inv_ne_zero (two_nonzero q hq)).symm
  · exact (neg_ne_zero.mpr (inv_ne_zero (two_nonzero q hq))).symm

private lemma pair_survives (b : Bool) {p q : ℕ} (hp : p.Prime)
    (hnext : (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime)
    (hq : q.Prime) (hsmall : q < p) (hodd : 2 < q) : (p : ZMod q) ∉ pairResidues b q := by
  let : Fact q.Prime := ⟨hq⟩
  have hcast {a : ℕ} (h : a.Prime) (ha : q < a) : (a : ZMod q) ≠ 0 := by
    exact (ZMod.natCast_eq_zero_iff a q).not.mpr fun hd =>
      ha.ne ((Nat.prime_dvd_prime_iff_eq hq h).mp hd)
  have h2 := two_nonzero q hodd
  have h0 := hcast hp hsmall
  have hpos := hp.two_le
  cases b
  · simp only [Bool.false_eq_true, if_false, secondKindTerm] at hnext
    have hn := hcast hnext (by omega)
    intro hx
    have hh : (p : ZMod q) = (2 : ZMod q)⁻¹ := by simpa [pairResidues, h0] using hx
    apply hn
    rw [Nat.cast_sub (by omega : 1 ≤ 2*p), Nat.cast_mul, Nat.cast_two, Nat.cast_one, hh,
      mul_inv_cancel₀ h2, sub_self]
  · simp only [if_true, firstKindTerm] at hnext
    have hn := hcast hnext (by omega)
    intro hx
    have hh : (p : ZMod q) = -(2 : ZMod q)⁻¹ := by simpa [pairResidues, h0] using hx
    apply hn
    push_cast
    rw [hh, mul_neg, mul_inv_cancel₀ h2, neg_add_cancel]

private lemma prefix_sieve (b : Bool) (N z : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q ∧ q ≤ z) :
    (((range N).filter fun p => z < p ∧ p.Prime ∧
      (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime).card : ℝ) ≤
      survivorCount N Q (pairResidues b) := by
  apply Nat.cast_le.mpr
  unfold survivorCount
  apply card_le_card
  intro p hp
  obtain ⟨hi, hz, hprime, hn⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨hi, fun q hq => ?_⟩
  obtain ⟨hq', hodd, hsmall⟩ := hQ q hq
  exact pair_survives b hprime hn hq' (hsmall.trans_lt hz) hodd

private lemma pair_trunc_error (b : Bool) (Q : Finset ℕ) (m z : ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q ∧ q ≤ z) :
    truncError Q (pairResidues b) m ≤ ((m : ℝ)+1) * (2*((z : ℝ)+1)+1)^m := by
  have hsize : Q.card ≤ z+1 := by
    simpa using card_le_card (show Q ⊆ range (z+1) from fun q hq => mem_range.mpr
      (Nat.lt_succ_of_le (hQ q hq).2.2))
  have h (j : ℕ) (T : Finset ℕ) (hT : T ∈ Q.powersetCard j) :
      (∏ q ∈ T, ((pairResidues b q).card : ℝ)) = 2^j := by
    obtain ⟨ht, hc⟩ := mem_powersetCard.mp hT
    calc
      _ = ∏ _q ∈ T, (2 : ℝ) := prod_congr rfl fun q hq =>
        by exact_mod_cast pairResidues_card b (hQ q (ht hq)).1 (hQ q (ht hq)).2.1
      _ = _ := by simp [hc]
  calc
    _ ≤ ∑ _j ∈ range (m+1), (2*((z : ℝ)+1)+1)^m := by
      apply sum_le_sum
      intro j hj
      rw [sum_congr rfl (h j), sum_const, nsmul_eq_mul, card_powersetCard]
      have hchoose : (Q.card.choose j : ℝ) ≤ (Q.card : ℝ)^j := by exact_mod_cast Nat.choose_le_pow Q.card j
      calc
        _ ≤ (Q.card : ℝ)^j * 2^j := by gcongr
        _ = (2*Q.card : ℝ)^j := by ring
        _ ≤ (2*((z : ℝ)+1)+1)^j := by gcongr; exact_mod_cast (by omega : 2*Q.card ≤ 2*(z+1)+1)
        _ ≤ _ := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) z]) (by simpa using mem_range.mp hj)
    _ = _ := by simp

/-- A finite pure-sieve bound for either recurrence. The threshold `L` controls
the density of the retained sieve classes. Terms up to `z` are excluded so a
prime seed or its prime successor cannot equal a sieving prime. -/
private lemma pair_pure_sieve (b : Bool) (N z r : ℕ) (hz : 2 ≤ z) (L : ℝ)
    (hl : 0 < L) (h1 : L ≤ 1) (hlog : 4 ≤ L * (Real.log ((z : ℝ)+1))^2) :
    (((range N).filter fun p => z < p ∧ p.Prime ∧
      (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime).card : ℝ) ≤
      N * (L + 9 / ((2 : ℝ)^(2*r+1) * L^2)) +
        ((2*r : ℕ)+1 : ℝ) * (2*((z : ℝ)+1)+1)^(2*r) := by
  classical
  let P := (z+1).primesBelow.erase 2
  let f (q : ℕ) := 1 - 2 / (q : ℝ)
  have hP {q : ℕ} (hq : q ∈ P) : q.Prime ∧ 2 < q ∧ q ≤ z := by
    obtain ⟨hn, hm⟩ := mem_erase.mp hq
    obtain ⟨hlt, hp⟩ := Nat.mem_primesBelow.mp hm
    exact ⟨hp, by have := hp.two_le; omega, by omega⟩
  have hlower : ∀ q ∈ P, 1 / 3 ≤ f q := by
    intro q hq
    have ha : (3 : ℝ) ≤ q := by exact_mod_cast (hP hq).2.1
    have hpos : (0 : ℝ) < q := by linarith
    dsimp [f]
    have hh : 2 / (q : ℝ) ≤ 2 / 3 := by gcongr
    linarith
  have hfull : ∏ q ∈ P, f q ≤ L := by
    have h := odd_local_density z hz
    change Real.log ((z : ℝ)+1)^2 * (∏ q ∈ P, f q) ≤ 4 at h
    have hpos : 0 < Real.log ((z : ℝ)+1) := Real.log_pos (by exact_mod_cast (by omega : 1 < z+1))
    exact le_of_mul_le_mul_left (h.trans (by linarith)) (sq_pos_of_pos hpos)
  obtain ⟨Q, hQP, hlo, hhi⟩ := select_product P f h1 hlower hfull
  have hQ (q : ℕ) (hq : q ∈ Q) := hP (hQP hq)
  let u (q : ℕ) := ((pairResidues b q).card : ℝ) / q
  have hu {q : ℕ} (hq : q ∈ Q) : u q = 2/(q : ℝ) := by
    simp [u, pairResidues_card b (hQ q hq).1 (hQ q hq).2.1]
  have hV : (∏ q ∈ Q, (1-u q)) = ∏ q ∈ Q, f q :=
    prod_congr rfl fun q hq => by rw [hu hq]
  have hu₀ (q : ℕ) (hq : q ∈ Q) : 0 ≤ u q ∧ u q ≤ 1 := by
    rw [hu hq]
    have h : (2 : ℝ) < q := by exact_mod_cast (hQ q hq).2.1
    exact ⟨by positivity, (div_le_one (by linarith)).mpr h.le⟩
  have ht := symmetric_tail Q u (2*r+1) hu₀
  rw [hV] at ht
  let E := ∑ T ∈ Q.powersetCard (2*r+1), hitMass T (pairResidues b)
  change 2^(2*r+1) * E * (∏ q ∈ Q, f q)^2 ≤ 1 at ht
  have he : 0 ≤ E := sum_nonneg fun T _ => prod_nonneg fun q _ => div_nonneg (by positivity) (by positivity)
  have hsq : (L/3)^2 ≤ (∏ q ∈ Q, f q)^2 := by gcongr
  have hE : E ≤ 9 / ((2 : ℝ)^(2*r+1) * L^2) := by
    apply (le_div_iff₀ (by positivity)).2
    have hh := (mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2^(2*r+1)*E by positivity)).trans ht
    linarith [show E * (2^(2*r+1)*L^2) = 9 * ((2^(2*r+1)*E) * (L/3)^2) by ring]
  have H := finite_brun_bound N Q (fun q hq => (hQ q hq).1) (pairResidues b) r
  change _ ≤ N * ((∏ q ∈ Q, (1-u q)) + E) + _ at H
  rw [hV] at H
  exact (prefix_sieve b N z Q hQ).trans (H.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add hhi hE) (Nat.cast_nonneg N))
    (pair_trunc_error b Q (2*r) z hQ)))

private lemma trunc_exponent {k n : ℕ} (hk : 12 ≤ k) (hn : 8^k ≤ n) :
    (16*(k+1)+1) + (4^k+3)*(16*(k+1)) + 4*k ≤ n := by
  have h : 100*(k+1) ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => decide
    | succ k hk ih => rw [pow_succ]; omega
  have hd : 1 ≤ 4^k := Nat.one_le_pow _ _ (by decide)
  have hprod := Nat.mul_le_mul_left (4^k) h
  have haux := Nat.mul_le_mul_right (k+1) hd
  rw [← mul_pow] at hprod
  norm_num at hprod
  nlinarith

private lemma trunc_scaled {k n : ℕ} (hk : 12 ≤ k) (hn : 8^k ≤ n) :
    ((16*(k+1)+1) * (2*(2^(4^k)+1)+1)^(16*(k+1))) * (4^k)^2 ≤ (2 : ℕ)^n := by
  let s := 16*(k+1)
  have hd : 1 ≤ (2 : ℕ)^(4^k) := Nat.one_le_pow _ _ (by decide)
  have hbase : 2*(2^(4^k)+1)+1 ≤ (2 : ℕ)^(4^k+3) := by rw [pow_add]; omega
  have hfour : ((4 : ℕ)^k)^2 = 2^(4*k) := by
    rw [show (4 : ℕ) = 2^2 by decide, ← pow_mul, ← pow_mul]
    congr 1
    omega
  change ((s+1) * (2*(2^(4^k)+1)+1)^s) * (4^k)^2 ≤ _
  calc
    _ ≤ (2^(s+1) * (2^(4^k+3))^s) * (4^k)^2 := by
      gcongr
      exact Nat.lt_two_pow_self.le
    _ = 2^((s+1) + (4^k+3)*s + 4*k) := by rw [hfour, ← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (trunc_exponent hk hn)

private noncomputable def pairBlock (b : Bool) (n : ℕ) : Finset ℕ :=
  (Ico (2^n) (2^(n+1))).filter fun p => p.Prime ∧
    (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime

private lemma dyadic_pair_bound (b : Bool) {k n : ℕ} (hk : 12 ≤ k) (hn : 8^k ≤ n) :
    ((pairBlock b n).card : ℝ) * ((4 : ℝ)^k)^2 ≤ 35 * (2 : ℝ)^n := by
  let d := (4 : ℕ)^k
  let z := (2 : ℕ)^d
  let r := 8*(k+1)
  let D := (d : ℝ)^2
  have hd : 4 ≤ d := by exact Nat.le_self_pow (by omega) _
  have hz : 2 ≤ z := by exact Nat.le_self_pow (by omega) _
  have hD : 0 < D := by dsimp [D]; positivity
  have hD16 : 16 ≤ D := by dsimp [D]; nlinarith [show (4 : ℝ) ≤ d by exact_mod_cast hd]
  have hlog : 4 ≤ (16/D) * (Real.log ((z : ℝ)+1))^2 := by
    have hz0 : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
    have hlogz := Real.log_le_log hz0 (show (z : ℝ) ≤ z+1 by linarith)
    have hzeq : Real.log (z : ℝ) = (d : ℝ) * Real.log 2 := by simp [z, Real.log_pow]
    rw [hzeq] at hlogz
    have hhalf : (d : ℝ)/2 ≤ Real.log ((z : ℝ)+1) := by
      have hh := mul_le_mul_of_nonneg_left (by linarith [Real.log_two_gt_d9] : (1:ℝ)/2 ≤ Real.log 2)
        (Nat.cast_nonneg (α := ℝ) d)
      linarith
    have hs := sq_le_sq' (by linarith [Nat.cast_nonneg (α := ℝ) d] :
      -Real.log ((z : ℝ)+1) ≤ (d : ℝ)/2) hhalf
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    dsimp [D]
    linarith
  have H := pair_pure_sieve b (2^(n+1)) z r hz (16/D) (by positivity)
    ((div_le_one hD).mpr hD16) hlog
  have hcard : (pairBlock b n).card ≤ ((range (2^(n+1))).filter fun p => z < p ∧ p.Prime ∧
      (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime).card := by
    apply card_le_card
    intro p hp
    obtain ⟨hi, hprop⟩ := mem_filter.mp hp
    obtain ⟨hl, hu⟩ := mem_Ico.mp hi
    refine mem_filter.mpr ⟨mem_range.mpr hu, ?_, hprop⟩
    have hk0 : k ≠ 0 := by omega
    have hh : 4^k < (8 : ℕ)^k := Nat.pow_lt_pow_left (by decide) hk0
    exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (hh.trans_le hn)).trans_le hl
  have htail : 9 / ((2 : ℝ)^(2*r+1) * (16/D)^2) ≤ 1/D := by
    have h6 : D^3 ≤ (2 : ℝ)^(2*r+1) := by
      have hh : D^3 = (2 : ℝ)^(12*k) := by
        dsimp [D, d]
        push_cast
        rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        omega
      rw [hh]
      apply pow_le_pow_right₀ (by norm_num)
      dsimp [r]
      omega
    rw [div_le_div_iff₀ (by positivity) hD]
    field_simp
    nlinarith [show 0 < (2 : ℝ)^(2*r+1) by positivity]
  have herr : (((2*r : ℕ)+1 : ℝ) * (2*((z : ℝ)+1)+1)^(2*r)) * D ≤ (2 : ℝ)^n := by
    have h := trunc_scaled hk hn
    have hr : 2*r = 16*(k+1) := by dsimp [r]; omega
    rw [hr]
    dsimp [D, z, d]
    exact_mod_cast h
  have H' := mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hcard).trans H) hD.le
  have hmain := mul_le_mul_of_nonneg_left (add_le_add (le_refl (16/D)) htail)
    (Nat.cast_nonneg (α := ℝ) (2^(n+1)))
  have h := (mul_le_mul_of_nonneg_right hmain hD.le)
  have hncast : ((2^(n+1) : ℕ) : ℝ) = 2*(2 : ℝ)^n := by push_cast; ring
  rw [hncast] at H' h
  have hclean : (2*(2:ℝ)^n*(16/D+1/D))*D = 34*2^n := by field_simp; ring
  rw [hclean] at h
  rw [add_mul] at H'
  have hh : ((pairBlock b n).card : ℝ) * D ≤ 35*2^n := by linarith only [H', h, herr]
  simpa [D, d] using hh

/-- Group a nonnegative series over consecutive intervals bounded by powers of `c`. -/
private lemma summable_of_power_blocks {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (c : ℕ) (hc : 2 ≤ c)
    (hs : Summable fun j : ℕ => ∑ i ∈ Ico (c^j) (c^(j+1)), f i) : Summable f := by
  let g (j : ℕ) := ∑ i ∈ Ico (c^j) (c^(j+1)), f i
  have hpartial (j : ℕ) : ∑ i ∈ range (c^j), f i = f 0 + ∑ i ∈ range j, g i := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [sum_range_succ, ← add_assoc, ← ih]
      exact (sum_range_add_sum_Ico _ (Nat.pow_le_pow_right (by omega : 0 < c) (Nat.le_succ j))).symm
  apply summable_of_sum_range_le (c := f 0 + ∑' j, g j) hf
  intro n
  have hn : n ≤ c^n := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hc n)
  calc
    _ ≤ ∑ i ∈ range (c^n), f i := sum_le_sum_of_subset_of_nonneg (range_mono hn) (fun i _ _ => hf i)
    _ = _ := hpartial n
    _ ≤ _ := add_le_add (le_refl _) (hs.sum_le_tsum (range n) fun j _ => sum_nonneg fun i _ => hf i)

private noncomputable def pairWeight (b : Bool) (p : ℕ) : ℝ :=
  if p.Prime ∧ (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime then (p : ℝ)⁻¹ else 0

private lemma sum_pairWeight_block (b : Bool) {k n : ℕ} (hk : 12 ≤ k) (hn : 8^k ≤ n) :
    ∑ p ∈ Ico (2^n) (2^(n+1)), pairWeight b p ≤ 35 / ((4 : ℝ)^k)^2 := by
  have h := dyadic_pair_bound b hk hn
  have hsum : ∑ p ∈ Ico (2^n) (2^(n+1)), pairWeight b p =
      ∑ p ∈ pairBlock b n, (p : ℝ)⁻¹ := by simp [pairBlock, pairWeight, sum_filter]
  rw [hsum]
  calc
    _ ≤ ∑ _p ∈ pairBlock b n, ((2 : ℝ)^n)⁻¹ := by
      refine sum_le_sum fun p hp => ?_
      have hh := (mem_Ico.mp (mem_filter.mp hp).1).1
      exact inv_anti₀ (by positivity) (by exact_mod_cast hh)
    _ = ((pairBlock b n).card : ℝ) / 2^n := by simp [div_eq_mul_inv]
    _ ≤ _ := (div_le_div_iff₀ (by positivity) (by positivity)).mpr h

/-- The sum of reciprocal seeds with prime first and second terms converges for
either Cunningham recurrence. The proof uses a finite Brun sieve. -/
theorem summable_prime_pair_reciprocals (b : Bool) :
    Summable fun p : ℕ => if p.Prime ∧
      (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime then (p : ℝ)⁻¹ else 0 := by
  change Summable (pairWeight b)
  have hpos (p : ℕ) : 0 ≤ pairWeight b p := by unfold pairWeight; split <;> positivity
  apply summable_of_power_blocks hpos 2 (by decide)
  let g (n : ℕ) := ∑ p ∈ Ico (2^n) (2^(n+1)), pairWeight b p
  have hg (n : ℕ) : 0 ≤ g n := sum_nonneg fun p _ => hpos p
  change Summable g
  apply summable_of_power_blocks hg 8 (by decide)
  rw [← summable_nat_add_iff 12]
  have geom : Summable fun k : ℕ => (280 : ℝ) * ((1 : ℝ)/2)^k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 280
  apply Summable.of_nonneg_of_le (fun k => sum_nonneg fun n _ => hg n) _ geom
  intro k
  let j := k+12
  have hsum : ∑ n ∈ Ico (8^j) (8^(j+1)), g n ≤
      ∑ _n ∈ Ico (8^j) (8^(j+1)), 35 / ((4 : ℝ)^j)^2 :=
    sum_le_sum fun n hn => sum_pairWeight_block b (by dsimp [j]; omega) (mem_Ico.mp hn).1
  have hcard : (Ico (8^j) (8^(j+1)) : Finset ℕ).card ≤ 8^(j+1) := by simp
  have hbound : (8 : ℝ)^(j+1) * (35 / ((4 : ℝ)^j)^2) = 280*((1 : ℝ)/2)^j := by
    have hp : ((4 : ℝ)^j)^2 = 16^j := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
    rw [pow_succ, hp, show (1:ℝ)/2 = 8/16 by norm_num, div_pow]
    ring
  calc
    _ ≤ _ := hsum
    _ ≤ (8 : ℝ)^(j+1) * (35 / ((4 : ℝ)^j)^2) := by
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := hbound
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (show k ≤ j by dsimp [j]; omega)) (by norm_num)

private lemma exact_one_pair (b : Bool) (p : ℕ) :
    (if b then IsFirstKindChainOfLength p 1 else IsSecondKindChainOfLength p 1) ↔
      p.Prime ∧ ¬(if b then firstKindTerm p 1 else secondKindTerm p 1).Prime := by
  cases b <;> simp [IsFirstKindChainOfLength, IsSecondKindChainOfLength, firstKindTerm, secondKindTerm]

/-- For Jones's exact-length predicates, reciprocal seeds are summable exactly
when the length differs from one. Length zero has no seeds. -/
theorem summable_exact_length_reciprocals_iff (b : Bool) (k : ℕ) :
    Summable (fun p : {p : ℕ // if b then IsFirstKindChainOfLength p k else
      IsSecondKindChainOfLength p k} => (p.val : ℝ)⁻¹) ↔ k ≠ 1 := by
  classical
  let S : Set ℕ := {p | if b then IsFirstKindChainOfLength p k else IsSecondKindChainOfLength p k}
  change Summable ((fun p : ℕ => (p : ℝ)⁻¹) ∘ (Subtype.val : S → ℕ)) ↔ k ≠ 1
  rw [summable_subtype_iff_indicator]
  have hpair : Summable (pairWeight b) := summable_prime_pair_reciprocals b
  constructor
  · intro hex hk
    subst k
    apply not_summable_one_div_on_primes
    apply (hex.add hpair).congr
    intro p
    have hs : p ∈ S ↔ p.Prime ∧ ¬(if b then firstKindTerm p 1 else secondKindTerm p 1).Prime :=
      exact_one_pair b p
    by_cases hp : p.Prime <;>
      by_cases hn : (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime <;>
      simp [hs, hp, hn, pairWeight, one_div]
  · intro hk
    apply hpair.of_nonneg_of_le (fun p => Set.indicator_nonneg (fun _ _ => by positivity) _)
    intro p
    rw [Set.indicator_apply]
    split_ifs with hp
    · have hex : (if b then IsFirstKindChainOfLength p k else IsSecondKindChainOfLength p k) := hp
      have hprime : p.Prime ∧ (if b then firstKindTerm p 1 else secondKindTerm p 1).Prime := by
        cases b
        · change IsSecondKindChainOfLength p k at hex
          exact ⟨hex.2.1 0 hex.1, hex.2.1 1 (by have := hex.1; omega)⟩
        · change IsFirstKindChainOfLength p k at hex
          exact ⟨hex.2.1 0 hex.1, hex.2.1 1 (by have := hex.1; omega)⟩
      simp [pairWeight, hprime]
    · unfold pairWeight
      split <;> positivity

#print axioms summable_prime_pair_reciprocals
#print axioms summable_exact_length_reciprocals_iff

end CunninghamChain
