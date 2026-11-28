import Green50Downsets

/-! # Optimal logarithmic codimension for downward-closed families

Hamming balls give the converse to `Green50Downsets.downward_sum`, even when
translated subspaces are allowed. See `POLYNOMIAL-BOGOLYUBOV.md`.
-/

open Finset
open scoped Pointwise

namespace Green50Sharp

open Green50Downsets

/-- Coordinates at which a binary vector is nonzero. -/
def supp {n : ℕ} (x : Cube n) : Finset (Fin n) := univ.filter fun j => x j ≠ 0

/-- An affine space contains a vector whose Hamming weight is at least its dimension. -/
theorem max_weight {n : ℕ} (W : Submodule (ZMod 2) (Cube n)) (v : Cube n) :
    ∃ y, y ∈ (v +ᵥ (W : Set (Cube n))) ∧ Module.finrank (ZMod 2) W ≤ (supp y).card := by
  classical
  obtain ⟨w, _, hm⟩ := exists_max_image (univ : Finset W) (fun w => (supp (v + w.val)).card)
    ⟨0, mem_univ _⟩
  let y : Cube n := v + w.val
  have hy : y ∈ v +ᵥ (W : Set (Cube n)) := ⟨w.val, w.property, rfl⟩
  let L : W →ₗ[ZMod 2] (supp y → ZMod 2) :=
    (LinearMap.pi (fun j : supp y => LinearMap.proj (R := ZMod 2) j.val)).comp W.subtype
  have hker : ∀ z : W, L z = 0 → z = 0 := by
    intro z hz
    by_contra hne
    have hj : ∃ j, z.val j ≠ 0 := by
      by_contra! ha
      apply hne
      exact Subtype.ext (funext ha)
    obtain ⟨j, hj⟩ := hj
    have hoff (i) (hi : i ∈ supp y) : z.val i = 0 := congrFun hz (⟨i, hi⟩ : supp y)
    have hyj : y j = 0 := by
      by_contra h
      exact hj (hoff j (mem_filter.mpr ⟨mem_univ _, h⟩))
    have hsub : supp y ⊂ supp (y + z.val) := by
      refine Finset.ssubset_iff_of_subset ?_ |>.mpr ?_
      · exact fun i hi => mem_filter.mpr ⟨mem_univ _, by
          simpa [Pi.add_apply, hoff i hi] using (mem_filter.mp hi).2⟩
      · exact ⟨j, by simpa [supp, Pi.add_apply, hyj] using hj, by simp [supp, hyj]⟩
    have h := hm (w + z) (mem_univ _)
    have h' := card_lt_card hsub
    change (supp (v + (w.val + z.val))).card ≤ (supp y).card at h
    apply h'.not_ge
    simpa only [y, add_assoc] using h
  have hi : Function.Injective L := (injective_iff_map_eq_zero L).mpr hker
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  refine ⟨y, hy, ?_⟩
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] using hh

/-- The binary Hamming ball of radius `k` centered at zero. -/
def ball (n k : ℕ) : Finset (Cube n) := univ.filter (fun x => (supp x).card ≤ k)

private theorem weight_add {n : ℕ} (x y : Cube n) :
    (supp (x + y)).card ≤ (supp x).card + (supp y).card := by
  apply le_trans (card_le_card (t := supp x ∪ supp y) ?_) (card_union_le _ _)
  intro i hi
  simp only [supp, mem_union, mem_filter, mem_univ, true_and, Pi.add_apply] at hi ⊢
  by_contra! h
  simp [h.1, h.2] at hi

private theorem weight_of_mem_sum {n k r : ℕ} {y : Cube n} (hy : y ∈ r • ball n k) :
    (supp y).card ≤ r * k := by
  induction r generalizing y with
  | zero =>
    simp only [zero_nsmul, Finset.mem_zero] at hy
    simp [hy, supp]
  | succ r ih =>
    rw [succ_nsmul, Finset.mem_add] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    have h₁ := ih ha
    have h₂ := (mem_filter.mp hb).2
    simpa only [Nat.succ_mul] using (weight_add a b).trans (Nat.add_le_add h₁ h₂)

/-- Every affine flat in the `r`-fold sum of a radius-`k` ball has dimension at most `r*k`. -/
theorem ball_dimension {n k r : ℕ} (W : Submodule (ZMod 2) (Cube n)) (v : Cube n)
    (h : v +ᵥ (W : Set (Cube n)) ⊆ (↑(r • ball n k) : Set (Cube n))) :
    Module.finrank (ZMod 2) W ≤ r * k := by
  obtain ⟨y, hy, hw⟩ := max_weight W v
  exact hw.trans (weight_of_mem_sum (h hy))

private theorem weight_cons {n : ℕ} (b : ZMod 2) (x : Cube n) :
    (supp (Fin.cons b x)).card = (if b = 0 then 0 else 1) + (supp x).card := by
  simp [supp, card_filter, Fin.sum_univ_succ]

/-- The Hamming weight generating function for the binary cube. -/
theorem weight_polynomial (n : ℕ) (t : ℝ) :
    ∑ x : Cube n, t ^ (supp x).card = (1 + t) ^ n := by
  induction n with
  | zero => simp [Cube, supp]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2)
    rw [← Equiv.sum_comp e (fun x => t ^ (supp x).card), Fintype.sum_prod_type]
    have two : (univ : Finset (ZMod 2)) = {0, 1} := by decide
    simp only [two, sum_insert (by decide : (0 : ZMod 2) ∉ ({1} : Finset _)), sum_singleton]
    change (∑ x : Cube n, t ^ (supp (Fin.cons 0 x)).card) +
      (∑ x : Cube n, t ^ (supp (Fin.cons 1 x)).card) = _
    simp [weight_cons, pow_add, ← mul_sum, ih, pow_succ]
    ring

/-- The logarithmic codimension bound on all Hamming balls forces the base condition. -/
theorem necessary (r : ℕ) {c : ℝ} (hc : 1 < c) (N : ℕ)
    (h : ∀ n ≥ N, ∀ k, ∃ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
      v +ᵥ (W : Set (Cube n)) ⊆ (↑(r • ball n k) : Set (Cube n)) ∧
      (n : ℝ) - Real.logb c (1 / ((ball n k).dens : ℝ)) ≤ Module.finrank (ZMod 2) W) :
    c⁻¹ ^ r ≤ 2 * c⁻¹ - 1 := by
  classical
  have hcp : 0 < c := by linarith
  let t := c⁻¹ ^ r
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have spec (n : ℕ) (hn : N ≤ n) (k : ℕ) : ((ball n k).card : ℝ) / c ^ (r * k) ≤ (2 / c) ^ n := by
    obtain ⟨W, v, hW, hdim⟩ := h n hn k
    have dim : (Module.finrank (ZMod 2) W : ℝ) ≤ (r * k : ℕ) := by
      exact_mod_cast ball_dimension W v hW
    have hne : (ball n k).Nonempty := ⟨0, by simp [ball, supp]⟩
    have da : ((ball n k).dens : ℝ) = ((ball n k).card : ℝ) / 2 ^ n := by
      simp [Finset.dens, Cube, Fintype.card_pi]
    have hpos : 0 < ((ball n k).dens : ℝ) := by
      rw [da]; exact div_pos (by exact_mod_cast card_pos.mpr hne) (by positivity)
    have hrk : (n : ℝ) - (r * k : ℕ) ≤ Real.logb c (1 / ((ball n k).dens : ℝ)) := by linarith
    have hp := (Real.le_logb_iff_rpow_le hc (div_pos one_pos hpos)).mp hrk
    rw [Real.rpow_sub hcp, Real.rpow_natCast, Real.rpow_natCast] at hp
    have hh := (div_le_div_iff₀ (pow_pos hcp _) hpos).mp hp
    rw [da] at hh
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hcp _) (pow_pos hcp _)).mpr
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    field_simp [h2.ne'] at hh
    linarith
  have poly (n : ℕ) (hn : N ≤ n) : (1 + t) ^ n ≤ (n + 1 : ℝ) * (2 / c) ^ n := by
    rw [← weight_polynomial]
    let S (k : ℕ) := (univ : Finset (Cube n)).filter (fun x => (supp x).card = k)
    have mem (x : Cube n) (_ : x ∈ univ) : (supp x).card ∈ range (n + 1) := by
      have := card_le_univ (supp x)
      simpa using (Nat.lt_succ_of_le (by simpa using this : (supp x).card ≤ n))
    rw [← sum_fiberwise_of_maps_to mem]
    calc
      _ ≤ ∑ k ∈ range (n + 1), (2 / c) ^ n := by
        apply sum_le_sum
        intro k _
        have hsub : S k ⊆ ball n k := fun x hx => mem_filter.mpr
          ⟨mem_univ _, le_of_eq (mem_filter.mp hx).2⟩
        calc
          _ = ∑ _x ∈ S k, t ^ k := sum_congr rfl (fun x hx => by rw [(mem_filter.mp hx).2])
          _ = ((S k).card : ℝ) / c ^ (r * k) := by
            simp [t, ← pow_mul, inv_pow, div_eq_mul_inv]
          _ ≤ ((ball n k).card : ℝ) / c ^ (r * k) := by
            gcongr
          _ ≤ _ := spec n hn k
      _ = _ := by simp
  let z := (1 + t) / (2 / c)
  have hz (n : ℕ) (hn : N ≤ n) : z ^ n ≤ n + 1 := by
    dsimp [z]
    rw [div_pow]
    exact (div_le_iff₀ (by positivity)).mpr (poly n hn)
  have hz1 : z ≤ 1 := by
    by_contra! hn
    have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hn
    have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hn
    have limit : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) / z ^ n) Filter.atTop (nhds 0) := by
      simpa only [pow_one, pow_zero, ← add_div, add_zero] using h₁.add h₀
    obtain ⟨n, hnN, hh⟩ := ((Filter.eventually_ge_atTop N).and
      (limit.eventually_lt_const (show (0 : ℝ) < 1 by norm_num))).exists
    exact (not_lt_of_ge (hz n hnN)) (by simpa only [one_mul] using (div_lt_iff₀ (pow_pos (by linarith : 0 < z) n)).mp hh)
  have hb := (div_le_one (show (0 : ℝ) < 2 / c by positivity)).mp hz1
  change t ≤ 2 * c⁻¹ - 1
  rw [div_eq_mul_inv] at hb
  linarith

/-- The Green 50 codimension bound in base c, restricted to downward-closed sets.
The translate is free to vary. -/
def DownsetBound (r : ℕ) (c : ℝ) : Prop :=
  ∀ n (A : Finset (Cube n)), A.Nonempty → Green50Downsets.Downward A →
    ∃ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
      v +ᵥ (W : Set (Cube n)) ⊆ (↑(r • A) : Set (Cube n)) ∧
      (n : ℝ) - Real.logb c (1 / (A.dens : ℝ)) ≤ Module.finrank (ZMod 2) W

private theorem ball_nonempty (n k : ℕ) : (ball n k).Nonempty := ⟨0, by simp [ball, supp]⟩

private theorem ball_downward (n k : ℕ) : Green50Downsets.Downward (ball n k) := by
  intro x hx y hxy
  have hsub : supp y ⊆ supp x := fun j hj => mem_filter.mpr ⟨mem_univ _, hxy j (mem_filter.mp hj).2⟩
  exact mem_filter.mpr ⟨mem_univ _, (card_le_card hsub).trans (mem_filter.mp hx).2⟩

/-- Hamming balls already force the complete range of bases, even for translated flats. -/
theorem sharp_iff {r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 1 < c) :
    DownsetBound r c ↔ c⁻¹ ^ r ≤ 2 * c⁻¹ - 1 := by
  refine ⟨fun h => necessary r hc 0 (fun n _ k => h n _ (ball_nonempty n k) (ball_downward n k)), ?_⟩
  intro h n A hne ha
  obtain ⟨W, hw, hd⟩ := Green50Downsets.downward_sum hr hc h A hne ha
  exact ⟨W, 0, by simpa only [zero_vadd] using hw, hd⟩

/-- Every inadmissible base fails in unbounded dimensions on Hamming balls. -/
theorem large_ball_counterexamples {r : ℕ} {c : ℝ} (hc : 1 < c)
    (hroot : 2 * c⁻¹ - 1 < c⁻¹ ^ r) (N : ℕ) :
    ∃ n ≥ N, ∃ k, ∀ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
      v +ᵥ (W : Set (Cube n)) ⊆ (↑(r • ball n k) : Set (Cube n)) →
      (Module.finrank (ZMod 2) W : ℝ) < (n : ℝ) - Real.logb c (1 / ((ball n k).dens : ℝ)) := by
  by_contra! h
  exact hroot.not_ge (necessary r hc N h)

private theorem logb_change {C : ℝ} (hC : 0 < C) (x : ℝ) :
    Real.logb ((2 : ℝ) ^ C⁻¹) x = C * Real.logb 2 x := by
  rw [Real.logb, Real.logb, Real.log_rpow (by norm_num)]
  field_simp [hC.ne', (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne']

/-- Every fixed coefficient in a two-summand, base-two bound fails on arbitrarily large balls. -/
theorem two_summands_fail {C : ℝ} (hC : 0 < C) (N : ℕ) :
    ∃ n ≥ N, ∃ k, ∀ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
      v +ᵥ (W : Set (Cube n)) ⊆ (↑((2 : ℕ) • ball n k) : Set (Cube n)) →
      (Module.finrank (ZMod 2) W : ℝ) < (n : ℝ) - C * Real.logb 2 (1 / ((ball n k).dens : ℝ)) := by
  let c := (2 : ℝ) ^ C⁻¹
  have hc : 1 < c := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hC)
  have hx : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  have root : 2 * c⁻¹ - 1 < c⁻¹ ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hx.ne)]
  simpa only [c, logb_change hC] using large_ball_counterexamples hc root N

/-- The best base for ten summands lies in this interval of width one millionth. -/
theorem tenfold_bracket :
    DownsetBound 10 (1998029 / 1000000) ∧ ¬ DownsetBound 10 (1998030 / 1000000) := by
  rw [sharp_iff (by norm_num) (by norm_num), sharp_iff (by norm_num) (by norm_num)]
  norm_num

/-- Every coefficient in the unrestricted ten-summand statement must pass the same numerical test. -/
theorem necessary_for_green50 {C : ℝ} (hC : 0 < C)
    (h : ∀ n (A : Finset (Cube n)), A.Nonempty →
      ∃ (W : Submodule (ZMod 2) (Cube n)) (v : Cube n),
        v +ᵥ (W : Set (Cube n)) ⊆ (↑((10 : ℕ) • A) : Set (Cube n)) ∧
        (n : ℝ) - C * Real.logb 2 (1 / (A.dens : ℝ)) ≤ Module.finrank (ZMod 2) W) :
    let c := (2 : ℝ) ^ C⁻¹
    c⁻¹ ^ 10 ≤ 2 * c⁻¹ - 1 := by
  apply (sharp_iff (by norm_num) (Real.one_lt_rpow (by norm_num) (inv_pos.mpr hC))).mp
  intro n A hne _
  simpa only [logb_change hC] using h n A hne

#print axioms max_weight
#print axioms ball_dimension
#print axioms weight_polynomial
#print axioms necessary
#print axioms sharp_iff
#print axioms large_ball_counterexamples
#print axioms two_summands_fail
#print axioms tenfold_bracket
#print axioms necessary_for_green50

end Green50Sharp