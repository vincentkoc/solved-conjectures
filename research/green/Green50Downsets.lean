import Mathlib

/-! # Green 50 for downward-closed families in the binary cube

The bound on uncovered coordinates is related to Frankl’s estimates for families
with restricted unions. See `POLYNOMIAL-BOGOLYUBOV.md` for statements and references.
-/

open Finset

namespace Green50Downsets

private theorem tradeoff {c t : ℝ} {r : ℕ} (hr : 0 < r) (hc : 1 < c)
    (hroot : (c⁻¹) ^ r ≤ 2 * c⁻¹ - 1) (ht : 1 ≤ t) (htc : t ≤ c) :
    1 ≤ t ^ (r - 1) * (2 - t) := by
  let g (u : ℝ) := u ^ r - 2 * u + 1
  have hg : ConvexOn ℝ (Set.Ici 0) g := by
    refine ⟨convex_Ici _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := (convexOn_pow (𝕜 := ℝ) r).2 hx hy ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    dsimp [g]
    linarith
  have hcp : 0 < c := by linarith
  have htp : 0 < t := by linarith
  have hc1 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc.le
  have hmem : t⁻¹ ∈ segment ℝ c⁻¹ 1 := by
    rw [segment_eq_Icc hc1]
    exact ⟨inv_anti₀ htp htc, inv_le_one_of_one_le₀ ht⟩
  have hbound := hg.le_on_segment (show 0 ≤ c⁻¹ from (inv_pos.mpr hcp).le)
    (show (0 : ℝ) ≤ 1 by norm_num) hmem
  have h0 : g 1 = 0 := by norm_num [g]
  have hc0 : g c⁻¹ ≤ 0 := by dsimp [g]; linarith
  rw [h0, max_eq_right hc0] at hbound
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  dsimp [g] at hbound
  rw [inv_pow] at hbound
  have hm : (t ^ (k + 1))⁻¹ ≤ 2 * t⁻¹ - 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ t ^ (k + 1) by positivity)
  rw [inv_mul_cancel₀ (pow_ne_zero _ htp.ne')] at hh
  have he : (2 * t⁻¹ - 1) * t ^ (k + 1) = t ^ k * (2 - t) := by
    rw [pow_succ]
    field_simp [htp.ne']
  simpa only [he, Nat.succ_sub_one] using hh

/-- For binary marginal splits with an admissible base, either one can cover
this coordinate without losing product density, or omitting it gains a fixed factor
in the product. The entries are twice the probabilities of omission. -/
theorem choose_slices {r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 1 < c)
    (hroot : c⁻¹ ^ r ≤ 2 * c⁻¹ - 1) (a : Fin r → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, a i ≤ 2) :
    (∃ b : Fin r → Bool, (∃ i, b i = false) ∧
      1 ≤ ∏ i, if b i then a i else 2 - a i) ∨ c ^ r ≤ ∏ i, a i := by
  classical
  by_cases h : ∃ i, a i ≤ 1
  · obtain ⟨i, hi⟩ := h
    refine Or.inl ⟨fun j => decide (1 < a j), ⟨i, by simp [not_lt.mpr hi]⟩, ?_⟩
    have hstep (j : Fin r) : 1 ≤ if decide (1 < a j) then a j else 2 - a j := by
      by_cases h : 1 < a j <;> simp [h] <;> linarith
    simpa only [prod_const_one] using
      (prod_le_prod (s := (univ : Finset (Fin r))) (f := fun _ => (1 : ℝ))
        (fun _ _ => zero_le_one) (fun j _ => hstep j))
  push Not at h
  by_cases hh : ∀ i, c ≤ a i
  · right
    simpa only [prod_const, card_univ, Fintype.card_fin] using (prod_le_prod (s := (univ : Finset (Fin r)))
      (f := fun _ => c) (fun _ _ => by linarith) (fun i _ => hh i))
  push Not at hh
  obtain ⟨j, hj⟩ := hh
  obtain ⟨i, _, hi⟩ := exists_min_image (univ : Finset (Fin r)) a ⟨j, mem_univ _⟩
  have hm : a i < c := (hi j (mem_univ _)).trans_lt hj
  let b (k : Fin r) := decide (k ≠ i)
  refine Or.inl ⟨b, ⟨i, by simp [b]⟩, ?_⟩
  let f (k : Fin r) := if b k then a k else 2 - a k
  change 1 ≤ ∏ k, f k
  rw [← prod_erase_mul univ f (mem_univ i)]
  have hf : f i = 2 - a i := by simp [f, b]
  rw [hf]
  have hprod : (a i) ^ (r - 1) ≤ ∏ k ∈ univ.erase i, f k := by
    have := prod_le_prod (s := univ.erase i) (f := fun _ => a i) (g := f)
      (fun _ _ => ha i) (fun k hk => by simpa [f, b, ne_of_mem_erase hk] using hi k (mem_univ _))
    simpa using this
  have hl := tradeoff hr hc hroot (h i).le hm.le
  exact hl.trans (mul_le_mul_of_nonneg_right hprod (sub_nonneg.mpr (hb i)))

#print axioms choose_slices

abbrev Cube (n : ℕ) := Fin n → ZMod 2

private def slice {n : ℕ} (A : Finset (Cube (n + 1))) (b : ZMod 2) : Finset (Cube n) :=
  univ.filter fun x => Fin.cons b x ∈ A

private theorem slice_card {n : ℕ} (A : Finset (Cube (n + 1))) :
    (slice A 0).card + (slice A 1).card = A.card := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => ZMod 2)
  have eqf (b : ZMod 2) : (slice A b).card =
      ∑ x : Cube n, if e (b, x) ∈ A then 1 else 0 := by
    exact Finset.card_filter _ _
  have two (f : ZMod 2 → ℕ) : f 0 + f 1 = ∑ b, f b := by
    rw [show (univ : Finset (ZMod 2)) = {0, 1} from by decide]
    simp
  rw [eqf, eqf, two (fun b : ZMod 2 => ∑ x : Cube n, if e (b, x) ∈ A then 1 else 0)]
  calc
    _ = ∑ p : ZMod 2 × Cube n, if e p ∈ A then (1 : ℕ) else 0 := (Fintype.sum_prod_type _).symm
    _ = ∑ y : Cube (n + 1), if y ∈ A then (1 : ℕ) else 0 :=
      Equiv.sum_comp e (fun y => if y ∈ A then (1 : ℕ) else 0)
    _ = _ := by simp

private def holes {r n : ℕ} (x : Fin r → Cube n) : ℕ :=
  (univ.filter fun j => ∀ i, x i j = 0).card

private theorem holes_cons {r n : ℕ} (b : Fin r → ZMod 2) (y : Fin r → Cube n) :
    holes (fun i => Fin.cons (b i) (y i)) = (if ∀ i, b i = 0 then 1 else 0) + holes y := by
  simp only [holes, card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

private noncomputable def mass {n : ℕ} (A : Finset (Cube n)) : ℝ :=
  (A.card : ℝ) / 2 ^ n

private theorem mass_pos_iff {n : ℕ} (A : Finset (Cube n)) : 0 < mass A ↔ A.Nonempty := by
  rw [mass, div_pos_iff_of_pos_right (by positivity), Nat.cast_pos, card_pos]

private theorem good_fibres {r n : ℕ} (hr : 0 < r) {c : ℝ} (hc : 1 < c)
    (hroot : c⁻¹ ^ r ≤ 2 * c⁻¹ - 1) (A : Fin r → Finset (Cube (n + 1)))
    (hne : ∀ i, (A i).Nonempty) :
    ∃ u : Fin r → ZMod 2, (∀ i, (slice (A i) (u i)).Nonempty) ∧
      (if ∀ i, u i = 0 then c ^ r else 1) * (∏ i, mass (A i)) ≤
        ∏ i, mass (slice (A i) (u i)) := by
  classical
  have hcp : 0 < c := by linarith
  let P i := mass (A i)
  let S i (v : ZMod 2) := mass (slice (A i) v)
  have hp i : 0 < P i := (mass_pos_iff _).mpr (hne i)
  have hs i v : 0 ≤ S i v := by unfold S mass; positivity
  have hsum i : S i 0 + S i 1 = 2 * P i := by
    dsimp [P, S, mass]
    rw [← add_div, ← Nat.cast_add, slice_card, pow_succ]
    ring
  let a i := S i 0 / P i
  have hratio i : 2 - a i = S i 1 / P i := by
    dsimp [a]
    field_simp [(hp i).ne']
    linarith [hsum i]
  have ha i : 0 ≤ a i := div_nonneg (hs i _) (hp i).le
  have hb i : a i ≤ 2 := by
    apply (div_le_iff₀ (hp i)).mpr
    linarith [hsum i, hs i 1]
  have hstep : ∃ u : Fin r → ZMod 2, (if ∀ i, u i = 0 then c ^ r else 1) ≤
      ∏ i, S i (u i) / P i := by
    rcases choose_slices hr hc hroot a ha hb with ⟨b, ⟨j, hj⟩, h⟩ | h
    · let u (i : Fin r) : ZMod 2 := if b i then 0 else 1
      have hno : ¬∀ i, u i = 0 := fun hall => by simpa [u, hj] using hall j
      refine ⟨u, ?_⟩
      rw [if_neg hno]
      convert h using 1
      apply prod_congr rfl
      intro i _
      cases he : b i <;> simp [u, he, a, ← hratio i]
    · refine ⟨fun _ => 0, ?_⟩
      simpa [a] using h
  obtain ⟨u, hu⟩ := hstep
  rw [prod_div_distrib] at hu
  have hpp : 0 < ∏ i, P i := prod_pos fun i _ => hp i
  have he := (le_div_iff₀ hpp).mp hu
  have hmul : 0 < ∏ i, S i (u i) := lt_of_lt_of_le (mul_pos (by split <;> positivity) hpp) he
  refine ⟨u, fun i => (mass_pos_iff _).mp ?_, he⟩
  by_contra! hn
  have hz : S i (u i) = 0 := le_antisymm hn (hs i _)
  exact hmul.ne' (prod_eq_zero (mem_univ i) hz)

private theorem cross_cover {r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 1 < c)
    (hroot : c⁻¹ ^ r ≤ 2 * c⁻¹ - 1) (n : ℕ) (A : Fin r → Finset (Cube n))
    (hne : ∀ i, (A i).Nonempty) :
    ∃ x : Fin r → Cube n, (∀ i, x i ∈ A i) ∧
      (c ^ r) ^ holes x * (∏ i, mass (A i)) ≤ 1 := by
  classical
  have hcp : 0 < c := by linarith
  induction n with
  | zero =>
    choose x hx using hne
    refine ⟨x, hx, ?_⟩
    have hcard (i : Fin r) : (A i).card = 1 := le_antisymm
      (by simpa [Cube] using (card_le_univ (A i))) (card_pos.mpr ⟨x i, hx i⟩)
    simp [holes, mass, hcard]
  | succ n ih =>
    obtain ⟨u, hu, hprod⟩ := good_fibres hr hc hroot A hne
    obtain ⟨y, hy, hys⟩ := ih (fun i => slice (A i) (u i)) hu
    refine ⟨fun i => Fin.cons (u i) (y i), fun i => (mem_filter.mp (hy i)).2, ?_⟩
    have hnon : 0 ≤ (c ^ r) ^ holes y := by positivity
    rw [holes_cons, pow_add]
    by_cases hz : ∀ i, u i = 0
    · simp only [if_pos hz, pow_one] at hprod ⊢
      calc
        _ = (c ^ r) ^ holes y * ((c ^ r) * ∏ i, mass (A i)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod hnon
        _ ≤ 1 := hys
    · simp only [if_neg hz, pow_zero, one_mul] at hprod ⊢
      exact (mul_le_mul_of_nonneg_left hprod hnon).trans hys

open scoped Pointwise

/-- A family is downward closed if erasing any subset of the nonzero coordinates
of a member gives another member. -/
def Downward {n : ℕ} (A : Finset (Cube n)) : Prop :=
  ∀ x ∈ A, ∀ y : Cube n, (∀ j, y j ≠ 0 → x j ≠ 0) → y ∈ A

private theorem sum_mem {n r : ℕ} {A : Finset (Cube n)} {z : Fin r → Cube n}
    (hz : ∀ i, z i ∈ A) : ∑ i, z i ∈ r • A := by
  classical
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_succ, succ_nsmul, add_comm (r • A) A]
    exact Finset.add_mem_add (hz 0) (ih (z := fun i => z i.succ) (fun i => hz i.succ))

/-- The entire coordinate subspace on the union of the supports of the selected members
lies in their iterated sumset. -/
private theorem support_flat {n r : ℕ} {A : Finset (Cube n)} (ha : Downward A)
    (x : Fin r → Cube n) (hx : ∀ i, x i ∈ A) :
    ∃ W : Submodule (ZMod 2) (Fin n → ZMod 2), (W : Set (Fin n → ZMod 2)) ⊆ (↑(r • A) : Set (Cube n)) ∧
      n ≤ holes x + Module.finrank (ZMod 2) W := by
  classical
  let H := univ.filter (fun j => ∀ i, x i j = 0)
  let L : (Fin n → ZMod 2) →ₗ[ZMod 2] (H → ZMod 2) := LinearMap.pi (fun j => LinearMap.proj j.val)
  refine ⟨L.ker, ?_, ?_⟩
  · intro y hy
    have hy0 (j : Fin n) (hj : j ∈ H) : y j = 0 :=
      congrFun (LinearMap.mem_ker.mp hy) (⟨j, hj⟩ : H)
    have assigns (j : Fin n) (hj : y j ≠ 0) : ∃ i, x i j ≠ 0 := by
      by_contra! hall
      exact hj (hy0 j (mem_filter.mpr ⟨mem_univ _, hall⟩))
    let z (i : Fin r) (j : Fin n) : ZMod 2 := if h : y j ≠ 0 then
      if (assigns j h).choose = i then y j else 0 else 0
    have hz (i : Fin r) : z i ∈ A := by
      apply ha _ (hx i) _
      intro j hj
      by_cases h : y j ≠ 0
      · by_cases he : (assigns j h).choose = i
        · exact he ▸ (assigns j h).choose_spec
        · simp [z, h, he] at hj
      · simp [z, h] at hj
    have hsum : ∑ i, z i = y := by
      funext j
      rw [Finset.sum_apply]
      by_cases h : y j ≠ 0
      · simp only [z, dif_pos h]
        exact sum_ite_eq_of_mem univ _ (fun _ => y j) (mem_univ _)
      · have h0 : y j = 0 := not_ne_iff.mp h
        simp only [z, dif_neg h, sum_const_zero, h0]
    exact hsum ▸ sum_mem hz
  · have h₁ := L.finrank_range_add_finrank_ker
    have h₂ := Submodule.finrank_le (LinearMap.range L)
    have e₁ : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by simp
    have e₂ : Module.finrank (ZMod 2) (H → ZMod 2) = holes x := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
      rfl
    rw [e₁] at h₁
    rw [e₂] at h₂
    omega

private theorem mass_eq_dens {n : ℕ} (A : Finset (Cube n)) : mass A = (A.dens : ℝ) := by
  simp [mass, Finset.dens, Cube, Fintype.card_pi]

/-- Pick one member of each family. The product of their densities bounds the number
of coordinates missed by every selected member. -/
theorem cross_union {n r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 1 < c)
    (hroot : c⁻¹ ^ r ≤ 2 * c⁻¹ - 1) (A : Fin r → Finset (Cube n))
    (hne : ∀ i, (A i).Nonempty) :
    ∃ x : Fin r → Cube n, (∀ i, x i ∈ A i) ∧
      (c ^ r) ^ (univ.filter (fun j => ∀ i, x i j = 0)).card *
        (∏ i, ((A i).dens : ℝ)) ≤ 1 := by
  simpa only [holes, mass_eq_dens] using cross_cover hr hc hroot n A hne

#print axioms cross_union

/-- For an admissible base, the sumset of a nonempty downward-closed family contains a coordinate
subspace with codimension logarithmic in the reciprocal density. -/
theorem downward_sum {n r : ℕ} (hr : 0 < r) {c : ℝ} (hc : 1 < c)
    (hroot : c⁻¹ ^ r ≤ 2 * c⁻¹ - 1) (A : Finset (Cube n)) (hne : A.Nonempty)
    (ha : Downward A) :
    ∃ W : Submodule (ZMod 2) (Fin n → ZMod 2),
      (W : Set (Fin n → ZMod 2)) ⊆ (↑(r • A) : Set (Cube n)) ∧
      (n : ℝ) - Real.logb c (1 / (A.dens : ℝ)) ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨x, hx, hd⟩ := cross_cover hr hc hroot n (fun _ => A) (fun _ => hne)
  obtain ⟨W, hW, hw⟩ := support_flat ha x hx
  refine ⟨W, hW, ?_⟩
  have hpos := (mass_pos_iff A).mpr hne
  simp only [prod_const, card_univ, Fintype.card_fin] at hd
  rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow] at hd
  have hsmall : c ^ holes x * mass A ≤ 1 := by
    by_contra! hn
    exact (not_lt_of_ge hd) (one_lt_pow₀ hn (by omega))
  have hlead := ((Real.logb_le_logb hc (pow_pos (by linarith : 0 < c) _) (div_pos one_pos hpos)).mpr
    ((le_div_iff₀ hpos).mpr hsmall))
  rw [Real.logb_pow, Real.logb_self_eq_one hc, mul_one, mass_eq_dens] at hlead
  have hdim : (n : ℝ) ≤ (holes x : ℝ) + Module.finrank (ZMod 2) W := by exact_mod_cast hw
  linarith

#print axioms downward_sum

/-- For three summands one can take the golden ratio as the logarithm base. -/
theorem threefold {n : ℕ} (A : Finset (Cube n)) (hne : A.Nonempty) (ha : Downward A) :
    ∃ W : Submodule (ZMod 2) (Cube n),
      (W : Set (Cube n)) ⊆ (↑((3 : ℕ) • A) : Set (Cube n)) ∧
      (n : ℝ) - Real.logb ((1 + Real.sqrt 5) / 2) (1 / (A.dens : ℝ)) ≤
        Module.finrank (ZMod 2) W := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hp := Real.sqrt_nonneg 5
  refine downward_sum (by norm_num) ?_ ?_ A hne ha
  · nlinarith
  · have hi : ((1 + Real.sqrt 5) / 2)⁻¹ = (Real.sqrt 5 - 1) / 2 := by
      field_simp [(show 1 + Real.sqrt 5 ≠ 0 by positivity)]
      nlinarith
    rw [hi]
    nlinarith [congrArg (fun x : ℝ => x * Real.sqrt 5) hs]

#print axioms threefold

/-- Green 50 with the original ten summands and base-two logarithm, for downward-closed sets. -/
theorem green_50_downward :
    ∃ C > (0 : ℝ), ∀ n (A : Finset (Fin n → ZMod 2)), A.Nonempty → Downward A →
      let α : ℝ := A.dens
      ∃ (W : Submodule (ZMod 2) (Fin n → ZMod 2)) (v : Fin n → ZMod 2),
        v +ᵥ (W : Set (Fin n → ZMod 2)) ⊆ (↑((10 : ℕ) • A) : Set (Fin n → ZMod 2)) ∧
        (n : ℝ) - C * Real.logb 2 (1 / α) ≤ Module.finrank (ZMod 2) W := by
  let C := Real.log 2 / Real.log (999 / 500)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log (999 / 500) := Real.log_pos (by norm_num)
  refine ⟨C, div_pos h2 hc, ?_⟩
  intro n A hne ha
  obtain ⟨W, hW, hd⟩ := downward_sum (r := 10)
    (by norm_num) (c := 999 / 500) (by norm_num) (by norm_num) A hne ha
  refine ⟨W, 0, by simpa only [zero_vadd] using hW, ?_⟩
  have eq (z : ℝ) : C * Real.logb 2 z = Real.logb (999 / 500) z := by
    dsimp [C, Real.logb]
    field_simp [h2.ne', hc.ne']
  rw [eq]
  exact hd

#print axioms green_50_downward

end Green50Downsets
