import OMAReductions.R_Green3_green_3_R2

-- Reduction Green3.green_3.R2.H1.R1 of step Green3.green_3.R2.H1
-- Credit: @vincentkoc

/-!
# Splitting Franchi–Gowers–Yip Lemma 2.1 along the paper

Reduction of `Green3.green_3.R2.H1` along the paper. We rescale to `min A = 1`.
Lean by @vincentkoc, drafted with AI assistance (Grok Bot).

* `H1` is FGY Theorem 3.12: `|A + B| ≥ 2|A| + 2|B| - d(A) - d(B)` when `d(A) = d(B)`, for nonempty
  finite unions of closed intervals, where `d(A) = sup_{a ≤ b} (2|A ∩ [a,b]| - (b - a))`.
* `H2` is FGY Lemma 4.4. A failure of `f(z-1) + f(z) + f(z+1) ≤ z` moves to a point `x` where it
  fails on a neighbourhood and `x ± 1` lie inside `A` with room `ε`.
* `H3` is the rigidity argument of FGY §4.3 (Lemmas 4.5–4.16), assuming Theorem 3.12. No such `x`
  exists.
-/

namespace OMA.R_Green3_green_3_R2_H1_R1

open Set MeasureTheory Pointwise

/-- FGY Theorem 3.12. -/
def H1 : Prop := ∀ A B : Set ℝ, (∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Icc p.1 p.2) →
    (∃ s : Finset (ℝ × ℝ), B = ⋃ p ∈ s, Icc p.1 p.2) → A.Nonempty → B.Nonempty →
    sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (A ∩ Icc a b) - (b - a)} =
      sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (B ∩ Icc a b) - (b - a)} →
    2 * volume.real A + 2 * volume.real B
        - sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (A ∩ Icc a b) - (b - a)}
        - sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (B ∩ Icc a b) - (b - a)}
      ≤ volume.real (A + B)

/-- FGY Lemma 4.4. -/
def H2 : Prop := ∀ A : Set ℝ, (∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Icc p.1 p.2) →
    IsLeast A 1 → (∀ a ∈ A, ∀ b ∈ A, a + b ∉ A) → ∀ z : ℝ, 1 ≤ z →
    z < volume.real (A ∩ Icc 0 (z - 1)) + volume.real (A ∩ Icc 0 z) +
      volume.real (A ∩ Icc 0 (z + 1)) →
    ∃ x ε : ℝ, 1 ≤ x ∧ 0 < ε ∧
      (∀ y ∈ Icc (x - ε) (x + ε), y < volume.real (A ∩ Icc 0 (y - 1)) +
        volume.real (A ∩ Icc 0 y) + volume.real (A ∩ Icc 0 (y + 1))) ∧
      Icc (x - 1 - ε) (x - 1 + ε) ⊆ A ∧ Icc (x + 1 - ε) (x + 1 + ε) ⊆ A

/-- FGY §4.3, given Theorem 3.12. -/
def H3 : Prop := (∀ A B : Set ℝ, (∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Icc p.1 p.2) →
      (∃ s : Finset (ℝ × ℝ), B = ⋃ p ∈ s, Icc p.1 p.2) → A.Nonempty → B.Nonempty →
      sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (A ∩ Icc a b) - (b - a)} =
        sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (B ∩ Icc a b) - (b - a)} →
      2 * volume.real A + 2 * volume.real B
          - sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (A ∩ Icc a b) - (b - a)}
          - sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (B ∩ Icc a b) - (b - a)}
        ≤ volume.real (A + B)) →
    ∀ A : Set ℝ, (∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Icc p.1 p.2) →
    IsLeast A 1 → (∀ a ∈ A, ∀ b ∈ A, a + b ∉ A) → ∀ x ε : ℝ, 1 ≤ x → 0 < ε →
    (∀ y ∈ Icc (x - ε) (x + ε), y < volume.real (A ∩ Icc 0 (y - 1)) +
        volume.real (A ∩ Icc 0 y) + volume.real (A ∩ Icc 0 (y + 1))) →
    Icc (x - 1 - ε) (x - 1 + ε) ⊆ A → Icc (x + 1 - ε) (x + 1 + ε) ⊆ A → False

lemma scale_inter (B : Set ℝ) {δ : ℝ} (hδ : 0 < δ) (w : ℝ) :
    volume.real (((fun x => δ * x) ⁻¹' B) ∩ Icc 0 w) = volume.real (B ∩ Icc 0 (δ * w)) / δ := by
  have hset : ((fun x => δ * x) ⁻¹' B) ∩ Icc 0 w = (fun x => δ * x) ⁻¹' (B ∩ Icc 0 (δ * w)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hb, h0, hw⟩
      exact ⟨hb, by positivity, by nlinarith⟩
    · rintro ⟨hb, h0, hw⟩
      refine ⟨hb, ?_, ?_⟩
      · by_contra h; push Not at h; nlinarith
      · by_contra h; push Not at h; nlinarith
  rw [hset, measureReal_def, Real.volume_preimage_mul_left hδ.ne', measureReal_def,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr hδ)]
  ring

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R2.H1 := by
  intro h1 h2 h3 B δ ⟨s, hs⟩ hδ hδpos hsf u hu
  set A := (fun x => δ * x) ⁻¹' B with hA
  have hAfin : ∃ s : Finset (ℝ × ℝ), A = ⋃ p ∈ s, Icc p.1 p.2 := by
    refine ⟨s.image (fun p => (p.1 / δ, p.2 / δ)), ?_⟩
    rw [Finset.set_biUnion_finset_image, hA, hs, preimage_iUnion₂]
    exact iUnion₂_congr fun p _ => preimage_const_mul_Icc₀ _ _ hδpos
  have hAleast : IsLeast A 1 := by
    refine ⟨by simp [hA, hδ.1], fun a ha => ?_⟩
    have := hδ.2 ha
    by_contra h; push Not at h; nlinarith
  have hAsf : ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A := by
    intro a ha b hb hab
    exact hsf _ ha _ hb (by simpa [hA, mul_add] using hab)
  set w := u / δ with hw
  have hu' : u = δ * w := by rw [hw]; field_simp
  have hFB : ∀ t, volume.real (B ∩ Icc 0 (δ * t)) = δ * volume.real (A ∩ Icc 0 t) := by
    intro t; rw [hA, scale_inter B hδpos t]; field_simp
  have hgoal : volume.real (A ∩ Icc 0 (w - 1)) + volume.real (A ∩ Icc 0 w) +
      volume.real (A ∩ Icc 0 (w + 1)) ≤ w := by
    by_contra hgt
    push Not at hgt
    rcases lt_or_ge w 1 with hw1 | hw1
    · have e1 : A ∩ Icc 0 (w - 1) = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        intro hx _ hx2; have := hAleast.2 hx; linarith
      have e2 : A ∩ Icc 0 w = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        intro hx _ hx2; have := hAleast.2 hx; linarith
      have e3 : volume.real (A ∩ Icc 0 (w + 1)) ≤ w := by
        have hsub : A ∩ Icc 0 (w + 1) ⊆ Icc 1 (w + 1) := fun x hx => ⟨hAleast.2 hx.1, hx.2.2⟩
        calc volume.real (A ∩ Icc 0 (w + 1)) ≤ volume.real (Icc (1 : ℝ) (w + 1)) :=
              measureReal_mono hsub (by simp)
          _ = w := by
              rw [Real.volume_real_Icc]
              have : 0 ≤ w := by rw [hw]; positivity
              rw [max_eq_left (by linarith)]; ring
      rw [e1, e2] at hgt
      simp at hgt
      linarith
    · obtain ⟨x, ε, hx1, hε, hH, hl, hr⟩ := h2 A hAfin hAleast hAsf w hw1 hgt
      exact h3 h1 A hAfin hAleast hAsf x ε hx1 hε hH hl hr
  have e1 : u - δ = δ * (w - 1) := by rw [hu']; ring
  have e3 : u + δ = δ * (w + 1) := by rw [hu']; ring
  rw [e1, e3, hu', hFB, hFB, hFB]
  nlinarith

end OMA.R_Green3_green_3_R2_H1_R1
