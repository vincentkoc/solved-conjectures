import FormalConjectures.GreensOpenProblems.«3»

-- Reduction Green3.green_3.R2 of Ben Green's Open Problem 3
-- Credit: @vincentkoc (drafted with AI assistance: Grok Bot)
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Green's problem 3 via the Franchi–Gowers–Yip key lemma

Follows L. Franchi, W. T. Gowers, F. Yip, *Product-free subsets of (0,1)*, arXiv:2607.06073.
Pass to `B = -log K` for a finite union `K` of closed intervals inside the open set, so that
products become sums.

* `H1` is their Lemma 2.1, rescaled to `min B = δ`. If `B` is a sum-free finite union of closed
  intervals with least element `δ > 0` and `f(u) = |B ∩ [0,u]|`, then
  `f(u-δ) + f(u) + f(u+δ) ≤ u` for `u ≥ 0`. Section 4 of the paper proves it for finite unions of
  closed intervals.
* `H2` is the integral argument of their Section 2. Since `|exp(-B)| = ∫ e^{-u} f(u) du`,
  integrating `H1` against `e^{-u}` and shifting by `±δ` gives `(e^{-δ} + 1 + e^{δ}) |exp(-B)| ≤ 1`.
* `main` approximates the open set from inside by finitely many closed intervals in `(0,1)`, moves
  to `B = -log K` (a finite union of closed intervals, compact, with positive minimum, sum-free) and
  uses `exp(-B) = K`.
-/

namespace OMA.R_Green3_green_3_R2

open Set MeasureTheory Real

lemma neg_log_image_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (fun x : ℝ => -Real.log x) '' Icc a b = Icc (-Real.log b) (-Real.log a) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hax, hxb⟩, rfl⟩
    have hx : 0 < x := lt_of_lt_of_le ha hax
    exact ⟨neg_le_neg (Real.log_le_log hx hxb), neg_le_neg (Real.log_le_log ha hax)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨rexp (-y), ⟨?_, ?_⟩, by simp⟩
    · have : Real.log a ≤ -y := by linarith
      calc a = rexp (Real.log a) := (Real.exp_log ha).symm
        _ ≤ rexp (-y) := Real.exp_le_exp.mpr this
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      have : -y ≤ Real.log b := by linarith
      calc rexp (-y) ≤ rexp (Real.log b) := Real.exp_le_exp.mpr this
        _ = b := Real.exp_log hb

lemma inner_approx (U : Set ℝ) (hU : IsOpen U) (c : ENNReal) (hc : c < volume U) :
    ∃ s : Finset (ℝ × ℝ), (∀ p ∈ s, p.1 ≤ p.2 ∧ Icc p.1 p.2 ⊆ U) ∧
      c < volume (⋃ p ∈ s, Icc p.1 p.2) := by
  obtain ⟨C, hCU, hCc, hcC⟩ := hU.exists_lt_isCompact hc
  have hε : ∀ x ∈ C, ∃ ε > 0, Icc (x - ε) (x + ε) ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x (hCU hx)
    refine ⟨ε / 2, by positivity, ?_⟩
    intro y hy
    apply hball
    rw [Real.ball_eq_Ioo]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  choose! ε hεpos hεU using hε
  obtain ⟨t, htC, hcover⟩ := hCc.elim_nhds_subcover (fun x => Icc (x - ε x) (x + ε x))
    (fun x hx => Icc_mem_nhds (by linarith [hεpos x hx]) (by linarith [hεpos x hx]))
  refine ⟨t.image (fun x => (x - ε x, x + ε x)), ?_, ?_⟩
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨by linarith [hεpos x (htC x hx)], hεU x (htC x hx)⟩
  · refine lt_of_lt_of_le hcC (measure_mono ?_)
    rw [Finset.set_biUnion_finset_image]
    exact hcover

/-- Franchi–Gowers–Yip, Lemma 2.1 (rescaled to least element `δ`). -/
def H1 : Prop := ∀ (B : Set ℝ) (δ : ℝ), (∃ s : Finset (ℝ × ℝ), B = ⋃ p ∈ s, Icc p.1 p.2) →
    IsLeast B δ → 0 < δ →
    (∀ a ∈ B, ∀ b ∈ B, a + b ∉ B) →
    ∀ u : ℝ, 0 ≤ u → volume.real (B ∩ Icc 0 (u - δ)) + volume.real (B ∩ Icc 0 u) +
      volume.real (B ∩ Icc 0 (u + δ)) ≤ u

/-- The integral bridge of Franchi–Gowers–Yip, Section 2. -/
def H2 : Prop := ∀ (B : Set ℝ) (δ : ℝ), (∃ s : Finset (ℝ × ℝ), B = ⋃ p ∈ s, Icc p.1 p.2) →
    IsLeast B δ → 0 < δ →
    (∀ u : ℝ, 0 ≤ u → volume.real (B ∩ Icc 0 (u - δ)) + volume.real (B ∩ Icc 0 u) +
      volume.real (B ∩ Icc 0 (u + δ)) ≤ u) →
    volume.real ((fun u => rexp (-u)) '' B) ≤ 1 / 3

theorem main : H1 → H2 → type_of% @Green3.green_3 := by
  intro h1 h2 A hA hsub hvol
  by_contra hno
  push Not at hno
  set U := A ∩ Ioo 0 1 with hUdef
  have hUo : IsOpen U := hA.inter isOpen_Ioo
  have hAU : A ⊆ U ∪ {0, 1} := by
    intro x hx
    rcases eq_or_lt_of_le (hsub hx).1 with h | h
    · right; simp [h]
    rcases eq_or_lt_of_le (hsub hx).2 with h' | h'
    · right; simp [h']
    · left; exact ⟨hx, h, h'⟩
  have hUvol : (1 / 3 : ENNReal) < volume U := by
    have : volume A ≤ volume U := by
      calc volume A ≤ volume (U ∪ {0, 1}) := measure_mono hAU
        _ ≤ volume U + volume ({0, 1} : Set ℝ) := measure_union_le _ _
        _ = volume U := by
          rw [(Set.toFinite ({0, 1} : Set ℝ)).measure_zero, add_zero]
    exact lt_of_lt_of_le hvol this
  obtain ⟨s, hs, hsvol⟩ := inner_approx U hUo _ hUvol
  set K := ⋃ p ∈ s, Icc p.1 p.2 with hKdef
  have hKU : K ⊆ U := by
    intro x hx
    simp only [hKdef, mem_iUnion] at hx
    obtain ⟨p, hp, hxp⟩ := hx
    exact (hs p hp).2 hxp
  have hKpos : ∀ x ∈ K, 0 < x ∧ x < 1 := fun x hx => (hKU hx).2
  set g : ℝ → ℝ := fun x => -Real.log x with hg
  set B := g '' K with hBdef
  have hpos : ∀ p ∈ s, Icc p.1 p.2 ≠ ∅ → 0 < p.1 := by
    intro p hp _
    exact (hKpos p.1 (by
      simp only [hKdef, mem_iUnion]
      exact ⟨p, hp, left_mem_Icc.mpr (hs p hp).1⟩)).1
  have hBfin : ∃ s : Finset (ℝ × ℝ), B = ⋃ p ∈ s, Icc p.1 p.2 := by
    refine ⟨s.image (fun p => (-Real.log p.2, -Real.log p.1)), ?_⟩
    rw [Finset.set_biUnion_finset_image, hBdef, hKdef, Set.image_iUnion₂]
    refine iUnion₂_congr fun p hp => ?_
    exact neg_log_image_Icc (hpos p hp (nonempty_Icc.mpr (hs p hp).1).ne_empty) (hs p hp).1
  have hKne : K.Nonempty := by
    apply nonempty_of_measure_ne_zero (μ := volume)
    exact (lt_of_le_of_lt zero_le hsvol).ne'
  have hKc : IsCompact K := s.isCompact_biUnion (fun p _ => isCompact_Icc)
  have hBc : IsCompact B := by
    apply hKc.image_of_continuousOn
    exact (Real.continuousOn_log.mono (fun x hx => (ne_of_gt (hKpos x hx).1))).neg
  obtain ⟨δ, hδ⟩ := hBc.exists_isLeast (hKne.image g)
  have hδpos : 0 < δ := by
    obtain ⟨x, hx, hxδ⟩ := hδ.1
    rw [← hxδ]
    have := Real.log_neg (hKpos x hx).1 (hKpos x hx).2
    simp only [hg]; linarith
  have hsf : ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B := by
    rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ ⟨z, hz, hzeq⟩
    have hx0 := (hKpos x hx).1
    have hy0 := (hKpos y hy).1
    have hz0 := (hKpos z hz).1
    have hlog : Real.log z = Real.log (x * y) := by
      rw [Real.log_mul hx0.ne' hy0.ne']
      simp only [hg] at hzeq
      linarith
    have hzxy : z = x * y :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hz0) (Set.mem_Ioi.mpr (mul_pos hx0 hy0)) hlog
    exact hno x y z (hKU hx).1 (hKU hy).1 (hKU hz).1 hzxy.symm
  have hbound := h2 B δ hBfin hδ hδpos (h1 B δ hBfin hδ hδpos hsf)
  have himg : (fun u => rexp (-u)) '' B = K := by
    rw [hBdef, Set.image_image]
    conv_rhs => rw [← Set.image_id K]
    refine Set.image_congr fun x hx => ?_
    simp only [hg, neg_neg, id]
    exact Real.exp_log (hKpos x hx).1
  rw [himg] at hbound
  have hfin : volume K ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (Ioo (0 : ℝ) 1)) (by simp) ?_
    exact measure_mono (fun x hx => hKU hx |>.2)
  have : (1 / 3 : ENNReal).toReal < (volume K).toReal :=
    (ENNReal.toReal_lt_toReal (by simp) hfin).mpr hsvol
  have h13 : (1 / 3 : ENNReal).toReal = 1 / 3 := by
    rw [ENNReal.toReal_div]; simp
  rw [h13] at this
  exact absurd hbound (not_le.mpr this)

end OMA.R_Green3_green_3_R2
