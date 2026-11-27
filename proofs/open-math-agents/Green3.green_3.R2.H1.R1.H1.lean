import OMAReductions.R_Green3_green_3_R2_H1_R1
import Mathlib

/-! FGY §3 toolbox (Franchi–Gowers–Yip, arXiv:2607.06073), toward Theorem 3.12 (R2.H1.R1.H1).
Discrepancy `d_A([a,b]) = 2|A ∩ [a,b]| - (b - a)`, left/right balanced intervals,
Lemma 3.3, Corollary 3.4(ii), the "subinterval discrepancy" bound, and Lemma 3.5.
Lean by @vincentkoc, drafted with AI assistance (Grok Bot). -/

open Set MeasureTheory

namespace OMA.Green3Sec3

/-- `d_A([a,b])`. -/
noncomputable def dA (A : Set ℝ) (a b : ℝ) : ℝ := 2 * volume.real (A ∩ Icc a b) - (b - a)

/-- `[a,b]` is left balanced w.r.t. `A` (FGY Def. 3.2, with the convention for `a = b`). -/
def LeftBal (A : Set ℝ) (a b : ℝ) : Prop := a ≤ b ∧ a ∈ A ∧ ∀ x ∈ Icc a b, 0 ≤ dA A a x
/-- `[a,b]` is right balanced w.r.t. `A`. -/
def RightBal (A : Set ℝ) (a b : ℝ) : Prop := a ≤ b ∧ b ∈ A ∧ ∀ x ∈ Icc a b, 0 ≤ dA A x b
/-- `[a,b]` is balanced w.r.t. `A`. -/
def Bal (A : Set ℝ) (a b : ℝ) : Prop := LeftBal A a b ∧ RightBal A a b

variable {A B : Set ℝ}

lemma fin_inter (A : Set ℝ) (a b : ℝ) : volume (A ∩ Icc a b) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right)

lemma vol_split (hA : MeasurableSet A) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    volume.real (A ∩ Icc a c) = volume.real (A ∩ Icc a b) + volume.real (A ∩ Icc b c) := by
  have hu : A ∩ Icc a c = (A ∩ Icc a b) ∪ (A ∩ Icc b c) := by
    rw [← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc]
  have hnull : volume.real ((A ∩ Icc a b) ∩ (A ∩ Icc b c)) = 0 :=
    measureReal_mono_null (s₂ := Icc b b) (fun t ht => ⟨ht.2.2.1, ht.1.2.2⟩)
      (by rw [Real.volume_real_Icc]; simp) measure_Icc_lt_top.ne
  have h := measureReal_union_add_inter₀ (μ := volume) (s := A ∩ Icc a b)
    (hA.inter measurableSet_Icc).nullMeasurableSet (fin_inter A a b) (fin_inter A b c)
  rw [hnull, add_zero] at h
  rw [hu, h]

lemma dA_split (hA : MeasurableSet A) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    dA A a c = dA A a b + dA A b c := by
  unfold dA; rw [vol_split hA hab hbc]; ring

lemma dA_le_len (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) : dA A a b ≤ b - a := by
  unfold dA
  have : volume.real (A ∩ Icc a b) ≤ b - a := by
    calc _ ≤ volume.real (Icc a b) := measureReal_mono inter_subset_right measure_Icc_lt_top.ne
      _ = b - a := by rw [Real.volume_real_Icc, max_eq_left (by linarith)]
  linarith

lemma dA_of_disj {a b : ℝ} (h : A ∩ Icc a b = ∅) : dA A a b = -(b - a) := by
  unfold dA; rw [h]; simp

/-- FGY Lemma 3.3. -/
lemma leftBal_union (hA : MeasurableSet A) {a b c d : ℝ} (hI : LeftBal A a b)
    (hJ : LeftBal A c d) (hac : a ≤ c) (hcb : c ≤ b) : LeftBal A a (max b d) := by
  refine ⟨hI.1.trans (le_max_left _ _), hI.2.1, fun x hx => ?_⟩
  rcases le_or_gt x b with hxb | hxb
  · exact hI.2.2 x ⟨hx.1, hxb⟩
  · have hxd : x ≤ d := by
      rcases le_max_iff.mp hx.2 with h | h
      · linarith
      · exact h
    rw [dA_split hA hac (hcb.trans hxb.le)]
    have := hI.2.2 c ⟨hac, hcb⟩
    have := hJ.2.2 x ⟨by linarith, hxd⟩
    linarith

/-- FGY Lemma 3.3, right-balanced version. -/
lemma rightBal_union (hA : MeasurableSet A) {a b c d : ℝ} (hI : RightBal A a b)
    (hJ : RightBal A c d) (hcb : c ≤ b) (hbd : b ≤ d) : RightBal A (min a c) d := by
  refine ⟨(min_le_right _ _).trans hJ.1, hJ.2.1, fun x hx => ?_⟩
  rcases le_or_gt c x with hcx | hxc
  · exact hJ.2.2 x ⟨hcx, hx.2⟩
  · have hax : a ≤ x := by
      rcases min_le_iff.mp hx.1 with h | h
      · exact h
      · linarith
    rw [dA_split hA (hxc.le.trans hcb) hbd]
    have := hI.2.2 x ⟨hax, hxc.le.trans hcb⟩
    have := hJ.2.2 b ⟨hcb, hbd⟩
    linarith

/-- FGY Corollary 3.4(ii). -/
lemma bal_union (hA : MeasurableSet A) {a b c d : ℝ} (hI : Bal A a b) (hJ : Bal A c d)
    (hac : a ≤ c) (hcb : c ≤ b) : Bal A a (max b d) := by
  rcases le_total d b with hdb | hbd
  · rw [max_eq_left hdb]; exact hI
  · rw [max_eq_right hbd]
    have h1 := leftBal_union hA hI.1 hJ.1 hac hcb
    have h2 := rightBal_union hA hI.2 hJ.2 hcb hbd
    rw [max_eq_right hbd] at h1
    rw [min_eq_left hac] at h2
    exact ⟨h1, h2⟩

/-- A balanced interval dominates the discrepancy of its subintervals. -/
lemma bal_sub (hA : MeasurableSet A) {a b x y : ℝ} (hI : Bal A a b) (hax : a ≤ x) (hxy : x ≤ y)
    (hyb : y ≤ b) : dA A x y ≤ dA A a b := by
  rw [dA_split hA hax (hxy.trans hyb), dA_split hA hxy hyb]
  have := hI.1.2.2 x ⟨hax, hxy.trans hyb⟩
  have := hI.2.2.2 y ⟨hax.trans hxy, hyb⟩
  linarith

lemma nonempty_of_pos {S : Set ℝ} (h : 0 < volume.real S) : S.Nonempty := by
  by_contra h'
  rw [not_nonempty_iff_eq_empty] at h'
  rw [h'] at h; simp at h

/-- Two closed sets filling a nondegenerate interval in measure must meet there. -/
lemma inter_nonempty (hA : IsClosed A) (hB : IsClosed B) {c d : ℝ} (hcd : c < d)
    (hAne : (A ∩ Icc c d).Nonempty) (hBne : (B ∩ Icc c d).Nonempty)
    (h : d - c ≤ volume.real (A ∩ Icc c d) + volume.real (B ∩ Icc c d)) :
    (Icc c d ∩ (A ∩ B)).Nonempty := by
  by_contra hE
  rw [not_nonempty_iff_eq_empty] at hE
  have hdisj : Disjoint (A ∩ Icc c d) (B ∩ Icc c d) := by
    rw [Set.disjoint_left]
    intro t htA htB
    have : t ∈ Icc c d ∩ (A ∩ B) := ⟨htA.2, htA.1, htB.1⟩
    rw [hE] at this; exact this
  have hS : volume.real ((A ∩ Icc c d) ∪ (B ∩ Icc c d)) =
      volume.real (A ∩ Icc c d) + volume.real (B ∩ Icc c d) :=
    measureReal_union hdisj (hB.measurableSet.inter measurableSet_Icc) (fin_inter A c d)
      (fin_inter B c d)
  have hcover : Icc c d ⊆ A ∪ B := by
    intro t ht
    by_contra htU
    have hUo : IsOpen (A ∪ B)ᶜ := (hA.union hB).isOpen_compl
    have hne : ((A ∪ B)ᶜ ∩ Ioo c d).Nonempty := by
      have : t ∈ closure (Ioo c d) := by rw [closure_Ioo hcd.ne]; exact ht
      exact mem_closure_iff.mp this _ hUo htU
    have hpos : 0 < volume.real ((A ∪ B)ᶜ ∩ Ioo c d) :=
      ENNReal.toReal_pos ((hUo.inter isOpen_Ioo).measure_ne_zero volume hne)
        (ne_top_of_le_ne_top measure_Icc_lt_top.ne
          (measure_mono (inter_subset_right.trans Ioo_subset_Icc_self)))
    have hsub : (A ∪ B)ᶜ ∩ Ioo c d ⊆ Icc c d \ ((A ∩ Icc c d) ∪ (B ∩ Icc c d)) := by
      rintro y ⟨hyU, hy⟩
      refine ⟨Ioo_subset_Icc_self hy, ?_⟩
      rintro (h1 | h1)
      · exact hyU (Or.inl h1.1)
      · exact hyU (Or.inr h1.1)
    have hdiff := measureReal_sdiff (μ := volume) (s₁ := Icc c d)
      (s₂ := (A ∩ Icc c d) ∪ (B ∩ Icc c d))
      (union_subset inter_subset_right inter_subset_right)
      ((hA.measurableSet.inter measurableSet_Icc).union (hB.measurableSet.inter measurableSet_Icc))
      measure_Icc_lt_top.ne
    have hle := measureReal_mono (μ := volume) hsub
      (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono sdiff_subset))
    rw [hdiff, hS, Real.volume_real_Icc, max_eq_left (by linarith)] at hle
    linarith
  obtain ⟨x, hx⟩ := hAne
  obtain ⟨y, hy⟩ := hBne
  have := (isPreconnected_closed_iff.mp isPreconnected_Icc) A B hA hB hcover ⟨x, hx.2, hx.1⟩
    ⟨y, hy.2, hy.1⟩
  rw [hE] at this
  exact not_nonempty_empty this

/-- FGY Lemma 3.5 (with `min I ≤ min J`; the other case is symmetric). -/
theorem lemma_3_5 (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ} (hI : Bal A a b)
    (hJ : Bal B c d) (hac : a ≤ c) (hcb : c ≤ b) (hd : dA A a b = dA B c d) :
    ((A ∩ Icc a b) ∩ (B ∩ Icc c d)).Nonempty := by
  have hAm := hA.measurableSet
  have hcd := hJ.1.1
  suffices H : ∃ t, t ∈ A ∧ t ∈ B ∧ c ≤ t ∧ t ≤ b ∧ t ≤ d by
    obtain ⟨t, h1, h2, h3, h4, h5⟩ := H
    exact ⟨t, ⟨h1, hac.trans h3, h4⟩, h2, h3, h5⟩
  rcases eq_or_lt_of_le hcb with hcb' | hcb'
  · exact ⟨c, by rw [hcb']; exact hI.2.2.1, hJ.1.2.1, le_rfl, hcb, hcd⟩
  rcases le_or_gt b d with hbd | hdb
  · have h1 : 0 ≤ dA A c b := hI.2.2.2 c ⟨hac, hcb⟩
    have h2 : 0 ≤ dA B c b := hJ.1.2.2 b ⟨hcb, hbd⟩
    unfold dA at h1 h2
    obtain ⟨t, ht, htA, htB⟩ := inter_nonempty hA hB hcb' (nonempty_of_pos (by linarith))
      (nonempty_of_pos (by linarith)) (by linarith)
    exact ⟨t, htA, htB, ht.1, ht.2, ht.2.trans hbd⟩
  by_cases hAJ : (A ∩ Icc c d).Nonempty
  · rcases eq_or_lt_of_le hcd with hcd' | hcd'
    · obtain ⟨t, htA, ht⟩ := hAJ
      have : t = c := le_antisymm (ht.2.trans hcd'.symm.le) ht.1
      subst this
      exact ⟨t, htA, hJ.1.2.1, le_rfl, hcb, hcd⟩
    · have e1 : dA A a d = dA A a c + dA A c d := dA_split hAm hac hcd
      have e2 : dA A c b = dA A c d + dA A d b := dA_split hAm hcd hdb.le
      have e3 : dA A a b = dA A a c + dA A c b := dA_split hAm hac hcb
      have g1 : 0 ≤ dA A a d := hI.1.2.2 d ⟨hac.trans hcd, hdb.le⟩
      have g2 : 0 ≤ dA A c b := hI.2.2.2 c ⟨hac, hcb⟩
      have hsum : 0 ≤ dA A c d + dA B c d := by linarith
      unfold dA at hsum
      obtain ⟨t, ht, htA, htB⟩ :=
        inter_nonempty hA hB hcd' hAJ ⟨c, hJ.1.2.1, le_rfl, hcd⟩ (by linarith)
      exact ⟨t, htA, htB, ht.1, ht.2.trans hdb.le, ht.2⟩
  · exfalso
    rw [not_nonempty_iff_eq_empty] at hAJ
    have hca : a < c := by
      rcases eq_or_lt_of_le hac with h | h
      · have : c ∈ A ∩ Icc c d := ⟨h ▸ hI.1.2.1, le_rfl, hcd⟩
        rw [hAJ] at this; exact this.elim
      · exact h
    obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hA.isOpen_compl
      (show Icc c d ⊆ Aᶜ from fun t ht htA => by
        have : t ∈ A ∩ Icc c d := ⟨htA, ht⟩
        rw [hAJ] at this; exact this)
    set η := min δ (min (c - a) (b - d)) with hηdef
    have hη : 0 < η := lt_min hδ (lt_min (by linarith) (by linarith))
    have hη1 : η ≤ δ := min_le_left _ _
    have hη2 : η ≤ c - a := (min_le_right _ _).trans (min_le_left _ _)
    have hη3 : η ≤ b - d := (min_le_right _ _).trans (min_le_right _ _)
    have hgap : A ∩ Icc (c - η) (d + η) = ∅ := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro htA ht1 ht2
      have hm : t ∈ Metric.cthickening δ (Icc c d) := by
        refine Metric.mem_cthickening_of_dist_le t (max c (min t d)) δ (Icc c d)
          ⟨le_max_left _ _, max_le hcd (min_le_right _ _)⟩ ?_
        rw [Real.dist_eq, abs_le]
        constructor
        · have : max c (min t d) ≤ t + δ := max_le (by linarith) (by linarith [min_le_left t d])
          linarith
        · have : t - δ ≤ min t d := le_min (by linarith) (by linarith)
          linarith [le_max_right c (min t d)]
      exact hsub hm htA
    have hc' : a ≤ c - η := by linarith
    have hd' : d + η ≤ b := by linarith
    have hmid : dA A (c - η) (d + η) = -((d + η) - (c - η)) := dA_of_disj hgap
    have s1 : dA A a (d + η) = dA A a (c - η) + dA A (c - η) (d + η) :=
      dA_split hAm hc' (by linarith)
    have s2 : dA A (c - η) b = dA A (c - η) (d + η) + dA A (d + η) b :=
      dA_split hAm (by linarith) hd'
    have s3 : dA A a b = dA A a (c - η) + dA A (c - η) b := dA_split hAm hc' (by linarith)
    have g1 : 0 ≤ dA A a (d + η) := hI.1.2.2 _ ⟨by linarith, hd'⟩
    have g2 : 0 ≤ dA A (c - η) b := hI.2.2.2 _ ⟨hc', by linarith⟩
    have g3 : dA B c d ≤ d - c := dA_le_len B hcd
    linarith

/-- Reflection `y ↦ x - y` preserves discrepancy. -/
lemma refl_dA (hB : MeasurableSet B) (x p q : ℝ) :
    dA ((fun y => x - y) ⁻¹' B) p q = dA B (x - q) (x - p) := by
  have hpre : (fun y => x - y) ⁻¹' (B ∩ Icc (x - q) (x - p)) =
      (fun y => x - y) ⁻¹' B ∩ Icc p q := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  unfold dA
  rw [← hpre, (Measure.measurePreserving_sub_left volume x).measureReal_preimage
    (hB.inter measurableSet_Icc).nullMeasurableSet]
  ring

lemma bal_refl (hB : MeasurableSet B) {c d : ℝ} (x : ℝ) (hJ : Bal B c d) :
    Bal ((fun y => x - y) ⁻¹' B) (x - d) (x - c) := by
  refine ⟨⟨by linarith [hJ.1.1], ?_, fun z hz => ?_⟩, ⟨by linarith [hJ.1.1], ?_, fun z hz => ?_⟩⟩
  · show x - (x - d) ∈ B; rw [sub_sub_cancel]; exact hJ.2.2.1
  · rw [refl_dA hB, sub_sub_cancel]; exact hJ.2.2.2 _ ⟨by linarith [hz.2], by linarith [hz.1]⟩
  · show x - (x - c) ∈ B; rw [sub_sub_cancel]; exact hJ.1.2.1
  · rw [refl_dA hB, sub_sub_cancel]; exact hJ.1.2.2 _ ⟨by linarith [hz.2], by linarith [hz.1]⟩

open Pointwise in
/-- FGY Corollary 3.6: `(A ∩ I) + (B ∩ J) = I + J` when `d_A(I) = d_B(J)`
(the nontrivial inclusion). -/
theorem cor_3_6 (hA : IsClosed A) (hB : IsClosed B) {a b c d : ℝ} (hI : Bal A a b)
    (hJ : Bal B c d) (hd : dA A a b = dA B c d) :
    Icc (a + c) (b + d) ⊆ (A ∩ Icc a b) + (B ∩ Icc c d) := by
  intro x hx
  have hB' : IsClosed ((fun y => x - y) ⁻¹' B) := hB.preimage (continuous_const.sub continuous_id)
  have hJ' := bal_refl hB.measurableSet x hJ
  have hd' : dA A a b = dA ((fun y => x - y) ⁻¹' B) (x - d) (x - c) := by
    rw [refl_dA hB.measurableSet, sub_sub_cancel, sub_sub_cancel]; exact hd
  obtain ⟨t, ⟨htA, htI⟩, htB, htJ⟩ :
      ((A ∩ Icc a b) ∩ ((fun y => x - y) ⁻¹' B ∩ Icc (x - d) (x - c))).Nonempty := by
    rcases le_total a (x - d) with h | h
    · exact lemma_3_5 hA hB' hI hJ' h (by linarith [hx.2]) hd'
    · obtain ⟨t, h1, h2⟩ := lemma_3_5 hB' hA hJ' hI h (by linarith [hx.1]) hd'.symm
      exact ⟨t, h2, h1⟩
  exact Set.mem_add.mpr ⟨t, ⟨htA, htI⟩, x - t, ⟨htB, by linarith [htJ.2], by linarith [htJ.1]⟩,
    by ring⟩

lemma empty_of_not {S : Set ℝ} {p q : ℝ} (h : ¬ ∃ t ∈ S, p ≤ t ∧ t ≤ q) : S ∩ Icc p q = ∅ := by
  ext t
  simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false, not_and]
  intro h1 h2 h3
  exact h ⟨t, h1, h2, h3⟩

lemma empty_mono {S : Set ℝ} {p q p' q' : ℝ} (h : S ∩ Icc p q = ∅) (h1 : p ≤ p') (h2 : q' ≤ q) :
    S ∩ Icc p' q' = ∅ := by
  rw [← subset_empty_iff, ← h]
  exact inter_subset_inter_right _ (Icc_subset_Icc h1 h2)

/-- A closed set missing `[p,q]` misses a neighbourhood of it. -/
lemma gap (hA : IsClosed A) {p q : ℝ} (hpq : p ≤ q) (h : A ∩ Icc p q = ∅) :
    ∃ η > 0, A ∩ Icc (p - η) (q + η) = ∅ := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_cthickening_subset_open hA.isOpen_compl
    (show Icc p q ⊆ Aᶜ from fun t ht htA => by
      have : t ∈ A ∩ Icc p q := ⟨htA, ht⟩
      rw [h] at this; exact this)
  refine ⟨δ, hδ, ?_⟩
  ext t
  simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false, not_and]
  intro htA ht1 ht2
  have hm : t ∈ Metric.cthickening δ (Icc p q) := by
    refine Metric.mem_cthickening_of_dist_le t (max p (min t q)) δ (Icc p q)
      ⟨le_max_left _ _, max_le hpq (min_le_right _ _)⟩ ?_
    rw [Real.dist_eq, abs_le]
    constructor
    · have : max p (min t q) ≤ t + δ := max_le (by linarith) (by linarith [min_le_left t q])
      linarith
    · have : t - δ ≤ min t q := le_min (by linarith) (by linarith)
      linarith [le_max_right p (min t q)]
  exact hsub hm htA

/-- Translation `y ↦ y - x` preserves discrepancy. -/
lemma shift_dA (hA : MeasurableSet A) (x p q : ℝ) :
    dA ((fun y => y - x) ⁻¹' A) p q = dA A (p - x) (q - x) := by
  have hpre : (fun y => y - x) ⁻¹' (A ∩ Icc (p - x) (q - x)) =
      (fun y => y - x) ⁻¹' A ∩ Icc p q := by
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith, by linarith⟩
  unfold dA
  rw [← hpre, (measurePreserving_sub_right volume x).measureReal_preimage
    (hA.inter measurableSet_Icc).nullMeasurableSet]
  ring

/-- `(A + x) ∩ B ∩ [p,q] ≠ ∅` from the discrepancy inequality, both sets meeting `[p,q]`. -/
lemma meet_shift (hA : IsClosed A) (hB : IsClosed B) {p q x : ℝ} (hpq : p ≤ q)
    (hAne : ∃ s ∈ A, p - x ≤ s ∧ s ≤ q - x) (hBne : ∃ t ∈ B, p ≤ t ∧ t ≤ q)
    (h : 0 ≤ dA A (p - x) (q - x) + dA B p q) : ∃ t ∈ B, p ≤ t ∧ t ≤ q ∧ t - x ∈ A := by
  have hA' : IsClosed ((fun y => y - x) ⁻¹' A) := hA.preimage (continuous_id.sub continuous_const)
  obtain ⟨s, hs, h1, h2⟩ := hAne
  obtain ⟨t, ht, h3, h4⟩ := hBne
  rcases eq_or_lt_of_le hpq with hpq' | hpq'
  · refine ⟨t, ht, h3, h4, ?_⟩
    have : t - x = s := by linarith
    rw [this]; exact hs
  · rw [← shift_dA hA.measurableSet] at h
    unfold dA at h
    obtain ⟨y, hy, hyA, hyB⟩ := inter_nonempty hA' hB hpq'
      ⟨s + x, show s + x - x ∈ A by simpa using hs, by linarith, by linarith⟩ ⟨t, ht, h3, h4⟩
      (by linarith)
    exact ⟨y, hyB, hy.1, hy.2, hyA⟩

/-- FGY Lemma 3.8. Here `D` is any upper bound for the discrepancies of `B` (e.g. `d(B)`). -/
theorem lemma_3_8 (hA : IsClosed A) (hB : IsClosed B) {a b c d D : ℝ} (hI : RightBal A a b)
    (hJ : LeftBal B c d) (hD : ∀ p q, p ≤ q → dA B p q ≤ D) (hDI : D ≤ dA A a b) {x : ℝ}
    (hx1 : c - b ≤ x) (hx2 : x ≤ c - b + 2 * volume.real (B ∩ Icc c d)) :
    ∃ u ∈ A ∩ Icc a b, ∃ v ∈ B ∩ Icc c d, v - u = x := by
  have hAm := hA.measurableSet
  have hBm := hB.measurableSet
  have hab := hI.1
  have hcd := hJ.1
  have hIlen := dA_le_len A hab
  have hJD := hD c d hcd
  have hdJ : dA B c d = 2 * volume.real (B ∩ Icc c d) - (d - c) := rfl
  have hxda : x ≤ d - a := by linarith
  have hvol : volume.real (B ∩ Icc c d) ≤ d - c := by
    calc _ ≤ volume.real (Icc c d) := measureReal_mono inter_subset_right measure_Icc_lt_top.ne
      _ = d - c := by rw [Real.volume_real_Icc, max_eq_left (by linarith)]
  rcases le_or_gt x (d - b) with hxdb | hxdb
  · rcases le_or_gt x (c - a) with hxca | hxca
    · have g1 : 0 ≤ dA B c (b + x) := hJ.2.2 _ ⟨by linarith, by linarith⟩
      have g2 : 0 ≤ dA A (c - x) b := hI.2.2 _ ⟨by linarith, by linarith⟩
      have e : b + x - x = b := by ring
      obtain ⟨t, htB, ht1, ht2, htA⟩ := meet_shift hA hB (p := c) (q := b + x) (x := x)
        (by linarith) ⟨b, hI.2.1, by linarith, by linarith⟩ ⟨c, hJ.2.1, le_rfl, by linarith⟩
        (by rw [e]; linarith)
      exact ⟨t - x, ⟨htA, by linarith, by linarith⟩, t, ⟨htB, by linarith, by linarith⟩, by ring⟩
    · have hBK : ∃ t ∈ B, a + x ≤ t ∧ t ≤ b + x := by
        by_contra hne
        obtain ⟨η, hη, hgap⟩ := gap hB (by linarith) (empty_of_not hne)
        have hη' : 0 < min η (a + x - c) := lt_min hη (by linarith)
        have hη'1 : min η (a + x - c) ≤ η := min_le_left _ _
        have hη'2 : min η (a + x - c) ≤ a + x - c := min_le_right _ _
        have hempty' := empty_mono hgap (p' := a + x - min η (a + x - c)) (q' := b + x)
          (by linarith) (by linarith)
        have s1 := dA_split hBm (a := c) (b := a + x - min η (a + x - c)) (c := b + x)
          (by linarith) (by linarith)
        rw [dA_of_disj hempty'] at s1
        have g1 : 0 ≤ dA B c (b + x) := hJ.2.2 _ ⟨by linarith, by linarith⟩
        have g2 := hD c (a + x - min η (a + x - c)) (by linarith)
        linarith
      have g1 : 0 ≤ dA B c (b + x) := hJ.2.2 _ ⟨by linarith, by linarith⟩
      have s1 := dA_split hBm (a := c) (b := a + x) (c := b + x) (by linarith) (by linarith)
      have g2 := hD c (a + x) (by linarith)
      have e1 : a + x - x = a := by ring
      have e2 : b + x - x = b := by ring
      obtain ⟨t, htB, ht1, ht2, htA⟩ := meet_shift hA hB (p := a + x) (q := b + x) (x := x)
        (by linarith) ⟨b, hI.2.1, by linarith, by linarith⟩ hBK (by rw [e1, e2]; linarith)
      exact ⟨t - x, ⟨htA, by linarith, by linarith⟩, t, ⟨htB, by linarith, by linarith⟩, by ring⟩
  · have hB1 : x - d + b ≤ dA B c d := by rw [hdJ]; linarith
    rcases lt_or_ge x (c - a) with hxca | hxca
    · have hAK : ∃ s ∈ A, c - x ≤ s ∧ s ≤ d - x := by
        by_contra hne
        obtain ⟨η, hη, hgap⟩ := gap hA (by linarith) (empty_of_not hne)
        have hη' : 0 < min η (b - (d - x)) := lt_min hη (by linarith)
        have hη'1 : min η (b - (d - x)) ≤ η := min_le_left _ _
        have hη'2 : min η (b - (d - x)) ≤ b - (d - x) := min_le_right _ _
        have hempty' := empty_mono hgap (p' := c - x) (q' := d - x + min η (b - (d - x)))
          (by linarith) (by linarith)
        have s1 := dA_split hAm (a := c - x) (b := d - x + min η (b - (d - x))) (c := b)
          (by linarith) (by linarith)
        rw [dA_of_disj hempty'] at s1
        have g1 : 0 ≤ dA A (c - x) b := hI.2.2 _ ⟨by linarith, by linarith⟩
        have g2 := dA_le_len A (a := d - x + min η (b - (d - x))) (b := b) (by linarith)
        linarith
      have g1 : 0 ≤ dA A (c - x) b := hI.2.2 _ ⟨by linarith, by linarith⟩
      have s1 := dA_split hAm (a := c - x) (b := d - x) (c := b) (by linarith) (by linarith)
      have g2 := dA_le_len A (a := d - x) (b := b) (by linarith)
      obtain ⟨t, htB, ht1, ht2, htA⟩ := meet_shift hA hB (p := c) (q := d) (x := x) hcd hAK
        ⟨c, hJ.2.1, le_rfl, hcd⟩ (by linarith)
      exact ⟨t - x, ⟨htA, by linarith, by linarith⟩, t, ⟨htB, ht1, ht2⟩, by ring⟩
    · have hAK : ∃ s ∈ A, a ≤ s ∧ s ≤ d - x := by
        by_contra hne
        have hempty := empty_of_not hne
        obtain ⟨η, hη, hgap⟩ := gap hA (by linarith) hempty
        have hη' : 0 < min η (b - (d - x)) := lt_min hη (by linarith)
        have hη'1 : min η (b - (d - x)) ≤ η := min_le_left _ _
        have hη'2 : min η (b - (d - x)) ≤ b - (d - x) := min_le_right _ _
        have hempty2 := empty_mono hgap (p' := d - x) (q' := d - x + min η (b - (d - x)))
          (by linarith) (by linarith)
        have s1 := dA_split hAm (a := a) (b := d - x) (c := b) (by linarith) (by linarith)
        have s2 := dA_split hAm (a := d - x) (b := d - x + min η (b - (d - x))) (c := b)
          (by linarith) (by linarith)
        rw [dA_of_disj hempty] at s1
        rw [dA_of_disj hempty2] at s2
        have g2 := dA_le_len A (a := d - x + min η (b - (d - x))) (b := b) (by linarith)
        have s3 := dA_split hBm (a := c) (b := a + x) (c := d) (by linarith) (by linarith)
        have g3 := hD c (a + x) (by linarith)
        have g4 := dA_le_len B (a := a + x) (b := d) (by linarith)
        linarith
      have hBK : ∃ t ∈ B, a + x ≤ t ∧ t ≤ d := by
        by_contra hne
        rcases eq_or_lt_of_le (show c ≤ a + x by linarith) with hc | hc
        · exact hne ⟨c, hJ.2.1, by linarith, hcd⟩
        obtain ⟨η, hη, hgap⟩ := gap hB (by linarith) (empty_of_not hne)
        have hη' : 0 < min η (a + x - c) := lt_min hη (by linarith)
        have hη'1 : min η (a + x - c) ≤ η := min_le_left _ _
        have hη'2 : min η (a + x - c) ≤ a + x - c := min_le_right _ _
        have hempty' := empty_mono hgap (p' := a + x - min η (a + x - c)) (q' := d)
          (by linarith) (by linarith)
        have s1 := dA_split hBm (a := c) (b := a + x - min η (a + x - c)) (c := d)
          (by linarith) (by linarith)
        rw [dA_of_disj hempty'] at s1
        have g := hD c (a + x - min η (a + x - c)) (by linarith)
        linarith
      have s1 := dA_split hAm (a := a) (b := d - x) (c := b) (by linarith) (by linarith)
      have g2 := dA_le_len A (a := d - x) (b := b) (by linarith)
      have s3 := dA_split hBm (a := c) (b := a + x) (c := d) (by linarith) (by linarith)
      have g3 := hD c (a + x) (by linarith)
      have e1 : a + x - x = a := by ring
      obtain ⟨s, hs, hs1, hs2⟩ := hAK
      obtain ⟨t, htB, ht1, ht2, htA⟩ := meet_shift hA hB (p := a + x) (q := d) (x := x)
        (by linarith) ⟨s, hs, by linarith, hs2⟩ hBK (by rw [e1]; linarith)
      exact ⟨t - x, ⟨htA, by linarith, by linarith⟩, t, ⟨htB, by linarith, ht2⟩, by ring⟩

lemma leftBal_refl (hA : MeasurableSet A) {a b : ℝ} (x : ℝ) (h : LeftBal A a b) :
    RightBal ((fun y => x - y) ⁻¹' A) (x - b) (x - a) := by
  refine ⟨by linarith [h.1], ?_, fun z hz => ?_⟩
  · show x - (x - a) ∈ A; rw [sub_sub_cancel]; exact h.2.1
  · rw [refl_dA hA, sub_sub_cancel]; exact h.2.2 _ ⟨by linarith [hz.2], by linarith [hz.1]⟩

lemma rightBal_refl (hA : MeasurableSet A) {a b : ℝ} (x : ℝ) (h : RightBal A a b) :
    LeftBal ((fun y => x - y) ⁻¹' A) (x - b) (x - a) := by
  refine ⟨by linarith [h.1], ?_, fun z hz => ?_⟩
  · show x - (x - b) ∈ A; rw [sub_sub_cancel]; exact h.2.1
  · rw [refl_dA hA, sub_sub_cancel]; exact h.2.2 _ ⟨by linarith [hz.2], by linarith [hz.1]⟩

open Pointwise in
/-- FGY Corollary 3.9, first assertion. -/
theorem cor_3_9_left (hA : IsClosed A) (hB : IsClosed B) {a b c d D : ℝ} (hI : LeftBal A a b)
    (hJ : LeftBal B c d) (hD : ∀ p q, p ≤ q → dA B p q ≤ D) (hDI : D ≤ dA A a b) :
    Icc (a + c) (a + c + 2 * volume.real (B ∩ Icc c d)) ⊆ (A ∩ Icc a b) + (B ∩ Icc c d) := by
  intro x hx
  have hA' : IsClosed ((fun y => (0 : ℝ) - y) ⁻¹' A) :=
    hA.preimage (continuous_const.sub continuous_id)
  have hI' := leftBal_refl hA.measurableSet 0 hI
  have hd' : dA ((fun y => (0 : ℝ) - y) ⁻¹' A) (0 - b) (0 - a) = dA A a b := by
    rw [refl_dA hA.measurableSet, sub_sub_cancel, sub_sub_cancel]
  obtain ⟨u, ⟨huA, hu1, hu2⟩, v, hvB, huv⟩ := lemma_3_8 hA' hB hI' hJ hD (by rw [hd']; exact hDI)
    (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  exact Set.mem_add.mpr ⟨0 - u, ⟨huA, by linarith, by linarith⟩, v, hvB, by linarith⟩

open Pointwise in
/-- FGY Corollary 3.9, second assertion. -/
theorem cor_3_9_right (hA : IsClosed A) (hB : IsClosed B) {a b c d D : ℝ} (hI : RightBal A a b)
    (hJ : RightBal B c d) (hD : ∀ p q, p ≤ q → dA B p q ≤ D) (hDI : D ≤ dA A a b) :
    Icc (b + d - 2 * volume.real (B ∩ Icc c d)) (b + d) ⊆ (A ∩ Icc a b) + (B ∩ Icc c d) := by
  intro x hx
  have hA' : IsClosed ((fun y => (0 : ℝ) - y) ⁻¹' A) :=
    hA.preimage (continuous_const.sub continuous_id)
  have hB' : IsClosed ((fun y => (0 : ℝ) - y) ⁻¹' B) :=
    hB.preimage (continuous_const.sub continuous_id)
  have hI' := rightBal_refl hA.measurableSet 0 hI
  have hJ' := rightBal_refl hB.measurableSet 0 hJ
  have hD' : ∀ p q, p ≤ q → dA ((fun y => (0 : ℝ) - y) ⁻¹' B) p q ≤ D := fun p q hpq => by
    rw [refl_dA hB.measurableSet]; exact hD _ _ (by linarith)
  have hd' : dA ((fun y => (0 : ℝ) - y) ⁻¹' A) (0 - b) (0 - a) = dA A a b := by
    rw [refl_dA hA.measurableSet, sub_sub_cancel, sub_sub_cancel]
  have hvol : volume.real ((fun y => (0 : ℝ) - y) ⁻¹' B ∩ Icc (0 - d) (0 - c)) =
      volume.real (B ∩ Icc c d) := by
    have := refl_dA hB.measurableSet 0 (0 - d) (0 - c)
    rw [sub_sub_cancel, sub_sub_cancel] at this
    unfold dA at this; linarith
  have hmem := cor_3_9_left hA' hB' hI' hJ' hD' (by rw [hd']; exact hDI)
    (show -x ∈ Icc _ _ from ⟨by linarith [hx.2], by rw [hvol]; linarith [hx.1]⟩)
  obtain ⟨u, ⟨huA, hu1, hu2⟩, v, ⟨hvB, hv1, hv2⟩, huv⟩ := Set.mem_add.mp hmem
  exact Set.mem_add.mpr ⟨0 - u, ⟨huA, by linarith, by linarith⟩, 0 - v,
    ⟨hvB, by linarith, by linarith⟩, by linarith⟩

lemma dA_ge (A : Set ℝ) {a b : ℝ} : -(b - a) ≤ dA A a b := by
  unfold dA
  have := measureReal_nonneg (μ := volume) (s := A ∩ Icc a b)
  linarith

/-- Local structure of a finite union of closed intervals just to the right of a point. -/
lemma local_struct (s : Finset (ℝ × ℝ)) (M : ℝ) : ∃ ε > 0,
    Ioo M (M + ε) ⊆ (⋃ p ∈ s, Icc p.1 p.2) ∨ (⋃ p ∈ s, Icc p.1 p.2) ∩ Ioo M (M + ε) = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, Or.inr (by simp)⟩
  | insert p s hp ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hloc : ∃ δ > 0, Ioo M (M + δ) ⊆ Icc p.1 p.2 ∨ Icc p.1 p.2 ∩ Ioo M (M + δ) = ∅ := by
      by_cases h1 : p.1 ≤ M ∧ M < p.2
      · exact ⟨p.2 - M, by linarith [h1.2],
          Or.inl fun t ht => ⟨by linarith [ht.1, h1.1], by linarith [ht.2]⟩⟩
      · by_cases h2 : M < p.1
        · refine ⟨p.1 - M, by linarith, Or.inr ?_⟩
          ext t
          simp only [mem_inter_iff, mem_Icc, mem_Ioo, mem_empty_iff_false, iff_false]
          rintro ⟨⟨h3, _⟩, _, h4⟩
          linarith
        · refine ⟨1, one_pos, Or.inr ?_⟩
          ext t
          simp only [mem_inter_iff, mem_Icc, mem_Ioo, mem_empty_iff_false, iff_false]
          rintro ⟨⟨h3, h5⟩, h6, _⟩
          have h2' : p.1 ≤ M := not_lt.mp h2
          have : p.2 ≤ M := by
            by_contra h7
            exact h1 ⟨h2', not_le.mp h7⟩
          linarith
    obtain ⟨δ, hδ, h'⟩ := hloc
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    have hsub1 : Ioo M (M + min ε δ) ⊆ Ioo M (M + ε) :=
      Ioo_subset_Ioo le_rfl (by linarith [min_le_left ε δ])
    have hsub2 : Ioo M (M + min ε δ) ⊆ Ioo M (M + δ) :=
      Ioo_subset_Ioo le_rfl (by linarith [min_le_right ε δ])
    rw [Finset.set_biUnion_insert]
    rcases h' with h' | h'
    · exact Or.inl ((hsub2.trans h').trans subset_union_left)
    · rcases h with h | h
      · exact Or.inl ((hsub1.trans h).trans subset_union_right)
      · right
        rw [union_inter_distrib_right]
        rw [← subset_empty_iff] at h h' ⊢
        exact union_subset ((inter_subset_inter_right _ hsub2).trans h')
          ((inter_subset_inter_right _ hsub1).trans h)

/-- Existence of the maximal left-balanced interval starting at a point of `A`. -/
lemma exists_maxLB (hA : MeasurableSet A) (hfin : volume A ≠ ⊤) {c : ℝ} (hc : c ∈ A) :
    ∃ M, LeftBal A c M ∧ ∀ y, LeftBal A c y → y ≤ M := by
  set S := {y | LeftBal A c y} with hSdef
  have hcS : c ∈ S := ⟨le_rfl, hc, fun x hx => by
    have : x = c := le_antisymm hx.2 hx.1
    rw [this]
    have := dA_ge A (a := c) (b := c)
    linarith⟩
  have hbdd : BddAbove S := ⟨c + 2 * volume.real A, fun y hy => by
    have h1 := hy.2.2 y ⟨hy.1, le_rfl⟩
    unfold dA at h1
    have := measureReal_mono (μ := volume) (inter_subset_left : A ∩ Icc c y ⊆ A) hfin
    linarith⟩
  refine ⟨sSup S, ⟨le_csSup hbdd hcS, hc, fun x hx => ?_⟩, fun y hy => le_csSup hbdd hy⟩
  rcases eq_or_lt_of_le hx.2 with hxM | hxM
  · rw [hxM]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y, hyS, hy⟩ := exists_lt_of_lt_csSup ⟨c, hcS⟩ (show sSup S - ε < sSup S by linarith)
    have hyM : y ≤ sSup S := le_csSup hbdd hyS
    have h1 := hyS.2.2 y ⟨hyS.1, le_rfl⟩
    have h2 := dA_split hA hyS.1 hyM
    have h3 := dA_ge A (a := y) (b := sSup S)
    linarith
  · obtain ⟨y, hyS, hy⟩ := exists_lt_of_lt_csSup ⟨c, hcS⟩ hxM
    exact hyS.2.2 x ⟨hx.1, hy.le⟩

/-- The next left-balanced block starts beyond `c + 2|A ∩ [c, M]|` (proof of FGY Cor. 3.11). -/
lemma gap_next (hA : MeasurableSet A) {c M c' d' : ℝ} (hJ : LeftBal A c M)
    (hmax : ∀ y, LeftBal A c y → y ≤ M) (hc' : M < c') (hJ' : LeftBal A c' d') :
    c + 2 * volume.real (A ∩ Icc c M) < c' := by
  by_contra hcon
  have hcon' : c' ≤ c + 2 * volume.real (A ∩ Icc c M) := not_lt.mp hcon
  have hcM := hJ.1
  have hmid : ∀ x, M ≤ x → x ≤ c' → 0 ≤ dA A c x := fun x h1 h2 => by
    have := measureReal_mono (μ := volume)
      (inter_subset_inter_right A (Icc_subset_Icc le_rfl h1) : A ∩ Icc c M ⊆ A ∩ Icc c x)
      (fin_inter A c x)
    unfold dA; linarith
  have hLB : LeftBal A c d' := ⟨by linarith [hJ'.1], hJ.2.1, fun x hx => by
    rcases le_total x M with h | h
    · exact hJ.2.2 x ⟨hx.1, h⟩
    · rcases le_total x c' with h' | h'
      · exact hmid x h h'
      · rw [dA_split hA (by linarith : c ≤ c') h']
        have := hmid c' hc'.le le_rfl
        have := hJ'.2.2 x ⟨h', hx.2⟩
        linarith⟩
  have := hmax d' hLB
  linarith [hJ'.1]

open Pointwise in
/-- FGY Corollary 3.11, first assertion, for `B` a nonempty finite union of closed intervals.
`D` bounds all discrepancies of `B`, and `R` bounds the right discrepancies `d_B([x, max B])`. -/
theorem cor_3_11 (hA : IsClosed A) {a b D : ℝ} (hI : LeftBal A a b) (hDI : D ≤ dA A a b) :
    ∀ n : ℕ, ∀ s : Finset (ℝ × ℝ), s.card ≤ n → ∀ R : ℝ,
      (⋃ p ∈ s, Icc p.1 p.2).Nonempty →
      (∀ p q, p ≤ q → dA (⋃ p ∈ s, Icc p.1 p.2) p q ≤ D) →
      (∀ x ≤ sSup (⋃ p ∈ s, Icc p.1 p.2),
        dA (⋃ p ∈ s, Icc p.1 p.2) x (sSup (⋃ p ∈ s, Icc p.1 p.2)) ≤ R) →
      2 * volume.real (⋃ p ∈ s, Icc p.1 p.2) ≤
        volume.real (((A ∩ Icc a b) + ⋃ p ∈ s, Icc p.1 p.2) ∩
          Icc (a + sInf (⋃ p ∈ s, Icc p.1 p.2)) (a + sSup (⋃ p ∈ s, Icc p.1 p.2) + R)) := by
  classical
  intro n
  induction n with
  | zero =>
    intro s hs R hne
    rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hs)] at hne
    simp at hne
  | succ n ih =>
    intro s hs R hne hD hR
    set B := ⋃ p ∈ s, Icc p.1 p.2 with hBdef
    have hBc : IsCompact B := s.isCompact_biUnion fun p _ => isCompact_Icc
    have hBcl := hBc.isClosed
    have hBm := hBcl.measurableSet
    have hfin : volume B ≠ ⊤ := hBc.measure_lt_top.ne
    have hcB : sInf B ∈ B := hBc.sInf_mem hne
    have hMxB : sSup B ∈ B := hBc.sSup_mem hne
    have hbddB : BddAbove B := hBc.bddAbove
    have hbddB' : BddBelow B := hBc.bddBelow
    set c := sInf B with hcdef
    set Mx := sSup B with hMxdef
    have hBsub : ∀ t ∈ B, c ≤ t ∧ t ≤ Mx := fun t ht => ⟨csInf_le hbddB' ht, le_csSup hbddB ht⟩
    have hcMx : c ≤ Mx := (hBsub _ hcB).2
    obtain ⟨M, hJ, hmax⟩ := exists_maxLB hBm hfin hcB
    have hAI : IsCompact (A ∩ Icc a b) := isCompact_Icc.inter_left hA
    have hS : IsCompact ((A ∩ Icc a b) + B) := hAI.add hBc
    have hR0 : 0 ≤ R := le_trans (by have := dA_ge B (a := Mx) (b := Mx); linarith) (hR Mx le_rfl)
    have hK1 := cor_3_9_left hA hBcl hI hJ hD hDI
    have hK1S : (A ∩ Icc a b) + (B ∩ Icc c M) ⊆ (A ∩ Icc a b) + B :=
      Set.add_subset_add_left inter_subset_left
    have hvolK : ∀ u v : ℝ, u ≤ v → volume.real (Icc u v) = v - u := fun u v huv => by
      rw [Real.volume_real_Icc, max_eq_left (by linarith)]
    have hvJ : 0 ≤ volume.real (B ∩ Icc c M) := measureReal_nonneg
    rcases le_or_gt Mx M with hMxM | hMMx
    · have hBJ : B ∩ Icc c M = B :=
        inter_eq_left.mpr fun t ht => ⟨(hBsub t ht).1, (hBsub t ht).2.trans hMxM⟩
      rw [hBJ] at hK1 hK1S hvJ
      have hRc := hR c hcMx
      have hBI : B ∩ Icc c Mx = B := inter_eq_left.mpr fun t ht => ⟨(hBsub t ht).1, (hBsub t ht).2⟩
      have hdc : dA B c Mx = 2 * volume.real B - (Mx - c) := by
        unfold dA
        rw [hBI]
      calc 2 * volume.real B = volume.real (Icc (a + c) (a + c + 2 * volume.real B)) := by
            rw [hvolK _ _ (by linarith)]; ring
        _ ≤ _ := by
          refine measureReal_mono ?_ (ne_top_of_le_ne_top measure_Icc_lt_top.ne
            (measure_mono inter_subset_right))
          intro t ht
          exact ⟨hK1S (hK1 ht), by linarith [ht.1], by linarith [ht.2]⟩
    · obtain ⟨ε, hε, hloc⟩ := local_struct s M
      rcases hloc with hloc | hloc
      · exfalso
        have hLB : LeftBal B c (M + ε / 2) := ⟨by linarith [hJ.1], hJ.2.1, fun x hx => by
          rcases le_total x M with h | h
          · exact hJ.2.2 x ⟨hx.1, h⟩
          · rw [dA_split hBm hJ.1 h]
            have h1 := hJ.2.2 M ⟨hJ.1, le_rfl⟩
            have h2 : x - M ≤ volume.real (B ∩ Icc M x) := by
              calc x - M = volume.real (Ioo M x) := by
                    rw [Real.volume_real_Ioo, max_eq_left (by linarith)]
                _ ≤ _ := by
                  refine measureReal_mono ?_ (fin_inter B M x)
                  intro t ht
                  exact ⟨hloc ⟨ht.1, by linarith [ht.2, hx.2]⟩, ht.1.le, ht.2.le⟩
            unfold dA at h1 ⊢
            linarith⟩
        have := hmax _ hLB
        linarith
      · set s₂ := s.filter (fun p => M < p.1) with hs₂def
        set B₂ := ⋃ p ∈ s₂, Icc p.1 p.2 with hB₂def
        have hB₂B : B₂ ⊆ B := biUnion_subset_biUnion_left (Finset.coe_subset.mpr
          (Finset.filter_subset _ _))
        have hB₂far : ∀ t ∈ B₂, M + ε ≤ t := by
          intro t ht
          simp only [hB₂def, mem_iUnion, exists_prop, hs₂def, Finset.mem_filter] at ht
          obtain ⟨p, ⟨hp, hMp⟩, htp⟩ := ht
          have : M + ε ≤ p.1 := by
            by_contra h
            have hpB : p.1 ∈ B := mem_biUnion hp ⟨le_rfl, htp.1.trans htp.2⟩
            have : p.1 ∈ B ∩ Ioo M (M + ε) := ⟨hpB, hMp, not_le.mp h⟩
            rw [hloc] at this; exact this
          linarith [htp.1]
        have hBsplit : B ⊆ (B ∩ Icc c M) ∪ B₂ := by
          intro t ht
          have ht' := ht
          simp only [hBdef, mem_iUnion, exists_prop] at ht'
          obtain ⟨p, hp, htp⟩ := ht'
          by_cases hMp : M < p.1
          · right
            exact mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hp, hMp⟩)) htp
          · left
            refine ⟨ht, (hBsub t ht).1, ?_⟩
            by_contra htM
            have htM' : M < t := not_le.mp htM
            have hm2 : M < min t (M + ε / 2) := lt_min htM' (by linarith)
            have hu : min t (M + ε / 2) ∈ B ∩ Ioo M (M + ε) :=
              ⟨mem_biUnion hp ⟨by linarith [not_lt.mp hMp, hm2],
                (min_le_left _ _).trans htp.2⟩,
                lt_min htM' (by linarith), by linarith [min_le_right t (M + ε / 2)]⟩
            rw [hloc] at hu; exact hu
        have hMxB₂ : Mx ∈ B₂ := by
          rcases hBsplit hMxB with h | h
          · linarith [h.2.2]
          · exact h
        have hne₂ : B₂.Nonempty := ⟨Mx, hMxB₂⟩
        have hB₂c : IsCompact B₂ := s₂.isCompact_biUnion fun p _ => isCompact_Icc
        have hsup₂ : sSup B₂ = Mx :=
          IsGreatest.csSup_eq ⟨hMxB₂, fun t ht => (hBsub t (hB₂B ht)).2⟩
        have hc₂B₂ : sInf B₂ ∈ B₂ := hB₂c.sInf_mem hne₂
        have hc₂far := hB₂far _ hc₂B₂
        have hc₂Mx : sInf B₂ ≤ Mx := csInf_le hB₂c.bddBelow hMxB₂
        have hcard : s₂.card ≤ n := by
          have hcs : c ∈ ⋃ p ∈ s, Icc p.1 p.2 := hcB
          obtain ⟨p, hp, hcp⟩ := mem_iUnion₂.mp hcs
          have hss : s₂ ⊂ s := Finset.filter_ssubset.mpr ⟨p, hp,
            fun h => by have h' : M < p.1 := h; linarith [hcp.1, hJ.1]⟩
          have := Finset.card_lt_card hss
          omega
        have hmono : ∀ p q, volume.real (B₂ ∩ Icc p q) ≤ volume.real (B ∩ Icc p q) := fun p q =>
          measureReal_mono (inter_subset_inter_left _ hB₂B) (fin_inter B p q)
        have hD₂ : ∀ p q, p ≤ q → dA B₂ p q ≤ D := fun p q hpq => by
          have := hD p q hpq; have := hmono p q; unfold dA at *; linarith
        have hR₂ : ∀ x ≤ sSup B₂, dA B₂ x (sSup B₂) ≤ R := fun x hx => by
          rw [hsup₂] at hx ⊢
          have := hR x hx; have := hmono x Mx; unfold dA at *; linarith
        have hIH := ih s₂ hcard R hne₂ hD₂ hR₂
        rw [hsup₂] at hIH
        have hB₂cB : sInf B₂ ∈ B := hB₂B hc₂B₂
        have hgap := gap_next hBm hJ hmax (c' := sInf B₂) (d' := sInf B₂) (by linarith)
          ⟨le_rfl, hB₂cB, fun x hx => by
            have : x = sInf B₂ := le_antisymm hx.2 hx.1
            rw [this]; have := dA_ge B (a := sInf B₂) (b := sInf B₂); linarith⟩
        have hdisjB : Disjoint (B ∩ Icc c M) B₂ := Set.disjoint_left.mpr fun t h1 h2 => by
          linarith [h1.2.2, hB₂far t h2]
        have hBeq : B = (B ∩ Icc c M) ∪ B₂ :=
          Subset.antisymm hBsplit (union_subset inter_subset_left hB₂B)
        have hvolB : volume.real B = volume.real (B ∩ Icc c M) + volume.real B₂ := by
          conv_lhs => rw [hBeq]
          exact measureReal_union hdisjB hB₂c.isClosed.measurableSet (fin_inter B c M)
            (hB₂c.measure_lt_top.ne)
        set K1 := Icc (a + c) (a + c + 2 * volume.real (B ∩ Icc c M)) with hK1def
        set X := ((A ∩ Icc a b) + B₂) ∩ Icc (a + sInf B₂) (a + Mx + R) with hXdef
        have hXm : MeasurableSet X :=
          (hAI.add hB₂c).isClosed.measurableSet.inter measurableSet_Icc
        have hdisjKX : Disjoint K1 X := Set.disjoint_left.mpr fun t h1 h2 => by
          linarith [h1.2, h2.2.1]
        have hKX : K1 ∪ X ⊆ ((A ∩ Icc a b) + B) ∩ Icc (a + c) (a + Mx + R) := by
          rintro t (ht | ht)
          · exact ⟨hK1S (hK1 ht), by linarith [ht.1], by linarith [ht.2]⟩
          · exact ⟨Set.add_subset_add_left hB₂B ht.1, by linarith [ht.2.1], ht.2.2⟩
        have hvK1 : volume.real K1 = 2 * volume.real (B ∩ Icc c M) := by
          rw [hK1def, hvolK _ _ (by linarith)]; ring
        have hfinK : volume K1 ≠ ⊤ := measure_Icc_lt_top.ne
        have hfinX : volume X ≠ ⊤ :=
          ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right)
        have hU := measureReal_union hdisjKX hXm hfinK hfinX
        have hle := measureReal_mono (μ := volume) hKX
          (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right))
        linarith

lemma neg_union (s : Finset (ℝ × ℝ)) : (fun y => (0 : ℝ) - y) ⁻¹' (⋃ p ∈ s, Icc p.1 p.2) =
    ⋃ p ∈ s.image (fun p => (-p.2, -p.1)), Icc p.1 p.2 := by
  classical
  ext y
  simp only [mem_preimage, mem_iUnion, mem_Icc, exists_prop, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨(-p.2, -p.1), ⟨p, hp, rfl⟩, by dsimp only; linarith, by dsimp only; linarith⟩
  · rintro ⟨q, ⟨p, hp, rfl⟩, h1, h2⟩
    dsimp only at h1 h2
    exact ⟨p, hp, by linarith, by linarith⟩

open Pointwise in
/-- FGY Corollary 3.11, second assertion (`I` right balanced). `L` bounds the left
discrepancies `d_B([min B, x])`. -/
theorem cor_3_11_right (hA : IsClosed A) {a b D : ℝ} (hI : RightBal A a b) (hDI : D ≤ dA A a b)
    (s : Finset (ℝ × ℝ)) (L : ℝ) (hne : (⋃ p ∈ s, Icc p.1 p.2).Nonempty)
    (hD : ∀ p q, p ≤ q → dA (⋃ p ∈ s, Icc p.1 p.2) p q ≤ D)
    (hL : ∀ x, sInf (⋃ p ∈ s, Icc p.1 p.2) ≤ x →
      dA (⋃ p ∈ s, Icc p.1 p.2) (sInf (⋃ p ∈ s, Icc p.1 p.2)) x ≤ L) :
    2 * volume.real (⋃ p ∈ s, Icc p.1 p.2) ≤
      volume.real (((A ∩ Icc a b) + ⋃ p ∈ s, Icc p.1 p.2) ∩
        Icc (b + sInf (⋃ p ∈ s, Icc p.1 p.2) - L) (b + sSup (⋃ p ∈ s, Icc p.1 p.2))) := by
  classical
  have hB' := neg_union s
  set B := ⋃ p ∈ s, Icc p.1 p.2 with hBdef
  set s' := s.image (fun p => (-p.2, -p.1)) with hs'def
  set B' := ⋃ p ∈ s', Icc p.1 p.2 with hB'def
  have hBc : IsCompact B := s.isCompact_biUnion fun p _ => isCompact_Icc
  have hBm := hBc.isClosed.measurableSet
  have hinf : sInf B ∈ B := hBc.sInf_mem hne
  have hsup : sSup B ∈ B := hBc.sSup_mem hne
  have hmemB' : ∀ y, y ∈ B' ↔ 0 - y ∈ B := fun y => by rw [← hB']; exact Iff.rfl
  have hsup' : sSup B' = -sInf B := IsGreatest.csSup_eq ⟨(hmemB' _).mpr (by simpa using hinf),
    fun y hy => by have := csInf_le hBc.bddBelow ((hmemB' y).mp hy); linarith⟩
  have hinf' : sInf B' = -sSup B := IsLeast.csInf_eq ⟨(hmemB' _).mpr (by simpa using hsup),
    fun y hy => by have := le_csSup hBc.bddAbove ((hmemB' y).mp hy); linarith⟩
  have hne' : B'.Nonempty := ⟨_, (hmemB' (-sInf B)).mpr (by simpa using hinf)⟩
  have hA' : IsClosed ((fun y => (0 : ℝ) - y) ⁻¹' A) :=
    hA.preimage (continuous_const.sub continuous_id)
  have hI' := rightBal_refl hA.measurableSet 0 hI
  have hd' : dA ((fun y => (0 : ℝ) - y) ⁻¹' A) (0 - b) (0 - a) = dA A a b := by
    rw [refl_dA hA.measurableSet, sub_sub_cancel, sub_sub_cancel]
  have hdB' : ∀ p q, dA B' p q = dA B (0 - q) (0 - p) := fun p q => by
    rw [← hB', refl_dA hBm]
  have hD' : ∀ p q, p ≤ q → dA B' p q ≤ D := fun p q hpq => by
    rw [hdB']; exact hD _ _ (by linarith)
  have hR' : ∀ x ≤ sSup B', dA B' x (sSup B') ≤ L := fun x hx => by
    rw [hsup'] at hx ⊢
    rw [hdB']
    have := hL (0 - x) (by linarith)
    simpa using this
  have hvolB' : volume.real B' = volume.real B := by
    rw [← hB']
    exact (Measure.measurePreserving_sub_left volume (0 : ℝ)).measureReal_preimage
      hBm.nullMeasurableSet
  have key := cor_3_11 hA' hI' (by rw [hd']; exact hDI) s'.card s' le_rfl L hne' hD' hR'
  rw [hvolB', hsup', hinf'] at key
  refine key.trans ?_
  have hT : MeasurableSet (((A ∩ Icc a b) + B) ∩ Icc (b + sInf B - L) (b + sSup B)) :=
    ((isCompact_Icc.inter_left hA).add hBc).isClosed.measurableSet.inter measurableSet_Icc
  have hsub : (((fun y => (0 : ℝ) - y) ⁻¹' A ∩ Icc (0 - b) (0 - a)) + B') ∩
      Icc ((0 - b) + -sSup B) ((0 - b) + -sInf B + L) ⊆
      (fun y => (0 : ℝ) - y) ⁻¹' (((A ∩ Icc a b) + B) ∩ Icc (b + sInf B - L) (b + sSup B)) := by
    rintro y ⟨hy, hy1, hy2⟩
    obtain ⟨u, ⟨huA, hu1, hu2⟩, v, hv, rfl⟩ := Set.mem_add.mp hy
    exact ⟨Set.mem_add.mpr ⟨0 - u, ⟨huA, by linarith, by linarith⟩, 0 - v, (hmemB' v).mp hv,
      by ring⟩, by linarith, by linarith⟩
  calc _ ≤ volume.real ((fun y => (0 : ℝ) - y) ⁻¹'
        (((A ∩ Icc a b) + B) ∩ Icc (b + sInf B - L) (b + sSup B))) := by
        refine measureReal_mono hsub (ne_top_of_le_ne_top measure_Icc_lt_top.ne
          (measure_mono (show _ ⊆ Icc (0 - (b + sSup B)) (0 - (b + sInf B - L)) from
            fun y hy => ⟨by linarith [hy.2.2], by linarith [hy.2.1]⟩)))
    _ = _ := (Measure.measurePreserving_sub_left volume (0 : ℝ)).measureReal_preimage
        hT.nullMeasurableSet

/-! ### Toward Theorem 3.12 -/

/-- Finite union of closed intervals indexed by `s`. -/
def U (s : Finset (ℝ × ℝ)) : Set ℝ := ⋃ p ∈ s, Icc p.1 p.2

lemma U_compact (s : Finset (ℝ × ℝ)) : IsCompact (U s) :=
  s.isCompact_biUnion fun p _ => isCompact_Icc

/-- The discrepancy `d(X) = sup_{a ≤ b} d_X([a,b])`, written as in the reduction. -/
noncomputable def dsup (X : Set ℝ) : ℝ :=
  sSup {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (X ∩ Icc a b) - (b - a)}

lemma dsup_bdd {X : Set ℝ} (hX : volume X ≠ ⊤) :
    BddAbove {t | ∃ a b : ℝ, a ≤ b ∧ t = 2 * volume.real (X ∩ Icc a b) - (b - a)} :=
  ⟨2 * volume.real X, by
    rintro t ⟨a, b, hab, rfl⟩
    have := measureReal_mono (μ := volume) (inter_subset_left : X ∩ Icc a b ⊆ X) hX
    linarith⟩

lemma dA_le_dsup {X : Set ℝ} (hX : volume X ≠ ⊤) {p q : ℝ} (hpq : p ≤ q) : dA X p q ≤ dsup X :=
  le_csSup (dsup_bdd hX) ⟨p, q, hpq, rfl⟩

lemma dsup_le {X : Set ℝ} {C : ℝ} (h : ∀ p q, p ≤ q → dA X p q ≤ C) : dsup X ≤ C :=
  csSup_le ⟨_, 0, 0, le_rfl, rfl⟩ (by rintro t ⟨a, b, hab, rfl⟩; exact h a b hab)

lemma dsup_nonneg {X : Set ℝ} (hX : volume X ≠ ⊤) : 0 ≤ dsup X :=
  le_trans (by have := dA_ge X (a := 0) (b := 0); linarith) (dA_le_dsup hX (le_refl (0 : ℝ)))

lemma g_lip {X : Set ℝ} (hX : MeasurableSet X) {x0 a b : ℝ} (ha : x0 ≤ a) (hab : a ≤ b) :
    |dA X x0 b - dA X x0 a| ≤ b - a := by
  rw [dA_split hX ha hab, abs_le]
  have := dA_le_len X hab
  have := dA_ge X (a := a) (b := b)
  constructor <;> linarith

lemma exists_GL {X : Set ℝ} (hX : MeasurableSet X) {x0 M : ℝ} (h : x0 ≤ M) :
    ∃ e ∈ Icc x0 M, ∀ x ∈ Icc x0 M, dA X x0 x ≤ dA X x0 e := by
  have hc : ContinuousOn (fun x => dA X x0 x) (Icc x0 M) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    refine ⟨ε, hε, fun a ha hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    rcases le_total a b with hab | hab
    · have := g_lip hX ha.1 hab
      rw [abs_sub_comm]
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hd
      linarith
    · have := g_lip hX hb.1 hab
      rw [abs_of_nonneg (by linarith)] at hd
      linarith
  obtain ⟨e, he, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr h) hc
  exact ⟨e, he, fun x hx => hmax hx⟩

lemma leftBal_mono {X : Set ℝ} {c M e : ℝ} (h : LeftBal X c M) (hce : c ≤ e) (heM : e ≤ M) :
    LeftBal X c e := ⟨hce, h.2.1, fun x hx => h.2.2 x ⟨hx.1, hx.2.trans heM⟩⟩

lemma maxLB_gap (s : Finset (ℝ × ℝ)) {c M : ℝ} (hJ : LeftBal (U s) c M)
    (hmax : ∀ y, LeftBal (U s) c y → y ≤ M) : ∃ ε > 0, U s ∩ Ioo M (M + ε) = ∅ := by
  have hm : MeasurableSet (U s) := (U_compact s).isClosed.measurableSet
  obtain ⟨ε, hε, hloc⟩ := local_struct s M
  refine ⟨ε, hε, ?_⟩
  rcases hloc with hloc | hloc
  · exfalso
    have hLB : LeftBal (U s) c (M + ε / 2) := ⟨by linarith [hJ.1], hJ.2.1, fun x hx => by
      rcases le_total x M with h | h
      · exact hJ.2.2 x ⟨hx.1, h⟩
      · rw [dA_split hm hJ.1 h]
        have h1 := hJ.2.2 M ⟨hJ.1, le_rfl⟩
        have h2 : x - M ≤ volume.real (U s ∩ Icc M x) := by
          calc x - M = volume.real (Ioo M x) := by
                rw [Real.volume_real_Ioo, max_eq_left (by linarith)]
            _ ≤ _ := by
              refine measureReal_mono ?_ (fin_inter (U s) M x)
              intro t ht
              exact ⟨hloc ⟨ht.1, by linarith [ht.2, hx.2]⟩, ht.1.le, ht.2.le⟩
        unfold dA at h1 ⊢
        linarith⟩
    have := hmax _ hLB
    linarith
  · exact hloc

lemma split_after (s : Finset (ℝ × ℝ)) {c M ε : ℝ} (hε : 0 < ε) (hcM : c ≤ M) (hc : c ∈ U s)
    (hcmin : ∀ t ∈ U s, c ≤ t) (hgap : U s ∩ Ioo M (M + ε) = ∅) :
    U (s.filter (fun p => M < p.1)) ⊆ U s ∧
    (∀ t ∈ U (s.filter (fun p => M < p.1)), M + ε ≤ t) ∧
    U s ⊆ (U s ∩ Icc c M) ∪ U (s.filter (fun p => M < p.1)) ∧
    (s.filter (fun p => M < p.1)).card < s.card := by
  classical
  refine ⟨biUnion_subset_biUnion_left (Finset.coe_subset.mpr (Finset.filter_subset _ _)),
    ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, hp, htp⟩ := mem_iUnion₂.mp ht
    obtain ⟨hp, hMp⟩ := Finset.mem_filter.mp hp
    have : M + ε ≤ p.1 := by
      by_contra h
      have hpB : p.1 ∈ U s := mem_biUnion hp ⟨le_rfl, htp.1.trans htp.2⟩
      have : p.1 ∈ U s ∩ Ioo M (M + ε) := ⟨hpB, hMp, not_le.mp h⟩
      rw [hgap] at this; exact this
    linarith [htp.1]
  · intro t ht
    obtain ⟨p, hp, htp⟩ := mem_iUnion₂.mp ht
    by_cases hMp : M < p.1
    · right
      exact mem_biUnion (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hp, hMp⟩)) htp
    · left
      refine ⟨ht, hcmin t ht, ?_⟩
      by_contra htM
      have htM' : M < t := not_le.mp htM
      have hu : min t (M + ε / 2) ∈ U s ∩ Ioo M (M + ε) :=
        ⟨mem_biUnion hp ⟨by linarith [not_lt.mp hMp, lt_min htM' (by linarith : M < M + ε / 2)],
          (min_le_left _ _).trans htp.2⟩,
          lt_min htM' (by linarith), by linarith [min_le_right t (M + ε / 2)]⟩
      rw [hgap] at hu; exact hu
  · obtain ⟨p, hp, hcp⟩ := mem_iUnion₂.mp hc
    have hss : s.filter (fun p => M < p.1) ⊂ s := Finset.filter_ssubset.mpr ⟨p, hp,
      fun h => by have h' : M < p.1 := h; linarith [hcp.1]⟩
    exact Finset.card_lt_card hss

open Pointwise in
/-- Case 1 of Theorem 3.12: a left-balanced block at `min A` and a right-balanced block at
`max B`, both of discrepancy at least `d(A) = d(B)`. -/
lemma case1 (sA sB : Finset (ℝ × ℝ)) (hAne : (U sA).Nonempty) (hBne : (U sB).Nonempty)
    (hδ : dsup (U sA) = dsup (U sB)) {e f : ℝ}
    (hIA : LeftBal (U sA) (sInf (U sA)) e) (hIA' : dsup (U sA) ≤ dA (U sA) (sInf (U sA)) e)
    (hJB : RightBal (U sB) f (sSup (U sB))) (hJB' : dsup (U sB) ≤ dA (U sB) f (sSup (U sB))) :
    2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
      ≤ volume.real (U sA + U sB) := by
  have hAc := U_compact sA
  have hBc := U_compact sB
  have hAfin : volume (U sA) ≠ ⊤ := hAc.measure_lt_top.ne
  have hBfin : volume (U sB) ≠ ⊤ := hBc.measure_lt_top.ne
  have hδ0 : 0 ≤ dsup (U sB) := dsup_nonneg hBfin
  have P1 := cor_3_11 hAc.isClosed hIA (D := dsup (U sB)) (by rw [← hδ]; exact hIA') sB.card sB
    le_rfl (dsup (U sB)) hBne (fun p q hpq => dA_le_dsup hBfin hpq)
    (fun x hx => dA_le_dsup hBfin hx)
  have P2 := cor_3_11_right hBc.isClosed hJB (D := dsup (U sB)) hJB' sA (dsup (U sB)) hAne
    (fun p q hpq => by rw [← hδ]; exact dA_le_dsup hAfin hpq)
    (fun x hx => by rw [← hδ]; exact dA_le_dsup hAfin hx)
  change 2 * volume.real (U sB) ≤ volume.real (((U sA ∩ Icc (sInf (U sA)) e) + U sB) ∩
    Icc (sInf (U sA) + sInf (U sB)) (sInf (U sA) + sSup (U sB) + dsup (U sB))) at P1
  change 2 * volume.real (U sA) ≤ volume.real (((U sB ∩ Icc f (sSup (U sB))) + U sA) ∩
    Icc (sSup (U sB) + sInf (U sA) - dsup (U sB)) (sSup (U sB) + sSup (U sA))) at P2
  set S := U sA + U sB with hSdef
  have hSc : IsCompact S := hAc.add hBc
  have hSfin : volume S ≠ ⊤ := hSc.measure_lt_top.ne
  set X1 := S ∩ Icc (sInf (U sA) + sInf (U sB)) (sInf (U sA) + sSup (U sB) + dsup (U sB))
  set X2 := S ∩ Icc (sSup (U sB) + sInf (U sA) - dsup (U sB)) (sSup (U sB) + sSup (U sA))
  have h1 : volume.real (((U sA ∩ Icc (sInf (U sA)) e) + U sB) ∩
      Icc (sInf (U sA) + sInf (U sB)) (sInf (U sA) + sSup (U sB) + dsup (U sB))) ≤ volume.real X1 :=
    measureReal_mono (inter_subset_inter_left _ (Set.add_subset_add_right inter_subset_left))
      (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right))
  have h2 : volume.real (((U sB ∩ Icc f (sSup (U sB))) + U sA) ∩
      Icc (sSup (U sB) + sInf (U sA) - dsup (U sB)) (sSup (U sB) + sSup (U sA))) ≤
      volume.real X2 := by
    refine measureReal_mono (inter_subset_inter_left _ ?_)
      (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right))
    rw [hSdef, add_comm (U sA)]
    exact Set.add_subset_add_right inter_subset_left
  have hX2m : MeasurableSet X2 := hSc.isClosed.measurableSet.inter measurableSet_Icc
  have hU := measureReal_union_add_inter₀ (μ := volume) (s := X1) hX2m.nullMeasurableSet
    (ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
    (ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
  have hun : volume.real (X1 ∪ X2) ≤ volume.real S :=
    measureReal_mono (union_subset inter_subset_left inter_subset_left) hSfin
  have hint : volume.real (X1 ∩ X2) ≤ 2 * dsup (U sB) := by
    calc volume.real (X1 ∩ X2) ≤ volume.real (Icc (sSup (U sB) + sInf (U sA) - dsup (U sB))
          (sInf (U sA) + sSup (U sB) + dsup (U sB))) := by
          refine measureReal_mono ?_ measure_Icc_lt_top.ne
          intro t ht
          exact ⟨ht.2.2.1, ht.1.2.2⟩
      _ ≤ 2 * dsup (U sB) := by
          rw [Real.volume_real_Icc]
          apply max_le <;> linarith
  rw [hδ]
  linarith

open Pointwise in
/-- Case 2 of Theorem 3.12 (inductive step). `J = [min B, M]` is the maximal left-balanced
interval of `B`, `g` is the maximum of `d_B([min B, x])` on `J`, `g < d(B)`, and `A` has a
left-balanced block at `min A` of discrepancy `≥ g`. -/
lemma case2 (sA sB : Finset (ℝ × ℝ)) (hAne : (U sA).Nonempty) (hBne : (U sB).Nonempty)
    (hδ : dsup (U sA) = dsup (U sB)) {e M g : ℝ}
    (hIA : LeftBal (U sA) (sInf (U sA)) e) (hIAg : g ≤ dA (U sA) (sInf (U sA)) e)
    (hJ : LeftBal (U sB) (sInf (U sB)) M) (hmax : ∀ y, LeftBal (U sB) (sInf (U sB)) y → y ≤ M)
    (hg : ∀ x ∈ Icc (sInf (U sB)) M, dA (U sB) (sInf (U sB)) x ≤ g) (hgδ : g < dsup (U sB))
    (IH : ∀ s₂ : Finset (ℝ × ℝ), s₂.card < sB.card → (U s₂).Nonempty →
      dsup (U sA) = dsup (U s₂) →
      2 * volume.real (U sA) + 2 * volume.real (U s₂) - dsup (U sA) - dsup (U s₂)
        ≤ volume.real (U sA + U s₂)) :
    2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
      ≤ volume.real (U sA + U sB) := by
  have hAc := U_compact sA
  have hBc := U_compact sB
  have hBm : MeasurableSet (U sB) := hBc.isClosed.measurableSet
  have hBfin : volume (U sB) ≠ ⊤ := hBc.measure_lt_top.ne
  set A := U sA with hAdef
  set B := U sB with hBdef
  set a0 := sInf A with ha0
  set b0 := sInf B with hb0
  have hb0B : b0 ∈ B := hBc.sInf_mem hBne
  have hBmin : ∀ t ∈ B, b0 ≤ t := fun t ht => csInf_le hBc.bddBelow ht
  have hb1B : sSup B ∈ B := hBc.sSup_mem hBne
  have hBmax : ∀ t ∈ B, t ≤ sSup B := fun t ht => le_csSup hBc.bddAbove ht
  have hAmin : ∀ t ∈ A, a0 ≤ t := fun t ht => csInf_le hAc.bddBelow ht
  have hg0 : 0 ≤ g := le_trans (by have := dA_ge B (a := b0) (b := b0); linarith)
    (hg b0 ⟨le_rfl, hJ.1⟩)
  -- discrepancies of `B ∩ J` are at most `g`
  have hdBJ : ∀ p q, p ≤ q → dA (B ∩ Icc b0 M) p q ≤ g := by
    intro p q hpq
    have hset : (B ∩ Icc b0 M) ∩ Icc p q = B ∩ Icc (max b0 p) (min M q) := by
      rw [inter_assoc, Icc_inter_Icc]
    rcases le_or_gt (max b0 p) (min M q) with h | h
    · have s1 := dA_split hBm (a := b0) (b := max b0 p) (c := min M q) (le_max_left _ _) h
      have g1 := hJ.2.2 (max b0 p) ⟨le_max_left _ _, h.trans (min_le_left _ _)⟩
      have g2 := hg (min M q) ⟨(le_max_left _ _).trans h, min_le_left _ _⟩
      have hl : dA (B ∩ Icc b0 M) p q ≤ dA B (max b0 p) (min M q) := by
        unfold dA; rw [hset]; linarith [le_max_right b0 p, min_le_right M q]
      linarith
    · unfold dA
      rw [hset, Icc_eq_empty (not_le.mpr h), inter_empty]
      simp only [measureReal_empty, mul_zero]
      linarith
  have hBJcl : IsClosed (B ∩ Icc b0 M) := hBc.isClosed.inter isClosed_Icc
  have hLBJ : LeftBal (B ∩ Icc b0 M) b0 M := ⟨hJ.1, ⟨hb0B, le_rfl, hJ.1⟩, fun x hx => by
    have h1 : dA (B ∩ Icc b0 M) b0 x = dA B b0 x := by
      unfold dA; rw [inter_assoc, Icc_inter_Icc, max_self, min_eq_right hx.2]
    rw [h1]; exact hJ.2.2 x hx⟩
  have hK := cor_3_9_left hAc.isClosed hBJcl hIA hLBJ hdBJ hIAg
  rw [inter_assoc, inter_self] at hK
  -- `B` is not contained in `J`
  have hMb1 : M < sSup B := by
    by_contra h
    have h' : sSup B ≤ M := not_lt.mp h
    have hBJ : B ∩ Icc b0 M = B :=
      inter_eq_left.mpr fun t ht => ⟨hBmin t ht, (hBmax t ht).trans h'⟩
    have : dsup B ≤ g := dsup_le fun p q hpq => by
      have := hdBJ p q hpq; rwa [hBJ] at this
    linarith
  obtain ⟨ε, hε, hgap⟩ := maxLB_gap sB hJ hmax
  obtain ⟨h2sub, h2far, hsplit, hcard⟩ := split_after sB hε hJ.1 hb0B hBmin hgap
  set s₂ := sB.filter (fun p => M < p.1) with hs₂
  set B₂ := U s₂ with hB₂
  have hB₂c := U_compact s₂
  have hB₂fin : volume B₂ ≠ ⊤ := hB₂c.measure_lt_top.ne
  have hb1B₂ : sSup B ∈ B₂ := by
    rcases hsplit hb1B with h | h
    · linarith [h.2.2]
    · exact h
  have hne₂ : B₂.Nonempty := ⟨_, hb1B₂⟩
  have hc₂B₂ : sInf B₂ ∈ B₂ := hB₂c.sInf_mem hne₂
  set c₂ := sInf B₂ with hc₂
  have hc₂far : M + ε ≤ c₂ := h2far _ hc₂B₂
  have hB₂min : ∀ t ∈ B₂, c₂ ≤ t := fun t ht => csInf_le hB₂c.bddBelow ht
  have hgapn := gap_next hBm hJ hmax (c' := c₂) (d' := c₂) (by linarith)
    ⟨le_rfl, h2sub hc₂B₂, fun x hx => by
      have : x = c₂ := le_antisymm hx.2 hx.1
      rw [this]; have := dA_ge B (a := c₂) (b := c₂); linarith⟩
  have F1 : ∀ t ∈ B, t ≤ M ∨ c₂ ≤ t := fun t ht =>
    (hsplit ht).elim (fun h => Or.inl h.2.2) (fun h => Or.inr (hB₂min t h))
  have F4 : ∀ p q, M < p → B ∩ Icc p q = B₂ ∩ Icc p q := by
    intro p q hMp
    ext t
    constructor
    · rintro ⟨ht, htI⟩
      rcases hsplit ht with h | h
      · linarith [h.2.2, htI.1]
      · exact ⟨h, htI⟩
    · rintro ⟨ht, htI⟩
      exact ⟨h2sub ht, htI⟩
  have F3 : ∀ u v, M ≤ u → v ≤ c₂ → volume.real (B ∩ Icc u v) = 0 := by
    intro u v hu hv
    have hnull : volume.real (Icc M M ∪ Icc c₂ c₂) = 0 := by
      refine le_antisymm ((measureReal_union_le _ _).trans ?_) measureReal_nonneg
      rw [Real.volume_real_Icc, Real.volume_real_Icc]
      simp
    refine measureReal_mono_null ?_ hnull
      (measure_union_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
    intro t ht
    rcases F1 t ht.1 with h | h
    · exact Or.inl ⟨by linarith [ht.2.1], h⟩
    · exact Or.inr ⟨h, by linarith [ht.2.2]⟩
  have hmono : ∀ p q, volume.real (B₂ ∩ Icc p q) ≤ volume.real (B ∩ Icc p q) := fun p q =>
    measureReal_mono (inter_subset_inter_left _ h2sub) (fin_inter B p q)
  -- `d(B₂) = d(B)`
  have hδ₂ : dsup B₂ = dsup B := by
    apply le_antisymm
    · exact dsup_le fun p q hpq => by
        have := dA_le_dsup hBfin hpq; have := hmono p q; unfold dA at *; linarith
    · by_contra hlt
      have hlt' : dsup B₂ < dsup B := not_le.mp hlt
      have hgM : dA B b0 M ≤ g := hg M ⟨hJ.1, le_rfl⟩
      have hgapM : dA B b0 M < c₂ - M := by unfold dA; linarith
      have hmain : ∀ p q, b0 ≤ p → p ≤ q → dA B p q ≤ max g (dsup B₂) := by
        intro p q hp hpq
        have hgm : g ≤ max g (dsup B₂) := le_max_left _ _
        have h2m : dsup B₂ ≤ max g (dsup B₂) := le_max_right _ _
        rcases le_or_gt p M with hpM | hpM
        · have gp := hJ.2.2 p ⟨hp, hpM⟩
          rcases le_or_gt q M with hqM | hqM
          · have s1 := dA_split hBm hp hpq
            have := hg q ⟨hp.trans hpq, hqM⟩
            linarith
          · have s1 := dA_split hBm hp hpM
            have s2 := dA_split hBm hpM hqM.le
            rcases le_or_gt q c₂ with hqc | hqc
            · have h0 := F3 M q le_rfl hqc
              have : dA B M q = -(q - M) := by unfold dA; rw [h0]; ring
              linarith
            · have s3 := dA_split hBm (a := M) (b := c₂) (c := q) (by linarith) hqc.le
              have h0 := F3 M c₂ le_rfl le_rfl
              have hMc : dA B M c₂ = -(c₂ - M) := by unfold dA; rw [h0]; ring
              have hcq : dA B c₂ q = dA B₂ c₂ q := by
                unfold dA; rw [F4 c₂ q (by linarith)]
              have := dA_le_dsup hB₂fin hqc.le
              linarith
        · have : dA B p q = dA B₂ p q := by unfold dA; rw [F4 p q hpM]
          have := dA_le_dsup hB₂fin hpq
          linarith
      have hall : dsup B ≤ max g (dsup B₂) := dsup_le fun p q hpq => by
        rcases le_or_gt b0 p with hp | hp
        · exact hmain p q hp hpq
        · have hnull : volume.real (B ∩ Icc p b0) ≤ 0 := by
            refine le_of_eq (measureReal_mono_null (s₂ := Icc b0 b0) ?_
              (by rw [Real.volume_real_Icc]; simp) measure_Icc_lt_top.ne)
            intro t ht
            exact ⟨hBmin t ht.1, ht.2.2⟩
          have hm0 : 0 ≤ max g (dsup B₂) := hg0.trans (le_max_left _ _)
          rcases le_or_gt b0 q with hq | hq
          · have s1 := dA_split hBm hp.le hq
            have := hmain b0 q le_rfl hq
            have : dA B p b0 ≤ 0 := by unfold dA; linarith
            linarith
          · have : volume.real (B ∩ Icc p q) ≤ 0 :=
              le_trans (measureReal_mono (inter_subset_inter_right _ (Icc_subset_Icc le_rfl hq.le))
                (fin_inter B p b0)) hnull
            unfold dA; linarith
      have := max_lt hgδ hlt'
      linarith
  have hIH := IH s₂ hcard hne₂ (by rw [hδ, hδ₂])
  -- measure bookkeeping
  have hdisjB : Disjoint (B ∩ Icc b0 M) B₂ := Set.disjoint_left.mpr fun t h1 h2 => by
    linarith [h1.2.2, h2far t h2]
  have hBeq : B = (B ∩ Icc b0 M) ∪ B₂ :=
    Subset.antisymm hsplit (union_subset inter_subset_left h2sub)
  have hvolB : volume.real B = volume.real (B ∩ Icc b0 M) + volume.real B₂ := by
    conv_lhs => rw [hBeq]
    exact measureReal_union hdisjB hB₂c.isClosed.measurableSet (fin_inter B b0 M) hB₂fin
  set K := Icc (a0 + b0) (a0 + b0 + 2 * volume.real (B ∩ Icc b0 M)) with hKdef
  have hS₂c : IsCompact (A + B₂) := hAc.add hB₂c
  have hdisjK : Disjoint K (A + B₂) := Set.disjoint_left.mpr fun t h1 h2 => by
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp h2
    linarith [h1.2, hAmin u hu, hB₂min v hv]
  have hsub : K ∪ (A + B₂) ⊆ A + B := union_subset
    (hK.trans (Set.add_subset_add inter_subset_left inter_subset_left))
    (Set.add_subset_add_left h2sub)
  have hvJ : 0 ≤ volume.real (B ∩ Icc b0 M) := measureReal_nonneg
  have hvK : volume.real K = 2 * volume.real (B ∩ Icc b0 M) := by
    rw [hKdef, Real.volume_real_Icc, max_eq_left (by linarith)]; ring
  have hU := measureReal_union (μ := volume) hdisjK hS₂c.isClosed.measurableSet
    measure_Icc_lt_top.ne hS₂c.measure_lt_top.ne
  have hle := measureReal_mono (μ := volume) hsub
    ((hAc.add hBc).measure_lt_top (μ := volume)).ne
  rw [hδ₂] at hIH
  linarith

lemma neg_neg_set (X : Set ℝ) : (fun y => (0 : ℝ) - y) ⁻¹' ((fun y => (0 : ℝ) - y) ⁻¹' X) = X := by
  ext y; simp

lemma dsup_neg {X : Set ℝ} (hX : MeasurableSet X) :
    dsup ((fun y => (0 : ℝ) - y) ⁻¹' X) = dsup X := by
  unfold dsup
  congr 1
  ext t
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    exact ⟨0 - b, 0 - a, by linarith, refl_dA hX 0 a b⟩
  · rintro ⟨a, b, hab, rfl⟩
    refine ⟨0 - b, 0 - a, by linarith, ?_⟩
    have := refl_dA hX 0 (0 - b) (0 - a)
    rw [sub_sub_cancel, sub_sub_cancel] at this
    exact this.symm

lemma vol_neg {X : Set ℝ} (hX : MeasurableSet X) :
    volume.real ((fun y => (0 : ℝ) - y) ⁻¹' X) = volume.real X :=
  (Measure.measurePreserving_sub_left volume (0 : ℝ)).measureReal_preimage hX.nullMeasurableSet

lemma sInf_neg {X : Set ℝ} (hX : IsCompact X) (hne : X.Nonempty) :
    sInf ((fun y => (0 : ℝ) - y) ⁻¹' X) = -sSup X :=
  IsLeast.csInf_eq ⟨show 0 - -sSup X ∈ X by simpa using hX.sSup_mem hne,
    fun y hy => by have := le_csSup hX.bddAbove (show 0 - y ∈ X from hy); linarith⟩

open Pointwise in
lemma add_neg_set (X Y : Set ℝ) : (fun y => (0 : ℝ) - y) ⁻¹' (X + Y) =
    (fun y => (0 : ℝ) - y) ⁻¹' X + (fun y => (0 : ℝ) - y) ⁻¹' Y := by
  ext y
  simp only [mem_preimage, Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    exact ⟨0 - u, by simpa using hu, 0 - v, by simpa using hv, by linarith⟩
  · rintro ⟨u, hu, v, hv, huv⟩
    exact ⟨0 - u, hu, 0 - v, hv, by linarith⟩

/-- A left block of the reflected set gives a right block of the set. -/
lemma right_of_refl {X : Set ℝ} (hX : IsCompact X) (hne : X.Nonempty) {e : ℝ}
    (h : LeftBal ((fun y => (0 : ℝ) - y) ⁻¹' X) (sInf ((fun y => (0 : ℝ) - y) ⁻¹' X)) e) :
    RightBal X (0 - e) (sSup X) ∧
    dA X (0 - e) (sSup X) =
      dA ((fun y => (0 : ℝ) - y) ⁻¹' X) (sInf ((fun y => (0 : ℝ) - y) ⁻¹' X)) e := by
  have hm := hX.isClosed.measurableSet
  have hXm : MeasurableSet ((fun y => (0 : ℝ) - y) ⁻¹' X) :=
    measurableSet_preimage (measurable_const.sub measurable_id) hm
  have h1 := leftBal_refl hXm 0 h
  rw [neg_neg_set, sInf_neg hX hne, show (0 : ℝ) - -sSup X = sSup X by ring] at h1
  refine ⟨h1, ?_⟩
  rw [refl_dA hm, sInf_neg hX hne, show (0 : ℝ) - -sSup X = sSup X by ring]

lemma GLdata (s : Finset (ℝ × ℝ)) (hne : (U s).Nonempty) :
    ∃ M e, LeftBal (U s) (sInf (U s)) M ∧ (∀ y, LeftBal (U s) (sInf (U s)) y → y ≤ M) ∧
      e ∈ Icc (sInf (U s)) M ∧
      ∀ x ∈ Icc (sInf (U s)) M, dA (U s) (sInf (U s)) x ≤ dA (U s) (sInf (U s)) e := by
  have hc := U_compact s
  have hm := hc.isClosed.measurableSet
  obtain ⟨M, hJ, hmax⟩ := exists_maxLB hm hc.measure_lt_top.ne (hc.sInf_mem hne)
  obtain ⟨e, he, hg⟩ := exists_GL hm hJ.1
  exact ⟨M, e, hJ, hmax, he, hg⟩

open Pointwise in
/-- **FGY Theorem 3.12.** For nonempty finite unions of closed intervals with `d(A) = d(B)`,
`|A + B| ≥ 2|A| + 2|B| - d(A) - d(B)`. -/
theorem thm_3_12 : ∀ n : ℕ, ∀ sA sB : Finset (ℝ × ℝ), sA.card + sB.card ≤ n →
    (U sA).Nonempty → (U sB).Nonempty → dsup (U sA) = dsup (U sB) →
    2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
      ≤ volume.real (U sA + U sB) := by
  classical
  intro n
  induction n with
  | zero =>
    intro sA sB h hA
    have : sA = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    obtain ⟨x, hx⟩ := hA
    simp [U] at hx
  | succ n ih =>
    intro sA sB hcard hA hB hδ
    have hAc := U_compact sA
    have hBc := U_compact sB
    have hAm := hAc.isClosed.measurableSet
    have hBm := hBc.isClosed.measurableSet
    set tA := sA.image (fun p => (-p.2, -p.1)) with htA
    set tB := sB.image (fun p => (-p.2, -p.1)) with htB
    have hUA : U tA = (fun y => (0 : ℝ) - y) ⁻¹' U sA := (neg_union sA).symm
    have hUB : U tB = (fun y => (0 : ℝ) - y) ⁻¹' U sB := (neg_union sB).symm
    have hcA : tA.card ≤ sA.card := Finset.card_image_le
    have hcB : tB.card ≤ sB.card := Finset.card_image_le
    have hA' : (U tA).Nonempty := by
      obtain ⟨x, hx⟩ := hA
      exact ⟨0 - x, by rw [hUA]; show 0 - (0 - x) ∈ U sA; simpa using hx⟩
    have hB' : (U tB).Nonempty := by
      obtain ⟨x, hx⟩ := hB
      exact ⟨0 - x, by rw [hUB]; show 0 - (0 - x) ∈ U sB; simpa using hx⟩
    have hdA' : dsup (U tA) = dsup (U sA) := by rw [hUA, dsup_neg hAm]
    have hdB' : dsup (U tB) = dsup (U sB) := by rw [hUB, dsup_neg hBm]
    have hvA' : volume.real (U tA) = volume.real (U sA) := by rw [hUA, vol_neg hAm]
    have hvB' : volume.real (U tB) = volume.real (U sB) := by rw [hUB, vol_neg hBm]
    have hS' : volume.real (U tA + U tB) = volume.real (U sA + U sB) := by
      rw [hUA, hUB, ← add_neg_set, vol_neg (hAc.add hBc).isClosed.measurableSet]
    have hcomm : volume.real (U sB + U sA) = volume.real (U sA + U sB) := by rw [add_comm]
    have hcomm' : volume.real (U tB + U tA) = volume.real (U tA + U tB) := by rw [add_comm]
    obtain ⟨MA, eA, hJA, hmaxA, heA, hgA⟩ := GLdata sA hA
    obtain ⟨MB, eB, hJB, hmaxB, heB, hgB⟩ := GLdata sB hB
    obtain ⟨MA', eA', hJA', hmaxA', heA', hgA'⟩ := GLdata tA hA'
    obtain ⟨MB', eB', hJB', hmaxB', heB', hgB'⟩ := GLdata tB hB'
    have hlA := leftBal_mono hJA heA.1 heA.2
    have hlB := leftBal_mono hJB heB.1 heB.2
    have hlA' := leftBal_mono hJA' heA'.1 heA'.2
    have hlB' := leftBal_mono hJB' heB'.1 heB'.2
    have hlA'' : LeftBal ((fun y => (0 : ℝ) - y) ⁻¹' U sA)
        (sInf ((fun y => (0 : ℝ) - y) ⁻¹' U sA)) eA' := by rw [← hUA]; exact hlA'
    have hlB'' : LeftBal ((fun y => (0 : ℝ) - y) ⁻¹' U sB)
        (sInf ((fun y => (0 : ℝ) - y) ⁻¹' U sB)) eB' := by rw [← hUB]; exact hlB'
    obtain ⟨hrA, hrAv⟩ := right_of_refl hAc hA hlA''
    obtain ⟨hrB, hrBv⟩ := right_of_refl hBc hB hlB''
    rw [← hUA] at hrAv
    rw [← hUB] at hrBv
    set δ := dsup (U sB) with hδdef
    set gA := dA (U sA) (sInf (U sA)) eA
    set gB := dA (U sB) (sInf (U sB)) eB
    set gA' := dA (U tA) (sInf (U tA)) eA'
    set gB' := dA (U tB) (sInf (U tB)) eB'
    -- the four instances of case 2
    have cI : gB < δ → gB ≤ gA → _ := fun h1 h2 =>
      case2 sA sB hA hB hδ hlA h2 hJB hmaxB hgB h1
        (fun s₂ hc hne heq => ih sA s₂ (by omega) hA hne heq)
    have cII : gA < δ → gA ≤ gB →
        2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
          ≤ volume.real (U sA + U sB) := fun h1 h2 => by
      have := case2 sB sA hB hA hδ.symm hlB h2 hJA hmaxA hgA (by rw [hδ]; exact h1)
        (fun s₂ hc hne heq => ih sB s₂ (by omega) hB hne heq)
      rw [hcomm] at this; linarith
    have cIII : gB' < δ → gB' ≤ gA' →
        2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
          ≤ volume.real (U sA + U sB) := fun h1 h2 => by
      have := case2 tA tB hA' hB' (by rw [hdA', hdB', hδ]) hlA' h2 hJB' hmaxB' hgB'
        (by rw [hdB']; exact h1) (fun s₂ hc hne heq => ih tA s₂ (by omega) hA' hne heq)
      rw [hvA', hvB', hdA', hdB', hS'] at this; exact this
    have cIV : gA' < δ → gA' ≤ gB' →
        2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
          ≤ volume.real (U sA + U sB) := fun h1 h2 => by
      have := case2 tB tA hB' hA' (by rw [hdA', hdB', hδ]) hlB' h2 hJA' hmaxA' hgA'
        (by rw [hdA', hδ]; exact h1) (fun s₂ hc hne heq => ih tB s₂ (by omega) hB' hne heq)
      rw [hvA', hvB', hdA', hdB', hcomm', hS'] at this; linarith
    have cR : gB' < δ → gA' < δ →
        2 * volume.real (U sA) + 2 * volume.real (U sB) - dsup (U sA) - dsup (U sB)
          ≤ volume.real (U sA + U sB) := fun h1 h2 => by
      rcases le_total gB' gA' with h | h
      · exact cIII h1 h
      · exact cIV h2 h
    by_cases h1a : δ ≤ gA ∧ δ ≤ gB'
    · exact case1 sA sB hA hB hδ hlA (by rw [hδ]; exact h1a.1) hrB (by rw [hrBv]; exact h1a.2)
    by_cases h1b : δ ≤ gB ∧ δ ≤ gA'
    · have := case1 sB sA hB hA hδ.symm hlB h1b.1 hrA (by rw [hrAv, hδ]; exact h1b.2)
      rw [hcomm] at this; linarith
    rcases le_total gA gB with hab | hab
    · by_cases hlt : gA < δ
      · exact cII hlt hab
      · exact cR (by by_contra h; exact h1a ⟨not_lt.mp hlt, not_lt.mp h⟩)
          (by by_contra h; exact h1b ⟨le_trans (not_lt.mp hlt) hab, not_lt.mp h⟩)
    · by_cases hlt : gB < δ
      · exact cI hlt hab
      · exact cR (by by_contra h; exact h1a ⟨le_trans (not_lt.mp hlt) hab, not_lt.mp h⟩)
          (by by_contra h; exact h1b ⟨not_lt.mp hlt, not_lt.mp h⟩)

end OMA.Green3Sec3

open Pointwise in
theorem OMA.solution : OMA.R_Green3_green_3_R2_H1_R1.H1 := by
  rintro A B ⟨sA, rfl⟩ ⟨sB, rfl⟩ hA hB hδ
  exact OMA.Green3Sec3.thm_3_12 _ sA sB le_rfl hA hB hδ
