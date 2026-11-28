import Green28MassSpectrum

/-! Inverse stability of discrete convolution at uniform laws of bounded support size. -/

namespace Green28InverseStability
open Green28 Finset Set
open scoped ENNReal

/-- Small errors for a continuous nonnegative residual on a compact parameter space force
proximity to a point with zero residual. -/
private theorem near_zero {X : Type*} [PseudoMetricSpace X] [CompactSpace X] {f : X → ℝ}
    (cont : Continuous f) (pos : ∀ x, 0 ≤ f x) {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ x, f x < δ → ∃ y, f y = 0 ∧ dist x y < ε := by
  classical
  let bad : Set X := {x | ∀ y, f y = 0 → ε ≤ dist x y}
  have closed : IsClosed bad := by
    change IsClosed {x : X | ∀ y, f y = 0 → ε ≤ dist x y}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  by_cases ex : bad.Nonempty
  · obtain ⟨a,ha,least⟩ := closed.isCompact.exists_isMinOn ex cont.continuousOn
    have away : 0 < f a := lt_of_le_of_ne (pos a) (by
      intro zero
      have := ha a zero.symm
      rw [dist_self] at this
      exact he.not_ge this)
    refine ⟨f a,away,fun x hx => ?_⟩
    by_contra! hn
    exact (not_le.mpr hx) (least hn)
  · refine ⟨1,one_pos,fun x _ => ?_⟩
    by_contra! hn
    exact ex ⟨x,hn⟩

/-- A translate of the output set captures at least the same mass up to any strict threshold. -/
theorem heavy_translate (P Q : PMF ℤ) (S : Set ℤ) {r : ℝ≥0∞}
    (hr : r < (indepSum P Q).toOuterMeasure S) :
    ∃ a : ℤ, r < Q.toOuterMeasure ((fun y => a+y) ⁻¹' S) := by
  by_contra! h
  change r < (P.bind fun x => Q.map (fun y => x+y)).toOuterMeasure S at hr
  rw [PMF.toOuterMeasure_bind_apply] at hr
  have all := ENNReal.tsum_le_tsum fun x => show P x * (Q.map (fun y => x+y)).toOuterMeasure S ≤ P x * r by
    rw [PMF.toOuterMeasure_map_apply]
    gcongr
    exact h x
  rw [ENNReal.tsum_mul_right,P.tsum_coe,one_mul] at all
  exact hr.not_ge all

private theorem repair_constraints {X I : Type*} [PseudoMetricSpace X] [CompactSpace X]
    [Fintype I] [Nonempty I] (g : I → X → ℝ) (cont : ∀ i, Continuous (g i))
    {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ x, (∀ i, g i x < δ) → ∃ y, (∀ i, g i y ≤ 0) ∧ dist x y < ε := by
  classical
  let f (x : X) := max 0 (univ.sup' univ_nonempty (fun i => g i x))
  have cf : Continuous f := continuous_const.max (Continuous.finset_sup'_apply _ (fun i _ => cont i))
  obtain ⟨δ,hd,h⟩ := near_zero cf (fun _ => le_max_left ..) he
  refine ⟨δ,hd,fun x hx => ?_⟩
  obtain ⟨y,zero,near⟩ := h x (max_lt hd ((sup'_lt_iff ..).mpr (fun i _ => hx i)))
  refine ⟨y,fun i => ?_,near⟩
  calc
    g i y ≤ univ.sup' univ_nonempty (fun j => g j y) := le_sup' (fun j => g j y) (mem_univ i)
    _ ≤ f y := le_max_right ..
    _ = 0 := zero

abbrev PairWeights (m : ℕ) := (Fin m → Set.Icc (0:ℝ) 1) × (Fin m → Set.Icc (0:ℝ) 1)
abbrev Pattern (m : ℕ) := Fin m → Fin m → Option (Fin m)

private def cell {m : ℕ} (p : Pattern m) (z : Fin m) (x : PairWeights m) : ℝ :=
  ∑ i, ∑ j, (if p i j = some z then 1 else 0) * ((x.1 i:ℝ)*(x.2 j:ℝ))

private abbrev Constraint (m : ℕ) := Bool ⊕ (Fin m ⊕ (Fin m × Fin m))

private noncomputable def violation {m : ℕ} (p : Pattern m) : Constraint m → PairWeights m → ℝ
  | .inl false, x => |(∑ i, (x.1 i:ℝ))-1|
  | .inl true, x => |(∑ j, (x.2 j:ℝ))-1|
  | .inr (.inl z), x => cell p z x - (m:ℝ)⁻¹
  | .inr (.inr (i,j)), x => if p i j = none then (x.1 i:ℝ)*(x.2 j:ℝ) else 0

private theorem continuous_violation {m : ℕ} (p : Pattern m) (i : Constraint m) :
    Continuous (violation p i) := by
  rcases i with b|z|⟨i,j⟩
  · cases b <;> unfold violation <;> fun_prop
  · change Continuous (fun x : PairWeights m => cell p z x - (m:ℝ)⁻¹)
    unfold cell
    fun_prop
  · change Continuous (fun x : PairWeights m => if p i j = none then (x.1 i:ℝ)*(x.2 j:ℝ) else 0)
    by_cases hz : p i j = none <;> simp only [hz,if_true,if_false] <;> fun_prop

/-- The perturbation tolerance is uniform in the entire pair-sum incidence pattern:
there are only finitely many patterns at a fixed output count. -/
private theorem repair_patterns (m : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∃ δ > 0, ∀ (p : Pattern m) (x : PairWeights m), (∀ i, violation p i x < δ) →
      ∃ y, (∀ i, violation p i y ≤ 0) ∧ dist x y < ε := by
  classical
  have tol (p : Pattern m) := repair_constraints (violation p) (continuous_violation p) he
  choose d positive repair using tol
  let δ := univ.inf' univ_nonempty d
  refine ⟨δ,(lt_inf'_iff ..).mpr (fun p _ => positive p),fun p x h => repair p x (fun i => ?_)⟩
  exact (h i).trans_le (inf'_le _ (mem_univ p))

/-- At zero error, the one-sided bounds on the target cells become equalities by total mass. -/
private theorem exact_table {m : ℕ} (hm : 0 < m) {p : Pattern m} {x : PairWeights m}
    (exactRow : ∀ i, violation p i x ≤ 0) :
    (∑ i, (x.1 i:ℝ)) = 1 ∧ (∑ j, (x.2 j:ℝ)) = 1 ∧
    (∀ i j, p i j = none → (x.1 i:ℝ)*(x.2 j:ℝ) = 0) ∧ ∀ z, cell p z x = (m:ℝ)⁻¹ := by
  have left := exactRow (.inl false)
  have right := exactRow (.inl true)
  change |(∑ i, (x.1 i:ℝ))-1| ≤ 0 at left
  change |(∑ j, (x.2 j:ℝ))-1| ≤ 0 at right
  have L := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm left (abs_nonneg _)))
  have R := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm right (abs_nonneg _)))
  have off (i j : Fin m) (e : p i j = none) : (x.1 i:ℝ)*(x.2 j:ℝ) = 0 := by
    have h := exactRow (.inr (.inr (i,j)))
    change (if p i j = none then (x.1 i:ℝ)*(x.2 j:ℝ) else 0) ≤ 0 at h
    rw [if_pos e] at h
    exact le_antisymm h (mul_nonneg (x.1 i).property.1 (x.2 j).property.1)
  have bound (z : Fin m) : cell p z x ≤ (m:ℝ)⁻¹ := sub_nonpos.mp (exactRow (.inr (.inl z)))
  refine ⟨L,R,off,?_⟩
  have pair (i j : Fin m) : (∑ z : Fin m, (if p i j = some z then (1:ℝ) else 0) *
      ((x.1 i:ℝ)*(x.2 j:ℝ))) = (x.1 i:ℝ)*(x.2 j:ℝ) := by
    cases e : p i j with
    | none => simp [off _ _ e]
    | some b => simp [ite_mul]
  have total : ∑ z, cell p z x = ∑ _ : Fin m, (m:ℝ)⁻¹ := by
    unfold cell
    rw [sum_comm]
    simp_rw [sum_comm (s:=univ) (t:=univ) (f:=fun z j => (if p _ j = some z then (1:ℝ) else 0) * _),pair]
    simp_rw [←mul_sum,R,mul_one]
    simp [L,hm.ne']
  exact fun z => (sum_eq_sum_iff_of_le (fun z _ => bound z)).mp total z (mem_univ _)

open MeasureTheory

/-- Total variation at most `ε`, expressed by all events on the discrete integers. -/
def TVLe (ε : ℝ) (P Q : PMF ℤ) : Prop := ∀ E : Set ℤ, P.toMeasure.real E ≤ Q.toMeasure.real E + ε

theorem TVLe.symm {ε : ℝ} {P Q : PMF ℤ} (h : TVLe ε P Q) : TVLe ε Q P := by
  intro E
  have c := h Eᶜ
  rw [measureReal_compl (.of_discrete),measureReal_compl (.of_discrete),probReal_univ,probReal_univ] at c
  linarith

theorem tvLe_iff {ε : ℝ} {P Q : PMF ℤ} :
    TVLe ε P Q ↔ ∀ E : Set ℤ, |P.toMeasure.real E - Q.toMeasure.real E| ≤ ε := by
  constructor
  · intro h E
    exact abs_le.mpr ⟨by linarith [h.symm E],by linarith [h E]⟩
  · intro h E
    linarith [(abs_le.mp (h E)).2]

private noncomputable def indexed {m : ℕ} (u : Fin m → Set.Icc (0:ℝ) 1)
    (total : (∑ i,(u i:ℝ)) = 1) : PMF (Fin m) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (u i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (u i).property.1), total, ENNReal.ofReal_one])

private theorem image_mass {m : ℕ} (R : PMF ℤ) (l : Fin m → ℤ) (inj : Function.Injective l)
    (I : Finset (Fin m)) :
    (∑ i ∈ I, (R (l i)).toReal) = R.toMeasure.real (↑(I.image l) : Set ℤ) := by
  rw [Measure.real,PMF.toMeasure_apply_finset,ENNReal.toReal_sum (fun x _ => R.apply_ne_top x),
    sum_image inj.injOn]

open scoped Classical in
private theorem indexed_event {m : ℕ} (u : Fin m → Set.Icc (0:ℝ) 1)
    (total : (∑ i,(u i:ℝ)) = 1) (l : Fin m → ℤ) (E : Set ℤ) :
    ((indexed u total).map l).toMeasure.real E = ∑ i, if l i ∈ E then (u i:ℝ) else 0 := by
  classical
  rw [Measure.real,PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (.of_discrete),PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_apply_fintype,ENNReal.toReal_sum]
  · apply sum_congr rfl
    intro i _
    by_cases hi : l i ∈ E
    · simp [hi,indexed,ENNReal.toReal_ofReal (u i).property.1]
    · simp [hi]
  · intro i _
    by_cases hi : l i ∈ E <;> simp [hi,indexed]

/-- Coordinate errors on a finite set give total variation control against an arbitrary
integer law. The original law can have infinite support. -/
private theorem embed_close {m : ℕ} {R : PMF ℤ} (l : Fin m → ℤ) (inj : Function.Injective l)
    (u : Fin m → Set.Icc (0:ℝ) 1) (total : (∑ i,(u i:ℝ)) = 1) {t : ℝ} (ht : 0 ≤ t)
    (coord : ∀ i, (u i:ℝ) ≤ (R (l i)).toReal + t) :
    TVLe ((m:ℝ)*t) ((indexed u total).map l) R := by
  classical
  intro E
  let I := Finset.univ.filter (fun i => l i ∈ E)
  rw [indexed_event,←sum_filter]
  calc
    ∑ i ∈ I, (u i:ℝ) ≤ ∑ i ∈ I, ((R (l i)).toReal+t) := sum_le_sum (fun i _ => coord i)
    _ = R.toMeasure.real (↑(I.image l) : Set ℤ) + (I.card:ℝ)*t := by
      rw [sum_add_distrib,image_mass R l inj];simp
    _ ≤ R.toMeasure.real E + (m:ℝ)*t := by
      apply add_le_add
      · apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro x hx
        obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
        exact (mem_filter.mp hi).2
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by simpa using I.card_le_univ : I.card ≤ m)) ht

private def block {m : ℕ} (l r : Fin m → ℤ) (x : PairWeights m) (z : ℤ) : ℝ :=
  ∑ i, ∑ j, (if l i + r j = z then 1 else 0) * ((x.1 i:ℝ)*(x.2 j:ℝ))

private def crop {m : ℕ} (R : PMF ℤ) (l : Fin m → ℤ) (i : Fin m) : Set.Icc (0:ℝ) 1 :=
  ⟨(R (l i)).toReal,ENNReal.toReal_nonneg,by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (R.coe_le_one (l i))⟩

private theorem cropped_le {m : ℕ} (P Q : PMF ℤ) (l r : Fin m → ℤ)
    (li : Function.Injective l) (ri : Function.Injective r) (z : ℤ) :
    block l r (crop P l,crop Q r) z ≤ (indepSum P Q z).toReal := by
  classical
  have row (i : Fin m) : (∑ j, (if l i + r j = z then (1:ℝ) else 0) *
      ((P (l i)).toReal*(Q (r j)).toReal)) ≤ (P (l i)).toReal*(Q (z-l i)).toReal := by
    by_cases hit : ∃ j, l i + r j = z
    · obtain ⟨b,hb⟩ := hit
      rw [sum_eq_single b]
      · rw [if_pos hb,one_mul,show r b = z-l i by omega]
      · intro j _ hj
        rw [if_neg (fun hz => hj (ri (by omega))),zero_mul]
      · simp
    · push Not at hit
      simp [hit,mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  have trunc := ENNReal.sum_le_tsum (f:=fun a => P a * Q (z-a)) (Finset.univ.image l)
  rw [sum_image li.injOn,←Green28UniformSums.convolution] at trunc
  have real := ENNReal.toReal_mono ((indepSum P Q).apply_ne_top _) trunc
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (P.apply_ne_top _) (Q.apply_ne_top _))] at real
  unfold block crop
  exact (sum_le_sum (fun i _ => row i)).trans (by simpa only [ENNReal.toReal_mul] using real)

private theorem indexed_sum {m : ℕ} (l r : Fin m → ℤ) (x : PairWeights m)
    (L : (∑ i, (x.1 i:ℝ)) = 1) (R : (∑ j, (x.2 j:ℝ)) = 1) (z : ℤ) :
    (indepSum ((indexed x.1 L).map l) ((indexed x.2 R).map r) z).toReal = block l r x z := by
  classical
  change (((indexed x.1 L).map l).bind (fun a => ((indexed x.2 R).map r).bind
    (fun b => PMF.pure (a+b))) z).toReal = _
  simp only [PMF.bind_map,Function.comp_apply,PMF.bind_apply,tsum_fintype]
  rw [ENNReal.toReal_sum (fun i _ => by
    apply ENNReal.mul_ne_top ((indexed x.1 L).apply_ne_top i)
    apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ENNReal.mul_ne_top ((indexed x.2 R).apply_ne_top j) ((PMF.pure _).apply_ne_top _))]
  unfold block
  apply sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul,ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top
    ((indexed x.2 R).apply_ne_top j) ((PMF.pure _).apply_ne_top _)),mul_sum]
  apply sum_congr rfl
  intro j _
  by_cases eq : l i + r j = z
  · simp [PMF.pure_apply,eq,indexed,ENNReal.toReal_ofReal (x.1 i).property.1,
      ENNReal.toReal_ofReal (x.2 j).property.1]
  · simp [PMF.pure_apply,eq,Ne.symm eq]

private noncomputable def site (S : Finset ℤ) (i : Fin S.card) : ℤ := (S.equivFin.symm i).val

private theorem site_injective (S : Finset ℤ) : Function.Injective (site S) :=
  Subtype.val_injective.comp S.equivFin.symm.injective

private noncomputable def label (S : Finset ℤ) (z : ℤ) : Option (Fin S.card) :=
  if h : z ∈ S then some (S.equivFin ⟨z,h⟩) else none

private theorem label_some (S : Finset ℤ) (z : ℤ) (i : Fin S.card) :
    label S z = some i ↔ z = site S i := by
  classical
  by_cases h : z ∈ S
  · rw [label,dif_pos h,Option.some.injEq]
    exact ⟨fun e => congrArg Subtype.val ((S.equivFin.eq_symm_apply).mpr e),
      fun e => S.equivFin.eq_symm_apply.mp (Subtype.ext e)⟩
  · simp [label,h,show z ≠ site S i from fun e => h (e ▸ (S.equivFin.symm i).property)]

private theorem label_none (S : Finset ℤ) (z : ℤ) : label S z = none ↔ z ∉ S := by
  by_cases hz : z ∈ S <;> simp [label,hz]

private theorem uniform_singleton (S : Finset ℤ) (hs : S.Nonempty) (z : ℤ) :
    ((PMF.uniformOfFinset S hs) z).toReal = if z ∈ S then (S.card:ℝ)⁻¹ else 0 := by
  by_cases hz : z ∈ S <;> simp [PMF.uniformOfFinset_apply,hz]

private theorem singleton_bound {ε : ℝ} {P Q : PMF ℤ} (h : TVLe ε P Q) (z : ℤ) :
    (P z).toReal ≤ (Q z).toReal+ε := by
  have hb := h {z}
  simpa only [Measure.real,PMF.toMeasure_apply_singleton _ _ (.of_discrete)] using hb

private theorem heavy_row {P Q : PMF ℤ} (S : Finset ℤ) (ne : S.Nonempty) {δ : ℝ}
    (hd : 0 < δ) (small : δ < 1/2) (close : TVLe δ (indepSum P Q) (PMF.uniformOfFinset S ne)) :
    ∃ l : Fin S.card → ℤ, Function.Injective l ∧ 1-2*δ < ∑ i, (Q (l i)).toReal := by
  classical
  have prob : (PMF.uniformOfFinset S ne).toMeasure (S:Set ℤ) = 1 := by
    apply (PMF.toMeasure_apply_eq_one_iff _ (.of_discrete)).mpr
    rw [PMF.support_uniformOfFinset]
  have c := close.symm (S:Set ℤ)
  rw [Measure.real,prob,ENNReal.toReal_one,Measure.real,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (.of_discrete)] at c
  have pos : 0 ≤ 1-2*δ := by linarith
  have hm : ENNReal.ofReal (1-2*δ) < (indepSum P Q).toOuterMeasure (S:Set ℤ) := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) _).mp
    · rw [ENNReal.toReal_ofReal pos]
      linarith
    · rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (.of_discrete)]
      exact measure_ne_top _ _
  obtain ⟨a,ha⟩ := heavy_translate P Q (S:Set ℤ) hm
  let l := fun i => site S i - a
  have li : Function.Injective l := fun i j e => site_injective S (by dsimp [l] at e; omega)
  refine ⟨l,li,?_⟩
  have eq : (↑(Finset.univ.image l) : Set ℤ) = (fun y => a+y) ⁻¹' (S:Set ℤ) := by
    ext z
    change z ∈ Finset.univ.image l ↔ a+z ∈ S
    constructor
    · intro hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      simp [l,site]
    · intro hz
      let i := S.equivFin ⟨a+z,hz⟩
      exact mem_image.mpr ⟨i,mem_univ _,by simp [l,site,i]⟩
  rw [←eq,←PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (.of_discrete)] at ha
  have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mpr ha
  rw [ENNReal.toReal_ofReal pos] at h
  exact h.trans_le (le_of_eq (image_mass Q l li Finset.univ).symm)

private noncomputable def pattern (S : Finset ℤ) (l r : Fin S.card → ℤ) : Pattern S.card :=
  fun i j => label S (l i+r j)

private theorem cell_site (S : Finset ℤ) (l r : Fin S.card → ℤ) (v : PairWeights S.card)
    (z : Fin S.card) : cell (pattern S l r) z v = block l r v (site S z) := by
  simp only [cell,block,pattern,label_some]

private theorem single_product_le (P Q : PMF ℤ) (a b : ℤ) :
    (P a).toReal * (Q b).toReal ≤ (indepSum P Q (a+b)).toReal := by
  have bound := ENNReal.le_tsum (f:=fun x => P x * Q (a+b-x)) a
  rw [←Green28UniformSums.convolution,show a+b-a = b by omega] at bound
  simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono ((indepSum P Q).apply_ne_top _) bound

private theorem small_violations {P Q : PMF ℤ} {S : Finset ℤ} (hs : S.Nonempty)
    {δ t : ℝ} (hd : 0 < δ) (tol : 2*δ < t) (h : TVLe δ (indepSum P Q) (PMF.uniformOfFinset S hs))
    (l r : Fin S.card → ℤ) (li : Function.Injective l) (ri : Function.Injective r)
    (L : 1-2*δ < ∑ i, (P (l i)).toReal) (R : 1-2*δ < ∑ j, (Q (r j)).toReal) :
    ∀ i, violation (pattern S l r) i (crop P l,crop Q r) < t := by
  have normalize (A : PMF ℤ) (a : Fin S.card → ℤ) (inj : Function.Injective a)
      (mass : 1-2*δ < ∑ i, (A (a i)).toReal) : |(∑ i, (A (a i)).toReal)-1| < t := by
    have top : (∑ i, (A (a i)).toReal) ≤ 1 := by
      rw [image_mass A a inj Finset.univ]
      simpa only [probReal_univ] using (measureReal_mono (μ:=A.toMeasure) (Set.subset_univ _) (measure_ne_top _ _))
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  intro i
  rcases i with b|z|⟨i,j⟩
  · cases b
    · exact normalize P l li L
    · exact normalize Q r ri R
  · change cell _ z _ - (S.card:ℝ)⁻¹ < t
    rw [cell_site]
    have bound := singleton_bound h (site S z)
    rw [uniform_singleton,if_pos (show site S z ∈ S from (S.equivFin.symm z).property)] at bound
    linarith [cropped_le P Q l r li ri (site S z)]
  · change (if label S (l i+r j) = none then (P (l i)).toReal * (Q (r j)).toReal else 0) < t
    split
    next hz =>
      have bound := singleton_bound h (l i+r j)
      rw [uniform_singleton,if_neg ((label_none ..).mp hz)] at bound
      linarith [single_product_le P Q (l i) (r j)]
    · linarith

private theorem realized_uniform (S : Finset ℤ) (hs : S.Nonempty) (l r : Fin S.card → ℤ)
    (y : PairWeights S.card) (L : (∑ i, (y.1 i:ℝ)) = 1) (R : (∑ j, (y.2 j:ℝ)) = 1)
    (off : ∀ i j, pattern S l r i j = none → (y.1 i:ℝ)*(y.2 j:ℝ) = 0)
    (on : ∀ z, cell (pattern S l r) z y = (S.card:ℝ)⁻¹) :
    indepSum ((indexed y.1 L).map l) ((indexed y.2 R).map r) = PMF.uniformOfFinset S hs := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' ((indepSum _ _).apply_ne_top _) ((PMF.uniformOfFinset S hs).apply_ne_top _)).mp
  rw [indexed_sum,uniform_singleton]
  by_cases hz : z ∈ S
  · rw [if_pos hz]
    let i := S.equivFin ⟨z,hz⟩
    have atSite : site S i = z := by simp [site,i]
    rw [←atSite,←cell_site]
    exact on i
  · rw [if_neg hz]
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
    by_cases eq : l i+r j = z
    · change (if l i+r j = z then (1:ℝ) else 0)*_ = 0
      rw [if_pos eq,one_mul]
      exact off i j ((label_none ..).mpr (eq ▸ hz))
    · simp [eq]

/-- For a fixed positive number of outcomes, closeness of the independent sum to uniform
forces both original laws to be close to a simultaneous exact factorization of that same law. -/
theorem repair_exact_size (m : ℕ) {ε : ℝ} (he : 0 < ε) : ∃ δ > 0,
    ∀ (S : Finset ℤ) (hs : S.Nonempty), S.card = m → ∀ P Q : PMF ℤ,
      TVLe δ (indepSum P Q) (PMF.uniformOfFinset S hs) →
      ∃ P' Q' : PMF ℤ, indepSum P' Q' = PMF.uniformOfFinset S hs ∧ TVLe ε P P' ∧ TVLe ε Q Q' := by
  let η := ε/((m:ℝ)+1)
  have positive : 0 < η := by dsimp [η];positivity
  obtain ⟨t,ht,repair⟩ := repair_patterns m positive
  let δ := min 1 t / 4
  have hd : 0 < δ := by dsimp [δ];positivity
  have small : δ < 1/2 := by dsimp [δ];linarith [min_le_left (1:ℝ) t]
  have tol : 2*δ < t := by dsimp [δ];linarith [min_le_right (1:ℝ) t]
  refine ⟨δ,hd,fun S hs eq P Q h => ?_⟩
  subst m
  obtain ⟨r,ri,R⟩ := heavy_row S hs hd small h
  have swapped : indepSum Q P = indepSum P Q := by
    change (Q.bind fun x => P.bind fun y => PMF.pure (x+y)) = _
    rw [PMF.bind_comm]
    simp only [indepSum,Bind.bind,add_comm]
  obtain ⟨l,li,L⟩ := heavy_row S hs hd small (swapped ▸ h)
  let x : PairWeights S.card := (crop P l,crop Q r)
  obtain ⟨y,good,near⟩ := repair (pattern S l r) x (small_violations hs hd tol h l r li ri L R)
  obtain ⟨ly,ry,off,on⟩ := exact_table hs.card_pos good
  have budget : (S.card:ℝ)*η ≤ ε := by
    dsimp [η]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have closeRow {A : PMF ℤ} {a : Fin S.card → ℤ} (inj : Function.Injective a)
      {v : Fin S.card → Set.Icc (0:ℝ) 1} (total : (∑ i, (v i:ℝ)) = 1)
      (rowDist : dist (crop A a) v < η) : TVLe ε A ((indexed v total).map a) := by
    have localBound := embed_close a inj v total positive.le (fun i => by
      have d := (dist_le_pi_dist (crop A a) v i).trans_lt rowDist
      change |(A (a i)).toReal - (v i:ℝ)| < η at d
      linarith [(abs_lt.mp d).1])
    exact fun E => (localBound.symm E).trans (by linarith)
  rw [Prod.dist_eq,max_lt_iff] at near
  exact ⟨_,_,realized_uniform S hs l r y ly ry off on,closeRow li ly near.1,closeRow ri ry near.2⟩

/-- A single tolerance covers all supports of at most `k` sites, without any bound on their gaps. -/
theorem repair (k : ℕ) {ε : ℝ} (he : 0 < ε) : ∃ δ > 0,
    ∀ (S : Finset ℤ) (hs : S.Nonempty), S.card ≤ k → ∀ P Q : PMF ℤ,
      TVLe δ (indepSum P Q) (PMF.uniformOfFinset S hs) →
      ∃ P' Q' : PMF ℤ, indepSum P' Q' = PMF.uniformOfFinset S hs ∧ TVLe ε P P' ∧ TVLe ε Q Q' := by
  classical
  have each (i : Fin (k+1)) := repair_exact_size i.val he
  choose d pos useD using each
  let δ := Finset.univ.inf' univ_nonempty d
  refine ⟨δ,(lt_inf'_iff ..).mpr (fun i _ => pos i),fun S hs hk P Q h => ?_⟩
  let i : Fin (k+1) := ⟨S.card,by omega⟩
  exact useD i S hs rfl P Q fun E => (h E).trans (add_le_add le_rfl (inf'_le d (mem_univ i)))

private theorem finite_gap (A : Finset ℝ) : ∃ ρ > 0, ∀ x ∈ A, ∀ y ∈ A, |x-y| ≤ 2*ρ → x=y := by
  classical
  let gap (xy : ℝ × ℝ) := if xy.1 = xy.2 then 1 else |xy.1-xy.2|
  let G := insert 1 ((A ×ˢ A).image gap)
  have nonempty : G.Nonempty := ⟨1,mem_insert_self ..⟩
  have pos (w : ℝ) (hw : w ∈ G) : 0 < w := by
    rcases mem_insert.mp hw with rfl|hw
    · exact one_pos
    · obtain ⟨⟨a,b⟩,_,rfl⟩ := mem_image.mp hw
      by_cases eq : a = b <;> simp [gap,eq,abs_pos,sub_ne_zero]
  let g := G.min' nonempty
  have hg := pos g (G.min'_mem nonempty)
  refine ⟨g/3,by positivity,fun x hx y hy h => ?_⟩
  by_contra ne
  have member : gap (x,y) ∈ G := mem_insert_of_mem (mem_image_of_mem gap (mem_product.mpr ⟨hx,hy⟩))
  have le : g ≤ |x-y| := by simpa [gap,ne] using G.min'_le _ member
  linarith

/-- The same positive separation radius works for all marginal laws in the output budget,
including translates and marginals of different uniform sums. -/
theorem separated (k : ℕ) : ∃ ρ > 0, ∀ P Q : PMF ℤ,
    (∀ i, (P i).toReal ∈ Green28MassSpectrum.alphabet k) →
    (∀ i, (Q i).toReal ∈ Green28MassSpectrum.alphabet k) →
    TVLe (2*ρ) P Q → P = Q := by
  obtain ⟨ρ,pos,gap⟩ := finite_gap (Green28MassSpectrum.alphabet k)
  refine ⟨ρ,pos,fun P Q left right near => PMF.ext fun i => ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (P.apply_ne_top _) (Q.apply_ne_top _)).mp
  exact gap _ (left _) _ (right _) (abs_le.mpr
    ⟨by linarith [singleton_bound near.symm i],by linarith [singleton_bound near i]⟩)

/-- Below a radius depending only on the output budget, the nearby exact ordered pair is unique.
Its two factors may be required to lie within any smaller positive tolerance. -/
theorem unique_repair (k : ℕ) : ∃ ρ > 0, ∀ ε > 0, ∃ δ > 0,
    ∀ (S : Finset ℤ) (hs : S.Nonempty), S.card ≤ k → ∀ P Q : PMF ℤ,
      TVLe δ (indepSum P Q) (PMF.uniformOfFinset S hs) →
      ∃! w : PMF ℤ × PMF ℤ, indepSum w.1 w.2 = PMF.uniformOfFinset S hs ∧
        TVLe (min ε ρ) P w.1 ∧ TVLe (min ε ρ) Q w.2 := by
  obtain ⟨ρ,pos,sep⟩ := separated k
  refine ⟨ρ,pos,fun ε he => ?_⟩
  obtain ⟨δ,hd,fix⟩ := repair k (lt_min he pos)
  refine ⟨δ,hd,fun S hs hk P Q near => ?_⟩
  obtain ⟨U,V,exactSum,hu,hv⟩ := fix S hs hk P Q near
  refine ⟨(U,V),⟨exactSum,hu,hv⟩,?_⟩
  rintro ⟨U',V'⟩ ⟨other,hu',hv'⟩
  have joined {A B R : PMF ℤ} (a : TVLe (min ε ρ) R A) (b : TVLe (min ε ρ) R B) : TVLe (2*ρ) A B := by
    intro E
    linarith [a.symm E,b E,min_le_right ε ρ]
  have first := Green28MassSpectrum.atoms_in_alphabet hs hk exactSum
  have second := Green28MassSpectrum.atoms_in_alphabet hs hk other
  exact Prod.ext (sep U' U second.1 first.1 (joined hu' hu)) (sep V' V second.2 first.2 (joined hv' hv))

/-- A robust version of the fairness question. Both fair approximants must realize the
original uniform target exactly. The approximate input laws may have infinite support. -/
def RobustFairness : Prop :=
  ∀ k : ℕ, ∀ ε > (0:ℝ), ∃ δ > 0, ∀ (S : Finset ℤ) (hs : S.Nonempty), S.card ≤ k →
    ∀ P Q : PMF ℤ, TVLe δ (indepSum P Q) (PMF.uniformOfFinset S hs) →
      ∃ U V : PMF ℤ, indepSum U V = PMF.uniformOfFinset S hs ∧ IsUniformOnSupport U ∧
        IsUniformOnSupport V ∧ TVLe ε P U ∧ TVLe ε Q V

/-- The left-hand side is the literal type of the pinned open declaration. -/
theorem green_28_iff_robust : (type_of% Green28.green_28) ↔ RobustFairness := by
  constructor
  · intro fair k ε he
    obtain ⟨δ,hd,fix⟩ := repair k he
    refine ⟨δ,hd,fun S hs hk P Q h => ?_⟩
    obtain ⟨U,V,eq,hu,hv⟩ := fix S hs hk P Q h
    have hsum : IsUniformOnSupport (indepSum U V) := ⟨S,hs,eq⟩
    have finite := Green28UniformSums.finite_of_uniform_sum hsum
    have both := fair U V ⟨finite.1,finite.2,hsum⟩
    exact ⟨U,V,eq,both.1,both.2,hu,hv⟩
  · intro robust P Q ⟨_,_,S,hs,eq⟩
    obtain ⟨ρ,pos,sep⟩ := separated S.card
    obtain ⟨δ,hd,fix⟩ := robust S.card (2*ρ) (by positivity)
    obtain ⟨U,V,eq',fu,fv,hu,hv⟩ := fix S hs le_rfl P Q (by
      rw [eq];intro E;linarith)
    have first := Green28MassSpectrum.atoms_in_alphabet hs le_rfl eq
    have second := Green28MassSpectrum.atoms_in_alphabet hs le_rfl eq'
    exact ⟨sep P U first.1 second.1 hu ▸ fu,sep Q V first.2 second.2 hv ▸ fv⟩

#print axioms heavy_translate
#print axioms TVLe.symm
#print axioms tvLe_iff
#print axioms repair_exact_size
#print axioms repair
#print axioms separated
#print axioms unique_repair
#print axioms green_28_iff_robust
end Green28InverseStability
