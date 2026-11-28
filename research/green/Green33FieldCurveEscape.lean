import Green33SingerBasisCurves
import Green33PrimeSingerCounts
/-! Curve escape for cubic Singer lines over growing finite fields. -/
open Finset Filter Green33SingerBasisCurves Green33SingerCurveChart Green33SingerCurveSupport
open Green33SingerBlockingLayers Green33PrimeSingerIncidence Green33SingerAllCharacteristics
open scoped Pointwise Topology
namespace Green33FieldCurveEscape

section OddFields
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K]

/-- Every coordinate frame gives an affine chart for a cubic Singer hyperplane. -/
noncomputable def fieldChart (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F)
    (onto : Function.Surjective L) (e : K≃ₗ[F](Fin 3→F)) :
    Chart F (ZMod (order F)) (labels h L) :=
  singerChart (Green33PrimeSingerBasisGap.singer_map h L onto).some e

omit [DecidableEq F] [DecidableEq K] in
/-- Cubic cardinality supplies the coordinate frames used in the statement. -/
theorem frames_exist (h : Fintype.card K=(Fintype.card F)^3) : Nonempty (K≃ₗ[F](Fin 3→F)) := by
  have rank : Module.finrank F K=3 :=
    Nat.pow_right_injective (Fintype.one_lt_card : 1<Fintype.card F) ((Module.card_eq_pow_finrank (K:=F) (V:=K)).symm.trans h)
  exact ⟨(Module.finBasisOfFinrankEq F K rank).equivFun⟩
end OddFields

/-- In every growing family of eventually odd cubic fields, almost retaining
a Singer line forces the opposite parity class of a critical full basis to
escape every bounded-degree curve in any sequence of coordinate frames. -/
theorem odd_field_escape (F K : ℕ→Type*) [∀ i,Field (F i)] [∀ i,Fintype (F i)] [∀ i,DecidableEq (F i)]
    [∀ i,Field (K i)] [∀ i,Fintype (K i)] [∀ i,DecidableEq (K i)] [∀ i,Algebra (F i) (K i)]
    (h : ∀ i,Fintype.card (K i)=(Fintype.card (F i))^3) (L : ∀ i,K i→ₗ[F i] F i)
    (onto : ∀ i,Function.Surjective (L i)) (e : ∀ i,K i≃ₗ[F i](Fin 3→F i))
    (odd : ∀ᶠ i in atTop,ringChar (F i)≠2) (grow : Tendsto (fun i => Fintype.card (F i)) atTop atTop)
    (E B : ∀ i,Finset (ZMod (order (F i)))) (f : ∀ i,Polynomial (Polynomial (F i))) (d : ℕ)
    (ne : ∀ i,f i≠0) (dx : ∀ i m,((f i).coeff m).natDegree≤d) (dy : ∀ i,(f i).natDegree≤d)
    (full : ∀ i,split (v:=positiveOrder (F i)) (E i) (B i)+split (v:=positiveOrder (F i)) (E i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (v:=positiveOrder (F i)) (E i) (B i)).card:ℝ)/
      Real.sqrt ((2*order (F i):ℕ):ℝ)) atTop (𝓝 (Real.sqrt 2)))
    (retain : Tendsto (fun i => (((labels (h i) (L i))\(E i)).card:ℝ)/(Fintype.card (F i))) atTop (𝓝 0)) :
    Tendsto (fun i => ((B i∩locus (fieldChart (h i) (L i) (onto i) (e i)) (f i)).card:ℝ)/
      (Fintype.card (F i))) atTop (𝓝 0) := by
  apply stable_basis_escape (v:=fun i => positiveOrder (F i)) _ E B _ _ f d ne dx dy
    (fun i => perfect_labels (h i) (L i) (onto i)) _ (fun _ => Fintype.card_pos) grow _ full critical retain
  · intro i
    classical
    change (labels (h i) (L i)).card=_
    rw [labels,card_map,(Green33SingerKloosterman.cubic_parameters (L i) (onto i) (h i)).1]
  · intro a
    exact Green33PrimeSingerCounts.seven_eighths_field F odd K h L onto a grow

#print axioms fieldChart
#print axioms frames_exist
#print axioms odd_field_escape

section Binary
open Green33SingerCoordinates
open Green33SingerProjectiveOverlap (scalars Plane cyclic)
private noncomputable def valueEquiv {F K : Type*} [Field F] [Field K] [Algebra F K] (C : CubicFrame F K) :
    Coords F ≃ₗ[F] K := by
  let L : Coords F →ₗ[F] K := {
    toFun := value C.theta
    map_add' := by intro x y;simp [value,map_add,add_mul];ring
    map_smul' := by intro a x;simp [value,Algebra.smul_def,map_mul,mul_add];ring }
  exact LinearEquiv.ofBijective L C.basis

/-- The binary power-basis construction has the same projective chart property,
with the coordinates of its own cyclic quotient. -/
noncomputable def powerChart {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] (C : CubicFrame F K) (e : K≃ₗ[F](Fin 3→F)) :
    Chart F (ZMod (order F)) (Green33SingerProjectiveOverlap.labels C) := by
  classical
  let P:=QuotientGroup.mk' (scalars F K)
  let g:=cyclic C
  let tag (u : Kˣ):=g.symm (Additive.ofMul (P u))
  let V:=valueEquiv C
  let L:K→ₗ[F] F:=((LinearMap.snd F F F).comp (LinearMap.snd F F (F×F))).comp V.symm.toLinearMap
  have eval (x : Coords F) : L (value C.theta x)=x.2.2 := by
    change (V.symm (V x)).2.2=x.2.2
    rw [V.symm_apply_apply]
  have onto : Function.Surjective L := fun a => ⟨value C.theta (0,0,a),eval _⟩
  have same (u v:Kˣ) : P u=P v ↔ ∃ k:F,(u:K)=k • (v:K) := by
    constructor
    · intro eq
      obtain ⟨a,ha⟩:=QuotientGroup.eq_iff_div_mem.mp eq
      have hh:=congrArg (fun z:Kˣ => (z:K)) ha
      rw [Units.val_div_eq_div_val] at hh
      exact ⟨a,by rw [Algebra.smul_def];exact ((eq_div_iff v.ne_zero).mp hh).symm⟩
    · rintro ⟨a,ha⟩
      have nz:a≠0 := by rintro rfl;simp [u.ne_zero] at ha
      apply QuotientGroup.eq_iff_div_mem.mpr
      refine ⟨Units.mk0 a nz,Units.ext ?_⟩
      rw [Units.val_div_eq_div_val]
      change algebraMap F K a=(u:K)/(v:K)
      exact (eq_div_iff v.ne_zero).mpr (by simpa only [Algebra.smul_def] using ha.symm)
  apply singerChart (K:=K) (e:=e)
  refine ⟨L,onto,tag,?_,?_,?_,?_⟩
  · intro u v
    exact (congrArg (fun x => g.symm (Additive.ofMul x)) (P.map_mul u v)).trans (g.symm.map_add _ _)
  · intro x
    obtain ⟨u,hu⟩:=QuotientGroup.mk'_surjective (scalars F K) (g x).toMul
    exact ⟨u,(congrArg (fun y => g.symm (Additive.ofMul y)) hu).trans (g.symm_apply_apply x)⟩
  · intro u v
    exact g.symm.injective.eq_iff.trans (same u v)
  · intro u
    simp only [Green33SingerProjectiveOverlap.labels,mem_filter,mem_univ,true_and]
    change (g (g.symm (Additive.ofMul (P u)))).toMul ∈ Green33SingerProjectiveOverlap.seed C ↔ _
    rw [g.apply_symm_apply]
    change P u ∈ Green33SingerProjectiveOverlap.seed C ↔ L (u:K)=0
    rw [Green33SingerReflectedCoverage.mem_seed]
    obtain ⟨⟨a,b,c⟩,hu⟩:=C.basis.surjective (u:K)
    rw [←hu,eval]
    constructor
    · rintro ⟨j,k,h⟩
      exact (congrArg (fun z:Coords F => z.2.2) (C.basis.injective h)).symm
    · intro z;exact ⟨a,b,by simp only at z;rw [z]⟩

/-- The characteristic-two conclusion for the notebook's actual cubic
power-basis Singer line, with any ambient coordinate frames. -/
theorem binary_field_escape (F K : ℕ→Type*) [∀ i,Field (F i)] [∀ i,Fintype (F i)] [∀ i,CharP (F i) 2]
    [∀ i,DecidableEq (F i)] [∀ i,Field (K i)] [∀ i,Fintype (K i)] [∀ i,Algebra (F i) (K i)]
    (C : ∀ i,CubicFrame (F i) (K i)) (e : ∀ i,K i≃ₗ[F i](Fin 3→F i))
    (grow : Tendsto (fun i => Fintype.card (F i)) atTop atTop)
    (E B : ∀ i,Finset (ZMod (order (F i)))) (f : ∀ i,Polynomial (Polynomial (F i))) (d : ℕ)
    (ne : ∀ i,f i≠0) (dx : ∀ i m,((f i).coeff m).natDegree≤d) (dy : ∀ i,(f i).natDegree≤d)
    (full : ∀ i,split (v:=positiveOrder (F i)) (E i) (B i)+split (v:=positiveOrder (F i)) (E i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (v:=positiveOrder (F i)) (E i) (B i)).card:ℝ)/
      Real.sqrt ((2*order (F i):ℕ):ℝ)) atTop (𝓝 (Real.sqrt 2)))
    (retain : Tendsto (fun i => (((Green33SingerProjectiveOverlap.labels (C i))\(E i)).card:ℝ)/
      (Fintype.card (F i))) atTop (𝓝 0)) :
    Tendsto (fun i => ((B i∩locus (powerChart (C i) (e i)) (f i)).card:ℝ)/
      (Fintype.card (F i))) atTop (𝓝 0) := by
  apply stable_basis_escape (v:=fun i => positiveOrder (F i)) _ E B _ _ f d ne dx dy
    (fun i => Green33SingerReflectedCoverage.perfect (C i)) (fun i => Green33SingerReflectedCoverage.label_card (C i))
    (fun _ => Fintype.card_pos) grow _ full critical retain
  intro a
  exact Green33SingerReflectedCoverage.coverage C a grow

#print axioms powerChart
#print axioms binary_field_escape
end Binary

end Green33FieldCurveEscape
