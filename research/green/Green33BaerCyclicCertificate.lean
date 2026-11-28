import Green33BaerSubline
import Green33BaerQuadraticRetention
import Green33PrimeSingerBasisGap

/-! Non-Sidon rational subplanes in the cyclic double of a square-order Singer plane. -/
namespace Green33BaerCyclic
open Finset Green33SingerAllCharacteristics Green33PrimeSingerIncidence Green33BaerSubline Green33BaerForms
open Green33ReflectedLayers (doubleHom double_coordinates)
open scoped Pointwise
variable {F E K : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Field K] [Fintype K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    [DecidableEq E] [DecidableEq K]
noncomputable local instance : Fintype (Green33SingerProjectiveOverlap.Plane E K) := Fintype.ofFinite _

/-- Standard even-coordinate embedding of a Singer chart. Composing with a
cyclic automorphism allows either sign. Translation chooses the parity layer. -/
noncomputable def doubledTag {D:Finset (ZMod (order E))} (S:SingerMap E K D)
    (e:ZMod (order E)≃+ZMod (order E)) (u:Kˣ) : ZMod (2*order E) :=
  doubleHom (positiveOrder E) (e (S.tag u))

/-- Every cubic projective frame supplies an actual Singer chart in the cyclic
plane, with its predicate on the canonical hyperplane labels. -/
theorem chart_exists (frame:K≃ₗ[E](Fin 3→E)) :
    ∃ (h:Fintype.card K=(Fintype.card E)^3) (L:K→ₗ[E]E),
      Nonempty (SingerMap E K (labels h L)) := by
  have h:Fintype.card K=(Fintype.card E)^3 := by simpa using Fintype.card_congr frame.toEquiv
  let L:K→ₗ[E]E:=(LinearMap.proj (0:Fin 3)).comp frame.toLinearMap
  have sur : Function.Surjective L := fun x => ⟨frame.symm (fun _ => x),congrFun (frame.apply_symm_apply _) 0⟩
  exact ⟨h,L,Green33PrimeSingerBasisGap.singer_map h L sur⟩

omit [DecidableEq E] [DecidableEq K] in
/-- A non-Sidon Baer layer inside the doubled cyclic plane has the exact
projective size and contains the full translated split quadratic family. -/
theorem cyclic_certificate (frame:K≃ₗ[E](Fin 3→E)) {D:Finset (ZMod (order E))}
    (S:SingerMap E K D) (e:ZMod (order E)≃+ZMod (order E)) (z:ZMod (2*order E))
    (a b c d:Kˣ) (hw:∀ u∈([a,b,c,d]:List Kˣ),(u:K)∈rationalForm F frame)
    (collision:(a:K)*b=c*(d:K)) (ac:(a:K)∉F ∙ (c:K)) (ad:(a:K)∉F ∙ (d:K)) :
    let B:=layer (doubledTag S e) (rationalForm F frame) z
    B.card=(Fintype.card F)^2+Fintype.card F+1 ∧
    ∃ X:Finset (ZMod (2*order E)),∃ shift:ZMod (2*order E),X.card=Fintype.card F ∧
      (X+X).card=(Fintype.card F+1).choose 2 ∧ (X+X).image (shift+·)⊆B := by
  have pinj:=(double_coordinates (positiveOrder E) 0).1
  have same (u v:Kˣ) : doubledTag S e u=doubledTag S e v ↔ ∃ r:E,(u:K)=r • (v:K) :=
    pinj.eq_iff.trans (e.injective.eq_iff.trans (S.same u v))
  have mul (u v:Kˣ) : doubledTag S e (u*v)=doubledTag S e u+doubledTag S e v := by
    unfold doubledTag
    rw [S.mul,e.map_add]
    exact (doubleHom (positiveOrder E)).map_add _ _
  exact ⟨layer_card frame _ same z,baer_split frame _ mul (fun u v => (same u v).mp) z a b c d
    (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp)) collision ac ad⟩
#print axioms chart_exists
#print axioms cyclic_certificate
end Green33BaerCyclic

namespace Green33BaerCyclic
open Finset Filter Green33SingerAllCharacteristics Green33PrimeSingerIncidence Green33BaerSubline Green33BaerForms
open scoped Topology Pointwise

/-- Order of the doubled cyclic Singer plane over E. -/
abbrev modulus (E:Type*) [Fintype E] : ℕ+ := ⟨2*order E,by dsimp [order];omega⟩

/-- The actual cyclic labels of a rational subplane in an E-frame whose
three-dimensional F-space admits two inequivalent multiplicative pairs. -/
def IsNonSidonLayer (F E K:Type*) [Field F] [Field E] [Fintype E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
    (B:Finset (ZMod (modulus E))) : Prop :=
  ∃ (frame:K≃ₗ[E](Fin 3→E)) (D:Finset (ZMod (order E))) (S:SingerMap E K D)
    (e:ZMod (order E)≃+ZMod (order E)) (z:ZMod (modulus E)),
    B=layer (doubledTag S e) (rationalForm F frame) z ∧
    ∃ a b c d:Kˣ,(∀ u∈([a,b,c,d]:List Kˣ),(u:K)∈rationalForm F frame) ∧
      (a:K)*b=c*(d:K) ∧ (a:K)∉F ∙ (c:K) ∧ (a:K)∉F ∙ (d:K)

private theorem IsNonSidonLayer.bounds {F E K:Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Field K] [Fintype K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K] {B:Finset (ZMod (modulus E))}
    (h:IsNonSidonLayer F E K B) :
    B.card=(Fintype.card F)^2+Fintype.card F+1 ∧
    ∃ X:Finset (ZMod (modulus E)),∃ shift:ZMod (modulus E),X.card=Fintype.card F ∧
      (X+X).card=(Fintype.card F+1).choose 2 ∧ (X+X).image (shift+·)⊆B := by
  obtain ⟨frame,D,S,e,z,rfl,a,b,c,d,hw,hit,ac,ad⟩:=h
  exact cyclic_certificate frame S e z a b c d hw hit ac ad

section Families
variable {ι:Type*} {l:Filter ι} (F E K:ι→Type*) [∀ i,Field (F i)] [∀ i,Fintype (F i)]
    [∀ i,Field (E i)] [∀ i,Fintype (E i)] [∀ i,Field (K i)] [∀ i,Fintype (K i)]
    [∀ i,Algebra (F i) (E i)] [∀ i,Algebra (E i) (K i)] [∀ i,Algebra (F i) (K i)]
    [∀ i,IsScalarTower (F i) (E i) (K i)] (square:∀ i,Fintype.card (E i)=(Fintype.card (F i))^2)
    (grow:Tendsto (fun i => Fintype.card (F i)) l atTop)
    (B T:∀ i,Finset (ZMod (modulus (E i)))) (geometry:∀ i,IsNonSidonLayer (F i) (E i) (K i) (B i))
    (full:∀ i,T i+T i=univ)
include square grow geometry full

/-- Even after arbitrary other points are added, retaining the layer up to
o(t²) deletions forces the lower size coefficient 5/sqrt(12). -/
theorem baer_floor (missing:Tendsto (fun i => (((B i)\(T i)).card:ℝ)/(Fintype.card (F i):ℝ)^2) l (𝓝 0))
    {v:ℝ} (below:v<Real.sqrt (25/12)) :
    ∀ᶠ i in l,v<((T i).card:ℝ)/Real.sqrt (modulus (E i)) := by
  apply Green33BaerRetention.retained_floor _ _ B T (fun _ => Fintype.card_pos) grow _ full (fun i => (geometry i).bounds.2) missing below
  intro i
  change 2*((Fintype.card (E i))^2+Fintype.card (E i)+1)=_
  rw [square]
  ring

/-- An unrestricted critical full basis contains asymptotically at most half
the points of any non-Sidon rational subplane layer, in any cyclic coordinates. -/
theorem baer_half (critical:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (modulus (E i))) l (𝓝 (Real.sqrt 2)))
    {v:ℝ} (above:1/2<v) :
    ∀ᶠ i in l,((T i∩B i).card:ℝ)/(Fintype.card (F i):ℝ)^2<v := by
  apply Green33BaerRetention.critical_half _ _ B T (fun _ => Fintype.card_pos) grow _ full critical
    (fun i => (geometry i).bounds.1) (fun i => (geometry i).bounds.2) above
  intro i
  change 2*((Fintype.card (E i))^2+Fintype.card (E i)+1)=_
  rw [square]
  ring
end Families
#print axioms baer_floor
#print axioms baer_half
end Green33BaerCyclic
