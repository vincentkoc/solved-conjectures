import Erdos722ProjectiveSublines
import Erdos722FieldGraphCovers
import Mathlib.Tactic

/-!
# Circle–circle blocks from projectivities

A compatible triple prescribes a bijection between two ordered frames.
Its unique projective action gives a graph on the whole projective line.
-/

namespace Erdos722.PointedProduct
open Finset Function Matrix OnePoint
open scoped Classical
noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

private theorem identity_on_frame {g : GL (Fin 2) F} (hi : g • (∞ : OnePoint F)=∞)
    (hz : g • ((0 : F) : OnePoint F)=((0 : F) : OnePoint F))
    (ho : g • ((1 : F) : OnePoint F)=((1 : F) : OnePoint F)) (x : OnePoint F) : g • x=x := by
  have hc := smul_infty_eq_self_iff.mp hi
  have hd : g 1 1 ≠ 0 := fun h => g.det_ne_zero (by simp [det_fin_two,hc,h])
  have hb : g 0 1=0 := by
    simpa [smul_some_eq_ite,hc,hd,OnePoint.coe_eq_coe,div_eq_zero_iff] using hz
  have ha : g 0 0=g 1 1 := by
    simpa [smul_some_eq_ite,hc,hd,hb,OnePoint.coe_eq_coe,div_eq_one_iff_eq hd] using ho
  cases x with
  | infty => exact hi
  | coe x => simp [smul_some_eq_ite,hc,hd,hb,ha,mul_div_cancel_left₀]

private theorem frame_ext (a g h : GL (Fin 2) F)
    (hi : g • (a • (∞ : OnePoint F))=h • (a • ∞))
    (hz : g • (a • ((0 : F) : OnePoint F))=h • (a • ((0 : F) : OnePoint F)))
    (ho : g • (a • ((1 : F) : OnePoint F))=h • (a • ((1 : F) : OnePoint F)))
    (x : OnePoint F) : g • x=h • x := by
  have fix {w : OnePoint F} (hw : g • (a • w)=h • (a • w)) :
      (a⁻¹*(h⁻¹*(g*a))) • w=w := by simp [mul_smul,hw]
  have H := identity_on_frame (fix hi) (fix hz) (fix ho) (a⁻¹ • x)
  simpa only [mul_smul,smul_inv_smul,inv_smul_eq_iff] using H

/-- Circle–circle cover on the projective line over any finite field. -/
def projective_circle_circle (F : Type*) [Field F] [DecidableEq F] [Fintype F] :
    RectangleCover (Fintype.card F) .circle .circle (OnePoint F) (OnePoint F) := by
  classical
  let words (f : OnePoint F → OnePoint F) := ∃ g : GL (Fin 2) F, f=(g • ·)
  apply word_cover (U:=OnePoint F) (show Fintype.card (OnePoint F)=Fintype.card F+1 from Fintype.card_option) words
  · rintro f ⟨g,rfl⟩ S hs
    change (univ.image (fun x : S => g • x.val)).card=3
    have hi : Injective (fun x : S => g • x.val) := (MulAction.injective g).comp Subtype.val_injective
    rw [card_image_of_injective _ hi,card_univ,
      Fintype.card_coe,hs]
  · intro S hs d rich
    let e : Fin 3 ≃ S := (S.equivFinOfCardEq hs).symm
    let x (i : Fin 3) : OnePoint F := (e i).val
    have xi : Injective x := Subtype.val_injective.comp e.injective
    have hcard : (univ.image d).card=(univ : Finset S).card := by
      change (univ.image d).card=3 at rich
      simpa [hs] using rich
    have di : Injective d := fun i j he => card_image_iff.mp hcard (mem_univ i) (mem_univ j) he
    have yi := di.comp e.injective
    obtain ⟨a,ai,az,ao⟩ := Sublines.exists_frame (xi.ne (by decide : (0:Fin 3)≠1))
      (xi.ne (by decide : (0:Fin 3)≠2)) (xi.ne (by decide : (1:Fin 3)≠2))
    obtain ⟨b,bi,bz,bo⟩ := Sublines.exists_frame (yi.ne (by decide : (0:Fin 3)≠1))
      (yi.ne (by decide : (0:Fin 3)≠2)) (yi.ne (by decide : (1:Fin 3)≠2))
    let g := b*a⁻¹
    have act {z : OnePoint F} {i : Fin 3} (ha : a • z=x i) (hb : b • z=d (e i)) :
        g • x i=d (e i) := by rw [← ha,show g=b*a⁻¹ from rfl,mul_smul,inv_smul_smul,hb]
    have h0 := act ai bi
    have h1 := act az bz
    have h2 := act ao bo
    refine ⟨(g • ·),⟨⟨g,rfl⟩,?_⟩,?_⟩
    · intro w
      obtain ⟨i,rfl⟩ := e.surjective w
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    · rintro f ⟨⟨j,rfl⟩,hj⟩
      exact funext (frame_ext a j g (ai ▸ (hj (e 0)).trans h0.symm)
        (az ▸ (hj (e 1)).trans h1.symm) (ao ▸ (hj (e 2)).trans h2.symm))

#print axioms projective_circle_circle
end
end Erdos722.PointedProduct
