import Erdos722EqualSignatureFibres
import Erdos722BinaryProjectionBlocks

/-! # Every two-point signature fibre presentation is a switched quadruple double -/

namespace Erdos722.QuadSwitch
open Finset Function Module
noncomputable section
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {D : Finset (Finset V)} {H : Finset (Finset W)}

private theorem linear_labels {S T : Type*} [AddCommGroup S] [AddCommGroup T] [Module (ZMod 2) S]
    [Module (ZMod 2) T] [Finite S] [Finite T] (card : Nat.card S=Nat.card T) :
    Nonempty (S ≃ₗ[ZMod 2] T) := by
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=S),
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=T)] at card
  exact Nat.pow_right_injective (by decide : 2≤2) (by simpa [Nat.card_eq_fintype_card] using card)

/-- Suppose the short system separates its points by binary checks. Matching the
number of checks and doubling the point count force the large system to be one
of the independently switched doubles, up to an unrestricted relabelling. -/
theorem paired_presentation (hD : D.IsBlockDesign 3 4) (hH : H.IsBlockDesign 3 4) (sep : Separates H)
    (a : V) (b : W) (points : Nat.card V=2*Nat.card W) (checks : Nat.card (Checks D)=Nat.card (Checks H)) :
    ∃ (e : V ≃ W × Bool) (s : H → Bool), e.finsetCongr.finsetCongr D=doubling hH s := by
  classical
  let C : W ≃ labelSpace hH b := signatureCoordinates hH sep b
  have cb := Nat.card_congr C
  have size : Nat.card (labelSpace hD a)=Nat.card (labelSpace hH b) := by
    rw [label_card_checks hD a,label_card_checks hH b] at checks
    omega
  let L : labelSpace hD a ≃ₗ[ZMod 2] labelSpace hH b := (linear_labels size).some
  have mul := Nat.card_congr (labelProduct hD a)
  rw [Nat.card_prod,size,← cb,points,mul_comm 2] at mul
  have pos : 0<Nat.card W := by let : Nonempty W := ⟨b⟩; exact Nat.card_pos
  have fc : Nat.card (LabelFibre hD a 0)=2 := (Nat.eq_of_mul_eq_mul_left pos mul).symm
  let F : LabelFibre hD a 0 ≃ Bool := Fintype.equivOfCardEq (by simpa [Nat.card_eq_fintype_card] using fc)
  let e := (labelProduct hD a).trans ((L.toEquiv.trans C.symm).prodCongr F)
  have point (x : V) : signature H (e x).1 + signature H b=(L (label hD a x)).val :=
    congrArg Subtype.val (C.apply_symm_apply (L (label hD a x)))
  have plane (B : Finset V) (hb : B∈D) : ∑ x∈B,signature H (e x).1=0 := by
    have total : ∑ x∈B,(L (label hD a x)).val=0 := by
      change ∑ x∈B,(labelSpace hH b).subtype (L (label hD a x))=0
      rw [← map_sum,← map_sum,label_block_sum hD a hb,map_zero,map_zero]
    simp_rw [← point] at total
    rw [sum_add_distrib,sum_const,hD.1 B hb] at total
    have four : 4 • signature H b=0 := by
      funext u
      change 4 • (signature H b u)=0
      rw [nsmul_eq_mul]; norm_num; exact Or.inl (by decide)
    rwa [four,add_zero] at total
  have design := relabel_quadruples e hD
  have compat := compatible_of_projected_sums hH sep design (by
    intro B hb
    obtain ⟨A,hA,rfl⟩ := mem_map.mp hb
    simpa [Equiv.finsetCongr_apply] using plane A hA)
  obtain ⟨s,hs,_⟩ := (classification hH _).mp ⟨design,compat⟩
  exact ⟨e,s,hs⟩

#print axioms paired_presentation
end
end Erdos722.QuadSwitch
