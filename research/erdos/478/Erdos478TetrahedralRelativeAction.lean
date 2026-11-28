import Erdos478NormalSwapPower
import Erdos478TetrahedralVertexAction
import Erdos478TetrahedralFrobenius
import Erdos478QuinticJointLaw

/-! # Independence of the tetrahedral action from every lower gap action through five -/

namespace Erdos478.TetrahedralGap
open Polynomial Equiv Finset MulAction FirstCollision BinaryGap LowGapAction FrobeniusCounts
open scoped Classical
noncomputable section
local instance (n : ℕ) : Fintype (Perm (Fin n)) := fintypePerm
set_option maxRecDepth 32768
set_option maxHeartbeats 3000000

private theorem cube2 : ∀ u : Perm (Fin 2), pointCount u=2 → u^3=1 := by decide +kernel
private theorem cube3 : ∀ u : Perm (Fin 3), pointCount u=0 → u^3=1 := by decide +kernel
private theorem cube4 : ∀ u : Perm (Fin 4), pointCount u=4 → u^3=1 := by decide +kernel
private theorem cube5 : ∀ u : Perm (Fin 5), pointCount u=2 → u^3=1 := by decide +kernel

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
private theorem vertex_swap (g : Aut K) (h : fixed K (quartic ℤ) g=2)
    (sp : ((quartic ℚ).map (algebraMap ℚ K)).Splits) : (vertexAction K g).IsSwap := by
  classical
  let X := Vertex K
  let T := univ.filter fun x : X => vertexAction K g x=x
  have cnt : T.card=2 := by
    have e : T ≃ fixedBy X g := Equiv.subtypeEquivRight fun x => by simp [T,vertexAction,mem_fixedBy]
    unfold fixed rootType at h
    rw [quartic_map] at h
    exact (Nat.card_eq_finsetCard T).symm.trans ((Nat.card_congr e).trans h)
  have size : T.card+(vertexAction K g).support.card=Fintype.card X := by
    simpa [T,Perm.support] using card_filter_add_card_filter_not (s:=(univ : Finset X))
      (fun x => vertexAction K g x=x)
  apply Perm.card_support_eq_two.mp
  rw [show Fintype.card X=4 from vertex_card K sp,cnt] at size
  omega

/-- Any allowed permutation of the lower roots can be held fixed while the
four auxiliary roots are permuted arbitrarily. -/
theorem vertex_relative_surjective
    (split : ∀ k, 2≤k → k≤6 → ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    Function.Surjective ((vertexAction K).comp (LowerKernel K (short 5)).subtype) := by
  classical
  have qs := quartic_splits_of_sextic K (split 6 (by decide) (by decide))
  obtain ⟨g,h₂,h₃,h₄,h₅,hq⟩ := TetrahedralSample.simultaneous_profile K
    (fun k lo hi => split k lo (by omega)) qs
  apply relative_swap_power (lowerAction K (short 5)) (vertexAction K) (vertex_surjective K qs) g 3
  · apply _root_.funext
    intro i
    obtain ⟨lo,hi⟩ := mem_Icc.mp i.prop
    let e := rootLabels K (k:=i.val) (by omega) (split i lo (by omega))
    have cnt := numbered_fixed K e g
    have kill : (numberedAction K e g)^3=1 := by
      generalize hu : numberedAction K e g=u at cnt ⊢
      have slots : i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 := by omega
      rcases i with ⟨k,hk⟩
      dsimp only at slots cnt u
      rcases slots with rfl|rfl|rfl|rfl
      · exact cube2 _ (cnt.trans h₂)
      · exact cube3 _ (cnt.trans h₃)
      · exact cube4 _ (cnt.trans h₄)
      · exact cube5 _ (cnt.trans h₅)
    rw [← map_pow] at kill
    apply Perm.ext
    intro x
    apply e.injective
    change e ((g^3) • x)=e x
    simpa only [numbered_apply,e.symm_apply_apply,Perm.one_apply] using
      congrArg (fun a : Perm (Fin i.val) => a (e x)) kill
  · have hs := vertex_swap K g hq qs
    have h := pow_orderOf_eq_one (vertexAction K g)
    rw [hs.orderOf] at h
    rw [map_pow,pow_succ,h,one_mul]
    exact hs

#print axioms vertex_relative_surjective
end
end Erdos478.TetrahedralGap
