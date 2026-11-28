import Erdos722RankClassQuotient

/-! # The number of gauges in the minimum-rank affine orbit -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function Module
open scoped Classical
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V))

private def parityMap : (V → ZMod 2) →ₗ[ZMod 2] (H → ZMod 2) where
  toFun u i := blockSum u i.val
  map_add' _ _ := funext fun i => by simp [blockSum,sum_add_distrib]
  map_smul' c u := by
    funext i
    simp [blockSum,Finset.mul_sum]

private def checkKernel : Checks H ≃ LinearMap.ker (parityMap H) :=
  Equiv.subtypeEquivRight fun f => by
    rw [LinearMap.mem_ker]
    exact ⟨fun h => funext fun i => h i.val i.prop,fun h B hB => congrFun h ⟨B,hB⟩⟩

theorem mem_gauge_iff (s : H → Bool) : s∈gaugeAssignments H ↔ Coboundary s := by
  refine ⟨?_,gauge_mem⟩
  intro h
  obtain ⟨u,_,rfl⟩ := mem_image.mp h
  exact ⟨u,fun i => (flipBit_decode _).symm⟩

private def gaugeRange : gaugeAssignments H ≃ LinearMap.range (parityMap H) := by
  let F (s : gaugeAssignments H) : LinearMap.range (parityMap H) :=
    ⟨fun i => bitValue (s.val i),by
      obtain ⟨u,hu⟩ := (mem_gauge_iff H _).mp s.prop
      exact ⟨u,funext hu⟩⟩
  apply Equiv.ofBijective F
  constructor
  · intro s t eq
    apply Subtype.ext
    funext i
    exact (show Injective bitValue by decide) (congrArg (fun z : LinearMap.range (parityMap H) => z.val i) eq)
  · rintro ⟨_,u,rfl⟩
    let s (i : H) := flipBit (blockSum u i.val)
    refine ⟨⟨s,(mem_gauge_iff H s).mpr ⟨u,fun i => (flipBit_decode _).symm⟩⟩,?_⟩
    exact Subtype.ext (funext fun i => flipBit_decode _)

theorem exact_gauge_weight : (gaugeAssignments H).card*Nat.card (Checks H)=2^Fintype.card V := by
  let f := parityMap H
  have dim := f.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at dim
  rw [← Nat.card_eq_finsetCard,Nat.card_congr (gaugeRange H),Nat.card_congr (checkKernel H),
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=LinearMap.range f),
    Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=LinearMap.ker f),← pow_add,dim]
  simp [Nat.card_eq_fintype_card]

theorem affine_class_switches (d : ℕ) :
    (univ.filter (fun s : Switches d => classOf (binaryDouble d s)=affineClass d))=gaugeAssignments (binaryBase d).val := by
  classical
  ext s
  simp only [mem_filter,mem_univ,true_and,mem_gauge_iff]
  change classOf (binaryDouble d s)=classOf (binaryDouble d (fun _ => false)) ↔ Coboundary s
  rw [class_eq_iff]
  change Isomorphic ((binaryStepLabels d).finsetCongr.finsetCongr _) ((binaryStepLabels d).finsetCongr.finsetCongr _) ↔ _
  rw [relabel_iso_iff]
  refine ⟨fun he => (isomorphic_coboundary (binaryBase d).prop (binaryBase_separates d) he).mpr ?_,
    coboundary_zero_iso (binaryBase d).prop⟩
  exact ⟨fun _ => 0,fun _ => by simp [bitValue,blockSum]⟩

#print axioms mem_gauge_iff
#print axioms exact_gauge_weight
#print axioms affine_class_switches
end
end Erdos722.QuadSwitch
