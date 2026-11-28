import Green51SimplexFibres

/-! # An exterior triple bounds the total size in twelve dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51SimplexSection Green51SimplexFibres
open scoped Classical Pointwise
namespace Green51TwelveSections
local notation "F" => ZMod 2
local notation "V" => Cube 12

/-- At least five further labels in four quotient classes supply the exterior
pair prohibited by the fifteen-plus-three configuration. -/
theorem exterior_pair {A B : Finset V} (L : Cube 10 →ₗ[F] V) (inj : Function.Injective L)
    (t : V) (inc : core L t⊆A) (size : 23≤A.card) (inB : B⊆A) (three : B.card=3)
    (outB : Disjoint B (core L t)) (bDiff : ∀x∈B,∀y∈B,x+y∈L.range) : ∃p,FlatAt A p := by
  classical
  let R := A\(core L t∪B)
  have coreSize : (core L t).card=15 := by
    rw [core,card_image_of_injective _ (fun _ _ h => inj (add_right_cancel h)),model_card]
  have rest : 5≤R.card := by
    have total := card_le_card_sdiff_add_card (s:=A) (t:=core L t∪B)
    have bound := card_union_le (core L t) B
    change 5≤(A\(core L t∪B)).card; omega
  let Q := V ⧸ L.range
  let _ : Fintype Q := Fintype.ofFinite _
  have dim := L.range.finrank_quotient_add_finrank
  have rank : Module.finrank F L.range=10 := by simpa [Cube] using L.finrank_range_of_inj inj
  have small : Module.finrank F Q=2 := by
    change Module.finrank F (V ⧸ L.range)=2
    rw [rank,show Module.finrank F V=12 by simp [Cube]] at dim
    omega
  have four : Fintype.card Q=4 := by
    rw [Module.card_eq_pow_finrank (K:=F),small,ZMod.card]
    rfl
  let tag (x:R) : Q := L.range.mkQ x.val
  obtain ⟨d,e,ne,same⟩ := Fintype.exists_ne_map_eq_of_card_lt tag (by
    rw [four,Fintype.card_coe];omega)
  have diff : d.val≠e.val := fun eq => ne (Subtype.ext eq)
  have together : d.val+e.val∈L.range := by
    apply (Submodule.Quotient.mk_eq_zero L.range).mp
    change L.range.mkQ (d.val+e.val)=0
    rw [map_add,show L.range.mkQ d.val=L.range.mkQ e.val from same,ZModModule.add_self]
  let C : Finset V := {d.val,e.val}
  have inR : C⊆R := by
    intro x hx; rcases mem_insert.mp hx with rfl|ht
    · exact d.property
    · simpa only [mem_singleton.mp ht] using e.property
  have left {x} (h:x∈C) := mem_sdiff.mp (inR h)
  refine three_and_two L inj t inc (by omega) inB (fun _ h => (left h).1) three
    (by simp [C,diff]) (disjoint_left.mpr (fun _ hb hc => (left hc).2 (mem_union_right _ hb)))
    outB (disjoint_left.mpr (fun _ hc hx => (left hc).2 (mem_union_left _ hx))) bDiff ?_
  intro x hx y hy
  simp only [C,mem_insert,mem_singleton] at hx hy
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
  · simp only [ZModModule.add_self,Submodule.zero_mem]
  · exact together
  · simpa only [add_comm] using together
  · simp only [ZModModule.add_self,Submodule.zero_mem]

end Green51TwelveSections
#print axioms Green51TwelveSections.exterior_pair
