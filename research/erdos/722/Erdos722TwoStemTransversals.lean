import Erdos722TwoStemGeometry
import Erdos722HyperovalWords

/-!
# Transversal and one-group fillings

Any code in which three coordinates determine a unique word supplies
the blocks on a circle face. A singleton face consists of its fiber
and both stem points.
-/

namespace Erdos722.TwoStem
open Finset Function PointedProduct
open scoped Classical
noncomputable section

variable {U V : Type*} [Fintype U] [DecidableEq U]

private def graphEmb (f : U → V) : U ↪ Space U V :=
  ⟨fun x => some (some (x,f x)),fun _ _ h => congrArg Prod.fst (Option.some.inj (Option.some.inj h))⟩

private def graph (f : U → V) := univ.map (graphEmb f)

omit [DecidableEq U] in
private theorem graph_mem {f : U → V} {x y} : some (some (x,y))∈graph f ↔ f x=y := by
  constructor
  · intro h
    obtain ⟨z,_,he⟩ := mem_map.mp h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (Option.some.inj he))
    rfl
  · rintro rfl
    exact mem_map.mpr ⟨x,mem_univ _,rfl⟩

omit [Fintype U] in
private theorem graph_trace (S : Finset U) (f : U → V) : trace (S.map (graphEmb f))=S := by
  ext x
  constructor
  · intro h
    obtain ⟨y,hy⟩ := mem_trace.mp h
    obtain ⟨a,ha,he⟩ := mem_map.mp hy
    have hax : a=x := congrArg Prod.fst (Option.some.inj (Option.some.inj he))
    exact hax ▸ ha
  · intro h
    exact mem_trace.mpr ⟨f x,mem_map.mpr ⟨x,h,rfl⟩⟩

/-- A strength-three orthogonal array gives a unique covering graph for
every triple with three distinct finite projections. -/
def transversal {W : Type*} [Fintype V] (code : W → U → V)
    (interp : ∀ (S : Finset U), S.card=3 → Bijective (fun w : W => fun x : S => code w x.val)) :
    Template (Fintype.card U) .circle U V := by
  let blocks : Finset (Finset (Space U V)) := univ.filter (fun B => ∃ w, graph (code w)=B)
  have memB (B) : B∈blocks ↔ ∃ w, graph (code w)=B := by simp [blocks]
  refine ⟨blocks,?_,?_,?_⟩
  · intro B hB
    obtain ⟨w,rfl⟩ := (memB _).mp hB
    simp [graph]
  · intro B hB T hs hT
    obtain ⟨w,rfl⟩ := (memB _).mp hB
    change T⊆univ.map (graphEmb (code w)) at hs
    rw [map_eq_image] at hs
    obtain ⟨S,_,he⟩ := subset_image_iff.mp hs
    rw [← map_eq_image] at he
    subst T
    change (trace (S.map (graphEmb (code w)))).card=3
    simpa only [graph_trace,card_map] using hT
  · intro T hT hdistinct
    change (trace T).card=3 at hdistinct
    have chooseVal (x : trace T) := mem_trace.mp x.prop
    choose d hd using chooseVal
    let e : (trace T) ↪ Space U V := ⟨fun x => some (some (x.val,d x)),fun _ _ he =>
      Subtype.ext (congrArg Prod.fst (Option.some.inj (Option.some.inj he)))⟩
    have eqT : univ.map e=T := by
      apply eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨x,_,rfl⟩ := mem_map.mp hz
        exact hd x
      · simp [hT,hdistinct]
    have covers (w : W) : T⊆graph (code w) ↔ ∀ x : trace T, code w x.val=d x := by
      constructor
      · exact fun h x => graph_mem.mp (h (hd x))
      · intro h z hz
        obtain ⟨x,_,rfl⟩ := mem_map.mp (eqT.symm ▸ hz : z∈univ.map e)
        exact graph_mem.mpr (h x)
    obtain ⟨w,hw⟩ := (interp _ hdistinct).surjective d
    refine ⟨graph (code w),⟨(memB _).mpr ⟨w,rfl⟩,(covers _).mpr (congrFun hw)⟩,?_⟩
    rintro B ⟨hB,hs⟩
    obtain ⟨v,rfl⟩ := (memB _).mp hB
    have ev := (interp _ hdistinct).injective ((funext ((covers v).mp hs)).trans hw.symm)
    exact congrArg (fun i => graph (code i)) ev

def point_template (m : ℕ) : Template (m+2) .point (Fin 1) (Fin m) := by
  refine ⟨{univ},?_,?_,?_⟩
  · intro B hB
    obtain rfl := mem_singleton.mp hB
    simp [Space,Grid,Nat.add_assoc]
  · intro _ _ T _ ht
    have hp := (trace_bounds ht).1
    have hu := card_le_one_of_subsingleton (trace T)
    change (trace T).card=1
    omega
  · intro T _ _
    exact ⟨univ,⟨mem_singleton_self _,subset_univ _⟩,fun _ h => mem_singleton.mp h.1⟩

/-- The even-field array has q+2 groups of size q and two unused stems. -/
def hyperoval_template (F : Type*) [Field F] [DecidableEq F] [Fintype F] [CharP F 2] :
    Template (Fintype.card F+2) .circle (Fin (Fintype.card F+2)) (Fin (Fintype.card F)) := by
  let U := Option (Option F)
  have size : Fintype.card U=Fintype.card F+2 := by simp [U,Nat.add_assoc]
  let C := transversal (hyperWord (F:=F)) hyperoval_bijective
  let D := Template.relabel C (Fintype.equivFinOfCardEq size) (Fintype.equivFin F)
  exact size ▸ D

#print axioms transversal
#print axioms point_template
#print axioms hyperoval_template
end
end Erdos722.TwoStem
