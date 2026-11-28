import Green51PermutedCoordinates
import Green51PairedTypes

/-! # Compact binary coordinates for the paired and unpaired graphs -/

open Finset Green50Downsets Green51QuadraticFlats Green51PairedTypes
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2

variable {n:ℕ}
abbrev PackedSpace (n:ℕ) := Packed n × V n
def packedLabels (f:Cube n→Cube n) (b:Cube n→V n) : Finset (PackedSpace n) :=
  univ.image (fun x=>(pack x,b x)) ∪ univ.image (fun x=>(pack x,b x+delta f x))

theorem paired_copy (f:Cube n→Cube n) (b:Cube n→V n) :
    AffineCopy (packedLabels f b) (labels f b) := by
  let j := (expand n).prodMap (LinearMap.id (R:=F) (M:=V n))
  have inj:Function.Injective j := by
    intro x y e
    exact Prod.ext (expand_inj n (congrArg Prod.fst e)) (congrArg (fun z:E n=>z.2) e)
  refine ⟨j,(quad 0,0),inj,?_⟩
  rw [packedLabels,labels,image_union,image_image,image_image]
  congr 1
  · apply image_congr;rintro x _
    change (quad 0+expand n (pack x),0+b x)=(quad x,b x)
    rw [expand_pack,zero_add]
  · apply image_congr;rintro x _
    change (quad 0+expand n (pack x),0+(b x+delta f x))=(quad x,b x+delta f x)
    rw [expand_pack,zero_add]

def packedGraph (n:ℕ) : Finset (Packed n) := univ.image pack

theorem quadratic_copy (n:ℕ) : AffineCopy (packedGraph n) (graph n) := by
  refine ⟨expand n,quad 0,expand_inj n,?_⟩
  rw [packedGraph,graph,image_image]
  exact image_congr fun x _=>expand_pack x

variable {U T:Type*} [AddCommGroup U] [Module F U] [DecidableEq U]
  [AddCommGroup T] [Module F T] [DecidableEq T]
theorem avoids_of_copy {A:Finset U} {B:Finset T} (h:AffineCopy A B)
    (avoid:¬∃ W:Submodule F T,Module.finrank F W=3 ∧ ∀ w∈W,w∈B+B) :
    ¬∃ W:Submodule F U,Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  obtain ⟨j,c,inj,rfl⟩:=h
  rintro ⟨W,rank,inc⟩
  refine avoid ⟨W.map j,(W.equivMapOfInjective j inj).finrank_eq.symm.trans rank,?_⟩
  rintro _ ⟨w,hw,rfl⟩
  obtain ⟨x,hx,y,hy,rfl⟩:=mem_add.mp (inc w hw)
  apply mem_add.mpr
  exact ⟨_,mem_image_of_mem _ hx,_,mem_image_of_mem _ hy,by
    rw [add_add_add_comm,ZModModule.add_self,zero_add,map_add]⟩

omit [DecidableEq U] in
theorem copy_card {A:Finset U} {B:Finset T} (h:AffineCopy A B) : A.card=B.card := by
  obtain ⟨j,c,inj,rfl⟩:=h
  exact (card_image_of_injective _ (fun _ _ e=>inj (add_left_cancel e))).symm

end Green51PermutedPairs

#print axioms Green51PermutedPairs.paired_copy
#print axioms Green51PermutedPairs.quadratic_copy
#print axioms Green51PermutedPairs.avoids_of_copy
