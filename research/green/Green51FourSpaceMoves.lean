import Green51FourSpaceCoordinates

/-! # Normalizing a minimum word in the four-cube -/
open Finset Green50Downsets Green50Sharp
namespace Green51FourSpace.Moves
local notation "F" => ZMod 2

def moves : Array (Array Nat) := #[#[3,0,1,2,7,4,5,6,11,8,9,10,15,12,13,14],
  #[0,3,1,2,4,7,5,6,8,11,9,10,12,15,13,14],
  #[8,9,2,3,12,13,6,7,0,1,10,11,4,5,14,15],
  #[4,5,6,7,0,1,2,3,8,9,10,11,12,13,14,15],
  #[0,1,10,11,4,5,14,15,2,3,8,9,6,7,12,13],
  #[1,0,3,2,4,5,6,7,9,8,11,10,12,13,14,15],
  #[1,0,3,2,5,4,7,6,8,9,10,11,12,13,14,15],
  #[0,5,2,7,1,4,3,6,8,13,10,15,9,12,11,14],
  #[2,3,0,1,4,5,6,7,10,11,8,9,12,13,14,15],
  #[0,1,2,3,12,13,14,15,4,5,6,7,8,9,10,11],
  #[1,0,2,3,4,5,7,6,9,8,10,11,12,13,15,14],
  #[2,3,0,1,4,5,6,7,8,9,10,11,14,15,12,13]]
def step (k:Fin 12) (i:Fin 16) : Fin 16 := Fin.ofNat 16 ((moves[k.val]!)[i.val]!)
theorem bijections (k:Fin 12) : Function.Bijective (step k) := by
  have h : ∀k:Fin 12,Function.Injective (step k) := by decide +kernel
  exact (Finite.injective_iff_bijective.mp (h k))
noncomputable def perm (k:Fin 12) : Fin 16 ≃ Fin 16 := Equiv.ofBijective _ (bijections k)
def tag (s:Finset (Fin 16)) := ∑ i∈s,2^i.val

set_option maxHeartbeats 0 in
theorem preserved : ∀ k:Fin 12,∀ p∈Certificate.planes,∃ q∈Certificate.planes,
    (positions p).image (step k)=positions q := by
  intro k
  fin_cases k <;> decide +kernel

-- Use the 28 six-subsets of the given plane, rather than all subsets of the cube.
attribute [local instance 2500] Finset.decidableDforallFinset
set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem descent_table : ∀ p∈Certificate.planes,∀ s∈(positions p).powersetCard 6,
    s=positions 63 ∨ ∃ k:Fin 12,tag (s.image (step k))<tag s := by
  have rows : ∀ j:Fin 30,∀ s∈(positions Certificate.planes[j.val]!).powersetCard 6,
      s=positions 63 ∨ ∃ k:Fin 12,tag (s.image (step k))<tag s := by
    intro j
    fin_cases j <;> decide +kernel
  intro p hp
  obtain ⟨j,hj,rfl⟩:=List.getElem_of_mem hp
  have hh : j<30 := hj
  have row:=rows ⟨j,hh⟩
  change ∀s∈(positions Certificate.planes[j]!).powersetCard 6, _ at row
  rwa [getElem!_pos Certificate.planes j hj] at row

end Green51FourSpace.Moves
#print axioms Green51FourSpace.Moves.descent_table
