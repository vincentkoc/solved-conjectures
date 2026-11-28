import Green51StructureCounts
import Green51PermutedCounts

/-! # Five inequivalent extremal sets in dimension fifteen -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}


open Green51PairedTypes Green51WitnessIncidence

/-- Transfer a flat count to the compact binary space of dimension (n+2 choose 2). -/
theorem exists_witness_of_count (large:4≤n) (f:Cube n ≃ Cube n) :
    ∃ A:Finset (Cube ((n+2).choose 2)),
      WitnessWithCount n (1+(directions f).card+(extraDirections f).card) A := by
  classical
  have profile : WitnessWithCount n _ (labels f 0) :=
    ⟨labels_card _ _,avoids_linear f f.injective _,count_formula large f⟩
  let e : Cube ((n+2).choose 2) ≃ₗ[F] PackedSpace n :=
    LinearEquiv.ofFinrankEq _ _ (by rw [paired_dimension];simp [Cube])
  exact ⟨_,witness_of_copy (copy_in_equiv e _) (witness_of_copy (paired_copy f 0) profile)⟩

/-- Four binary coordinates, with coordinate zero as the low bit. -/
private def word (x:Cube 4) : Nat := (x 0).val+2*(x 1).val+4*(x 2).val+8*(x 3).val
private def vector (a:Nat) : Cube 4 := fun i=>if a.testBit i.val then 1 else 0

/-- Inversions in the binary fields of orders 16 and 8, two triangular maps, and identity. -/
private def samples (j:Fin 5) (x:Cube 4) : Cube 4 :=
  let a := word x
  match j.val with
  | 0 => vector ([0,1,9,14,13,11,7,6,15,2,12,5,10,4,3,8]:List Nat)[a]!
  | 1 => vector ([0,1,5,6,7,2,3,4,8,9,13,14,15,10,11,12]:List Nat)[a]!
  | 2 => vector (if a%8=7 then a^^^8 else a)
  | 3 => vector (if a%4=3 then a^^^8 else a)
  | _ => x

private theorem samples_involutive : ∀ j:Fin 5, ∀x:Cube 4,samples j (samples j x)=x := by
  decide +kernel
private def sampleEquiv (j:Fin 5) : Cube 4 ≃ Cube 4 :=
  ⟨samples j,samples j,samples_involutive j,samples_involutive j⟩

private def exampleCount (j:Fin 5) : Nat := [1,2,3,5,31][j.val]!

private theorem sample_counts : ∀j:Fin 5, 1+(directions (samples j)).card+
    (extraDirections (samples j)).card=exampleCount j := by
  decide +kernel

private theorem sample_index {c:ℕ} (hc:c∈([1,2,3,5,31]:List ℕ)) : ∃ j:Fin 5,c=exampleCount j := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩

/-- Exactly these counts occur among all permutations on four binary coordinates. -/
theorem permutation_spectrum (c:ℕ) :
    (∃ f:Cube 4 ≃ Cube 4,(familyAt 4 (labels f 0)).ncard=c) ↔ c∈([1,2,3,5,31]:List ℕ) := by
  constructor
  · rintro ⟨f,rfl⟩;exact four_dimensional_counts f
  · intro hc
    obtain ⟨j,rfl⟩:=sample_index hc
    exact ⟨sampleEquiv j,(count_formula (by decide) _).trans (sample_counts j)⟩

/-- All five counts occur for 32 labels in dimension 15, with maximum coset dimension four. -/
theorem five_flat_counts (c:ℕ) (hc:c∈([1,2,3,5,31]:List ℕ)) :
    ∃ A:Finset (Cube 15),WitnessWithCount 4 c A ∧ maxCosetDim F (Cube 15) ↑(A+A)=4 := by
  obtain ⟨j,rfl⟩:=sample_index hc
  obtain ⟨A,h⟩:=exists_witness_of_count (n:=4) (by decide) (sampleEquiv j)
  rw [show 1+(directions (sampleEquiv j)).card+(extraDirections (sampleEquiv j)).card=exampleCount j
    from sample_counts j] at h
  refine ⟨A,h,max_coset_dimension A (by decide) ?_ h⟩
  exact (show ∀ j:Fin 5,0<exampleCount j from by decide) j


end Green51PermutedPairs

#print axioms Green51PermutedPairs.exists_witness_of_count
#print axioms Green51PermutedPairs.five_flat_counts
#print axioms Green51PermutedPairs.permutation_spectrum
