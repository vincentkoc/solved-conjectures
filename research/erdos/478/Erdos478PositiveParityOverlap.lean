import Erdos478MixedParityTradeoff

/-! # Removing the zero index from the parity split -/

namespace Erdos478.ParityProducts
open Finset
open scoped Classical
noncomputable section

/-- Both parity sets now use the interval in the host statement. -/
def positiveValues (p b : ℕ) :=
  ((Ico 1 p).filter (fun i => i%2=b)).image (fun i => (i.factorial : ZMod p))

theorem positive_subset (p b : ℕ) : positiveValues p b ⊆ parityValues p b := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  have h := mem_filter.mp hi
  exact mem_parity.mpr ⟨i,(mem_Ico.mp h.1).2,h.2,rfl⟩

theorem positive_odd (p : ℕ) : positiveValues p 1=parityValues p 1 := by
  apply Subset.antisymm (positive_subset ..)
  intro x hx
  obtain ⟨i,hi,ho,rfl⟩ := mem_parity.mp hx
  exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,hi⟩,ho⟩,rfl⟩

theorem positive_even (p : ℕ) (hp : 0<p) : parityValues p 0=insert 1 (positiveValues p 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,he,rfl⟩ := mem_parity.mp hx
    cases i with
    | zero => simp
    | succ i => exact mem_insert_of_mem (mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,hi⟩,he⟩,rfl⟩)
  · intro hx
    rcases mem_insert.mp hx with rfl|h
    · exact mem_parity.mpr ⟨0,hp,rfl,by simp⟩
    · exact positive_subset _ _ h

/-- The number of distinct residues attained at both positive parities
differs from the extended overlap only at the residue one. -/
theorem positive_overlap {p : ℕ} [Fact p.Prime] :
    commonValues p=insert 1 (positiveValues p 0 ∩ positiveValues p 1) := by
  have hp := (Fact.out : p.Prime).two_le
  have one : (1:ZMod p)∈parityValues p 1 := mem_parity.mpr ⟨1,by omega,rfl,by simp⟩
  ext x
  rw [commonValues,positive_even p (by omega),positive_odd]
  simp only [mem_inter,mem_insert]
  grind

#print axioms positiveValues
#print axioms positive_subset
#print axioms positive_odd
#print axioms positive_even
#print axioms positive_overlap
end
end Erdos478.ParityProducts
