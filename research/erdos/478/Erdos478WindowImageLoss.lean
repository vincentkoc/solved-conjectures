import Erdos478WindowOccupancies

/-! # Finite bounds for image loss in a typical positive factorial window -/

namespace Erdos478.WindowAverage
open Finset LocalSpacing
open scoped Classical
noncomputable section

def loss (p a H : ℕ) := H+1-(windowValues p a H).card

theorem loss_le_energy (p a H : ℕ) : loss p a H≤pairEnergy p a H := by
  have h := multiplicity_bound p a H 1
  simp only [one_mul,show (1+1).choose 2=1 by decide] at h
  unfold loss
  omega

def exceptionalStarts (p H D : ℕ) := (starts p H).filter fun a => D≤loss p a H

theorem exceptional_starts_bound {p : ℕ} (prime : p.Prime) (H D : ℕ) :
    (exceptionalStarts p H D).card*D+H≤(H+2).choose 3 := by
  apply le_trans _ (total_energy_bound prime H)
  apply Nat.add_le_add_right
  calc
    _ = ∑ _a ∈ exceptionalStarts p H D,D := by simp
    _ ≤ ∑ a ∈ exceptionalStarts p H D,pairEnergy p a H :=
      sum_le_sum fun a ha => ((mem_filter.mp ha).2).trans (loss_le_energy p a H)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)

/-- The full family of linear bounds controls the mean number of distinct
residues even when the mean number of colliding pairs exceeds a window length. -/
theorem total_image_lower {p : ℕ} (prime : p.Prime) (H m : ℕ) :
    (p-1-H)*(m*(H+1))+H ≤ (m+1).choose 2*(∑ a ∈ starts p H,(windowValues p a H).card)+(H+2).choose 3 := by
  have h := sum_le_sum (s:=starts p H) fun a _ => multiplicity_bound p a H m
  rw [sum_add_distrib] at h
  simp only [sum_const,smul_eq_mul,starts_card] at h
  rw [← mul_sum] at h
  calc
    _ ≤ ((m+1).choose 2*(∑ a ∈ starts p H,(windowValues p a H).card)+(∑ a ∈ starts p H,pairEnergy p a H))+H := Nat.add_le_add_right h H
    _ ≤ _ := by rw [add_assoc]; exact Nat.add_le_add_left (total_energy_bound prime H) _

#print axioms loss
#print axioms loss_le_energy
#print axioms exceptionalStarts
#print axioms exceptional_starts_bound
#print axioms total_image_lower
end
end Erdos478.WindowAverage
