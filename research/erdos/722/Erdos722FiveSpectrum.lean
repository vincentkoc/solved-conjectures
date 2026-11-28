import Erdos722FiveMaster
import Erdos722QuartetDeletion
import Erdos722HananiFour

/-!
# The eventual five-point spectrum for Erdős 722

Every admissible order at least 12801 has a pair design with five-point blocks.
The endpoint has the exact divisibility hypotheses and filter of the pinned
Erdős 722 statement at `r = 2` and `k = 5`.
-/

namespace Erdos722.Five
open Erdos722.Quartet Filter

theorem of_residues {n : ℕ} (hn : 12801 ≤ n) (h : n%20=1 ∨ n%20=5) :
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5 := by
  let u := (n-1)/4
  have hu : 3200 ≤ u := by dsimp [u]; omega
  have hr : u%5 ≤ 1 := by dsimp [u]; omega
  have he : 4*u+1=n := by dsimp [u]; omega
  have hd := inflate_uniform (by decide : 0<4) (master u hu hr).some seed_design
  rw [Fintype.card_fin,he] at hd
  exact hd.some.design

private theorem residues {n : ℕ} (hn : 0<n)
    (H : ∀ i < 2, (5-i).choose (2-i) ∣ (n-i).choose (2-i)) :
    n%20=1 ∨ n%20=5 := by
  have h0 : 10 ∣ n.choose 2 := by simpa [show Nat.choose 5 2=10 by decide] using H 0 (by decide)
  have h1 : 4 ∣ n-1 := by simpa using H 1 (by decide)
  rw [Nat.choose_two_right] at h0
  have h2 := n.even_mul_pred_self.two_dvd
  have h5 : 5 ∣ n*(n-1) := by omega
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h5 with h | h <;> omega

theorem spectrum_above {n : ℕ} (hn : 12801 ≤ n) :
    (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5) ↔ n%20=1 ∨ n%20=5 := by
  refine ⟨?_,of_residues hn⟩
  rintro ⟨H,hH⟩
  exact residues (by omega) (fun i hi => design_divisibility hH (by omega) (by omega))

theorem eventually_five : ∀ᶠ n : ℕ in atTop,
    (∀ i < 2, (5-i).choose (2-i) ∣ (n-i).choose (2-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 5 := by
  filter_upwards [eventually_ge_atTop 12801] with n hn h
  exact of_residues hn (residues (by omega) h)

#print axioms of_residues
#print axioms spectrum_above
#print axioms eventually_five

end Erdos722.Five
