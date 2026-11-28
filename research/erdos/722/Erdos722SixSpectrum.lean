import Erdos722SixDilation
import Erdos722SixMixedSeeds
import Erdos722SixTail

/-!
# The eventual spectrum for pair designs with blocks of size six

Every sufficiently large admissible order supports a Steiner pair design
with blocks of size six. This is the pair (2,6) of the pinned Erdős 722
statement, with no restriction on the factorization of the order.
-/

namespace Erdos722.Six
open Erdos722.Quartet Filter

private theorem iterate {c : ℕ} (step : ∀ {l h}, Full l h → Full (c*l) (c*h))
    {l h : ℕ} (H : Full l h) (d : ℕ) : Full (c^d*l) (c^d*h) := by
  induction d with
  | zero => simpa using H
  | succ d ih => simpa only [pow_succ',Nat.mul_assoc] using step ih

theorem eventual_group_counts : ∃ N, ∀ u ≥ N, u%3≤1 → Local u := by
  obtain ⟨l,h,hl,hh,H⟩ := starting_interval local_thirty_nine local_forty
  obtain ⟨N,hN⟩ := scale_cover hl hh
  refine ⟨N,?_⟩
  intro u hu ha
  obtain ⟨z,⟨i,j,rfl⟩,hlo,hhi⟩ := hN u hu
  have H₄₀ := iterate (dilate (Or.inr rfl) local_thirty_nine local_forty) H j
  have H₃₁ := iterate (dilate (Or.inl rfl) local_thirty local_thirty_one) H₄₀ i
  have H' : Full (l*(31^i*40^j)) (h*(31^i*40^j)) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using H₃₁
  exact H'.2 u (by omega) (by omega) ha

private theorem residues {n : ℕ} (hn : 0<n)
    (H : ∀ i < 2, (6-i).choose (2-i) ∣ (n-i).choose (2-i)) :
    n%30=1 ∨ n%30=6 ∨ n%30=16 ∨ n%30=21 := by
  have h₀ : 15 ∣ n.choose 2 := by simpa [show Nat.choose 6 2=15 by decide] using H 0 (by decide)
  have h₁ : 5 ∣ n-1 := by simpa using H 1 (by decide)
  rw [Nat.choose_two_right] at h₀
  have he := n.even_mul_pred_self.two_dvd
  have hd : 3 ∣ n*(n-1) := by omega
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 3)).mp hd with h | h <;> omega

theorem eventual_spectrum : ∀ᶠ n : ℕ in atTop,
    (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 6) ↔
      n%30=1 ∨ n%30=6 ∨ n%30=16 ∨ n%30=21 := by
  obtain ⟨N,hN⟩ := eventual_group_counts
  filter_upwards [eventually_ge_atTop (5*N+1)] with n hn
  constructor
  · rintro ⟨H,hH⟩
    exact residues (by omega) (fun i hi => design_divisibility hH (by omega) (by omega))
  · intro ha
    let u := (n-1)/5
    have he : 5*u+1=n := by dsimp [u]; omega
    have H := hN u (by dsimp [u]; omega) (by dsimp [u]; omega)
    have hd := H.some.design
    rwa [he] at hd

theorem eventually_six : ∀ᶠ n : ℕ in atTop,
    (∀ i < 2, (6-i).choose (2-i) ∣ (n-i).choose (2-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 6 := by
  filter_upwards [eventual_spectrum,eventually_ge_atTop 1] with n hn hpos h
  exact hn.mpr (residues hpos h)

#print axioms eventual_group_counts
#print axioms eventual_spectrum
#print axioms eventually_six
end Erdos722.Six
