import Erdos722SixHeights

/-!
# Intervals of admissible group counts

Using the two neighboring heights independently makes each translation
available with an additional displacement of either zero or the number of
full columns. The displacements 30 and 39 span all sufficiently large
multiples of three inside a finite rectangle of coefficients.
-/

namespace Erdos722.Six
open Erdos722.Quartet

private theorem fan {s : ℕ} (hs : Local s) (hs' : Local (s+1)) (hk : s ≤ 39)
    (h₃ : 3 ∣ s) (B n : ℕ) :
    ∃ C, 3 ∣ C ∧ ∀ i ≤ n, ∀ x ≤ B, Local x → Local (C+s*i+x) := by
  induction n with
  | zero => exact ⟨0,dvd_zero _,by simp_all⟩
  | succ n ih =>
    obtain ⟨C,hC,h⟩ := ih
    obtain ⟨T,hT,⟨h₀,D₀⟩,⟨h₁,D₁⟩⟩ := adjacent_heights (C+s*n+B)
    refine ⟨s*T+C,dvd_add (dvd_mul_of_dvd_left h₃ _) hC,?_⟩
    intro i hi x hx hL
    by_cases hin : i ≤ n
    · have hr : C+s*i+x ≤ T :=
        le_trans (by gcongr) hT
      have hg := grow (restrict D₀.some hk) hs hs' hr (show 0≤1 by decide)
        (by simpa using h₀) (by simpa using h i hin x hx hL)
      simpa only [Nat.add_zero,Nat.add_assoc] using hg
    · have hi' : i=n+1 := by omega
      subst i
      have hr : C+s*n+x ≤ T+1 := by omega
      have hg := grow (restrict D₁.some hk) hs hs' hr (show 0≤1 by decide)
        (by simpa using h₁) (by simpa using h n le_rfl x hx hL)
      convert hg using 1
      ring

private theorem initial (z : ℕ) (hz : z≤1) : Local z := by
  rcases (by omega : z=0 ∨ z=1) with rfl | rfl
  · change Has (· = 6) 1
    exact ⟨Cover.empty (fun x y hxy _ => hxy (Subsingleton.elim x y))⟩
  · exact Has.single rfl

/-- A long interval with every admissible order, arbitrarily far from zero. -/
theorem seed_interval (h₃₉ : Local 39) (h₄₀ : Local 40) (W : ℕ) :
    ∃ L ≥ W, ∀ u, L ≤ u → u ≤ L+W → u%3 ≤ 1 → Local u := by
  let n := W+117
  obtain ⟨C,hC,h₁⟩ := fan local_thirty local_thirty_one (by decide) (by decide) 1 n
  obtain ⟨E,hE,h₂⟩ := fan h₃₉ h₄₀ (by decide) (by decide) (C+30*n+1) 9
  refine ⟨E+C+3*n,by dsimp [n]; omega,?_⟩
  intro u hlu hhu hu
  let m := (u-(E+C))/3
  let z := (u-(E+C))%3
  have hz : z≤1 := by obtain ⟨a,ha⟩ := hC; obtain ⟨b,hb⟩ := hE; dsimp [z]; omega
  have hm : 117≤m ∧ m≤10*n := by dsimp [m,n] at *; omega
  let j := (7*m)%10
  let i := (m-13*j)/10
  have hj : j≤9 := by dsimp [j]; omega
  have hrep : 10*i+13*j=m := by
    have hm' : 13*j≤m := by omega
    dsimp [i,j] at *
    omega
  have hi : i≤n := by omega
  have hl := h₁ i hi z hz (initial z hz)
  have hx : C+30*i+z≤C+30*n+1 := by omega
  have hm' := h₂ j hj _ hx hl
  convert hm' using 1
  dsimp [m,z] at *
  omega

#print axioms seed_interval
end Erdos722.Six
