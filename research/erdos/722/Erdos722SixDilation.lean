import Erdos722SixIntervals

/-!
# Dilating intervals of six-block designs

A buffer at each end absorbs the error from rounding the common column
height to one less than a multiple of 39!. Both inner endpoints may then
be multiplied by 31 or by 40.
-/

namespace Erdos722.Six

private def pad := 100*modulus

def Full (l h : ℕ) := 2*pad ≤ l ∧
  ∀ u, l ≤ u+pad → u ≤ h+pad → u%3 ≤ 1 → Local u

theorem starting_interval (h₃₉ : Local 39) (h₄₀ : Local 40) :
    ∃ l h, 0<l ∧ l<h ∧ Full l h := by
  obtain ⟨L,hL,h⟩ := seed_interval h₃₉ h₄₀ (3*pad+1)
  refine ⟨L+pad,L+pad+1,by omega,by omega,by omega,?_⟩
  intro u h₁ h₂ h₃
  exact h u (by omega) (by omega) h₃

private theorem rounded (s u : ℕ) :
    ∃ b, modulus ∣ b ∧ u/(s+1)+2 ≤ b ∧ b ≤ u/(s+1)+2+modulus := by
  let q := u/(s+1)+2
  refine ⟨modulus*(q/modulus+1),dvd_mul_right ..,?_⟩
  have h := Nat.mod_add_div q modulus
  have h' := Nat.mod_lt q modulus_pos
  rw [Nat.mul_add,Nat.mul_one]
  change q ≤ _ ∧ _ ≤ q+modulus
  omega

theorem dilate {s l h : ℕ} (hs : s=30 ∨ s=39) (h₀ : Local s) (h₁ : Local (s+1))
    (H : Full l h) : Full ((s+1)*l) ((s+1)*h) := by
  obtain ⟨hl,H⟩ := H
  refine ⟨by rcases hs with rfl|rfl <;> omega,?_⟩
  intro u hu hu' ha
  obtain ⟨b,hb,hb₁,hb₂⟩ := rounded s u
  let t := b-1
  let r := u-s*t-1
  have hM := modulus_pos
  have hbpos : 2≤b := (Nat.le_add_left ..).trans hb₁
  have ht : t+1=b := by dsimp [t]; omega
  have hd := modular_predecessor hbpos hb
  have hrange : r≤t ∧ s*t+r+1=u ∧ l≤b+pad ∧ b≤h+pad ∧ l≤r+1+pad ∧ r+1≤h+pad := by
    dsimp [r,t,pad] at *
    rcases hs with rfl|rfl <;> omega
  obtain ⟨hrt,he,hbl,hbh,hrl,hrh⟩ := hrange
  have hb₃ := three_dvd_modulus.trans hb
  have hba : b%3≤1 := by omega
  have hra : (r+1)%3≤1 := by rcases hs with rfl|rfl <;> omega
  rw [← he]
  apply grow (restrict hd.some (show s≤39 by omega)) h₀ h₁ hrt (by decide)
  · exact ht ▸ H b hbl hbh hba
  · exact H (r+1) hrl hrh hra

#print axioms starting_interval
#print axioms dilate
end Erdos722.Six
