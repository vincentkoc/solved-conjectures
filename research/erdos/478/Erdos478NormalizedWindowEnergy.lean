import Erdos478WindowImageLoss

/-! # Normalized collision and image inequalities at the cube-root and square-root scales -/

namespace Erdos478.WindowAverage
open Finset LocalSpacing
open scoped Classical
noncomputable section

theorem six_choose_three (H : ℕ) : 6*(H+2).choose 3=H*(H+1)*(H+2) := by
  have h := (Nat.descFactorial_eq_factorial_mul_choose (H+2) 3).symm
  simpa [Nat.descFactorial_succ,Nat.factorial,Nat.mul_assoc] using h

def exceptionalFraction (p H D : ℕ) : ℝ :=
  ((exceptionalStarts p H D).card:ℝ)/(starts p H).card

def meanImageFraction (p H : ℕ) : ℝ :=
  (∑ a ∈ starts p H,((windowValues p a H).card:ℝ))/(((starts p H).card:ℝ)*(H+1))

theorem normalized_exception {p : ℕ} (hp : p.Prime) (H D : ℕ) :
    6*((exceptionalStarts p H D).card:ℝ)*D+6*H≤(H:ℝ)*(H+1)*(H+2) := by
  have nat := Nat.mul_le_mul_left 6 (exceptional_starts_bound hp H D)
  rw [six_choose_three,Nat.mul_add] at nat
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_assoc] using
    (show ((6*((exceptionalStarts p H D).card*D)+6*H:ℕ):ℝ)≤((H*(H+1)*(H+2):ℕ):ℝ) by exact_mod_cast nat)

theorem relative_loss_bound {p H : ℕ} (hp : p.Prime) (ε : ℝ) :
    6*ε*((exceptionalStarts p H ⌈ε*(H+1)⌉₊).card:ℝ)≤(H:ℝ)*(H+2) := by
  let D := ⌈ε*(H+1)⌉₊
  let B : ℝ := (exceptionalStarts p H D).card
  have raw := normalized_exception hp H D
  have mul : 6*B*(ε*(H+1))≤6*B*D :=
    mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by dsimp [B]; positivity)
  have cancel : (6*ε*B)*((H:ℝ)+1)≤((H:ℝ)*(H+2))*(H+1) := by
    change 6*B*D+6*H≤_ at raw
    nlinarith only [mul,raw,show (0:ℝ)≤H by positivity]
  exact le_of_mul_le_mul_right cancel (by positivity)

theorem meanImage_nonneg (p H : ℕ) : 0≤meanImageFraction p H := by unfold meanImageFraction; positivity

theorem meanImage_le_one (p H : ℕ) : meanImageFraction p H≤1 := by
  have bound (a : ℕ) : (windowValues p a H).card≤H+1 := by
    have size : (Icc a (a+H)).card=H+1 := by rw [Nat.card_Icc]; omega
    exact card_image_le.trans size.le
  have lim := sum_le_sum (s:=starts p H) fun a _ => bound a
  simp only [sum_const,smul_eq_mul] at lim
  unfold meanImageFraction
  apply div_le_one_of_le₀ _ (by positivity)
  exact_mod_cast lim

/-- For every slope the relative mean image plus its explicit error bounds the slope from below. -/
theorem normalized_image_lower {p H : ℕ} (hp : p.Prime) (fits : H+1<p) (m : ℕ) :
    (m:ℝ) ≤ ((m+1).choose 2:ℕ)*meanImageFraction p H+((H:ℝ)*(H+2))/(6*(starts p H).card) := by
  let S : ℝ := (starts p H).card
  let T : ℝ := ∑ a ∈ starts p H, ((windowValues p a H).card:ℝ)
  have pos : 0<S := by dsimp [S]; rw [starts_card]; exact_mod_cast (show 0<p-1-H by omega)
  have nat := Nat.mul_le_mul_left 6 (total_image_lower hp H m)
  rw [← starts_card,Nat.mul_add 6 ((m+1).choose 2 * _),six_choose_three] at nat
  have real : 6*(S*((m:ℝ)*(H+1))+H) ≤
      6*(((m+1).choose 2:ℕ)*T)+(H:ℝ)*(H+1)*(H+2) := by
    dsimp [S,T]
    exact_mod_cast nat
  change (m:ℝ)≤_*(T/(S*(H+1)))+((H:ℝ)*(H+2))/(6*S)
  have hp1 : 0<(H:ℝ)+1 := by positivity
  field_simp
  nlinarith only [real,show (0:ℝ)≤H by positivity]

#print axioms six_choose_three
#print axioms exceptionalFraction
#print axioms meanImageFraction
#print axioms normalized_exception
#print axioms relative_loss_bound
#print axioms meanImage_nonneg
#print axioms meanImage_le_one
#print axioms normalized_image_lower
end
end Erdos478.WindowAverage
