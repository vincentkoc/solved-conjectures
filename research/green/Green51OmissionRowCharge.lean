import Green51DefectGrowthBounds
import Mathlib.Data.Nat.Log

/-! # A dyadic tail bound from the occupied-row encoding -/
namespace Green51FrameIsomorphisms

private theorem exponent_budget {h m b L : ℕ} (large : 10 ≤ h) (split : m+b=h)
    (many : 64*(L+1) ≤ b) :
    L + b*h/8 + (h+L*m+(L+(m*m/4+m))) + (L*h+(h+h/2)) ≤  h*h/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have trunc : 4*(m*m/4) ≤ m*m := by omega
  have trunc' : 8*(b*h/8) ≤ b*h := by omega
  have hh : 2*(h/2) ≤ h := by omega
  have m_le : m ≤ h := by omega
  have a := Nat.mul_le_mul_left L m_le
  have c : L ≤ L*h := by simpa using Nat.mul_le_mul_left L (show 1 ≤ h by omega)
  have enough := Nat.mul_le_mul_right h many
  have geom : m*m+b*h ≤ h*h := by
    rw [←split]
    nlinarith only [Nat.zero_le (m*b)]
  nlinarith only [a,c,enough,geom,trunc,trunc',hh,m_le]

theorem dyadic_row_charge {h b T : ℕ} (large : 10 ≤ h) (limit : b ≤ h)
    (many : 64*(Nat.log 2 h+2) ≤ b)
    (cnt : T ≤ 2^h*h^(h-b)*((h-b+1)*2^((h-b)*(h-b)/4+(h-b)))) :
    (h+1)*2^(b*h/8)*T ≤ universalDefectNumber h := by
  let m := h-b
  let L := Nat.log 2 h+1
  have hl : h+1 ≤ 2^L := Nat.lt_pow_succ_log_self (by decide) h
  have ml : m+1 ≤ 2^L := (Nat.add_le_add_right (Nat.sub_le h b) 1).trans hl
  have pw (j : ℕ) : h^j ≤ 2^(L*j) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.le_succ h).trans hl) _
  have room := exponent_budget (m := m) large (Nat.sub_add_cancel limit)
    (show 64*(L+1) ≤ b from many)
  have tail := lower_growth large
  let loss := h^h*2^(h+h/2)
  have pos : 0<loss := by dsimp [loss];positivity
  apply Nat.le_of_mul_le_mul_right _ pos
  calc
    (h+1)*2^(b*h/8)*T*loss ≤
      2^L*2^(b*h/8)*(2^h*2^(L*m)*(2^L*2^(m*m/4+m)))*(2^(L*h)*2^(h+h/2)) := by
        dsimp only [loss]
        apply Nat.mul_le_mul _ (Nat.mul_le_mul_right _ (pw h))
        apply Nat.mul_le_mul (Nat.mul_le_mul_right _ hl)
        exact cnt.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ (pw m)) (Nat.mul_le_mul_right _ ml))
    _ = 2^(L+b*h/8+(h+L*m+(L+(m*m/4+m)))+(L*h+(h+h/2))) := by simp only [pow_add]
    _ ≤  2^(h*h/4) := Nat.pow_le_pow_right (by decide) room
    _ ≤  universalDefectNumber h * loss := by simpa [loss,Nat.mul_assoc] using tail

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.dyadic_row_charge
