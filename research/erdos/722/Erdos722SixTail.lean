import Erdos722SixScales

/-!
# Covering a tail by multiplicative translates of an interval

For adjacent scales A and B, the d-fold products fill the entire interval
between its extreme dilates. Once that interval spans a factor of 31,
successive powers of 31 cover the tail.
-/

namespace Erdos722.Six

private def Fits (l h u : ℕ) := ∃ z, Scale z ∧ l*z≤u ∧ u≤h*z

private theorem tower {l h A B : ℕ} (hA : Scale A) (hB : Scale B) (hab : A ≤ B)
    (hover : l*B ≤ h*A) (d : ℕ) :
    ∀ z, Scale z → ∀ u, l*z*A^d ≤ u → u ≤ h*z*B^d → Fits l h u := by
  induction d with
  | zero =>
    intro z hz u hl hu
    exact ⟨z,hz,by simpa using hl,by simpa using hu⟩
  | succ d ih =>
    intro z hz u hl hu
    have mid : l*(z*B)*A^d ≤ h*(z*A)*B^d := calc
      _ = (l*B)*z*A^d := by ring
      _ ≤ (h*A)*z*B^d := by gcongr
      _ = _ := by ring
    by_cases hc : u≤h*(z*A)*B^d
    · apply ih (z*A) (scale_mul hz hA) u _ hc
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hl
    · apply ih (z*B) (scale_mul hz hB) u (by omega) _
      simpa only [pow_succ,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hu

private theorem ratio_growth {A B : ℕ} (hab : A<B) (d : ℕ) :
    (A+d)*A^d ≤ A*B^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs := Nat.mul_le_mul_right B ih
    have ht := Nat.mul_le_mul_left ((A+d)*A^d) (show A+1≤B from hab)
    rw [pow_succ,pow_succ]
    nlinarith only [hs,ht,Nat.zero_le (d*A^d)]

theorem scale_cover {l h : ℕ} (hl : 0<l) (hh : l<h) :
    ∃ N, ∀ u ≥ N, ∃ z, Scale z ∧ l*z ≤ u ∧ u ≤ h*z := by
  obtain ⟨A,B,hA,hB,hpos,hab,hnear⟩ := nearby_scales hl
  have hover := hnear.trans (Nat.mul_le_mul_right A hh)
  let d := 30*A
  have hwide : 31*A^d ≤ B^d := by
    apply (mul_le_mul_iff_right₀ hpos).mp
    have he : A+d=A*31 := by dsimp [d]; omega
    simpa only [he,Nat.mul_assoc] using ratio_growth hab d
  let L := l*A^d
  have hL : 0<L := Nat.mul_pos hl (pow_pos hpos _)
  refine ⟨L,?_⟩
  intro u hu
  have hq : 0<u/L := (Nat.div_pos hu hL)
  let e := Nat.log 31 (u/L)
  let z := 31^e
  have hlow : z*L ≤ u := (Nat.le_div_iff_mul_le hL).mp (Nat.pow_log_le_self _ hq.ne')
  have hup : u < (31*z)*L := (Nat.div_lt_iff_lt_mul hL).mp (by
    simpa only [z,e,pow_succ',Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by decide : 1<31) (u/L))
  have hz : Scale z := ⟨e,0,by simp [z]⟩
  apply tower hA hB hab.le hover d z hz u
  · simpa only [L,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hlow
  · exact hup.le.trans (calc
      (31*z)*L = l*z*(31*A^d) := by dsimp [L]; ring
      _ ≤ h*z*B^d := by gcongr)

#print axioms scale_cover
end Erdos722.Six
