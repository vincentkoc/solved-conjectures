import HosoyaLucasShiftIdentities

/-! Integer size estimates for an even Lucas window and its two ends. -/

namespace Arxiv.«2211.10788».ProgressionClosure

open CongruenceClosure

private lemma abs_fib (w : ℤ) : |Int.fib w| = (Nat.fib w.natAbs : ℤ) := by
  obtain ⟨n, rfl | rfl⟩ := w.eq_nat_or_neg
  · simp
  · simp [Int.fib_neg_natCast,abs_mul,abs_pow]

/-- Away from the ends of the centered window the signed value is at most half the modulus. -/
theorem interior_bound {w : ℤ} {h : ℕ} (hw : w.natAbs+6 ≤ h) :
    2*|signed w| ≤ (lucas h : ℤ) := by
  let k := h-4
  have he : h = k+4 := by dsimp [k]; omega
  have hw' : (w+2).natAbs ≤ k := by
    have := Int.natAbs_add_le w 2
    dsimp [k]; omega
  have h1 := Nat.fib_mono (show w.natAbs ≤ k by dsimp [k]; omega)
  have h2 := Nat.fib_mono hw'
  have hu : |signed w| ≤ 3*(Nat.fib k : ℤ) := by
    calc
      _ ≤ |2*Int.fib w| + |Int.fib (w+2)| := abs_add_le ..
      _ ≤ _ := by rw [abs_mul,abs_fib,abs_fib]; norm_num; omega
  rw [lucas_cast,he]
  have := Nat.fib_mono (show k ≤ k+1 by omega)
  have fibrec (a : ℕ) : (Nat.fib (a+2) : ℤ) = Nat.fib a+Nat.fib (a+1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  linarith [fibrec k,fibrec (k+1),fibrec (k+2),fibrec (k+3)]

/-- The offset correction is nonzero and bounded throughout the ends of the window. -/
private lemma end_correction {j : ℤ} (h₁ : -6 ≤ j) (h₂ : j ≤ 6) :
    0 < (2*signed (j+1)-signed j)^2 ∧ (2*signed (j+1)-signed j)^2 ≤ 10000 := by
  interval_cases j <;> decide +kernel

def threshold (y : ℤ) : ℕ := 20*y.natAbs^2+40000

/-- At either orientation of the window end a congruence would force a small positive multiple. -/
theorem end_excluded {h : ℕ} (he : Even h) {y j : ℤ} (hL : threshold y < lucas h)
    (h₁ : -6 ≤ j) (h₂ : j ≤ 6)
    (hit : (signed (j+h) : ZMod (lucas h))^2 = (y : ZMod (lucas h))^2) : False := by
  let v := 2*signed (j+1)-signed j
  have hh : 2*(signed (j+h) : ZMod (lucas h)) = (Nat.fib h : ZMod (lucas h))*v := by
    have := congrArg (fun n : ℤ => (n : ZMod (lucas h))) (half_shift j h)
    simpa [v] using this
  have hn : 5*(Nat.fib h : ZMod (lucas h))^2 = -4 := by
    have := congrArg (fun n : ℤ => (n : ZMod (lucas h))) (trace_norm he)
    simpa [neg_eq_iff_eq_neg] using congrArg Neg.neg (by simpa using this :
      -(5*(Nat.fib h : ZMod (lucas h))^2) = 4)
  have hz : ((4*(5*y^2+v^2) : ℤ) : ZMod (lucas h)) = 0 := by
    push_cast
    rw [←hit]
    calc
      _ = 5*(2*(signed (j+h) : ZMod (lucas h)))^2 + 4*(v : ZMod (lucas h))^2 := by ring
      _ = (5*(Nat.fib h : ZMod (lucas h))^2 + 4)*v^2 := by rw [hh]; ring
      _ = 0 := by rw [hn]; ring
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hz
  have hb := end_correction h₁ h₂
  change 0 < v^2 ∧ v^2 ≤ 10000 at hb
  have hsize : (20:ℤ)*y^2+40000 < lucas h := by
    have := (show ((threshold y : ℕ):ℤ) < lucas h by exact_mod_cast hL)
    simpa [threshold,Int.natCast_natAbs,sq_abs] using this
  have hp : 0 < 4*(5*y^2+v^2) := by nlinarith [sq_nonneg y]
  have hle := Int.le_of_dvd hp hd
  linarith

private lemma fib_growth (k : ℕ) : 2^k ≤ Nat.fib (2*k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ,show 2*(k+1)+1=2*k+1+2 by omega,Nat.fib_add_two]
    have := Nat.fib_mono (show 2*k+1 ≤ 2*k+1+1 by omega)
    omega

/-- Even window length with the required index divisibility and logarithmic candidate dependence. -/
def window (d : ℕ) (y : ℤ) : ℕ := 2*(d*((threshold y).log2+1))

theorem window_size {d : ℕ} (hd : 0 < d) (y : ℤ) : threshold y < lucas (window d y) := by
  let k := d*((threshold y).log2+1)
  have hlog : (threshold y).log2+1 ≤ k := by dsimp [k]; exact Nat.le_mul_of_pos_left _ hd
  have hpow : 2^((threshold y).log2+1) ≤ 2^k := Nat.pow_le_pow_right (by decide) hlog
  have hf := fib_growth k
  have := Nat.fib_mono (show 2*k ≤ 2*k+1 by omega)
  change threshold y < 2*Nat.fib (2*k+1)-Nat.fib (2*k)
  have hlt := Nat.lt_log2_self (n := threshold y)
  omega

#print axioms interior_bound
#print axioms end_excluded
#print axioms window_size

end Arxiv.«2211.10788».ProgressionClosure
