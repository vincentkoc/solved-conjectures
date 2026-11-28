import HosoyaLucasWindowBounds

/-! Lifting a modular hit to an integer hit in its original index class. -/

namespace Arxiv.«2211.10788».ProgressionClosure

open CongruenceClosure

private lemma shift_sign (w : ℤ) {h : ℕ} (he : Even h) (q : ℕ) :
    (signed (w+2*h*q) : ZMod (lucas h)) = signed w ∨
    (signed (w+2*h*q) : ZMod (lucas h)) = -(signed w : ZMod (lucas h)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show w+2*h*(q.succ:ℤ) = (w+2*h*q)+2*h by push_cast; ring, lucas_antiperiod _ he]
    rcases ih with hi | hi <;> simp [hi]

private lemma lift_close {L : ℕ} {x y : ℤ} (hx : 2*|x| ≤ (L:ℤ))
    (hy : 2*|y| < (L:ℤ)) (he : (x : ZMod L) = y) : x = y := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp he
  have hb := abs_sub_le y 0 x
  simp only [sub_zero,zero_sub,abs_neg] at hb
  have := Int.eq_zero_of_abs_lt_dvd hd (show |y-x| < (L:ℤ) by linarith)
  omega

private lemma negative_impossible {w n y : ℤ}
    (h11 : (signed n : ZMod 11) = y) (h : -signed w = y) : False := by
  have e : (signed n : ZMod 11) = -(signed w : ZMod 11) := by rw [h11,←h]; simp
  have bad := congrArg (fun a : ZMod 11 => a^5) e
  simp only [signed_fifth,Odd.neg_pow (by decide : Odd 5)] at bad
  exact (by decide : (1 : ZMod 11) ≠ -1) bad

/-- A hit at the two moduli lifts, preserving the index modulo twice the even window length. -/
theorem lift_at_lucas {h n : ℕ} (hp : 0 < h) (he : Even h) {y : ℤ}
    (hL : threshold y < lucas h)
    (h11 : (signed (n:ℤ) : ZMod 11) = y)
    (hit : (signed (n:ℤ) : ZMod (lucas h)) = y) :
    ∃ w q : ℤ, (n:ℤ) = w+2*h*q ∧ w.natAbs ≤ h ∧ signed w = y := by
  let q := (n+h)/(2*h)
  let a := (n+h)%(2*h)
  let w := (a:ℤ)-h
  have ha : a < 2*h := Nat.mod_lt _ (by omega)
  have hf : a+2*h*q = n+h := Nat.mod_add_div _ _
  have hn : (n:ℤ) = w+2*h*q := by
    have eq : (a:ℤ)+2*h*q = n+h := by exact_mod_cast hf
    dsimp [w]; linarith
  have hw : w.natAbs ≤ h := by dsimp [w]; omega
  have hor := shift_sign w he q
  rw [←hn,hit] at hor
  by_cases hi : w.natAbs+6 ≤ h
  · refine ⟨w,q,hn,hw,?_⟩
    have hb := interior_bound hi
    have hy : 2*|y| < (lucas h : ℤ) := by
      have hy' : 2*y.natAbs < threshold y := by unfold threshold; nlinarith [Nat.le_mul_self y.natAbs]
      have hcast : 2*(y.natAbs:ℤ) < lucas h := by exact_mod_cast hy'.trans hL
      simpa only [Int.natCast_natAbs] using hcast
    rcases hor with hor | hor
    · exact lift_close hb hy hor.symm
    · have hr : (-signed w : ℤ) = y := lift_close (by simpa using hb) hy (by simpa using hor.symm)
      exact (negative_impossible h11 hr).elim
  · have hs : (signed w : ZMod (lucas h))^2 = (y : ZMod (lucas h))^2 := by
      rcases hor with hor | hor <;> simp [hor]
    by_cases hw0 : 0 ≤ w
    · let j := w-h
      exact (end_excluded (j := j) he hL (by dsimp [j]; omega) (by dsimp [j]; omega)
        (by simpa [j] using hs)).elim
    · let j := w+h
      apply (end_excluded (j := j) he hL (by dsimp [j]; omega) (by dsimp [j]; omega) ?_).elim
      rw [show j+h = w+2*h by dsimp [j]; ring,lucas_antiperiod _ he,neg_sq]
      exact hs

#print axioms lift_at_lucas

end Arxiv.«2211.10788».ProgressionClosure
