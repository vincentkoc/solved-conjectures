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

lemma lift_close {L : ℕ} {x y : ℤ} (hx : 2*|x| ≤ (L:ℤ))
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

/-- A hit modulo any sufficiently large divisor of the Lucas number lifts up to sign. -/
theorem lift_up_to_sign {h n M : ℕ} (hp : 0 < h) (he : Even h) (hdvd : M ∣ lucas h)
    (hlarge : lucas h ≤ 2*M) {y : ℤ} (hL : threshold y < M)
    (hit : (signed (n:ℤ) : ZMod M) = y) :
    ∃ w q : ℤ, (n:ℤ) = w+2*h*q ∧ w.natAbs ≤ h ∧ (signed w = y ∨ -signed w = y) := by
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
  let cast := ZMod.castHom hdvd (ZMod M)
  have hor' : (y : ZMod M) = signed w ∨ (y : ZMod M) = -(signed w : ZMod M) := by
    rcases hor with hor | hor
    · left
      simpa only [←hn,map_intCast,hit] using congrArg cast hor
    · right
      simpa only [←hn,map_intCast,map_neg,hit] using congrArg cast hor
  clear hor
  by_cases hi : w.natAbs+6 ≤ h
  · refine ⟨w,q,hn,hw,?_⟩
    have hu := interior_quarter_bound hi
    have hb : 2*|signed w| ≤ (M:ℤ) := by
      linarith [show (lucas h:ℤ) ≤ 2*(M:ℤ) by exact_mod_cast hlarge]
    have hy : 2*|y| < (M : ℤ) := by
      have hy' : 2*y.natAbs < threshold y := by unfold threshold; nlinarith [Nat.le_mul_self y.natAbs]
      have hcast : 2*(y.natAbs:ℤ) < M := by exact_mod_cast hy'.trans hL
      simpa only [Int.natCast_natAbs] using hcast
    rcases hor' with hor | hor
    · exact Or.inl (lift_close hb hy hor.symm)
    · have hr : (-signed w : ℤ) = y := lift_close (by simpa using hb) hy (by simpa using hor.symm)
      exact Or.inr hr
  · have hs : (signed w : ZMod M)^2 = (y : ZMod M)^2 := by
      rcases hor' with hor | hor <;> simp [hor]
    by_cases hw0 : 0 ≤ w
    · let j := w-h
      exact (end_excluded_at_divisor (j := j) he hdvd hL (by dsimp [j]; omega) (by dsimp [j]; omega)
        (by simpa [j] using hs)).elim
    · let j := w+h
      apply (end_excluded_at_divisor (j := j) he hdvd hL (by dsimp [j]; omega) (by dsimp [j]; omega) ?_).elim
      have ea := congrArg cast (lucas_antiperiod w he)
      simp only [map_intCast,map_neg] at ea
      rw [show j+h = w+2*h by dsimp [j]; ring,ea,neg_sq]
      exact hs

/-- A hit at the two moduli lifts, preserving the index modulo twice the even window length. -/
theorem lift_at_lucas {h n : ℕ} (hp : 0 < h) (he : Even h) {y : ℤ}
    (hL : threshold y < lucas h)
    (h11 : (signed (n:ℤ) : ZMod 11) = y)
    (hit : (signed (n:ℤ) : ZMod (lucas h)) = y) :
    ∃ w q : ℤ, (n:ℤ) = w+2*h*q ∧ w.natAbs ≤ h ∧ signed w = y := by
  obtain ⟨w,q,hn,hw,hy | hy⟩ := lift_up_to_sign hp he (dvd_refl _) (by omega) hL hit
  · exact ⟨w,q,hn,hw,hy⟩
  · exact (negative_impossible h11 hy).elim

#print axioms lift_up_to_sign
#print axioms lift_at_lucas

end Arxiv.«2211.10788».ProgressionClosure
