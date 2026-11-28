import HosoyaProgressionDetection

/-! Two adjacent even Lucas windows recover the orientation without a fixed auxiliary prime. -/

namespace Arxiv.«2211.10788».ProgressionClosure
open CongruenceClosure

private lemma signed_lower_bound (w : ℤ) : (Nat.fib w.natAbs : ℤ) ≤ |signed w| := by
  obtain ⟨k,rfl | rfl⟩ := w.eq_nat_or_neg
  · simp [signed_nat,lucasFibonacciSum]
    rw [abs_of_nonneg (by positivity)]
    omega
  · rcases k with _ | _ | k
    · decide
    · decide
    · rw [signed_lower]
      simp only [Int.natAbs_neg,Int.natAbs_natCast,abs_mul,abs_pow,abs_neg,abs_one,
        one_pow,one_mul,Nat.abs_cast]
      change (Nat.fib (k+2):ℤ) ≤ _
      unfold lowerNeighborAtAddTwo
      push_cast
      omega

private lemma lucas_le_three_fib {h : ℕ} (hp : 0 < h) : lucas h ≤ 3*Nat.fib h := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have := Nat.fib_mono (show k ≤ k+1 by omega)
  unfold lucas
  rw [show k.succ+1=k+2 by omega,Nat.fib_add_two]
  change 2*(Nat.fib k+Nat.fib (k+1))-Nat.fib (k+1) ≤ 3*Nat.fib (k+1)
  omega

private lemma short_index {w y : ℤ} {h : ℕ} (hp : 0 < h) (hL : threshold y < lucas h)
    (hit : signed w=y ∨ -signed w=y) : w.natAbs < h := by
  by_contra! h
  have h₁ := Nat.fib_mono h
  have h₂ := signed_lower_bound w
  have h₃ := lucas_le_three_fib hp
  have hy : |signed w| = (y.natAbs:ℤ) := by
    rw [Int.natCast_natAbs]
    rcases hit with h | h
    · rw [h]
    · rw [←h,abs_neg]
  rw [hy] at h₂
  have : 3*y.natAbs < threshold y := by unfold threshold; nlinarith [Nat.le_mul_self y.natAbs]
  omega

/-- Testing large divisors of L_h and L_{2h} at the same index pins down the sign of the lift.
The recovered index agrees with the tested index modulo 4h. -/
theorem two_window_lift {h M N n : ℕ} (hp : 0 < h) (he : Even h)
    (hM : M ∣ lucas h) (hN : N ∣ lucas (2*h))
    (h₁ : lucas h ≤ 2*M) (h₂ : lucas (2*h) ≤ 2*N) {y : ℤ}
    (sM : threshold y < M) (sN : threshold y < N)
    (a : (signed (n:ℤ) : ZMod M)=y) (b : (signed (n:ℤ) : ZMod N)=y) :
    ∃ w q : ℤ, (n:ℤ)=w+4*h*q ∧ w.natAbs < h ∧ signed w=y := by
  obtain ⟨w,q,hn,_,hw⟩ := lift_up_to_sign hp he hM h₁ sM a
  obtain ⟨v,t,hn',_,hv⟩ := lift_up_to_sign (by omega : 0<2*h) (even_two_mul h) hN h₂ sN b
  have lpos : 0 < lucas h := by
    have hf := Nat.fib_pos.mpr (show 0 < h+1 by omega)
    have := Nat.fib_mono (show h ≤ h+1 by omega)
    unfold lucas; omega
  have sL := sM.trans_le (Nat.le_of_dvd lpos hM)
  have wb := short_index hp sL hw
  have vb := short_index hp sL hv
  have wx : w ≡ v [ZMOD 2*h] := Int.modEq_iff_dvd.mpr ⟨q-2*t,by push_cast at hn'; linarith⟩
  have eq : w=v := by
    have hd := wx.dvd
    have lim : |v-w| < 2*(h:ℤ) := by rw [abs_lt]; omega
    have := Int.eq_zero_of_abs_lt_dvd hd lim
    omega
  subst v
  have hnt : (n:ℤ)=w+4*h*t := by push_cast at hn'; linarith
  have per := (lucas_period he).int_mul t w
  change (signed (w+t*(4*h)) : ZMod (lucas h))=signed w at per
  rw [show w+t*(4*h) = (n:ℤ) by rw [hnt]; ring] at per
  have pm := congrArg (ZMod.castHom hM (ZMod M)) per
  simp only [map_intCast] at pm
  have eqmod := pm.symm.trans a
  have absEq : |signed w|=|y| := by rcases hw with h | h <;> simp [←h]
  have sy : 2*|y| < (M:ℤ) := by
    have h : 2*y.natAbs < threshold y := by unfold threshold; nlinarith [Nat.le_mul_self y.natAbs]
    have hcast : 2*(y.natAbs:ℤ) < M := by exact_mod_cast h.trans sM
    simpa only [Int.natCast_natAbs] using hcast
  exact ⟨w,t,hnt,wb,lift_close (by rw [absEq]; exact sy.le) sy eqmod⟩

#print axioms two_window_lift

end Arxiv.«2211.10788».ProgressionClosure
