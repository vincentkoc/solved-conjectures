import CunninghamPrimeDirichletMass

/-! Supply of prime orders with small total reciprocal cost for simultaneous
Cunningham orbit covers. -/

namespace CunninghamChain.PrimePeriodSupply
open Finset Filter Topology Real

/-- The reciprocals of primes in a reduced progression diverge. Here the
lower bound on the prime Dirichlet mass is the input from Dirichlet's theorem. -/
theorem progression_reciprocals {m : ℕ} [NeZero m] (a : ZMod m) (unit : IsUnit a) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ (p : ZMod m)=a then (p:ℝ)⁻¹ else 0) := by
  classical
  intro sum
  let A : Set ℕ := {p | (p:ZMod m)=a}
  let f (s : ℝ) (p : ℕ) := (s-1)*(PrimeMass.weight A p/(p:ℝ)^s)
  have point (p : ℕ) : Tendsto (f · p) (𝓝[>] 1) (𝓝 0) := by
    by_cases h : p.Prime ∧ (p:ZMod m)=a
    · have hp : (0:ℝ)<p := by exact_mod_cast h.1.pos
      have cont : ContinuousAt (fun s : ℝ => (s-1)*(log p/(p:ℝ)^s)) 1 :=
        (continuousAt_id.sub continuousAt_const).mul (continuousAt_const.div
          (Real.continuousAt_const_rpow hp.ne') (by simpa using hp.ne'))
      simpa [f,PrimeMass.weight,A,h] using cont.tendsto.mono_left nhdsWithin_le_nhds
    · simp [f,PrimeMass.weight,A,h]
  have bound : ∀ᶠ s : ℝ in 𝓝[>] 1, ∀ p : ℕ,
      ‖f s p‖ ≤ (if p.Prime ∧ (p:ZMod m)=a then (p:ℝ)⁻¹ else 0) := by
    filter_upwards [self_mem_nhdsWithin] with s hs p
    change 1<s at hs
    by_cases h : p.Prime ∧ (p:ZMod m)=a
    · have hp : (0:ℝ)<p := by exact_mod_cast h.1.pos
      have lg := Real.log_nonneg (by exact_mod_cast h.1.one_le : (1:ℝ)≤p)
      have dt : 0 < s-1 := by linarith
      have t := (le_div_iff₀ dt).mp (Real.log_le_rpow_div hp.le dt)
      simp only [f,PrimeMass.weight,A,Set.mem_ofPred_eq,if_pos h,Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity),←mul_div_assoc]
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hp s)).mpr
      have pw : (p:ℝ)^s=(p:ℝ)^(s-1)*p := by
        conv_lhs => rw [show s=(s-1)+1 by ring]
        rw [Real.rpow_add_one hp.ne']
      calc _ ≤ (p:ℝ)^(s-1) := by linarith only [t]
           _ = _ := by rw [pw]; field_simp
    · simp [f,PrimeMass.weight,A,h]
  have lim := tendsto_tsum_of_dominated_convergence sum point bound
  have eq (s : ℝ) : (∑' p, f s p)=(s-1)*PrimeMass.mass A s := by
    simp [f,PrimeMass.mass,tsum_mul_left]
  simp_rw [eq] at lim
  have bad : (m.totient:ℝ)⁻¹=0 := tendsto_nhds_unique (PrimeMass.mass_progression a unit) (by simpa using lim)
  exact (inv_ne_zero (by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne')) bad

/-- A prime in the class 1 modulo (B+1)! has a prime-order witness q with
reciprocal at most 1/(Bℓ). Taking a prime divisor of 2^ℓ−1 suffices. -/
theorem large_prime_of_order {B l : ℕ} (hl : l.Prime) (cl : l ≡ 1 [MOD (B+1).factorial]) :
    ∃ q : ℕ, q.Prime ∧ 2<q ∧ B*l<q ∧ orderOf (2:ZMod q)=l := by
  let u := 2^l-1
  let q := u.minFac
  have pow4 : 4≤2^l := Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) hl.two_le
  have hu : 1<u := by dsimp [u]; omega
  have hq : q.Prime := Nat.minFac_prime hu.ne'
  let : Fact q.Prime := ⟨hq⟩
  have dv : q ∣ 2^l-1 := Nat.minFac_dvd _
  have cl2 : 1 ≡ 2^l [MOD q] := (Nat.modEq_iff_dvd' (by omega)).mpr dv
  have root : (2:ZMod q)^l=1 := by
    simpa only [Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using
      ((ZMod.natCast_eq_natCast_iff ..).mpr cl2).symm
  have nz : (2:ZMod q)≠0 := by
    intro zero
    simp only [zero,zero_pow hl.ne_zero,zero_ne_one] at root
  have odd : 2<q := by
    by_contra! le
    have eq : q=2 := le_antisymm le hq.two_le
    exact nz ((ZMod.natCast_eq_zero_iff 2 q).mpr (eq ▸ dvd_rfl))
  have order : orderOf (2:ZMod q)=l := by
    rcases (Nat.dvd_prime hl).mp (orderOf_dvd_of_pow_eq_one root) with one|last
    · have e := pow_orderOf_eq_one (2:ZMod q)
      rw [one,pow_one] at e
      have eq := (ZMod.natCast_eq_natCast_iff 2 1 q).mp (by simpa only [Nat.cast_ofNat,Nat.cast_one] using e)
      change 2%q=1%q at eq
      rw [Nat.mod_eq_of_lt odd,Nat.mod_eq_of_lt hq.one_lt] at eq
      omega
    · exact last
  have ordDiv : l ∣ q-1 := order ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one nz)
  obtain ⟨v,hv⟩ := ordDiv
  have val : q=l*v+1 := by omega
  have vp : 0<v := by
    by_contra! h
    rw [show v=0 by omega,Nat.mul_zero] at hv
    omega
  have large : B<v := by
    by_contra! small
    have res := cl.of_dvd (Nat.dvd_factorial (Nat.succ_pos v) (Nat.succ_le_succ small))
    have qq : v+1 ∣ q := by
      apply Nat.modEq_zero_iff_dvd.mp
      rw [val]
      have eq := (res.mul_right v).add_right 1
      exact eq.trans (by simp [Nat.ModEq])
    rcases (Nat.dvd_prime hq).mp qq with one|eq
    · omega
    · have := Nat.mul_lt_mul_of_pos_right hl.one_lt vp
      omega
  exact ⟨q,hq,odd,by nlinarith [Nat.mul_lt_mul_of_pos_right large hl.pos],order⟩

#print axioms progression_reciprocals
#print axioms large_prime_of_order

end CunninghamChain.PrimePeriodSupply
