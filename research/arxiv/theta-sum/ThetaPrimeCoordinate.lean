import ThetaSmoothConditionalModel

/-! The effect of revealing one entire prime-power coordinate in a finite model. -/
namespace Arxiv.«2501.03234».ThetaPrimeCoordinate
open Finset Real ThetaSmoothConditionalModel ThetaIdentityFiber ThetaDivisorLogMean
open ThetaSmoothRows (logWeight)
open ThetaDivisorBudget
noncomputable section

theorem oscillation {m m₀ q a r u Y : ℕ} (hq : q.Prime) (ha : 0<a)
    (hm : m=m₀*q^a) (hm₀ : 0 < m₀) (hmP : m∣Y.factorial)
    (hr : r < m) (hu : u < m) (hrc : r.Coprime m) (huc : u.Coprime m)
    (hmod : r ≡ u [MOD m₀]) (V : Window) :
    |ThetaSmoothConditionalModel.cond m r Y V-ThetaSmoothConditionalModel.cond m u Y V| ≤
      2*envelope*((logMass m+log q*mass m)/q) := by
  classical
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  have hqm : q ∣ m := by rw [hm];exact dvd_mul_of_dvd_right (dvd_pow_self q ha.ne') _
  have hm₁ : 1 < m := by
    have hm' : 0 < m := by rw [hm];positivity [hq.pos]
    exact hq.one_lt.trans_le (Nat.le_of_dvd hm' hqm)
  let D := (Icc 2 Y).filter (q∣·)
  let G := m.divisors.filter (q∣·)
  have hG (d : ℕ) (hd : d∈D) : m.gcd d∈G := mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,by omega⟩,Nat.dvd_gcd hqm (mem_filter.mp hd).2⟩
  have vanish (d : ℕ) (hd : d∈Icc 2 Y) (hn : ¬q∣d) : term m r Y V d=term m u Y V d := by
    have hg : m.gcd d ∣ m₀*q^a := by rw [←hm];exact Nat.gcd_dvd_left ..
    have hc := (hq.coprime_iff_not_dvd.mpr hn).symm.coprime_dvd_left (Nat.gcd_dvd_right m d)
    have hg' : m.gcd d ∣ m₀ := (hc.pow_right a).dvd_of_dvd_mul_right hg
    simp only [term,residue_congr hm₁ hr hu hrc huc (hmod.of_dvd hg') (mem_Icc.mp hd).1 hmP
      (Nat.dvd_factorial (by have := (mem_Icc.mp hd).1;omega) (mem_Icc.mp hd).2)]
  have he : ThetaSmoothConditionalModel.cond m r Y V-ThetaSmoothConditionalModel.cond m u Y V = (∑ d∈D,term m r Y V d)-(∑ d∈D,term m u Y V d) := by
    rw [expand,expand,←sum_sub_distrib,←sum_sub_distrib,sum_filter]
    apply sum_congr rfl
    intro d hd
    split_ifs with h
    · rfl
    · rw [vanish d hd h,sub_self]
  have sup (x : ℕ) (hx : x < m) (hxc : x.Coprime m) :
      |∑ d∈D,term m x Y V d| ≤ envelope*((logMass m+log q*mass m)/q) := by
    have hh := restricted hm₁ hx hxc hmP V D G (filter_subset ..) hG
    exact hh.trans (mul_le_mul_of_nonneg_left (log_mass_multiple hq.pos) envelope_nonneg)
  rw [he]
  exact (abs_sub ..).trans ((add_le_add (sup r hr hrc) (sup u hu huc)).trans_eq (by ring))

theorem smooth_oscillation {m m₀ q a r u Y : ℕ} (hq : q.Prime) (ha : 0<a)
    (hm : m=m₀*q^a) (hm₀ : 0 < m₀) (hmP : m∣Y.factorial)
    (hr : r < m) (hu : u < m) (hrc : r.Coprime m) (huc : u.Coprime m)
    (hmod : r ≡ u [MOD m₀]) (hl : 1≤log q) (hs : ∀ k∈m.primeFactors,k≤q) (V : Window) :
    |ThetaSmoothConditionalModel.cond m r Y V-ThetaSmoothConditionalModel.cond m u Y V| ≤ 544*envelope*(log q)^2/q := by
  have hm' : 0 < m := by rw [hm];positivity [hq.pos]
  obtain ⟨hM,hL⟩ := smooth_bounds hm' hq.pos hl hs
  apply (oscillation hq ha hm hm₀ hmP hr hu hrc huc hmod V).trans
  have hq₀ : (0:ℝ)<q := Nat.cast_pos.mpr hq.pos
  have hsum : logMass m+log q*mass m≤272*(log q)^2 := by
    have h := mul_le_mul_of_nonneg_left hM (by linarith : 0≤log (q:ℝ))
    nlinarith only [h,hL,mul_le_mul_of_nonneg_left hl (by linarith : 0≤log (q:ℝ))]
  calc
    _ ≤ 2*envelope*(272*(log q)^2/q) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum hq₀.le) (by positivity [envelope_nonneg])
    _ = _ := by ring

#print axioms oscillation
#print axioms smooth_oscillation
end
end Arxiv.«2501.03234».ThetaPrimeCoordinate
