import ThetaExceptionalPrimeInput
import ThetaIdentityModels

/-! Numerical conditions for conditional prime means at a polynomial cutoff in the modulus. -/
namespace Arxiv.«2501.03234».ThetaExceptionalBudgets
open Real Filter ThetaIdentityModels ThetaExceptionalPrimeInput
noncomputable section

set_option maxRecDepth 8192 in
theorem fit {l N : ℕ} {κ M : ℝ} (hκ : 0<κ) (hk : κ≤1) (hl : 1≤l) (hL : 1≤log (N:ℝ))
    (hkl : 1≤κ*(l:ℝ)) (hM : κ*(N:ℝ)^64/(log N*(l:ℝ)^2) ≤ M)
    (hc : (3+18*Z)*log N*(l:ℝ)^2048 ≤ κ*radius N) :
    let Y := l^768
    let w := M/l.totient
    0≤M ∧ (((l^769:ℕ):ℝ) ≤ radius N) ∧ Y≤N ∧
    error N ≤ w ∧ (Y:ℝ)*(l*(3*Z*(1+log Y)*error N)) ≤ w ∧
    (N:ℝ)^64/(log N*(Y:ℝ)^(1/128:ℝ)) ≤ w ∧
    κ*(N:ℝ)^64/(log N*(l:ℝ)^3) ≤ w := by
  intro Y w
  let L := log (N:ℝ)
  let x := (N:ℝ)^64
  let a := (l:ℝ)
  let Q := radius N
  let C := 3+18*Z
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  have hC : 3≤C := by dsimp [C];linarith
  have hL' : 0<L := by dsimp [L];linarith
  have hQ : 0<Q := radius_pos _
  have ha : 1≤a := by dsimp only [a];exact_mod_cast hl
  have ha' : 0<a := by linarith
  have hx : 0≤x := by dsimp [x];positivity
  have hφ := Nat.cast_pos (α:=ℝ).mpr (Nat.totient_pos.mpr hl)
  have hφa : (l.totient:ℝ) ≤ a := by dsimp only [a];exact_mod_cast Nat.totient_le l
  change C*L*a^2048 ≤ κ*Q at hc
  change κ*x/(L*a^2) ≤ M at hM
  have hM₀ := (div_nonneg (mul_nonneg hκ.le hx) (mul_nonneg hL'.le (sq_nonneg a))).trans hM
  have hcut (j : ℕ) (hj : j≤2048) : a^j ≤ Q := calc
    _ ≤ a^2048 := pow_le_pow_right₀ ha hj
    _ ≤ C*L*a^2048 := le_mul_of_one_le_left (pow_nonneg ha'.le _) (one_le_mul_of_one_le_of_one_le (by linarith only [hC]) hL)
    _ ≤ κ*Q := hc
    _ ≤ Q := mul_le_of_le_one_left hQ.le hk
  have hw : κ*x/(L*a^3) ≤ w := calc
    _ = (κ*x/(L*a^2))/a := by ring
    _ ≤ M/a := div_le_div_of_nonneg_right hM ha'.le
    _ ≤ _ := div_le_div_of_nonneg_left hM₀ hφ hφa
  have hY : (Y:ℝ)=a^768 := Nat.cast_pow ..
  have hQ' : Q≤N := (radius_bounds hL (by
    by_contra! h;rw [show (N:ℝ)=0 by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],log_zero] at hL;linarith)).2
  have haux : C*L*a^1539 ≤ κ*Q := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ha (by decide : 1539≤2048)) (by positivity [show 0≤C by linarith])).trans hc
  have hbase : C*a^1536*(x/Q) ≤ κ*x/(L*a^3) := by
    rw [le_div_iff₀ (by positivity),show C*a^1536*(x/Q)*(L*a^3)=(C*L*a^1539*x)/Q by ring,div_le_iff₀ hQ]
    nlinarith only [mul_le_mul_of_nonneg_right haux hx]
  have hpow : (Y:ℝ)^(1/128:ℝ)=a^6 := by
    rw [hY,←rpow_natCast_mul ha'.le];norm_num
  refine ⟨hM₀,?_,?_,?_,?_,?_,hw⟩
  · simpa only [Nat.cast_pow] using hcut 769 (by decide)
  · exact_mod_cast (show (Y:ℝ)≤N from hY.le.trans ((hcut 768 (by decide)).trans hQ'))
  · apply le_trans _ (hbase.trans hw)
    change 3*x/Q ≤ _
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_right _ (div_nonneg hx hQ.le)
    exact hC.trans (le_mul_of_one_le_right (by linarith only [hC]) (one_le_pow₀ ha))
  · apply le_trans _ hw
    have hy := one_le_pow₀ (n:=768) ha
    have hh := log_le_self (x:=(Y:ℝ)) (Nat.cast_nonneg _)
    have he : 1+log Y ≤ 2*a^768 := by linarith only [hh,hY,hy]
    have hcost : 18*Z*L*a^1540 ≤ κ*Q := calc
      _ ≤ C*L*a^2048 := mul_le_mul (mul_le_mul_of_nonneg_right (by dsimp [C];linarith : 18*Z≤C) hL'.le) (pow_le_pow_right₀ ha (by decide)) (pow_nonneg ha'.le _) (by positivity [show 0≤C by linarith])
      _ ≤ _ := hc
    change (Y:ℝ)*(a*(3*Z*(1+log Y)*(3*x/Q))) ≤ _
    have hn := mul_le_mul_of_nonneg_right he (by positivity : 0≤9*Z*a*(Y:ℝ)*(x/Q))
    calc _ = (1+log Y)*(9*Z*a*(Y:ℝ)*(x/Q)) := by ring
         _ ≤ 2*a^768*(9*Z*a*(Y:ℝ)*(x/Q)) := hn
         _ = 18*Z*a^1537*(x/Q) := by rw [hY];ring
         _ ≤ _ := by
           rw [le_div_iff₀ (by positivity),show 18*Z*a^1537*(x/Q)*(L*a^3)=(18*Z*L*a^1540*x)/Q by ring,div_le_iff₀ hQ]
           nlinarith only [mul_le_mul_of_nonneg_right hcost hx]
  · apply le_trans _ hw
    rw [hpow]
    change x/(L*a^6) ≤ κ*x/(L*a^3)
    have ha3 := le_self_pow₀ ha (by decide : 3≠0)
    have hs : 1 ≤ κ*a^3 := hkl.trans (mul_le_mul_of_nonneg_left ha3 hκ.le)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_right hs (show 0≤x*(L*a^3) by positivity)]

#print axioms fit
end
end Arxiv.«2501.03234».ThetaExceptionalBudgets
