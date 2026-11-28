import ThetaCenteredPrimeBand

/-! Balancing the growing tilt, the moment order, and the period endpoint. -/
namespace Arxiv.«2501.03234».ThetaCenteredScales
open Real Filter ThetaSmoothConditionalModel ThetaTiltBudget
noncomputable section

private theorem ceil_exp {z : ℝ} (hz : 1≤z) :
    exp z≤(⌈exp z⌉₊:ℝ) ∧ (⌈exp z⌉₊:ℝ)≤exp (2*z) := by
  have he : 2≤exp z := by linarith only [add_one_le_exp z,hz]
  refine ⟨Nat.le_ceil _,?_⟩
  calc _ ≤ exp z+1 := (Nat.ceil_lt_add_one (exp_pos _).le).le
       _ ≤ exp z*exp z := by nlinarith only [he,sq_nonneg (exp z-1)]
       _ = _ := by rw [←exp_add];congr 1;ring

theorem parameters {b D : ℝ} (hb : 0<b) (hD : 0≤D) :
    ∃ a : ℝ, 0<a ∧ a≤1/64 ∧ ∀ U₀ : ℕ, ∀ᶠ r : ℝ in atTop, ∃ U T k : ℕ,
      U₀≤U ∧ 2≤T ∧ ThetaModelExponentialMoment.height U≤b*r^4 ∧
      exp (r^3)≤(T:ℝ) ∧ (T:ℝ)≤exp (2*r^4) ∧
      (((2*k:ℕ):ℝ)/(tilt U*(b*r^4)))^(2*k) ≤ exp (-a*r^3) ∧
      (D*(T:ℝ)^2/(b*r^4))^(2*k) ≤ exp (16*r^4) := by
  let J := 952*envelope+1
  have hJ : 0<J := by dsimp [J];positivity [envelope_nonneg]
  let d := min 1 (b/J)
  have hd : 0<d := lt_min (by norm_num) (div_pos hb hJ)
  have hd1 : d≤1 := min_le_left ..
  have hdJ : d*J≤b := (le_div_iff₀ hJ).mp (min_le_right ..)
  let a := min (1/64:ℝ) (d/2)
  refine ⟨a,lt_min (by norm_num) (by positivity),min_le_left ..,?_⟩
  intro U₀
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop ((U₀+1:ℝ)/d),
    eventually_ge_atTop (4/b),eventually_ge_atTop (D/b)] with r hr hlarge hrb hrD
  have hrp : 0<r := by linarith
  have h2 : r≤r^2 := by nlinarith only [mul_le_mul_of_nonneg_left hr hrp.le]
  have h3 : 1≤r^3 := one_le_pow₀ hr
  have h34 : r^3≤r^4 := pow_le_pow_right₀ hr (by decide)
  have h24 : r^2≤r^4 := pow_le_pow_right₀ hr (by decide)
  have hd2 : (U₀:ℝ)+1≤d*r^2 := by
    have h := (div_le_iff₀ hd).mp hlarge
    linarith only [h,mul_le_mul_of_nonneg_left h2 hd.le]
  have hz : 1≤d*r^2 := by linarith only [hd2,Nat.cast_nonneg (α:=ℝ) U₀]
  let U := ⌈exp (d*r^2)⌉₊
  let T := ⌈exp (r^3)⌉₊
  let k := ⌈r⌉₊
  obtain ⟨hUlo,hUhi⟩ := ceil_exp hz
  obtain ⟨hTlo,hThi⟩ := ceil_exp h3
  have hUtop : (U₀:ℝ)≤(U:ℝ) := by linarith only [hUlo,hd2,add_one_le_exp (d*r^2)]
  have hT2 : (2:ℝ)≤(T:ℝ) := by linarith only [hTlo,h3,add_one_le_exp (r^3)]
  have hUp : 0<(U:ℝ) := (exp_pos _).trans_le hUlo
  have hk : r≤(k:ℝ) := Nat.le_ceil _
  have hk2 : (k:ℝ)≤2*r := by linarith only [Nat.ceil_lt_add_one hrp.le,hr]
  have hheight : ThetaModelExponentialMoment.height U≤b*r^4 := by
    have hlog := log_le_log hUp hUhi
    rw [log_exp] at hlog
    have h0 : 0≤log (U:ℝ) := Real.log_nonneg (by linarith only [hUlo,hz,add_one_le_exp (d*r^2)])
    have hcoeff : 952*envelope*d^2≤b := by
      have hd' : d^2≤d := by nlinarith only [mul_le_mul_of_nonneg_left hd1 hd.le]
      dsimp only [J] at hdJ
      nlinarith only [mul_le_mul_of_nonneg_left hd' (by positivity [envelope_nonneg] : 0≤952*envelope),hdJ,hd.le]
    calc _ ≤ envelope*(238*(2*(d*r^2))^2) := by
              unfold ThetaModelExponentialMoment.height
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hlog 2) (by norm_num)) envelope_nonneg
         _ = (952*envelope*d^2)*r^4 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (by positivity)
  refine ⟨U,T,k,by exact_mod_cast hUtop,by exact_mod_cast hT2,hheight,hTlo,
    hThi.trans (exp_le_exp.mpr (by linarith)),?_,?_⟩
  · have ht : exp ((d*r^2)/4)≤tilt U := by
      unfold tilt
      rw [show d*r^2/4=(d*r^2)*(1/4:ℝ) by ring,exp_mul]
      exact rpow_le_rpow (exp_pos _).le hUlo (by norm_num)
    have hh : ((2*k:ℕ):ℝ)≤b*r^4 := by
      push_cast
      have h := (div_le_iff₀ hb).mp hrb
      nlinarith only [hk2,mul_le_mul_of_nonneg_right h hrp.le,mul_le_mul_of_nonneg_left h24 hb.le]
    have ht' : 0<tilt U := (exp_pos _).trans_le ht
    have hbase : ((2*k:ℕ):ℝ)/(tilt U*(b*r^4)) ≤ exp (-(d*r^2/4)) := by
      rw [exp_neg,←one_div,div_le_div_iff₀ (by positivity) (exp_pos _),one_mul]
      exact (mul_le_mul_of_nonneg_right hh (exp_pos _).le).trans
        (by simpa only [mul_comm _ (b*r^4)] using mul_le_mul_of_nonneg_left ht (by positivity : 0≤b*r^4))
    apply (pow_le_pow_left₀ (by positivity) hbase (2*k)).trans
    rw [←exp_nat_mul,exp_le_exp]
    push_cast
    have ha : a≤d/2 := min_le_right ..
    nlinarith only [mul_le_mul_of_nonneg_right hk (by positivity : 0≤d*r^2),mul_le_mul_of_nonneg_right ha (by positivity : 0≤r^3)]
  · have hdb : D≤b*r^4 := by
      have h := (div_le_iff₀ hb).mp hrD
      nlinarith only [h,mul_le_mul_of_nonneg_left (h2.trans h24) hb.le]
    have hbase : D*(T:ℝ)^2/(b*r^4)≤exp (4*r^3) := calc
      _ ≤ (T:ℝ)^2 := by rw [div_le_iff₀ (by positivity)];nlinarith only [mul_le_mul_of_nonneg_right hdb (sq_nonneg (T:ℝ))]
      _ ≤ (exp (2*r^3))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hThi _
      _ = _ := by rw [sq,←exp_add];congr 1;ring
    apply (pow_le_pow_left₀ (by positivity) hbase (2*k)).trans
    rw [←exp_nat_mul,exp_le_exp]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hk2 (by positivity : 0≤r^3)]

#print axioms parameters
end
end Arxiv.«2501.03234».ThetaCenteredScales
