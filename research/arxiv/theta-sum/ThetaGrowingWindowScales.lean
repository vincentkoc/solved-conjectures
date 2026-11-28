import ThetaWindowPrimeBand

/-! Simultaneous choice of the moment order and the denominator cutoff. -/
namespace Arxiv.«2501.03234».ThetaGrowingWindowScales
open Real Filter
noncomputable section

/-- Here `z` is the logarithm of the logarithm of the endpoint. -/
def height (z : ℝ) := exp (z/2)*sqrt z

theorem parameters {a b D : ℝ} (ha : 0<a) (hb : 0<b) (hD : 0≤D) :
    ∀ᶠ z : ℝ in atTop, ∃ T k : ℕ, 2≤T ∧ (T:ℝ)≤exp (2*exp z) ∧
      exp (height z)≤(T:ℝ) ∧
      (((2*k:ℕ):ℝ)/(a*(b*exp z)))^(2*k) ≤ exp (-height z/2) ∧
      (D*(T:ℝ)^2/(b*exp z))^(2*k) ≤ exp (16*exp z) := by
  have hlim : Tendsto (fun z : ℝ => exp (z/4)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<4))
  have hu := tendsto_exp_atTop.eventually_ge_atTop (D/b)
  filter_upwards [eventually_ge_atTop 1,hlim.eventually_ge_atTop (4/(a*b)), hu] with z hz hlarge hD'
  let r := exp (z/2)
  let w := sqrt z
  let q := r/w
  let H := height z
  have hr : 0<r := exp_pos _
  have hw : 1≤w := (Real.one_le_sqrt).mpr hz
  have hwp : 0<w := by linarith
  have hw2 : w^2=z := sq_sqrt (by linarith)
  have hr2 : r^2=exp z := by dsimp [r];rw [sq,← exp_add];ring_nf
  have hwle : w≤r := by nlinarith only [hw2,hr2,hr,Real.add_one_le_exp z]
  have hq : 1≤q := (one_le_div hwp).mpr hwle
  have hqr : q≤r := div_le_self hr.le hw
  have hH : 1≤H := by change 1≤r*w;exact one_le_mul_of_one_le_of_one_le (hw.trans hwle) hw
  have hHtop : H≤exp z := by rw [← hr2,sq]; exact mul_le_mul_of_nonneg_left hwle hr.le
  have hprod : q*H=exp z := by change r/w*(r*w)=_;rw [← hr2];field_simp
  have hqz : q*z=H := by change r/w*z=r*w;rw [← hw2];field_simp
  let T := ⌈exp H⌉₊
  let k := ⌈q⌉₊
  have hT : exp H≤(T:ℝ) := Nat.le_ceil _
  have hk : q≤(k:ℝ) := Nat.le_ceil _
  have hkr : (k:ℝ)≤2*q := by linarith only [Nat.ceil_lt_add_one (by positivity : 0≤q),hq]
  have heH : 2≤exp H := by linarith only [Real.add_one_le_exp H,hH]
  have hTtop : (T:ℝ)≤exp (2*H) := calc
    _ ≤ exp H+1 := (Nat.ceil_lt_add_one (exp_pos _).le).le
    _ ≤ exp H*exp H := by nlinarith only [heH,sq_nonneg (exp H-1)]
    _ = _ := by rw [← exp_add];congr 1;ring
  refine ⟨T,k,by exact_mod_cast heH.trans hT,hTtop.trans (exp_le_exp.mpr (by linarith only [hHtop])),hT,?_,?_⟩
  · have hu' : 4≤exp (z/4)*(a*b) := (div_le_iff₀ (mul_pos ha hb)).mp hlarge
    have hh : 4*r*exp (z/4)≤a*(b*exp z) := calc
      _ ≤ exp (z/4)*(a*b)*r*exp (z/4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu' hr.le) (exp_pos _).le
      _ = _ := by dsimp [r];rw [show exp z=exp (z/4)*exp (z/2)*exp (z/4) by rw [← exp_add,← exp_add];congr 1;ring];ring
    have hbase : ((2*k:ℕ):ℝ)/(a*(b*exp z))≤exp (-(z/4)) := by
      rw [Real.exp_neg,← one_div,div_le_div_iff₀ (by positivity) (exp_pos _),one_mul]
      push_cast
      nlinarith only [hh,mul_le_mul_of_nonneg_right (hkr.trans (mul_le_mul_of_nonneg_left hqr (by norm_num))) (exp_pos (z/4)).le]
    apply (pow_le_pow_left₀ (by positivity) hbase (2*k)).trans
    rw [← exp_nat_mul,exp_le_exp]
    push_cast
    change _ ≤ -H/2
    nlinarith only [mul_le_mul_of_nonneg_right hk (by linarith : 0≤z),hqz]
  · have hd : D≤b*exp z := by simpa [mul_comm] using (div_le_iff₀ hb).mp hD'
    have hbase : D*(T:ℝ)^2/(b*exp z) ≤ exp (4*H) := calc
      _ ≤ (T:ℝ)^2 := by rw [div_le_iff₀ (by positivity)];nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg (T:ℝ))]
      _ ≤ (exp (2*H))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hTtop _
      _ = _ := by rw [sq,← exp_add];congr 1;ring
    apply (pow_le_pow_left₀ (by positivity) hbase (2*k)).trans
    rw [← exp_nat_mul,exp_le_exp]
    push_cast
    nlinarith only [mul_le_mul_of_nonneg_right hkr (by linarith : 0≤H),hprod]

#print axioms parameters
end
end Arxiv.«2501.03234».ThetaGrowingWindowScales
