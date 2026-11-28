import ThetaRoughDivisorBudget

/-! A single rough inverse controls the cost of every divisor row
and lifts to every multiple of the original progression modulus. -/
namespace Arxiv.«2501.03234».ThetaRoughRepresentatives
open Real Finset
noncomputable section

theorem compatible {q r P : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q)
    (hP : 2≤P) (hscale : log q≤P) :
    ∃ a : ℕ, Odd a ∧ log a≤4*P ∧
      (∑ p∈a.primeFactors,(p:ℝ)⁻¹)≤4/log P ∧ ∀ m : ℕ, 0 < m → q ∣ m →
        ∃ n < m, n.Coprime m ∧ n%q=r ∧
          ∀ d : ℕ, d ∣ m → d.Coprime a → (n:ZMod d)⁻¹=(a:ZMod d) := by
  obtain ⟨a,ha,hle,haq,har,hrough⟩ := ThetaRoughInverseClasses.rough hq hr hc (P:=P)
  have hodd : Odd a := by
    rw [←Nat.not_even_iff_odd,even_iff_two_dvd]
    intro h
    have H := hrough 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,ha.ne'⟩)
    omega
  have hq' : 0<(q:ℝ) := by exact_mod_cast hq
  have hP' : (2:ℝ)≤P := by exact_mod_cast hP
  have h2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have h4 : log (4:ℝ)≤2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num only [Nat.cast_ofNat] at *; linarith only [h2]
  have hlog := log_le_log (by exact_mod_cast ha) (by exact_mod_cast hle :
      (a:ℝ)≤2*q*(4:ℝ)^P)
  rw [log_mul (by positivity) (by positivity),log_mul (by norm_num) hq'.ne',log_pow] at hlog
  have hsa : log a≤4*P := by nlinarith only [hlog,hscale,h2,hP',mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg P : (0:ℝ)≤P)]
  refine ⟨a,hodd,hsa,(ThetaRoughDivisorBudget.reciprocal ha (by omega) hrough).trans ?_,?_⟩
  · have hLp : 0<log P := log_pos (by linarith)
    rw [div_le_div_iff₀ (mul_pos (by positivity) hLp) hLp]
    nlinarith only [mul_le_mul_of_nonneg_right hsa hLp.le]
  · intro m hm hqm
    obtain ⟨n,hn,hnc,H⟩ := ThetaRoughInverseClasses.lift (a:=a) hm
    have he := H q hqm haq.symm
    have hnq : (n:ZMod q)=(r:ZMod q) := calc
      _ = (n:ZMod q)*((a:ZMod q)*(r:ZMod q)) := by rw [har,mul_one]
      _ = _ := by rw [←mul_assoc,he,one_mul]
    refine ⟨n,hn,hnc,((ZMod.natCast_eq_natCast_iff' _ _ _).mp hnq).trans (Nat.mod_eq_of_lt hr),?_⟩
    exact fun d hd h => ZMod.inv_eq_of_mul_eq_one _ _ _ (H d hd h)

#print axioms compatible
end
end Arxiv.«2501.03234».ThetaRoughRepresentatives
