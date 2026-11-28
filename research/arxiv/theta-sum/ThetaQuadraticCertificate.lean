import ThetaQuadraticEnergy
import Mathlib.Analysis.Real.Pi.Bounds

/-! A rational certificate from the first three nonzero quadratic conductors. -/
namespace Arxiv.«2501.03234».ThetaQuadraticCertificate
open Finset Filter Topology ThetaSpectrumDecay ThetaConductorProduct ThetaQuadraticExcess ThetaNaturalPrimeMeans
open ThetaLegendreFactors ThetaQuadraticEnergy

private lemma primes44 : (44:ℕ).primesBelow = {2,3,5,7,11,13,17,19,23,29,31,37,41,43} := by decide

private lemma symbol_eq (q n : ℕ) [Fact q.Prime] : symbol q n=legendreSym q (n:ℤ) := by
  simp only [symbol,legendreSym,Int.cast_natCast]

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private lemma prefix3 : inertPrefix 3 41 = 4529327622489/3885629440000 := by
  norm_num [inertPrefix,primes44,inertFactor,symbol_eq]
private lemma prefix7 : inertPrefix 7 41 = 20537400323/11796480000 := by
  norm_num [inertPrefix,primes44,inertFactor,symbol_eq]
private lemma prefix11 : inertPrefix 11 41 = 100081666172251/91767649075200 := by
  norm_num [inertPrefix,primes44,inertFactor,symbol_eq]

private lemma half3 : excess 3=1 := by norm_num [excess,symbol_eq,sum_range_succ]
private lemma half7 : excess 7=1 := by norm_num [excess,symbol_eq,sum_range_succ]
private lemma half11 : excess 11=3 := by norm_num [excess,symbol_eq,sum_range_succ]

private theorem finite_lower (hAP : ProgressionMangoldt) (r : OddPrime) (hr : r.val%4=3) (n : ℕ) :
    (3.14:ℝ)^2*(excess r.val:ℝ)^4*r.val*(inertPrefix r.val n)^2/
      (((r.val:ℝ)-1)^2*((r.val:ℝ)^2-1)^2) ≤ (coefficient r)^2 := by
  obtain ⟨C,hC,hmag,hprod⟩ := correlation_size r.val hAP hr
  have H := coefficient_limit hAP r
  simp only [symbol,legendreSym,Int.cast_natCast,ThetaCharacterPrimeMeans.residual] at H hC
  rw [← tendsto_nhds_unique H hC] at hmag
  have hp : (2:ℝ)≤r.val := by exact_mod_cast r.property.1.two_le
  have hq : 0<(r.val:ℝ) := by linarith
  have hs := Real.sqrt_pos.mpr hq
  have hm : (0:ℝ)<(r.val:ℝ)-1 := by linarith
  have hk : (0:ℝ)<(r.val:ℝ)^2-1 := by nlinarith
  have hP : 0 ≤ inertPrefix r.val n := by
    apply prod_nonneg; intro p _; unfold inertFactor; split_ifs <;> positivity
  let A := (3.14:ℝ)*(excess r.val:ℝ)^2/Real.sqrt r.val*
    ((r.val:ℝ)/(((r.val:ℝ)-1)*((r.val:ℝ)^2-1)))*inertPrefix r.val n
  have hA : 0≤A := by dsimp only [A]; positivity
  have hle : A ≤ |coefficient r| := by
    rw [hmag]
    dsimp only [A]
    gcongr <;> first | exact Real.pi_gt_d2.le | exact (hprod n).1
  calc _ = A^2 := by
          dsimp only [A]
          simp only [mul_pow,div_pow,Real.sq_sqrt hq.le,← pow_mul]
          field_simp
          ring
       _ ≤ |coefficient r|^2 := by gcongr
       _ = _ := sq_abs _

private abbrev q3 : OddPrime := ⟨3,by decide⟩
private abbrev q7 : OddPrime := ⟨7,by decide⟩
private abbrev q11 : OddPrime := ⟨11,by decide⟩

/-- Three finite Euler products suffice to certify a rational lower variance
bound for the prime theta residual. -/
theorem energy_gt_sixth (hAP : ProgressionMangoldt) : 1/6 < quadraticEnergy := by
  have h3 := finite_lower hAP q3 (by decide) 41
  have h7 := finite_lower hAP q7 (by decide) 41
  have h11 := finite_lower hAP q11 (by decide) 41
  norm_num only [q3,half3,prefix3,Nat.cast_ofNat,Int.cast_one,Int.cast_ofNat] at h3
  norm_num only [q7,half7,prefix7,Nat.cast_ofNat,Int.cast_one,Int.cast_ofNat] at h7
  norm_num only [q11,half11,prefix11,Nat.cast_ofNat,Int.cast_one,Int.cast_ofNat] at h11
  have H := finite_energy_strict hAP {q3,q7,q11}
  simp only [sum_insert (show q3∉({q7,q11}:Finset OddPrime) by decide),
    sum_insert (show q7∉({q11}:Finset OddPrime) by decide),sum_singleton] at H
  linarith only [h3,h7,h11,H]

#print axioms energy_gt_sixth

#print axioms prefix3
#print axioms prefix7
#print axioms prefix11
end Arxiv.«2501.03234».ThetaQuadraticCertificate
