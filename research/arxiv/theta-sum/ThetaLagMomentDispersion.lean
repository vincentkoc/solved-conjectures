import ThetaPopularLagCounts

/-! A fourth moment on individual pairs and a third moment of the pair
counts bound the second moment of signed sums over displacements. -/
namespace Arxiv.«2501.03234».ThetaLagMomentDispersion
open Finset Real ThetaLagSieveWeights ThetaPositiveLag
noncomputable section

private theorem cauchy {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    (∑ i∈s,g i)^2≤(s.card:ℝ)*(∑ i∈s,(g i)^2) := by
  simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] using
    sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) g

theorem fibre {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    ((∑ i∈s,g i)^2)^2≤(s.card:ℝ)^3*(∑ i∈s,(g i)^4) := by
  have a := pow_le_pow_left₀ (sq_nonneg _) (cauchy s g) 2
  have b := cauchy s (fun i => (g i)^2)
  simp only [←pow_mul] at b
  norm_num1 at b
  rw [mul_pow] at a
  nlinarith only [a,mul_le_mul_of_nonneg_left b (sq_nonneg (s.card:ℝ))]

theorem dispersion {ι κ : Type*} (I : Finset ι) (s : ι → Finset κ) (g : κ → ℝ) :
    (∑ h∈I,(∑ z∈s h,g z)^2)^2≤(∑ h∈I,((s h).card:ℝ)^3)*(∑ h∈I,∑ z∈s h,(g z)^4) := by
  let n (h : ι) := ((s h).card:ℝ)^3
  let v (h : ι) := ∑ z∈s h,(g z)^4
  have hn (h : ι) : 0≤n h := by dsimp [n];positivity
  have hv (h : ι) : 0≤v h := sum_nonneg (fun _ _ => by positivity)
  have e (h : ι) : (∑ z∈s h,g z)^2 ≤ sqrt (n h)*sqrt (v h) := by
    rw [←Real.sqrt_mul (hn h),Real.le_sqrt (by positivity) (mul_nonneg (hn h) (hv h))]
    exact fibre (s h) g
  have h := pow_le_pow_left₀ (sum_nonneg (s:=I) (fun i _ => sq_nonneg _)) (sum_le_sum (s:=I) (fun i _ => e i)) 2
  have h' := sum_mul_sq_le_sq_mul_sq I (fun i => sqrt (n i)) (fun i => sqrt (v i))
  simp only [Real.sq_sqrt (hn _),Real.sq_sqrt (hv _)] at h'
  exact h.trans h'

/-- The cube of the ordinary prime-pair sieve factor still has bounded mean. -/
theorem weight_cube (L : ℕ) : ∑ h∈offsets L,(weight 3 h)^3≤exp 64*L := by
  apply le_trans (sum_le_sum (g:=weight 64) ?_) (mean (by norm_num) L)
  intro h _
  simp only [weight,←prod_pow]
  apply prod_le_prod (fun p _ => by positivity)
  intro p hp
  have h₂ : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  field_simp [show (p:ℝ)≠0 by linarith]
  nlinarith only [h₂,mul_nonneg (show 0≤(p:ℝ)-2 by linarith) (show 0≤(p:ℝ)+2 by linarith),sq_nonneg ((p:ℝ)-2)]

#print axioms dispersion
#print axioms weight_cube
end
end Arxiv.«2501.03234».ThetaLagMomentDispersion
