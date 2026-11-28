import ThetaDivisorTriangle

/-! A uniform log-weighted reciprocal divisor bound for unrestricted moduli. -/
namespace Arxiv.«2501.03234».ThetaDivisorBudget
open Finset Real ThetaDivisorLogMean ThetaDivisorTriangle
noncomputable section

private lemma prime_logs (m : ℕ) : ∑ p∈m.primeFactors,log p≤ log m := by
  rw [Real.log_nat_eq_sum_factorization,Finsupp.sum]
  apply sum_le_sum
  intro p hp
  have he : 1≤ m.factorization p := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp)
  exact (one_mul (log p)).symm.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast he : (1:ℝ)≤ m.factorization p) (log_nonneg_nat p))

private lemma split_primes {m y : ℕ} (hy : 0< y) (hmy : log m≤ y) :
    ∑ p∈m.primeFactors,log p/p≤ 2*log y+1 := by
  classical
  let F := m.primeFactors
  let G := F.filter (·≤ y)
  let H := F.filter (fun p => ¬p≤ y)
  have hy' : 0<(y:ℝ) := by exact_mod_cast hy
  have hg : ∑ p∈G,log p/p≤ 2*log y := factorial_log y hy G (fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩)
  have hh : ∑ p∈H,log p/p≤ 1 := by
    calc _ ≤ ∑ p∈H,log p/y := sum_le_sum fun p hp => div_le_div_of_nonneg_left (log_nonneg_nat p) hy'
          (by exact_mod_cast (le_of_not_ge (mem_filter.mp hp).2 : y≤ p))
         _ = (∑ p∈H,log p)/y := (sum_div ..).symm
         _ ≤ 1 := by
           apply (div_le_iff₀ hy').mpr
           rw [one_mul]
           exact (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun p _ _ => log_nonneg_nat p)).trans ((prime_logs m).trans hmy)
  rw [←sum_filter_add_sum_filter_not m.primeFactors (·≤ y)]
  exact add_le_add hg hh

/-- When y ≥ log m and log y ≥ 1, the reciprocal divisors of m have total
mass O(log y), and their log moment is O((log y)²). -/
theorem bounds {m y : ℕ} (hm : 0< m) (hy : 0< y) (hmy : log m≤ y) (hlog : 1≤ log y) :
    mass m ≤ 2+32*log y ∧ logMass m≤ 238*(log y)^2 := by
  classical
  let D := mass m
  have hD : 0≤ D := mass_nonneg _
  have hz := logMass_upper hm
  have hf := mul_le_mul_of_nonneg_left (split_primes hy hmy) (show 0≤ 2*D by positivity)
  have hL : logMass m≤ 7*D*log y := by
    change logMass m≤ D+2*D*_ at hz
    nlinarith only [hz,hf,mul_le_mul_of_nonneg_left hlog hD]
  let z := y^16
  let A := m.divisors.filter (·≤ z)
  let F := m.divisors.filter (fun d => ¬d≤ z)
  let S (s : Finset ℕ) := ∑ d∈s,(d:ℝ)⁻¹
  have hsmall : S A≤ 1+16*log y := by
    have hi : A⊆Icc 1 z := by
      intro d hd; exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1,(mem_filter.mp hd).2⟩
    have h : S A≤ (harmonic z:ℝ) := by
      rw [harmonic_eq_sum_Icc,Rat.cast_sum]
      simp only [Rat.cast_inv,Rat.cast_natCast]
      exact sum_le_sum_of_subset_of_nonneg hi (fun _ _ _ => by positivity)
    exact h.trans ((harmonic_le_one_add_log z).trans_eq (by simp [z,Real.log_pow]))
  have hlarge : (16*log y)*S F≤ logMass m := by
    dsimp only [S]; rw [mul_sum]
    apply (sum_le_sum (g:=fun d : ℕ => (1+log d)/d) (fun d hd => ?_)).trans
      (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun d _ _ => div_nonneg (by linarith [log_nonneg_nat d]) (Nat.cast_nonneg _)))
    have hdz : z≤ d := (le_of_not_ge (mem_filter.mp hd).2)
    have h := Real.log_le_log (Nat.cast_pos.mpr (pow_pos hy _)) (by exact_mod_cast hdz : (z:ℝ)≤ d)
    simp only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at h
    rw [←div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have he : S A+S F=D := sum_filter_add_sum_filter_not ..
  have hF : 2*S F≤ D := by
    apply (mul_le_mul_iff_left₀ (by linarith : 0< log y)).mp
    nlinarith only [hlarge,hL,mul_nonneg hD (by linarith : 0≤ log y)]
  have hu : D≤ 2+32*log y := by linarith only [he,hsmall,hF]
  refine ⟨hu,?_⟩
  have hlim := mul_le_mul_of_nonneg_right hu (by linarith : 0≤ log y)
  nlinarith only [hL,hlim,mul_le_mul_of_nonneg_right hlog (by linarith : 0≤ log y)]

#print axioms bounds
end
end Arxiv.«2501.03234».ThetaDivisorBudget
