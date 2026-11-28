import ThetaTiltedDivisors
import ThetaSmoothRows

/-! Quantitative harmonic tails for divisors supported on small primes. -/
namespace Arxiv.«2501.03234».ThetaSmoothDivisorTails
open Finset Real ThetaTiltedDivisors ThetaDivisorLogMean ThetaDivisorTriangle ThetaSmoothRows
open scoped Classical
noncomputable section

theorem log_sum {m U : ℕ} (hm : 0 < m) (hu : 0 < U) (hsm : ∀ p∈m.primeFactors,p ≤ U)
    {s : ℝ} (hs : 0 ≤ s) (hlog : s*log U ≤ log (3/2)) :
    ∑ d∈m.divisors,log d*wt s d  ≤  total s m*(12*log U) := by
  have eq (d : ℕ) (hd : d∈m.divisors) : log d=∑ p∈m.primeFactors,(d.factorization p:ℝ)*log p := by
    rw [Real.log_nat_eq_sum_factorization,Finsupp.sum]
    apply sum_subset_zero_on_sdiff
    · exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hm.ne'
    · intro p hp;simp [Finsupp.notMem_support_iff.mp (show p∉d.factorization.support from (mem_sdiff.mp hp).2)]
    · intros;rfl
  calc _ = ∑ p∈m.primeFactors,(∑ d∈m.divisors,(d.factorization p:ℝ)*wt s d)*log p := by
             simp_rw [sum_mul];rw [sum_comm (s:=m.primeFactors) (t:=m.divisors)]
             apply sum_congr rfl;intro d hd;rw [eq d hd,sum_mul]
             apply sum_congr rfl;intros;ring
       _  ≤  ∑ p∈m.primeFactors,total s m*(6*(log p/p)) := by
             apply sum_le_sum;intro p hp
             exact (mul_le_mul_of_nonneg_right (valuation (m:=m) hs hlog (Nat.prime_of_mem_primeFactors hp) (hsm p hp)) (log_nonneg_nat p)).trans_eq (by ring)
       _  ≤  _ := by rw [←mul_sum,←mul_sum];apply mul_le_mul_of_nonneg_left _ (total_nonneg ..);nlinarith only [factorial_log U hu m.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hsm p hp⟩)]

theorem total_bound {m U : ℕ} (hm : 0 < m) (hU : 1 ≤ log U) (hsm : ∀ p∈m.primeFactors,p ≤ U)
    {s : ℝ} (hs : 0 ≤ s) (hlog : s*log U ≤ log (3/2)) :
    total s m  ≤  66*exp (32*log (3/2))*log U := by
  have hU₀ : 0 < U := by by_contra! h;rw [show U=0 by omega] at hU;norm_num at hU
  let Z := U^32
  let A := m.divisors.filter (· ≤ Z)
  let B := m.divisors.filter (fun d => ¬d ≤ Z)
  have hsmall (d : ℕ) (hd : d∈A) : wt s d  ≤  exp (32*log (3/2))*(d:ℝ)⁻¹ := by
    have h₀ : 0 < (d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors (mem_filter.mp hd).1
    have h := Real.log_le_log h₀ (show (d:ℝ) ≤ (Z:ℝ) by exact_mod_cast (mem_filter.mp hd).2)
    rw [show log (Z:ℝ)=32*log U by simp [Z,Real.log_pow]] at h
    have he : log d*s ≤ 32*log (3/2) := by nlinarith only [mul_le_mul_of_nonneg_right h hs,hlog]
    rw [wt,Real.rpow_sub h₀,Real.rpow_one,Real.rpow_def_of_pos h₀,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (by positivity)
  have hA : ∑ d∈A,wt s d  ≤  exp (32*log (3/2))*(1+32*log U) := by
    have hsub : A⊆Icc 1 Z := by intro d hd;exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors (mem_filter.mp hd).1,(mem_filter.mp hd).2⟩
    have harm : ∑ d∈A,(d:ℝ)⁻¹ ≤ 1+32*log U := by
      apply (sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => inv_nonneg.mpr (Nat.cast_nonneg d))).trans
      have hh := harmonic_le_one_add_log Z
      rw [harmonic_eq_sum_Icc,Rat.cast_sum] at hh
      simpa [Z,Real.log_pow] using hh
    exact (sum_le_sum hsmall).trans (by rw [←mul_sum];exact mul_le_mul_of_nonneg_left harm (exp_pos _).le)
  have hB : (32*log U)*(∑ d∈B,wt s d) ≤ total s m*(12*log U) := by
    rw [mul_sum]
    apply (sum_le_sum (g:=fun d : ℕ => log d*wt s d) (fun d hd => ?_)).trans
      ((sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun d _ _ => mul_nonneg (log_nonneg_nat d) (nonneg ..))).trans (log_sum hm hU₀ hsm hs hlog))
    have h := Real.log_le_log (Nat.cast_pos.mpr (pow_pos hU₀ 32)) (show (Z:ℝ) ≤ d by exact_mod_cast (le_of_not_ge (mem_filter.mp hd).2))
    apply mul_le_mul_of_nonneg_right _ (nonneg ..)
    simpa [Z,Real.log_pow] using h
  have half : 2*(∑ d∈B,wt s d) ≤ total s m := by
    apply (mul_le_mul_iff_left₀ (show 0 < log U by linarith)).mp
    nlinarith only [hB,mul_nonneg (total_nonneg s m) (show 0 ≤ log U by linarith)]
  have hsplit : (∑ d∈A,wt s d)+(∑ d∈B,wt s d)=total s m := sum_filter_add_sum_filter_not ..
  nlinarith only [half,hsplit,hA,mul_le_mul_of_nonneg_left hU (exp_pos (32*log (3/2))).le]

theorem tail {m U : ℕ} (hm : 0 < m) (hU : 1 ≤ log U) (hsm : ∀ p∈m.primeFactors,p ≤ U)
    {s : ℝ} (hs : 0 ≤ s) (hlog : s*log U ≤ log (3/2)) {Q : ℕ} (hQ : 0 < Q) :
    (∑ d∈m.divisors.filter (Q ≤ ·),logWeight d)  ≤
      (858*exp (32*log (3/2))*(log U)^2)/(Q:ℝ)^s := by
  have hU₀ : 0 < U := by by_contra! h;rw [show U=0 by omega] at hU;norm_num at hU
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (by exact_mod_cast hQ) _),sum_mul]
  have hu (d : ℕ) (hd : d∈m.divisors.filter (Q ≤ ·)) :
      logWeight d*(Q:ℝ)^s ≤ (1+log d)*wt s d := by
    have h₀ : 0 < (d:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors (mem_filter.mp hd).1
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg Q) (show (Q:ℝ) ≤ d by exact_mod_cast (mem_filter.mp hd).2) hs
    apply (mul_le_mul_of_nonneg_left hh (logWeight_nonneg d)).trans_eq
    rw [wt,Real.rpow_sub h₀,Real.rpow_one,logWeight];ring
  have he : (∑ d∈m.divisors,(1+log d)*wt s d)=total s m+∑ d∈m.divisors,log d*wt s d := by simp [add_mul,sum_add_distrib,total]
  have hh := (sum_le_sum hu).trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun d _ _ => mul_nonneg (by linarith [log_nonneg_nat d]) (nonneg ..)))
  rw [he] at hh
  have hb := total_bound hm hU hsm hs hlog
  have hl := log_sum hm hU₀ hsm hs hlog
  nlinarith only [hh,hl,hb,mul_le_mul_of_nonneg_right hb (show 0 ≤ log U by linarith),
    mul_le_mul_of_nonneg_left hU (mul_nonneg (exp_pos (32*log (3/2))).le (show 0 ≤ log U by linarith))]

#print axioms tail
end
end Arxiv.«2501.03234».ThetaSmoothDivisorTails
