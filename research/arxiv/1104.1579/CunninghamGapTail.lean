import CunninghamGapWeights

/-! Uniform estimates for the primes beyond a moving cutoff. -/

namespace CunninghamChain.GapMean

open Finset Real Filter BatemanHornConjecture
open scoped Topology

/-- All possible later changes to the normalized product have occurred here. -/
def stop (k l h : ℕ) := max (threshold (k+l)) (exceptionalProduct k l h+1)

noncomputable def limitingWeight (k l h : ℕ) := weight k l (stop k l h) h

private lemma subset_below {Y Z : ℕ} (le : Y≤Z) : Y.primesBelow ⊆ Z.primesBelow := by
  intro q h
  exact Nat.mem_primesBelow.mpr ⟨(Nat.lt_of_mem_primesBelow h).trans_le le,Nat.prime_of_mem_primesBelow h⟩

private lemma tail_mem {Y Z q : ℕ} (h : q∈Z.primesBelow \ Y.primesBelow) : q.Prime ∧ Y≤q := by
  have hn := mem_sdiff.mp h
  have hp := Nat.prime_of_mem_primesBelow hn.1
  exact ⟨hp,le_of_not_gt fun lt => hn.2 (Nat.mem_primesBelow.mpr ⟨lt,hp⟩)⟩

theorem stabilized_weight (k l h Z : ℕ) (past : stop k l h≤Z) :
    weight k l Z h = limitingWeight k l h := by
  unfold limitingWeight weight
  symm
  apply prod_subset (subset_below past)
  intro q hq no
  have b := tail_mem (mem_sdiff.mpr ⟨hq,no⟩)
  apply (ratio_bounds b.1 ((le_max_left ..).trans b.2) h).2.2
  intro hit
  have le := Nat.le_of_dvd (exceptional_pos k l h) hit
  have greater := (le_max_right (threshold (k+l)) (exceptionalProduct k l h+1)).trans b.2
  omega

private theorem log_divisors (D Y : ℕ) (dp : 0<D) (yp : 1<Y) (R : Finset ℕ)
    (good : ∀ q∈R, q.Prime ∧ q∣D ∧ Y≤q) : (R.card:ℝ)*log Y ≤ log D := by
  have sub : R ⊆ D.primeFactors := fun q h => Nat.mem_primeFactors.mpr
    ⟨(good q h).1,(good q h).2.1,dp.ne'⟩
  have le : (∏ q ∈ R, q)≤D := Nat.le_of_dvd dp
    ((prod_dvd_prod_of_subset _ _ _ sub).trans (Nat.prod_primeFactors_dvd _))
  calc
    _ = ∑ _q ∈ R, log Y := by simp
    _ ≤ ∑ q ∈ R, log q := sum_le_sum fun q h => log_le_log
      (by exact_mod_cast (show 0<Y by omega)) (by exact_mod_cast (good q h).2.2)
    _ = log (∏ q ∈ R, q : ℕ) := by
      rw [Nat.cast_prod,Real.log_prod (fun q h => by exact_mod_cast (good q h).1.ne_zero)]
    _ ≤ _ := log_le_log (by exact_mod_cast prod_pos (fun q h => (good q h).1.pos)) (by exact_mod_cast le)

/-- Truncating above the fixed small primes loses at most the displayed
multiplicative factor. No positivity assumption on the paired product is needed. -/
theorem weight_tail (k l h Y : ℕ) (large : threshold (k+l)≤Y) :
    weight k l Y h ≤ limitingWeight k l h ∧ limitingWeight k l h ≤
      weight k l Y h * exp (2*(k+l:ℕ)*log (exceptionalProduct k l h)/(Y*log Y)) := by
  classical
  let m := k+l
  let D := exceptionalProduct k l h
  let Z := max Y (stop k l h)
  let S := Z.primesBelow \ Y.primesBelow
  let R := S.filter (·∣D)
  have yp : 1<Y := by unfold threshold at large; have := Nat.zero_le (2^(k+l+2)); omega
  have yr : (1:ℝ)<Y := by exact_mod_cast yp
  have lp := Real.log_pos yr
  have good (q) (h : q∈R) : q.Prime ∧ q∣D ∧ Y≤q := by
    obtain ⟨mem,dv⟩ := mem_filter.mp h
    exact ⟨(tail_mem mem).1,dv,(tail_mem mem).2⟩
  have bound := log_divisors D Y (exceptional_pos ..) yp R good
  have rf (q) (hq : q∈R) := ratio_bounds (good q hq).1 (large.trans (good q hq).2.2) h
  have prodR : (∏ q∈S, ratio k l q h) = ∏ q∈R, ratio k l q h := by
    symm
    apply prod_subset (filter_subset _ _)
    intro q inS no
    have hp := tail_mem inS
    exact (ratio_bounds hp.1 (large.trans hp.2) h).2.2 (fun dv => no (mem_filter.mpr ⟨inS,dv⟩))
  have prodEq : limitingWeight k l h = weight k l Y h * ∏ q∈R, ratio k l q h := by
    rw [←stabilized_weight k l h Z (le_max_right ..),←prodR]
    unfold weight
    rw [mul_comm]
    exact (prod_sdiff (subset_below (le_max_left Y (stop k l h)))).symm
  have low : (1:ℝ) ≤ ∏ q∈R, ratio k l q h := one_le_prod fun q hq => (rf q hq).1
  have high : (∏ q∈R, ratio k l q h) ≤ exp (2*(m:ℝ)*log D/(Y*log Y)) := calc
    _ ≤ ∏ _q∈R, exp (2*(m:ℝ)/Y) := by
      apply prod_le_prod (fun q mem => zero_le_one.trans (rf q mem).1)
      intro q mem
      have le : (Y:ℝ)≤q := by exact_mod_cast (good q mem).2.2
      have hd : 2*(m:ℝ)/q ≤ 2*m/Y := div_le_div_of_nonneg_left (by positivity) (by linarith) le
      exact (rf q mem).2.1.trans ((add_le_add_right hd 1).trans (by simpa [add_comm] using Real.add_one_le_exp (2*(m:ℝ)/Y)))
    _ = exp ((R.card:ℝ)*(2*m/Y)) := by simp [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [le_div_iff₀ (mul_pos (by linarith) lp)]
      calc
        _ = 2*m*((R.card:ℝ)*log Y) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left bound (by positivity)
  rw [prodEq]
  exact ⟨le_mul_of_one_le_right (weight_nonneg ..) low,mul_le_mul_of_nonneg_left high (weight_nonneg ..)⟩

#print axioms stabilized_weight
#print axioms weight_tail

end CunninghamChain.GapMean
