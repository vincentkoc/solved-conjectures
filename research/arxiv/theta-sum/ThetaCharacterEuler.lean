import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.PSeries

/-! Euler factors of the modulo-three denominator correlation. -/
namespace Arxiv.«2501.03234».ThetaCharacterEuler
open Finset Filter
open scoped Topology

/-- Local weights after absorbing Euler's totient factors. -/
noncomputable def factor (keepThree : Bool) (p : ℕ) : ℝ :=
  if p=3 then (if keepThree then 3/2 else 0)
  else if p%6=5 then 2*((p:ℝ)+1)/(p-1) else 0

noncomputable def weight (b : Bool) (n : ℕ) : ℝ :=
  (∏ p∈n.primeFactors,factor b p)/(n:ℝ)^2

private lemma factor_estimate (b : Bool) {p : ℕ} (hp : p.Prime) :
    0 ≤ factor b p ∧ factor b p ≤ (p:ℝ)^(3/4:ℝ) := by
  have hp' : (0:ℝ)<p := by exact_mod_cast hp.pos
  have root (z : ℝ) (hz4 : z^4 ≤ (p:ℝ)^3) : z ≤ (p:ℝ)^(3/4:ℝ) := by
    have h : ((p:ℝ)^(3/4:ℝ))^4 = (p:ℝ)^3 := by
      rw [← Real.rpow_mul_natCast hp'.le]
      norm_num
    exact le_of_pow_le_pow_left₀ (by decide : 4≠0) (by positivity) (hz4.trans h.ge)
  unfold factor
  split_ifs with h hb h5
  · subst p
    exact ⟨by norm_num, root _ (by norm_num)⟩
  · exact ⟨le_rfl, by positivity⟩
  · have h5' : (5:ℝ) ≤ p := by exact_mod_cast (show 5≤p by omega)
    have hpos : (0:ℝ) < p-1 := by linarith
    have hub : 2*((p:ℝ)+1)/(p-1) ≤ 3 := (div_le_iff₀ hpos).mpr (by linarith)
    refine ⟨div_nonneg (by positivity) hpos.le,hub.trans (root 3 ?_)⟩
    exact le_trans (by norm_num : (3:ℝ)^4≤5^3) (pow_le_pow_left₀ (by norm_num) h5' 3)
  · exact ⟨le_rfl, by positivity⟩

private lemma weight_bound (b : Bool) (n : ℕ) :
    ‖weight b n‖ ≤ (n:ℝ)^(-(5/4):ℝ) := by
  by_cases hn : n=0
  · simp [hn,weight,Real.zero_rpow]
  have hp' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hb (p) (hp : p∈n.primeFactors) := factor_estimate b (Nat.prime_of_mem_primeFactors hp)
  rw [weight,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (prod_nonneg (fun p hp => (hb p hp).1)) (sq_nonneg _))]
  calc
    _ ≤ (∏ p∈n.primeFactors,(p:ℝ)^(3/4:ℝ))/(n:ℝ)^2 :=
      div_le_div_of_nonneg_right (prod_le_prod (fun p hp => (hb p hp).1) (fun p hp => (hb p hp).2)) (sq_nonneg _)
    _ ≤ (n:ℝ)^(3/4:ℝ)/(n:ℝ)^2 := by
      rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
    _ = _ := by
      rw [← Real.rpow_natCast,← Real.rpow_sub hp']
      norm_num

private theorem summable_weight_norm (b : Bool) : Summable (fun n => ‖weight b n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (weight_bound b)
    (Real.summable_nat_rpow.mpr (by norm_num))

private lemma weight_one (b : Bool) : weight b 1 = 1 := by simp [weight]
private lemma weight_zero (b : Bool) : weight b 0 = 0 := by simp [weight]

private lemma weight_mul (b : Bool) {m n : ℕ} (hmn : m.Coprime n) :
    weight b (m*n) = weight b m * weight b n := by
  by_cases hm : m=0
  · simp [hm,weight_zero]
  by_cases hn : n=0
  · simp [hn,weight_zero]
  simp only [weight,Nat.primeFactors_mul hm hn,prod_union hmn.disjoint_primeFactors,Nat.cast_mul]
  ring

private theorem local_series (b : Bool) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, weight b (p^e) = 1 + factor b p / ((p:ℝ)^2-1) := by
  have hp' : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  let r := ((p:ℝ)^2)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr : r < 1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have hgeo := hasSum_geometric_of_lt_one hr0 hr
  have he (e : ℕ) : weight b (p^(e+1)) = (factor b p*r)*r^e := by
    rw [weight,Nat.primeFactors_prime_pow (Nat.succ_ne_zero _) hp,prod_singleton,Nat.cast_pow]
    simp only [r,inv_pow,div_eq_mul_inv]
    ring
  have hs := (hgeo.mul_left (factor b p*r)).congr_fun he
  rw [tsum_eq_zero_add' (f := fun e : ℕ => weight b (p^e)) hs.summable,pow_zero,weight_one,hs.tsum_eq]
  congr 1
  dsimp [r]
  field_simp

private theorem product_limit (b : Bool) :
    Tendsto (fun N => ∏ p ∈ Nat.primesBelow N, (1+factor b p/((p:ℝ)^2-1)))
      atTop (𝓝 (∑' n : ℕ,weight b n)) := by
  have h := EulerProduct.eulerProduct (weight_one b) (@weight_mul b) (summable_weight_norm b) (weight_zero b)
  exact h.congr' (Eventually.of_forall fun N => prod_congr rfl (fun p hp =>
    local_series b (Nat.prime_of_mem_primesBelow hp)))

/-- The Euler product indexed by all primes, with the complement of 5 modulo 6
carrying the neutral factor one. -/
noncomputable def characterProduct : ℝ :=
  ∏' p : Nat.Primes, (if (p:ℕ)%6=5 then 1+2/(((p:ℕ):ℝ)-1)^2 else 1)

private lemma local_without_three {p : ℕ} (hp : p.Prime) :
    1+factor false p/((p:ℝ)^2-1) =
      (if p%6=5 then 1+2/((p:ℝ)-1)^2 else 1) := by
  have h : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  by_cases h3 : p=3
  · subst p; norm_num [factor]
  by_cases h5 : p%6=5
  · simp only [factor,if_neg h3,if_pos h5]
    have hm : (p:ℝ)-1 ≠ 0 := by linarith
    have hh : (p:ℝ)^2-1 ≠ 0 := by nlinarith
    field_simp [hm,hh]
    ring
  · simp [factor,h3,h5]

private lemma remove_three {N : ℕ} (hN : 3<N) :
    (∏ p∈Nat.primesBelow N, (1+factor true p/((p:ℝ)^2-1))) =
      19/16 * ∏ p∈Nat.primesBelow N, (1+factor false p/((p:ℝ)^2-1)) := by
  have hm : 3 ∈ Nat.primesBelow N := Nat.mem_primesBelow.mpr ⟨hN,by decide⟩
  let a (b : Bool) (p : ℕ) := 1+factor b p/((p:ℝ)^2-1)
  change (∏ p∈Nat.primesBelow N,a true p) = 19/16*∏ p∈Nat.primesBelow N,a false p
  rw [← prod_erase_mul _ _ hm,← prod_erase_mul _ (a false) hm]
  have H : (∏ p∈(Nat.primesBelow N).erase 3,a true p) =
      ∏ p∈(Nat.primesBelow N).erase 3,a false p :=
    prod_congr rfl (fun p hp => by simp only [a,factor,if_neg (mem_erase.mp hp).1])
  rw [H]
  norm_num [a,factor]
  ring

/-- Absolute convergence and the difference between keeping and deleting the prime three. -/
theorem weight_difference :
    (∑' n : ℕ,weight true n) - (∑' n : ℕ,weight false n) = 3/16*characterProduct := by
  have H := tendsto_nhds_unique (product_limit true)
    (((product_limit false).const_mul (19/16:ℝ)).congr' ((eventually_gt_atTop 3).mono
      (fun N h => (remove_three h).symm)))
  have F : (∑' n : ℕ,weight false n) = characterProduct := by
    rw [← EulerProduct.eulerProduct_tprod (weight_one false) (@weight_mul false)
      (summable_weight_norm false) (weight_zero false)]
    exact tprod_congr (fun p => (local_series false p.2).trans (local_without_three p.2))
  rw [H,F]; ring

/-- Signed difference of the two absolutely summable denominator weights. -/
theorem weight_difference_hasSum :
    HasSum (fun n : ℕ => weight true n - weight false n) (3/16*characterProduct) := by
  rw [← weight_difference]
  exact (summable_weight_norm true).of_norm.hasSum.sub (summable_weight_norm false).of_norm.hasSum

#print axioms weight_difference_hasSum
#print axioms weight_difference
end Arxiv.«2501.03234».ThetaCharacterEuler
