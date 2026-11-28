import CunninghamFiniteCoverSearch
import Mathlib.NumberTheory.Chebyshev

/-! Prime-relative frequency of seeds admitting a small divisibility cover. -/

namespace CunninghamChain.OrbitCover
open Finset Real Filter Topology

/-- Count each prime seed once if either sign has a cover of the given size. -/
noncomputable def coveredSeeds (X k : ℕ) : Finset ℕ := by
  classical
  exact X.primesLE.filter (fun p => ∃ (b : Bool) (S : Finset ℕ), (∀ q∈S,q.Prime) ∧ S.card≤k ∧ Covers b p S)

private theorem seeds_subset (X k : ℕ) : coveredSeeds X k⊆candidates k := by
  classical
  intro p hp
  obtain ⟨pr,b,S,prime,size,cover⟩ := mem_filter.mp hp
  obtain ⟨T,sub,mem,_⟩ := (finite_cover_iff b (Nat.mem_primesLE.mp pr).2).mp ⟨S,prime,size,cover⟩
  exact sub mem

private theorem mersenne_product_bound (D : ℕ) : mersenneProduct D≤2^(D*D) := by
  calc mersenneProduct D ≤ ∏ _i∈range D, 2^D := by
        apply Finset.prod_le_prod'
        intro i hi
        exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (mem_range.mp hi))
       _ = 2^(D*D) := by simp [pow_mul]

/-- A single product bound controls all prime seeds for both signs, without a cutoff. -/
theorem candidate_weight (k : ℕ) : (∑ q∈candidates k, log q) ≤ (4:ℝ)^k * log 2 := by
  classical
  let D := 2^(k-1)
  have pos (q : ℕ) (hq : q∈candidates k) : 0<q := (Nat.prime_of_mem_primeFactors hq).pos
  have hw : ∏ q∈candidates k, q ≤ mersenneProduct D := by
    exact Nat.le_of_dvd (Finset.prod_pos (fun i _ =>
      Nat.sub_pos_of_lt (one_lt_pow₀ (by decide : 1<(2:ℕ)) (Nat.succ_ne_zero i))))
      (Nat.prod_primeFactors_dvd _)
  have db : D≤2^k := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
  have ex : D*D≤4^k := by
    simpa [← mul_pow] using Nat.mul_le_mul db db
  calc ∑ q∈candidates k, log q = log (∏ q∈candidates k, (q:ℝ)) := by
         symm
         apply Real.log_prod
         exact fun q hq => by exact_mod_cast (pos q hq).ne'
       _ ≤ log ((2:ℝ)^(D*D)) := by
         apply log_le_log (Finset.prod_pos (fun q hq => by exact_mod_cast pos q hq))
         rw [← Nat.cast_prod]
         exact_mod_cast hw.trans (mersenne_product_bound D)
       _ ≤ (4:ℝ)^k * log 2 := by
         rw [log_pow]
         apply mul_le_mul_of_nonneg_right _ (by positivity)
         exact_mod_cast ex

private theorem seeds_weight (X k : ℕ) : (∑ q∈coveredSeeds X k, log q) ≤ (4:ℝ)^k*log 2 := by
  apply le_trans _ (candidate_weight k)
  exact sum_le_sum_of_subset_of_nonneg (seeds_subset X k) (fun _ _ _ => log_natCast_nonneg _)

/-- Splitting the candidate seeds at √X preserves the logarithm in the prime-counting scale. -/
theorem seed_count_bound {X : ℕ} (hx : 2≤X) (k : ℕ) :
    ((coveredSeeds X k).card:ℝ)*log X ≤ 2*(4:ℝ)^k*log 2+√X*log X := by
  classical
  let S := coveredSeeds X k
  have xp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have xl : 0≤log X := log_natCast_nonneg _
  have hc : (((S.filter (fun q : ℕ => (q:ℝ)≤√X)).card):ℝ)≤√X := by
    apply le_trans _ (Nat.floor_le (sqrt_nonneg _))
    norm_cast
    rw [show ⌊√(X:ℝ)⌋₊=(Icc 1 ⌊√(X:ℝ)⌋₊).card by simp]
    apply card_le_card
    intro q hq
    obtain ⟨hq,sm⟩ := mem_filter.mp hq
    have hp := Nat.prime_of_mem_primeFactors (seeds_subset X k hq)
    exact mem_Icc.mpr ⟨hp.one_le,Nat.le_floor sm⟩
  have low : (S.card:ℝ)*(log X/2) ≤ ∑ q∈S, (log q + if (q:ℝ)≤√X then log X/2 else 0) := by
    calc _ = ∑ _q∈S, log X/2 := by simp
         _ ≤ _ := by
           apply sum_le_sum
           intro q _
           split_ifs with h
           · linarith [log_natCast_nonneg q]
           · simpa [log_sqrt xp.le] using (log_le_log (sqrt_pos.mpr xp) (le_of_not_ge h))
  rw [sum_add_distrib,←sum_filter] at low
  simp only [sum_const,nsmul_eq_mul] at low
  have := mul_le_mul_of_nonneg_right hc (by linarith : 0≤log X/2)
  change (S.card:ℝ)*log X≤_
  linarith [seeds_weight X k]


private theorem prime_count_lower :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)*log 2/2 ≤ (Nat.primeCounting X:ℝ)*log X := by
  have lp : 0<log (2:ℝ) := log_pos (by norm_num)
  have sub := isLittleO_log_id_atTop.def (show 0<log (2:ℝ)/4 by positivity)
  have succ : Tendsto (fun X : ℕ => (X:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [succ.eventually sub,eventually_ge_atTop 2] with X h hx
  have xl : 0<log (X:ℝ) := log_pos (by exact_mod_cast (show 1<X by omega))
  have hnon : 0 ≤ (X:ℝ) := Nat.cast_nonneg X
  simp only [id_eq,Real.norm_eq_abs,abs_of_nonneg (log_nonneg (show 1≤(X:ℝ)+1 by linarith only [hnon])),
    abs_of_nonneg (show 0≤(X:ℝ)+1 by positivity)] at h
  have lower := (div_le_iff₀ xl).mp (Chebyshev.pi_ge X)
  have xp : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  nlinarith [mul_nonneg (sub_nonneg.mpr xp) lp.le]

/-- If 4^k is little-o of X, a density-zero fraction of the primes up
to X have a k-prime cover on even one of the two recurrences. -/
theorem covered_prime_fraction (k : ℕ → ℕ)
    (small : Tendsto (fun X : ℕ => (4:ℝ)^(k X)/X) atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => ((coveredSeeds X (k X)).card:ℝ)/Nat.primeCounting X) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have lp : 0<log (2:ℝ) := log_pos (by norm_num)
  have root := (isLittleO_log_rpow_atTop (show 0<(1/2:ℝ) by norm_num)).def
    (show 0<ε*log 2/8 by positivity)
  filter_upwards [prime_count_lower,tendsto_natCast_atTop_atTop.eventually root,
    small.eventually (gt_mem_nhds (show 0<ε/8 by positivity)),eventually_ge_atTop 2] with X low hr hs hx
  have xp : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have xl : 0<log (X:ℝ) := log_pos (by exact_mod_cast (show 1<X by omega))
  have primepos : 0<(Nat.primeCounting X:ℝ) := by
    by_contra! h
    linarith [mul_nonpos_of_nonpos_of_nonneg h xl.le,mul_pos xp lp]
  simp only [← sqrt_eq_rpow,Real.norm_eq_abs,abs_of_pos xl,abs_of_nonneg (sqrt_nonneg _)] at hr
  have hs' := (div_lt_iff₀ xp).mp hs
  have hroot := mul_le_mul_of_nonneg_left hr (sqrt_nonneg (X:ℝ))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ primepos]
  apply lt_of_mul_lt_mul_right (a := log X) (by
    have rootBound : √X*log X ≤ ε*log 2/8*X := by
      calc √X*log X ≤ √X*(ε*log 2/8*√X) := hroot
           _ = ε*log 2/8*X := by nlinarith only [congrArg (fun t : ℝ => ε*log 2/8*t) (sq_sqrt xp.le)]
    have weight := seed_count_bound hx (k X)
    have powBound := mul_lt_mul_of_pos_right hs' lp
    have lower := mul_le_mul_of_nonneg_left low ep.le
    nlinarith only [weight,rootBound,powBound,lower,mul_pos (mul_pos ep lp) xp]) xl.le

#print axioms candidate_weight
#print axioms seed_count_bound
#print axioms covered_prime_fraction

end CunninghamChain.OrbitCover
