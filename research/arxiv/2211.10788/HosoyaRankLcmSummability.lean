import HosoyaLargestPrimeBlock
import HosoyaLogRankShells
import HosoyaRoughCofactorMass
import ThetaReciprocalBlocks

/-! Absolute convergence of the reciprocal Fibonacci rank-lcm series with
a quantitative tail in its largest prime factor. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Real

def topPrime (n : ℕ) : ℕ := if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 0

private lemma topPrime_mem {n : ℕ} (h : topPrime n ≠ 0) : topPrime n∈n.primeFactors := by
  by_cases ne : n.primeFactors.Nonempty
  · rw [topPrime,dif_pos ne]
    exact max'_mem _ _
  · exact False.elim (h (by simp only [topPrime,dif_neg ne]))

private lemma smooth_at_top {n : ℕ} (hn : n≠0) {b : ℕ} (h : topPrime n < b) : n∈b.smoothNumbers := by
  apply Nat.mem_smoothNumbers'.mpr
  intro p pr pn
  have mem := pr.mem_primeFactors pn hn
  have ne : n.primeFactors.Nonempty := ⟨p,mem⟩
  exact lt_of_le_of_lt (n.primeFactors.le_max' p mem) (by simpa only [topPrime,dif_pos ne] using h)

private lemma one_block {p : ℕ} (hp : p.Prime) (h5 : p≠5) (euler : smoothEuler p≤2*exp 4*log p)
    (S : Finset ℕ) (hs : ∀ n∈S, topPrime n=p) :
    ∑ n ∈ S, lcmWeight n ≤ (4*exp 4)*logRootWeight p := by
  have block := largest_prime_block hp h5 S (by
    intro n hn
    have eq := hs n hn
    have mem : p∈n.primeFactors := eq ▸ topPrime_mem (eq ▸ hp.ne_zero)
    have np : n≠0 := (Nat.mem_primeFactors.mp mem).2.2
    exact ⟨Nat.dvd_of_mem_primeFactors mem,smooth_at_top np (by omega)⟩)
  apply block.trans
  have card : ((returnRank p).divisors.card:ℝ) ≤ 2*√(returnRank p:ℝ) := by
    have c := Arxiv.«2501.03234».ThetaReciprocalBlocks.divisors_card_sqrt (returnRank p)
    have cast : ((returnRank p).divisors.card:ℝ) ≤ 2*((returnRank p).sqrt:ℝ) := by exact_mod_cast c
    exact cast.trans (by gcongr; exact Real.nat_sqrt_le_real_sqrt)
  have w : 0≤rankWeight p := by unfold rankWeight; positivity
  have lg : 0≤log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  calc _ ≤ (2*√(returnRank p:ℝ))*rankWeight p*(2*exp 4*log p) := by
            calc _ ≤ ((returnRank p).divisors.card:ℝ)*rankWeight p*(2*exp 4*log p) :=
                        mul_le_mul_of_nonneg_left euler (by positivity)
                 _ ≤ _ := by gcongr
       _ = _ := by rw [logRootWeight,rootWeight_eq hp]; ring

/-- Weighted reciprocal mass of all integers with a large prime factor.
The constant and the lower threshold are independent of the finite set. -/
theorem rankLcm_largest_tail : ∀ᶠ K : ℕ in atTop, ∀ S : Finset ℕ, (∀ n∈S, K^2 ≤ topPrime n) →
    ∑ n ∈ S, lcmWeight n ≤ (64*exp 4)*(log (2*(K:ℝ))+4)/√(K:ℝ) := by
  obtain ⟨M,euler⟩ := eventually_atTop.mp CunninghamChain.prime_euler_product_log_bounds
  filter_upwards [eventually_ge_atTop (max M 64)] with K large S hs
  have hk : 64≤K := (le_max_right ..).trans large
  have ksq : K≤K^2 := by simpa only [pow_two] using Nat.le_mul_of_pos_right K (show 0<K by omega)
  let P := S.image topPrime
  have pp {p : ℕ} (hp : p∈P) : p.Prime ∧ K^2 ≤ p := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hp
    have lo := hs n hn
    exact ⟨Nat.prime_of_mem_primeFactors (topPrime_mem (by omega)),lo⟩
  rw [←sum_fiberwise_of_maps_to (s:=S) (t:=P) (g:=topPrime)
    (fun n hn => mem_image_of_mem _ hn) lcmWeight]
  calc _ ≤ ∑ p ∈ P, (4*exp 4)*logRootWeight p := by
            apply sum_le_sum
            intro p hp
            obtain ⟨pr,lo⟩ := pp hp
            apply one_block pr (by omega) (euler p ((le_max_left M 64).trans (large.trans (ksq.trans lo)))).2
            intro n hn
            exact (mem_filter.mp hn).2
       _ ≤ (4*exp 4)*(16*(log (2*(K:ℝ))+4)/√(K:ℝ)) := by
            rw [←mul_sum]
            exact mul_le_mul_of_nonneg_left (log_root_rank_tail hk P (fun _ h => pp h)) (by positivity)
       _ = _ := by ring

/-- The ordinary Fibonacci rank-lcm majorant from Sanna and Tron's Lemma 3.2.
It bounds the compatible terms for every shifted upper-value gcd progression. -/
theorem rankLcm_summable : Summable lcmWeight := by
  obtain ⟨K0,bound⟩ := eventually_atTop.mp rankLcm_largest_tail
  let K := max K0 64
  let C := smoothEuler (K^2)+(64*exp 4)*(log (2*(K:ℝ))+4)/√(K:ℝ)
  have allS (S : Finset ℕ) (nz : ∀ n∈S, n≠0) : ∑ n ∈ S, lcmWeight n≤C := by
    let A := S.filter fun n => K^2≤topPrime n
    let B := S.filter fun n => ¬K^2≤topPrime n
    have hi := bound K (le_max_left ..) A (fun _ h => (mem_filter.mp h).2)
    have lo : ∑ n ∈ B, lcmWeight n ≤ smoothEuler (K^2) := by
      apply le_trans _ (smooth_harmonic_bound _ B (by
        intro n hn
        obtain ⟨mem,lt⟩ := mem_filter.mp hn
        exact smooth_at_top (nz n mem) (by omega)))
      apply sum_le_sum
      intro n hn
      have np := Nat.pos_of_ne_zero (nz n (mem_filter.mp hn).1)
      apply inv_anti₀ (by exact_mod_cast np)
      exact_mod_cast Nat.le_of_dvd (Nat.lcm_pos np (rank_pos_all np)) (Nat.dvd_lcm_left n (returnRank n))
    have sumEq : (∑ n ∈ A, lcmWeight n)+(∑ n ∈ B, lcmWeight n)=∑ n ∈ S, lcmWeight n :=
      sum_filter_add_sum_filter_not ..
    dsimp [C]
    linarith
  apply summable_of_sum_le (c:=C) (fun n => by unfold lcmWeight; positivity)
  intro S
  have h := allS (S.erase 0) (fun _ mem => (mem_erase.mp mem).1)
  by_cases e : 0∈S
  · rw [←sum_erase_add _ _ e]
    simpa [lcmWeight,rankLcm] using h
  · simpa [erase_eq_of_notMem e] using h

#print axioms rankLcm_largest_tail
#print axioms rankLcm_summable

end Arxiv.«2211.10788».IndexDivisors
