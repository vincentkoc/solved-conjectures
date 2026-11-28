import Erdos478AbundanceCutoff
import Erdos478AbundanceRate
import Erdos478SievedLogInversion

/-!
# Abundance of factorial-deficit witnesses at every large cutoff

For `T = log log X`, at least `exp (exp (c T / log T))` primes through
`X` satisfy the second-order deficit bound with leading constant one.
All these primes witness the same initial family of even gap lengths.
-/

namespace Erdos478.EffectiveResolvent
open Finset Real Filter
open scoped Classical

/-- A common growing list of even gaps works at every prime counted below
the cutoff. The constant in the count depends on the denominator error. -/
theorem abundant_even_gaps (ε : ℝ) (hε : 0<ε) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop,
      let T := log (log X)
      ∃ n : ℕ, 0<n ∧ exp (max 1 ε) ≤ log T ∧
        T ≤ 2*(n:ℝ)*(log T-log (log T)+ε) ∧
        exp (exp (c*(T/log T))) ≤ (((range (X+1)).filter (EvenGapWitness n)).card : ℝ) := by
  obtain ⟨d,hdε⟩ := exists_nat_gt (16/ε)
  have hdpos : 0<d := by exact_mod_cast ((by positivity : 0<(16:ℝ)/ε).trans hdε)
  have hscale : (16:ℝ) ≤ ε*d := by
    have h := (div_lt_iff₀ hε).mp hdε
    linarith only [h,mul_comm (d:ℝ) ε]
  let c : ℝ := 1/(16*d)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  obtain ⟨U,V,hinv⟩ := SchurSieve.invert_shifted_ceiling 21 6 ε (by norm_num) (by norm_num) hε
  obtain ⟨k,hk⟩ := exists_nat_gt U
  let N := max (2*d) (k+1)
  have hdouble : Tendsto (fun X : ℕ => log (log X)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have htriple := tendsto_log_atTop.comp hdouble
  filter_upwards [eventually_ge_atTop (abundanceCeiling N d),
    htriple.eventually_ge_atTop (max (exp (max 1 ε)) V),
    hdouble.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with X hX hlog hT' hX2
  let T := log (log X)
  have hT : 0<T := zero_lt_one.trans_le hT'
  obtain ⟨hlarge,hV⟩ := max_le_iff.mp hlog
  change exp (max 1 ε) ≤ log T at hlarge
  obtain ⟨n,hN,hnX,hnext⟩ := bracket hX
  have hd : 2*d≤n := (le_max_left ..).trans hN
  have hn : 0<n := by omega
  have hk' : k≤n := (show k ≤ N by dsimp [N]; omega).trans hN
  have hx : U≤2*(n:ℝ) := by
    have h := hk.trans_le (by exact_mod_cast hk' : (k:ℝ)≤n)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have upper := loglog_successor (by omega : 1<X) hnext.le
  have cost := exclusion_cost hdpos hd hscale
  have hi := hinv (2*(n:ℝ)) T hx hV hT (by dsimp [T]; linarith only [upper,cost])
  have hlogT : 0 < log T := (exp_pos _).trans_le hlarge
  have hεlog : ε ≤ log (log T) := by
    have h := log_le_log (exp_pos _) hlarge
    rw [log_exp] at h
    exact (le_max_right ..).trans h
  have hratio : T/log T ≤ 2*(n:ℝ) := (div_le_iff₀ hlogT).mpr
    (hi.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))
  have harg : c*(T/log T) ≤ (2*(n:ℝ))/(16*d) := by
    calc
      _ ≤ c*(2*n) := mul_le_mul_of_nonneg_left hratio hc.le
      _ = _ := by dsimp [c]; ring
  refine ⟨n,hn,hlarge,hi,(exp_le_exp.mpr (exp_le_exp.mpr harg)).trans ?_⟩
  exact (count_exponential hdpos hd).trans (by exact_mod_cast (count_at_cutoff hn hnX).le)

/-- For every large cutoff the same abundance estimate counts primes by the
number of missing nonzero residues in the pinned factorial image. -/
theorem abundant_factorial_deficit (ε : ℝ) (hε : 0<ε) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop,
      let T := log (log X)
      exp (max 1 ε) ≤ log T ∧ exp (exp (c*(T/log T))) ≤
        (((range (X+1)).filter fun p => p.Prime ∧
          T ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*
            (log T-log (log T)+ε)).card : ℝ) := by
  obtain ⟨c,hc,h⟩ := abundant_even_gaps ε hε
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with X hX
  let T := log (log X)
  obtain ⟨n,_,hlarge,hi,hcount⟩ := hX
  have hlogT : 0 < log T := (exp_pos _).trans_le hlarge
  have hden : 0≤log T-log (log T)+ε := by linarith [log_le_sub_one_of_pos hlogT]
  refine ⟨hlarge,hcount.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro p hp
  obtain ⟨hpX,hw⟩ := mem_filter.mp hp
  obtain ⟨hprime,_,_,_,hdef⟩ := hw
  apply mem_filter.mpr
  refine ⟨hpX,hprime,hi.trans (mul_le_mul_of_nonneg_right ?_ hden)⟩
  exact_mod_cast (by omega : 2*n≤p-1-((Ico 1 p).image (fun j => j.factorial % p)).card)

#print axioms abundant_even_gaps
#print axioms abundant_factorial_deficit

end Erdos478.EffectiveResolvent
