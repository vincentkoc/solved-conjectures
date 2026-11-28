import Erdos478CompleteEvenCeiling
import Erdos478SievedLogInversion
import Erdos478EvenGapDeficit

/-!
# A doubled leading constant for missing nonzero factorial residues

For arbitrarily large primes, twice the double logarithm of the prime
is bounded by the nonzero deficit times its triple logarithm. The
effective construction forces complete splitting at every even gap
through a common cutoff.
-/

namespace Erdos478.EffectiveResolvent
open Finset Filter Real

private theorem invert_paired_ceiling (ε : ℝ) (hε : 0<ε) :
    ∃ A B : ℝ, ∀ n : ℕ, ∀ T : ℝ, A ≤ n → B ≤ log T → 0<T →
      T ≤ ((n:ℝ)*(n+1)+34)*log (2*n+4) →
      2*T ≤ (n:ℝ)*(n+1)*(log T-log (log T)+log 32+ε) := by
  obtain ⟨X,Y,hinv⟩ := SchurSieve.invert_shifted_ceiling 544 16 ε (by norm_num) (by norm_num) hε
  refine ⟨max X 1,max Y 1,?_⟩
  intro n T hn hY hT hceil
  let x : ℝ := (n:ℝ)*(n+1)/2
  have hn' : (1:ℝ) ≤ n := (le_max_right ..).trans hn
  have hx : 0≤x := by dsimp [x]; positivity
  have hX : X≤32*x := by
    apply ((le_max_left ..).trans hn).trans
    dsimp [x]; nlinarith [sq_nonneg (n:ℝ)]
  have hy : 0<log T := zero_lt_one.trans_le ((le_max_right ..).trans hY)
  have hlog : log T ≤ log (32*T) := log_le_log hT (by linarith)
  have harg : (2*(n:ℝ)+4)^2 ≤ 32*x+16 := by dsimp [x]; nlinarith [sq_nonneg (n:ℝ)]
  have hs := log_le_log (show 0<(2*(n:ℝ)+4)^2 by positivity) harg
  rw [log_pow] at hs
  have hb : T ≤ (x+17)*log (32*x+16) := by
    have hscale := mul_le_mul_of_nonneg_left hs (show 0≤x+17 by linarith)
    apply hceil.trans
    convert hscale using 1
    dsimp [x]
    ring
  have hh : 32*T ≤ (32*x+544)*log (32*x+16)+(ε/4)*(32*x) := by
    have := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 32)
    nlinarith only [this,mul_nonneg hε.le hx]
  have h := hinv (32*x) (32*T) hX (((le_max_left ..).trans hY).trans hlog) (by positivity) hh
  have hll := log_le_log hy hlog
  rw [log_mul (by norm_num) hT.ne'] at h hll
  have hcmp := mul_le_mul_of_nonneg_left hll hx
  have hx' : 2*x = (n:ℝ)*(n+1) := by dsimp [x]; ring
  rw [← hx']
  nlinarith only [h,hcmp]

/-- A second-order bound for the number of missing nonzero classes on the
exact prime filter and factorial image of Erdős 478. -/
theorem frequently_paired_deficit (ε : ℝ) (hε : 0<ε) :
    ∃ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime},
      let T := log (log p)
      exp (log 32+ε) ≤ log T ∧ 2*T ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*
        (log T-log (log T)+log 32+ε) := by
  obtain ⟨A,B,hinv⟩ := invert_paired_ceiling ε hε
  have ht : Tendsto (fun p : ℕ => log (log (log p))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have ht' : Tendsto (fun p : ℕ => log (log p)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((ht.eventually_ge_atTop (max (exp (log 32+ε)) B)).and (ht'.eventually_ge_atTop 1))
  obtain ⟨k,hk⟩ := exists_nat_gt A
  apply frequently_inf_principal.mpr
  apply frequently_atTop'.mpr
  intro N
  let n := max (max k L) N + 1
  have hn : 0<n := Nat.zero_lt_succ _
  obtain ⟨p,hp,hprime,_,_,hc⟩ := complete_even_prime n hn
  have hn' : n ≤ n*(n+1) := by simpa using Nat.mul_le_mul_left n (show 1≤n+1 by omega)
  have hp' := hprime.two_le
  have hnp : n<p := by omega
  have hmax : max (max k L) N < n := Nat.lt_succ_self _
  have hkn : k≤n := ((le_max_left k L).trans (le_max_left ..)).trans hmax.le
  have hLn : L≤n := ((le_max_right k L).trans (le_max_left ..)).trans hmax.le
  have hNp := ((le_max_right (max k L) N).trans_lt hmax).trans hnp
  let T := log (log p)
  obtain ⟨hlog,hB⟩ := max_le_iff.mp (hL p (hLn.trans hnp.le)).1
  have hT : 0<T := zero_lt_one.trans_le (hL p (hLn.trans hnp.le)).2
  have hceil : T ≤ ((n:ℝ)*(n+1)+34)*log (2*n+4) := by
    simpa [T] using loglog_power_ceiling (by omega : 1<p) hp
  have h := hinv n T (hk.le.trans (by exact_mod_cast hkn)) hB hT hceil
  have hd : (n:ℝ)*(n+1) ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ) := by
    exact_mod_cast (by omega : n*(n+1)≤p-1-((Ico 1 p).image (fun j => j.factorial % p)).card)
  have hy : 0<log T := (exp_pos _).trans_le hlog
  have hs : 0≤log T-log (log T)+log 32+ε := by linarith [log_le_sub_one_of_pos hy,log_nonneg (by norm_num : (1:ℝ)≤32)]
  exact ⟨p,hNp,hprime,hlog,h.trans (mul_le_mul_of_nonneg_right hd hs)⟩

theorem frequently_double_deficit :
    ∃ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime},
      let T := log (log p)
      exp 1 ≤ log T ∧ 2*T ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*log T := by
  apply (frequently_paired_deficit 1 (by norm_num)).mono
  intro p h
  dsimp only at h ⊢
  have hs := log_le_log (exp_pos _) h.1
  rw [log_exp] at hs
  have h32 := log_nonneg (by norm_num : (1:ℝ) ≤ 32)
  exact ⟨(exp_le_exp.mpr (by linarith)).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))⟩

#print axioms frequently_paired_deficit
#print axioms frequently_double_deficit

end Erdos478.EffectiveResolvent
