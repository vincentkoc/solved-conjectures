import Erdos478EvenGapScale
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A logarithmic deficit from simultaneous even gaps

Reflection provides two distinct factorial collision endpoints per gap
at a prime selected by the smaller joint-root polynomial.
-/

namespace Erdos478.EffectiveResolvent
open Finset

/-- An explicit bound for a prime simultaneously witnessing every even
gap through `2n`, with at least `2n` distinct collision endpoints. -/
theorem explicit_even_gap_prime (n : ℕ) (hn : 0<n) :
    ∃ p ≤ 2^((2*n+4)^(3*n+9)), p.Prime ∧ 2*n<p ∧
      (∏ i : Fin n, (descPochhammer (ZMod p) (2*(i.val+1))-1)).Separable ∧
      (∀ i : Fin n, ∃ z w : ZMod p, z ≠ w ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot z ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot w) ∧
      ((Ico 1 p).image (fun j => j.factorial % p)).card+2*n ≤ p-1 := by
  obtain ⟨p,hp,h⟩ := simultaneous_even_prime n hn
  exact ⟨p,hp.trans (evenWitnessBound_le n hn),h⟩

private theorem loglog_bound {n p : ℕ} (hn : 2≤n) (hp : n<p) (h : p≤2^((2*n+4)^(3*n+9))) :
    Real.log (Real.log p) ≤ (3*(n:ℝ)+9)*Real.log (2*n+4) := by
  have hr : (p:ℝ) ≤ (2:ℝ)^((2*n+4)^(3*n+9)) := by exact_mod_cast h
  have hl := Real.log_le_log (by exact_mod_cast (by omega : 0<p)) hr
  rw [Real.log_pow] at hl
  have h₂ : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hl' : Real.log p ≤ (((2*n+4)^(3*n+9) : ℕ):ℝ) :=
    hl.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _))
  have hx := Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1<p))) hl'
  push_cast at hx
  simpa [Real.log_pow] using hx

/-- For each positive `ε`, arbitrarily large primes miss at least
`log log p / ((3/2+ε) log log log p)` residues from the upstream factorial image. -/
theorem frequently_even_gap_deficit (ε : ℝ) (hε : 0<ε) :
    ∃ᶠ p : ℕ in Filter.atTop, p.Prime ∧ 1 ≤ Real.log (Real.log (Real.log p)) ∧
      Real.log (Real.log p) ≤ (3/2+ε)*
        (p-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*Real.log (Real.log (Real.log p)) := by
  have htop : Filter.Tendsto (fun p : ℕ => Real.log (Real.log (Real.log p))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop 1)
  obtain ⟨k,hk⟩ := exists_nat_gt (9/ε)
  apply Filter.frequently_atTop'.mpr
  intro N
  let n := max (max N L) (max k 2)
  have hn : 2≤n := le_trans (le_max_right ..) (le_max_right ..)
  have hkn : k≤n := le_trans (le_max_left ..) (le_max_right ..)
  obtain ⟨p,hp,hprime,hlen,_,_,hh⟩ := explicit_even_gap_prime n (by omega)
  have hpn : n<p := by omega
  have hNp : N<p := lt_of_le_of_lt (le_trans (le_max_left ..) (le_max_left ..)) hpn
  have hpL : L≤p := le_trans (le_trans (le_max_right ..) (le_max_left ..)) hpn.le
  let D := p-((Ico 1 p).image (fun j => j.factorial % p)).card
  have hd : 2*(n:ℝ)+1 ≤ D := by exact_mod_cast (by dsimp [D]; omega : 2*n+1≤D)
  let T := Real.log (Real.log p)
  have hT : 1 ≤ Real.log T := hL p hpL
  refine ⟨p,hNp,hprime,hT,?_⟩
  change T ≤ (3/2+ε)*(D:ℝ)*Real.log T
  have h9 : 9 ≤ ε*(n:ℝ) := by
    have hl : 9/ε < (n:ℝ) := hk.trans_le (by exact_mod_cast hkn)
    linarith [(div_lt_iff₀ hε).mp hl]
  have hconst : 3*(n:ℝ)+9 ≤ (3/2+ε)*(D:ℝ) := by
    have h' := mul_le_mul_of_nonneg_left hd (by linarith : 0≤3/2+ε)
    nlinarith only [h',h9,hε]
  have hcoef : 0 ≤ (3/2+ε)*(D:ℝ) := mul_nonneg (by linarith only [hε]) (Nat.cast_nonneg _)
  have hn₀ : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hbase : 1 ≤ 2*(n:ℝ)+4 := by linarith only [hn₀]
  by_cases h : 2*(n:ℝ)+4 ≤ T
  · exact (loglog_bound hn hpn hp).trans (mul_le_mul hconst
      (Real.log_le_log (by linarith only [hbase]) h) (Real.log_nonneg hbase) hcoef)
  · have h' : 2*(n:ℝ)+4 ≤ (3/2+ε)*(D:ℝ)  := by linarith only [hconst, show (0:ℝ) ≤ n by positivity]
    exact (le_of_not_ge h).trans (h'.trans (le_mul_of_one_le_right hcoef hT))

#print axioms frequently_even_gap_deficit
#print axioms explicit_even_gap_prime
end Erdos478.EffectiveResolvent
