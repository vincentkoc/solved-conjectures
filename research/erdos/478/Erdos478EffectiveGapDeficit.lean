import Erdos478ResolventScale
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos478DisjointGapFamilies

/-!
# Factorial deficits at explicitly bounded primes

A separable splitting prime for the falling-factorial gap of length `n`
has at least `n` repeated upper endpoints in the factorial sequence.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial
open scoped Polynomial

/-- For every prescribed gap length at least two, a prime with at least
that many repeated endpoints is bounded explicitly in terms of the length. -/
theorem factorial_deficit_bounded_prime (n : ℕ) (hn : 2≤n) :
    ∃ p ≤ splitBound n (n+1), p.Prime ∧ n < p ∧
      (FallingGap.gap (ZMod p) n).Splits ∧ (FallingGap.gap (ZMod p) n).Separable ∧
      ((Ico 1 p).image (fun j => j.factorial % p)).card + n ≤ p-1 := by
  let f : ℤ[X] := descPochhammer ℤ n-1
  have hmap (K : Type) [CommRing K] : f.map (Int.castRingHom K) = descPochhammer K n-1 := by
    simp [f]
  have hdeg : f.IsMonicOfDegree n := by
    have hm : (descPochhammer ℤ n).IsMonicOfDegree n :=
      ⟨descPochhammer_natDegree ℤ n,monic_descPochhammer ℤ n⟩
    simpa only [f,sub_eq_add_neg] using hm.add_right (q := -(1 : ℤ[X])) (by simpa using (by omega : 0<n))
  have hQ := (GapFamilies.irreducible_gap_rat (by omega : 0<n)).separable
  have hC : (f.map (Int.castRingHom ℂ)).Separable := by
    rw [hmap ℂ]
    simpa using hQ.map (f := algebraMap ℚ ℂ)
  obtain ⟨p,hp,hprime,hs,hd⟩ := bounded_splitting_prime f hdeg.monic hdeg.natDegree_eq
    (by omega) (show 0<n+1 by omega) hC (fun z hz => by
      rw [hmap ℂ] at hz
      simpa using gap_root_norm (by omega : 0<n) hz)
  let : Fact p.Prime := ⟨hprime⟩
  rw [hmap (ZMod p)] at hs hd
  have hh := FallingGap.card_add_of_splits n hn hs hd
  exact ⟨p,hp,hprime,by omega,hs,hd,hh⟩

/-- A simpler double-exponential upper bound for a witness at each length. -/
theorem explicit_gap_prime (n : ℕ) (hn : 2≤n) :
    ∃ p ≤ 2^((n+2)^(3*n+8)), p.Prime ∧ n < p ∧
      (FallingGap.gap (ZMod p) n).Splits ∧ (FallingGap.gap (ZMod p) n).Separable ∧
      ((Ico 1 p).image (fun j => j.factorial % p)).card + n ≤ p-1 := by
  obtain ⟨p,hp,h₁,h₂,h₃⟩ := factorial_deficit_bounded_prime n hn
  exact ⟨p,hp.trans (splitBound_gap_le n hn),h₁,h₂,h₃⟩

private theorem loglog_bound {n p : ℕ} (hn : 2≤n) (hp : n<p) (h : p≤2^((n+2)^(3*n+8))) :
    Real.log (Real.log p) ≤ (3*(n:ℝ)+8)*Real.log (n+2) := by
  have hr : (p:ℝ) ≤ (2:ℝ)^((n+2)^(3*n+8)) := by exact_mod_cast h
  have hl := Real.log_le_log (by exact_mod_cast (by omega : 0<p)) hr
  rw [Real.log_pow] at hl
  have h₂ : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have hl' : Real.log p ≤ (((n+2)^(3*n+8) : ℕ):ℝ) :=
    hl.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _))
  have hx := Real.log_le_log (Real.log_pos (by exact_mod_cast (by omega : 1<p))) hl'
  push_cast at hx
  simpa [Real.log_pow] using hx

/-- For each positive `ε`, arbitrarily large primes miss at least
`log log p / ((3+ε) log log log p)` residues from the upstream factorial image. -/
theorem frequently_logarithmic_deficit (ε : ℝ) (hε : 0<ε) :
    ∃ᶠ p : ℕ in Filter.atTop, p.Prime ∧ 1 ≤ Real.log (Real.log (Real.log p)) ∧
      Real.log (Real.log p) ≤ (3+ε)*
        (p-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*Real.log (Real.log (Real.log p)) := by
  have htop : Filter.Tendsto (fun p : ℕ => Real.log (Real.log (Real.log p))) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp (htop.eventually_ge_atTop 1)
  obtain ⟨k,hk⟩ := exists_nat_gt (8/ε)
  apply Filter.frequently_atTop'.mpr
  intro N
  let n := max (max N L) (max k 2)
  have hn : 2≤n := le_trans (le_max_right ..) (le_max_right ..)
  have hkn : k≤n := le_trans (le_max_left ..) (le_max_right ..)
  obtain ⟨p,hp,hprime,hpn,_,_,hh⟩ := explicit_gap_prime n hn
  have hNp : N<p := lt_of_le_of_lt (le_trans (le_max_left ..) (le_max_left ..)) hpn
  have hpL : L≤p := le_trans (le_trans (le_max_right ..) (le_max_left ..)) hpn.le
  let D := p-((Ico 1 p).image (fun j => j.factorial % p)).card
  have hd : (n:ℝ)+1 ≤ D := by exact_mod_cast (by dsimp [D]; omega : n+1≤D)
  let T := Real.log (Real.log p)
  have hT : 1 ≤ Real.log T := hL p hpL
  refine ⟨p,hNp,hprime,hT,?_⟩
  change T ≤ (3+ε)*(D:ℝ)*Real.log T
  have h8 : 8 ≤ ε*(n:ℝ) := by
    have hl : 8/ε < (n:ℝ) := hk.trans_le (by exact_mod_cast hkn)
    linarith [(div_lt_iff₀ hε).mp hl]
  have hconst : 3*(n:ℝ)+8 ≤ (3+ε)*(D:ℝ) := by
    have h' := mul_le_mul_of_nonneg_left hd (by linarith : 0≤3+ε)
    nlinarith
  by_cases h : (n:ℝ)+2 ≤ T
  · exact (loglog_bound hn hpn hp).trans (mul_le_mul hconst
      (Real.log_le_log (by positivity) h) (Real.log_nonneg (by linarith)) (by positivity))
  · have h' : (n:ℝ)+2 ≤ (3+ε)*(D:ℝ) := by linarith
    exact (le_of_not_ge h).trans (h'.trans (le_mul_of_one_le_right (by positivity) hT))

#print axioms frequently_logarithmic_deficit
#print axioms explicit_gap_prime
#print axioms factorial_deficit_bounded_prime
end Erdos478.EffectiveResolvent
