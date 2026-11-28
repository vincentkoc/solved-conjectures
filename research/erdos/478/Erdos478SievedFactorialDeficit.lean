import Erdos478SievedEvenScale
import Erdos478SievedLogInversion
import Erdos478EvenGapDeficit

/-!
# An elementary factorial deficit with leading constant one

Bounded simultaneous collisions at all even gaps give a second-order
logarithmic deficit for the exact factorial image and prime filter of Erdős 478.
Here the deficit counts only nonzero missing residue classes.
-/

namespace Erdos478.EffectiveResolvent
open Finset Filter Real

/-- One prime in the explicit range has two separate endpoints per even gap. -/
theorem sieved_even_prime (n : ℕ) (hn : 0<n) :
    ∃ p ≤ 2^((2*n+4)^(2*n+17)), p.Prime ∧ 2*n<p ∧
      (∏ i : Fin n, (descPochhammer (ZMod p) (2*(i.val+1))-1)).Separable ∧
      (∀ i : Fin n, ∃ z w : ZMod p, z ≠ w ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot z ∧
        (descPochhammer (ZMod p) (2*(i.val+1))-1).IsRoot w) ∧
      ((Ico 1 p).image (fun j => j.factorial % p)).card+2*n ≤ p-1 := by
  obtain ⟨p,hp,h⟩ := simultaneous_even_with sievedSchur n hn
  exact ⟨p,hp.trans (sieved_even_bound n),h⟩

/-- Infinitely often on the pinned prime filter, `F(p) ≥ T/(log T-log log T+ε)`
for `T = log log p` and the number `F(p)` of missing nonzero residues. -/
theorem frequently_sieved_deficit (ε : ℝ) (hε : 0<ε) :
    ∃ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime},
      let T := log (log p)
      exp 1 ≤ log T ∧ T ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*
        (log T-log (log T)+ε) := by
  obtain ⟨X,Y,hinv⟩ := SchurSieve.invert_ceiling ε hε
  have htop : Tendsto (fun p : ℕ => log (log (log p))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hdouble : Tendsto (fun p : ℕ => log (log p)) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((htop.eventually_ge_atTop (max (exp 1) Y)).and (hdouble.eventually_ge_atTop 1))
  obtain ⟨k,hk⟩ := exists_nat_gt X
  apply frequently_inf_principal.mpr
  apply frequently_atTop'.mpr
  intro N
  let n := max (max k L) (max N 2)
  have hn : 2≤n := le_trans (le_max_right ..) (le_max_right ..)
  have hkn : k≤n := le_trans (le_max_left ..) (le_max_left ..)
  obtain ⟨p,hp,hprime,hlen,_,_,hh⟩ := sieved_even_prime n (by omega)
  have hNp : N<p := (le_trans (le_max_left ..) (le_max_right ..) : N≤n).trans_lt (by omega)
  have hpL : L≤p := (le_trans (le_max_right ..) (le_max_left ..) : L≤n).trans (by omega)
  let T := log (log p)
  obtain ⟨h1,hY⟩ := max_le_iff.mp (hL p hpL).1
  have hT : 0<T := zero_lt_one.trans_le (hL p hpL).2
  have hx : X≤2*(n:ℝ) := by
    have := hk.trans_le (by exact_mod_cast hkn : (k:ℝ) ≤ n)
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have bound : T≤(2*(n:ℝ)+17)*log (2*n+4) := by
    simpa [T, Nat.cast_add, Nat.cast_mul] using loglog_power_ceiling (by omega : 1<p) hp
  have hi := hinv (2*(n:ℝ)) T hx hY hT bound
  have hd : 2*(n:ℝ) ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ) := by
    exact_mod_cast (by omega : 2*n≤p-1-((Ico 1 p).image (fun j => j.factorial % p)).card)
  have hy : 0 < log T := (exp_pos 1).trans_le h1
  have hc : 0≤ log T-log (log T)+ε := by linarith [log_le_sub_one_of_pos hy]
  exact ⟨p,hNp,hprime,h1,hi.trans (mul_le_mul_of_nonneg_right hd hc)⟩

/-- The Banks–Luca–Shparlinski–Stichtenoth leading constant for the nonzero
deficit, now from the bounded simultaneous even-gap construction. -/
theorem frequently_unit_deficit :
    ∃ᶠ p : ℕ in atTop ⊓ principal {p : ℕ | p.Prime},
      let T := log (log p)
      exp 1 ≤ log T ∧ T ≤ (p-1-((Ico 1 p).image (fun j => j.factorial % p)).card : ℕ)*log T := by
  apply (frequently_sieved_deficit 1 (by norm_num)).mono
  intro p h
  dsimp only at h ⊢
  refine ⟨h.1,h.2.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))⟩
  have hlog := log_le_log (exp_pos 1) h.1
  rw [log_exp] at hlog
  linarith

#print axioms sieved_even_prime
#print axioms frequently_sieved_deficit
#print axioms frequently_unit_deficit

end Erdos478.EffectiveResolvent
