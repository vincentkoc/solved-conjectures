import ThetaFactorialSequence
import Mathlib.NumberTheory.Chebyshev

/-! A modulus of logarithmic size O(T) captures all denominators through T.
Its saturated prime-power divisors are at least T². -/
namespace Arxiv.«2501.03234».ThetaCompactModulus
open Finset Real Chebyshev ThetaDivisorLogMean ThetaFactorialRows ThetaSmoothRows
noncomputable section

def modulus (T : ℕ) := (Nat.lcmUpto T)^4
def block (T p : ℕ) := (p^(p.log T))^4

theorem positive (T : ℕ) : 0< modulus T := pow_pos (Nat.lcmUpto_pos T) _

theorem contains {T d : ℕ} (hd : 0<d) (h : d≤T) : d∣modulus T :=
  (show d∣Nat.lcmUpto T from dvd_lcm (mem_Icc.mpr ⟨hd,h⟩)).trans (dvd_pow_self _ (by decide))

theorem size (T : ℕ) : log (modulus T:ℝ) ≤ 4*(log 4+4)*T := by
  simp only [modulus,Nat.cast_pow,log_pow,←psi_eq_log_lcmUpto,Nat.cast_ofNat]
  linarith only [psi_le_const_mul_self (Nat.cast_nonneg T : 0≤(T:ℝ))]

theorem smooth {T p : ℕ} (hp : p∈(modulus T).primeFactors) : p≤T := by
  obtain ⟨hpr,hd,_⟩ := Nat.mem_primeFactors.mp hp
  exact (Nat.Prime.dvd_factorial hpr).mp ((hpr.dvd_of_dvd_pow hd).trans (Nat.lcmUpto_dvd_factorial T))

theorem bulk (T : ℕ) : (harmonic T:ℝ)≤ mass (modulus T) := by
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd; exact Nat.mem_divisors.mpr ⟨contains (mem_Icc.mp hd).1 (mem_Icc.mp hd).2,(positive T).ne'⟩
  · intros; positivity

theorem block_bounds {T p : ℕ} (hp : 2≤p) (hpT : p≤T) :
    T^2 ≤ block T p ∧ block T p≤T^4 := by
  let w := p^(p.log T)
  have hle : w≤T := Nat.pow_log_le_self p (by omega : T≠0)
  have hpw : p≤w := by
    exact Nat.le_self_pow (Nat.ne_of_gt (Nat.log_pos_iff.mpr ⟨hpT,by omega⟩)) _
  have hlt := Nat.lt_pow_succ_log_self (by omega : 1<p) T
  rw [pow_succ] at hlt
  have hs : T≤w^2 := hlt.le.trans (by simpa [pow_two,w] using Nat.mul_le_mul_left w hpw)
  refine ⟨(Nat.pow_le_pow_left hs 2).trans_eq ?_,Nat.pow_le_pow_left hle 4⟩
  change (w^2)^2=w^4; ring

theorem saturated {T d p : ℕ} (hp : p.Prime) (hpT : p≤T) (hpd : p∣d/((modulus T).gcd d)) :
    block T p∣(modulus T).gcd d := by
  let m := modulus T
  let g := m.gcd d
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (positive T)
  have he : g*(m/g)=m := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hc : (m/g).Coprime (d/g) := Nat.coprime_div_gcd_div_gcd hg
  have hn : ¬p∣m/g := fun h => hp.not_dvd_one (hc ▸ Nat.dvd_gcd h hpd)
  let w := p^(p.log T)
  have hwt : w≤T := Nat.pow_log_le_self p (by have := hp.two_le; omega : T≠0)
  have hw : w∣Nat.lcmUpto T := dvd_lcm (mem_Icc.mpr ⟨pow_pos hp.pos _,hwt⟩)
  have hb : block T p∣g*(m/g) := he.symm ▸ pow_dvd_pow_of_dvd hw 4
  exact (((hp.coprime_iff_not_dvd.mpr hn).pow_left _).pow_left _).dvd_of_dvd_mul_right hb

#print axioms positive
#print axioms contains
#print axioms smooth
#print axioms bulk
#print axioms size
#print axioms block_bounds
#print axioms saturated
end
end Arxiv.«2501.03234».ThetaCompactModulus
