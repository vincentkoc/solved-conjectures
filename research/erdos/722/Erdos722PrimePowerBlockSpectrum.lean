import Erdos722IngredientDilation
import Erdos722CoprimeScales
import Erdos722HananiFour
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The rank-two spectrum for prime-power block sizes

Every sufficiently large admissible order supports a pair design with
blocks of any fixed prime-power size. The order is unrestricted.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet Filter

private theorem iterate {k J c : ℕ} (step : ∀ {l h}, Full k J l h → Full k J (c*l) (c*h))
    {l h : ℕ} (H : Full k J l h) (e : ℕ) : Full k J (c^e*l) (c^e*h) := by
  induction e with
  | zero => simpa using H
  | succ e ih => simpa only [pow_succ',Nat.mul_assoc] using step ih

private theorem coprime_next (m k : ℕ) : m.Coprime (k*m+1) := by
  rw [Nat.add_comm,Nat.coprime_add_mul_right_right]
  simp

theorem eventual_group_counts {k : ℕ} (hpp : IsPrimePow k) (hk : 2≤k) :
    ∃ N, ∀ u ≥ N, u%k≤1 → Local k u := by
  obtain ⟨m,hm,h₁,h₂⟩ := affine_widths hpp hk 1
  let c := k*m+1
  let d := k*c+1
  have hc : 1<c := by have : 0<k*m := Nat.mul_pos (by omega) hm; dsimp [c]; omega
  have hd : 1<d := by have : 0<k*c := Nat.mul_pos (by omega) (by omega); dsimp [d]; omega
  obtain ⟨N,hN⟩ := eventual_arrays (by omega : 2≤c)
  obtain ⟨M,hM⟩ := eventual_arrays (by omega : 2≤d)
  let J := N+M+(c+d)*(k+2)
  have hcj : c*(k+2)≤J := by dsimp [J]; nlinarith only [Nat.zero_le (d*(k+2)),Nat.zero_le N,Nat.zero_le M]
  have hdj : d*(k+2)≤J := by dsimp [J]; nlinarith only [Nat.zero_le (c*(k+2)),Nat.zero_le N,Nat.zero_le M]
  have hJ : 0<J := lt_of_lt_of_le (by positivity) hcj
  obtain ⟨L,hL,h⟩ := seed_interval hpp hk hm (by omega : 0<c) (coprime_next m k) h₁ h₂ (12*J+2)
  let l := L+4*J
  have H : Full k J l (l+1) := by
    refine ⟨by dsimp [l]; omega,?_⟩
    intro u hl hu ha
    exact h u (by dsimp [l] at hl; omega) (by dsimp [l] at hu; omega) ha
  obtain ⟨T,hT⟩ := Scales.scale_cover hc hd (coprime_next c k) (by dsimp [l]; omega : 0<l) (Nat.lt_succ_self l)
  refine ⟨T,?_⟩
  intro u hu ha
  obtain ⟨_,⟨i,j,rfl⟩,hlo,hhi⟩ := hT u hu
  have D := iterate (c:=d) (dilate hk (by positivity) (dvd_mul_right k c) h₂ hM (by dsimp [J]; omega) hdj) H j
  have C := iterate (c:=c) (dilate hk (by positivity) (dvd_mul_right k m) h₁ hN (by dsimp [J]; omega) hcj) D i
  have H' : Full k J (l*(c^i*d^j)) ((l+1)*(c^i*d^j)) := by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using C
  exact H'.2 u (hlo.trans (Nat.le_add_right ..)) (hhi.trans (Nat.le_add_right ..)) ha

private theorem admissible_counts {k n : ℕ} (hpp : IsPrimePow k) (hk : 2≤k) (hn : 0<n)
    (H : ∀ i < 2, (k-i).choose (2-i) ∣ (n-i).choose (2-i)) :
    ∃ u, n=(k-1)*u+1 ∧ u%k≤1 := by
  have h0 : k.choose 2 ∣ n.choose 2 := by simpa using H 0 (by decide)
  have h1 : k-1 ∣ n-1 := by simpa using H 1 (by decide)
  obtain ⟨u,hu⟩ := h1
  have he : (k-1)*u+1=n := by omega
  refine ⟨u,he.symm,?_⟩
  have hpair := Nat.mul_dvd_mul_right h0 2
  simp only [Nat.choose_two_right,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self _)] at hpair
  rw [hu] at hpair
  have hmul : k ∣ u*n := (Nat.mul_dvd_mul_iff_left (by omega : 0<k-1)).mp (by
    simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hpair)
  have hcop : u.Coprime n := he ▸ coprime_next u (k-1)
  rcases (hcop.isPrimePow_dvd_mul hpp).mp hmul with h | h
  · simp [Nat.mod_eq_zero_of_dvd h]
  · have eq : n+u=k*u+1 := by
      have hi : k-1+1=k := by omega
      nlinarith only [he,congrArg (·*u) hi]
    have hm := h.modEq_zero_nat.add_right u
    rw [eq,Nat.zero_add] at hm
    have hc := (dvd_mul_right k u).modEq_zero_nat.add_right 1
    have huv : u ≡ 1 [MOD k] := hm.symm.trans hc
    change u%k = 1%k at huv
    rw [Nat.mod_eq_of_lt (by omega : 1<k)] at huv
    omega

/-- The exact eventual spectrum, in the pinned binomial-divisibility form,
for every fixed prime-power block size and every sufficiently large order. -/
theorem prime_power_block_spectrum (k : ℕ) (hpp : IsPrimePow k) :
    ∀ᶠ n : ℕ in atTop,
      (∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 k) ↔
        ∀ i<2, (k-i).choose (2-i) ∣ (n-i).choose (2-i) := by
  have hk : 2≤k := hpp.one_lt
  obtain ⟨N,hN⟩ := eventual_group_counts hpp hk
  filter_upwards [eventually_ge_atTop ((k-1)*N+1)] with n hn
  constructor
  · rintro ⟨H,hH⟩ i hi
    exact design_divisibility hH (by omega) (by omega)
  · intro H
    obtain ⟨u,hu,hmod⟩ := admissible_counts hpp hk (by omega) H
    have hle : N ≤ u := (Nat.le_of_mul_le_mul_left (by omega : (k-1)*N≤(k-1)*u) (by omega))
    have hdesign := (hN u hle hmod).some.design
    rwa [hu]

/-- Forward implication in the exact quantifier order of the pinned problem. -/
theorem eventually_pair_prime_power (k : ℕ) (hpp : IsPrimePow k) :
    ∀ᶠ n : ℕ in atTop, (∀ i<2, (k-i).choose (2-i) ∣ (n-i).choose (2-i)) →
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 2 k :=
  (prime_power_block_spectrum k hpp).mono fun _ h => h.mpr

#print axioms eventually_pair_prime_power
#print axioms eventual_group_counts
#print axioms prime_power_block_spectrum
end Erdos722.PairDesign
