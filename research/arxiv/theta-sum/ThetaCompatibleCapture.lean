import ThetaInverseResidueRows
import ThetaDivisorTriangle
import ThetaIdentityModels

/-! The divisor contribution on a nonidentity unit class, including the
prime factor where the inverse residue is unrestricted. -/
namespace Arxiv.«2501.03234».ThetaCompatibleCapture
open Finset Real ThetaRowCorrelations ThetaOddHarmonicTriangle ThetaDivisorLogMean
open ThetaConditionalRows ThetaDivisorTriangle
noncomputable section

private lemma U_le (d : ℕ) : U d≤1+log d := by
  apply le_trans _ (harmonic_le_one_add_log d)
  rw [harmonic_eq_sum_Icc,Rat.cast_sum]
  simp only [Rat.cast_inv,Rat.cast_natCast]
  exact sum_le_sum_of_subset_of_nonneg ((filter_subset ..).trans (filter_subset ..))
    (fun _ _ _ => by positivity)

private lemma abs_row {d : ℕ} (hd : 1<d) (K n : ℕ) : |row d K n|≤3*(1+log d) := by
  have h := row_fiber (by omega : 0<d) (by decide : 0<1) (by simpa using hd : 1<d*1)
    (Nat.mod_lt n (by omega : 0<d)) K
  simpa [row_onMod d K n] using h.trans (by
    simpa using mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) (by norm_num : (0:ℝ)≤3) :
    3*((harmonic (d*1):ℝ)*(Nat.divisors 1).card)≤3*(1+log d))

def value (A : ℕ → ℝ) (K : ℕ → ℕ) (n d : ℕ) : ℝ :=
  if 1<d then A d*row d (K d) n/d else 0

theorem lower {a n m : ℕ} (ha : Odd a) (hn : n.Coprime m)
    (he : ∀ d,d∣m → ¬a∣d → (n:ZMod d)⁻¹=(a:ZMod d))
    (A : ℕ → ℝ) (K : ℕ → ℕ) {Z : ℝ} (hZ : 1≤Z)
    (hA : ∀ d∈m.divisors,1≤A d ∧ A d≤Z) (hK : ∀ d∈m.divisors,1<d → 2*d≤K d) :
    (mass m)^2/16-Z*(4*a+3)*mass m-
      (1+3*Z)*((logMass m+log a*mass m)/a) ≤ ∑ d∈m.divisors,value A K n d := by
  classical
  let C := Z*(4*(a:ℝ)+3)
  let B := 1+3*Z
  have hB : 0≤B := by dsimp [B]; linarith
  have hC : 1≤C := by dsimp [C]; nlinarith [Nat.cast_nonneg (α:=ℝ) a]
  have pt (d : ℕ) (hd : d∈m.divisors) :
      (if Odd d then U d/d else 0)-C*(d:ℝ)⁻¹-
        (if a∣d then B*((1+log d)/d) else 0) ≤ value A K n d := by
    obtain ⟨h₁,h₂⟩ := hA d hd
    have hd₀ := Nat.pos_of_mem_divisors hd
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hx : 0<(d:ℝ) := by exact_mod_cast hd₀
    have hl := log_nonneg_nat d
    have hbad : 0≤B*((1+log d)/d) := by positivity
    by_cases h : 1<d
    · rw [value,if_pos h]
      by_cases ho : Odd d
      · rw [if_pos ho]
        by_cases had : a∣d
        · rw [if_pos had,←div_eq_mul_inv,←sub_div,←mul_div_assoc,←sub_div]
          apply div_le_div_of_nonneg_right _ hx.le
          have H := (abs_le.mp (abs_row h (K d) n)).1
          have hrow := mul_le_mul_of_nonneg_left H (by linarith : 0≤A d)
          have hcost := mul_le_mul_of_nonneg_right h₂ (by linarith : 0≤3*(1+log d))
          dsimp only [B]
          linarith [U_le d]
        · rw [if_neg had,sub_zero,←div_eq_mul_inv,←sub_div]
          apply div_le_div_of_nonneg_right _ hx.le
          have H := ThetaInverseResidueRows.captured_lower ha h ho (hK d hd h)
            (hn.coprime_dvd_right hdiv) (he d hdiv had)
          have hu : 0≤U d := sum_nonneg fun _ _ => by positivity
          have hpos := mul_le_mul_of_nonneg_right h₁ hu
          have hneg := mul_le_mul_of_nonneg_right h₂ (by positivity : 0≤4*(a:ℝ)+3)
          have hh := mul_le_mul_of_nonneg_left H (by linarith : 0≤A d)
          dsimp only [C]; linarith
      · rw [if_neg ho,even_row ho]; simp only [mul_zero,zero_div]
        have hci : 0≤C*(d:ℝ)⁻¹ := by positivity
        split_ifs <;> linarith
    · have hd1 : d=1 := by omega
      subst d
      have hu := U_le 1
      simp only [Nat.cast_one,log_one,add_zero] at hu
      simp only [value,lt_irrefl,if_false,show Odd (1:ℕ) by decide,if_true,Nat.cast_one,
        div_one,inv_one,mul_one,log_one,add_zero]
      split_ifs <;> linarith
  have H := sum_le_sum pt
  rw [sum_sub_distrib,sum_sub_distrib,←sum_filter,←mul_sum,←sum_filter,←mul_sum] at H
  have hbad := mul_le_mul_of_nonneg_left (log_mass_multiple (m:=m) ha.pos) hB
  have hg := ThetaDivisorTriangle.triangle m
  change _ ≤ ∑ d∈m.divisors.filter Odd,U d/d at hg
  change _-C*mass m-B*_≤_
  change _-C*mass m-B*_≤_ at H
  linarith
end
end Arxiv.«2501.03234».ThetaCompatibleCapture
#print axioms Arxiv.«2501.03234».ThetaCompatibleCapture.lower
