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

/-- Only the explicitly exceptional divisor rows pay the full logarithmic envelope. -/
theorem capture_bound {n m : ℕ} (bad : ℕ → Prop) [DecidablePred bad] {L : ℝ} (hL : 1≤L)
    (A : ℕ → ℝ) (K : ℕ → ℕ) {Z : ℝ} (hZ : 1≤Z)
    (hA : ∀ d∈m.divisors,1≤A d ∧ A d≤Z)
    (hrow : ∀ d∈m.divisors,1<d → Odd d → ¬bad d → U d-L≤row d (K d) n) :
    (mass m)^2/16-Z*L*mass m-
      (1+3*Z)*(∑ d∈m.divisors.filter bad,(1+log d)/d) ≤ ∑ d∈m.divisors,value A K n d := by
  classical
  let C := Z*L
  let B := 1+3*Z
  have hB : 0≤B := by dsimp [B]; linarith
  have hC : 1≤C := by dsimp [C]; nlinarith only [hZ,hL,mul_nonneg (sub_nonneg.mpr hZ) (sub_nonneg.mpr hL)]
  have pt (d : ℕ) (hd : d∈m.divisors) :
      (if Odd d then U d/d else 0)-C*(d:ℝ)⁻¹-
        (if bad d then B*((1+log d)/d) else 0) ≤ value A K n d := by
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
        by_cases had : bad d
        · rw [if_pos had,←div_eq_mul_inv,←sub_div,←mul_div_assoc,←sub_div]
          apply div_le_div_of_nonneg_right _ hx.le
          have H := (abs_le.mp (abs_row h (K d) n)).1
          have hrow := mul_le_mul_of_nonneg_left H (by linarith : 0≤A d)
          have hcost := mul_le_mul_of_nonneg_right h₂ (by linarith : 0≤3*(1+log d))
          dsimp only [B]
          linarith [U_le d]
        · rw [if_neg had,sub_zero,←div_eq_mul_inv,←sub_div]
          apply div_le_div_of_nonneg_right _ hx.le
          have H := hrow d hd h ho had
          have hu : 0≤U d := sum_nonneg fun _ _ => by positivity
          have hpos := mul_le_mul_of_nonneg_right h₁ hu
          have hneg := mul_le_mul_of_nonneg_right h₂ (by linarith : 0≤L)
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
  have hg := ThetaDivisorTriangle.triangle m
  change _ ≤ ∑ d∈m.divisors.filter Odd,U d/d at hg
  change _-C*mass m-B*_≤_
  change _-C*mass m-B*_≤_ at H
  linarith

theorem lower {a n m : ℕ} (ha : Odd a) (hn : n.Coprime m)
    (he : ∀ d,d∣m → ¬a∣d → (n:ZMod d)⁻¹=(a:ZMod d))
    (A : ℕ → ℝ) (K : ℕ → ℕ) {Z : ℝ} (hZ : 1≤Z)
    (hA : ∀ d∈m.divisors,1≤A d ∧ A d≤Z) (hK : ∀ d∈m.divisors,1<d → 2*d≤K d) :
    (mass m)^2/16-Z*(4*a+3)*mass m-
      (1+3*Z)*((logMass m+log a*mass m)/a) ≤ ∑ d∈m.divisors,value A K n d := by
  have hL : 1≤4*(a:ℝ)+3 := by linarith [Nat.cast_nonneg (α:=ℝ) a]
  have H := capture_bound (n:=n) (m:=m) (a∣·) hL A K hZ hA
    (fun d hd h ho had => ThetaInverseResidueRows.captured_lower ha h ho (hK d hd h)
      (hn.coprime_dvd_right (Nat.mem_divisors.mp hd).1) (he d (Nat.mem_divisors.mp hd).1 had))
  have hbad := mul_le_mul_of_nonneg_left (log_mass_multiple (m:=m) ha.pos)
    (show 0≤1+3*Z by linarith)
  linarith only [H,hbad]

#print axioms capture_bound
end
end Arxiv.«2501.03234».ThetaCompatibleCapture
#print axioms Arxiv.«2501.03234».ThetaCompatibleCapture.lower
