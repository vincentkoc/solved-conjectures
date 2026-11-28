import ThetaPositiveDistribution

/-! Bombieri--Vinogradov transfer at all fixed logarithmic error exponents. -/
namespace Arxiv.«2501.03234».ThetaPositivePrimeLevel
open Filter Real ThetaPrimeDensity ThetaPositiveDistribution ThetaOccupancyScales
noncomputable section

/-- The ordinary discrepancy threshold may use any fixed main term depending
on the cutoff and modulus. Both selectors vary under the eventual quantifier. -/
def Distribution (P : ℕ → Prop) (level : ℕ → ℕ) (A : ℝ) (main : ℕ → ℕ → ℝ) := ∃ C : ℝ,0<C ∧
    ∀ᶠ X : ℕ in atTop, ∀ y b : ℕ → ℕ,
      (∀ q∈Finset.Icc 1 (level X),y q≤X) → (∀ q∈Finset.Icc 1 (level X),b q<q ∧ (b q).Coprime q) →
      discrepancy P (level X) y b (fun q => main (y q) q) ≤ C*X/(log X)^A

theorem absorption {A : ℝ} (hA : 0<A) : ∀ᶠ X : ℕ in atTop,
    (X.primeCounting:ℝ)*exp (-(2*saving X)) ≤ (X:ℝ)/(log X)^A := by
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hl := tendsto_log_atTop.comp hn
  have hh := hl.eventually ((isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)).bound
    (by positivity : 0<(1:ℝ)/(1073741824*A)))
  filter_upwards [hh,(tendsto_log_atTop.comp hl).eventually_ge_atTop 1,hl.eventually_gt_atTop 0] with X h hll hp
  let L := log (X:ℝ)
  let u := log L
  change 1≤u at hll
  have hu : 0≤u := by linarith
  change 0<L at hp
  change ‖u^(2:ℝ)‖≤1/(1073741824*A)*‖L^(1:ℝ)‖ at h
  rw [rpow_two,rpow_one,Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg hp.le,one_div_mul_eq_div] at h
  rw [le_div_iff₀ (by positivity)] at h
  have hs : A*u ≤ saving X := by
    change _ ≤ L/(1+u)/268435456
    rw [le_div_iff₀ (by norm_num),le_div_iff₀ (by linarith)]
    nlinarith only [h,mul_nonneg hA.le hu,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hll hu) hA.le]
  have hmass : X.primeCounting ≤ X := by
    rw [←Nat.primesLE_card_eq_primeCounting]
    have hsub : Nat.primesLE X ⊆ Finset.Icc 1 X := fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos,(Nat.mem_primesLE.mp hp).1⟩
    simpa using Finset.card_le_card hsub
  calc _ ≤ (X:ℝ)*exp (-(2*saving X)) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmass) (exp_pos _).le
       _ ≤ _ := by
         rw [rpow_def_of_pos hp,div_eq_mul_inv,←exp_neg]
         apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
         apply exp_le_exp.mpr
         change -(2*saving X) ≤ -(u*A)
         nlinarith only [hs,mul_nonneg hA.le hu]

/-- At every level in the stated range the usual prime discrepancy estimate
holds if and only if it holds after imposing the original theta slope. -/
theorem iff_ordinary {A : ℝ} (hA : 0<A) (k : ℕ) (level : ℕ → ℕ) (main : ℕ → ℕ → ℝ)
    (hlevel : ∀ᶠ X : ℕ in atTop,(level X:ℝ)^2 ≤ X*exp (saving X)) :
    Distribution (fun p => (k:ℤ)*p<S p) level A main ↔ Distribution (fun _ => True) level A main := by
  have e := ThetaPositiveDistribution.slope k
  have d := absorption hA
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+1,by positivity,?_⟩ <;>
    filter_upwards [e,d,h,hlevel] with X he hd hu hQ y b hy hb
  all_goals
    have h := he (level X) hQ y b hy (fun q hq => (hb q hq).1) (fun q => main (y q) q)
    have hh := hu y b hy hb
    rw [add_mul,add_div,one_mul]
    linarith only [(abs_le.mp h).1,(abs_le.mp h).2,hh,hd]

#print axioms iff_ordinary
end
end Arxiv.«2501.03234».ThetaPositivePrimeLevel
