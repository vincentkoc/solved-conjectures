import Erdos722SplitClassMass
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Almost all normalized four-fibre systems have minimum automorphism group -/

namespace Erdos722.FourPoint
open Finset Filter Topology
noncomputable section

private theorem root_pos (d : ℕ) : 0<rootOrder d := by
  let : Finite (Cube d ≃ₗ[ZMod 2] Cube d) := Finite.of_injective
    (fun L : Cube d ≃ₗ[ZMod 2] Cube d => (L : Cube d → Cube d)) DFunLike.coe_injective
  rw [rootOrder_eq]
  exact Nat.mul_pos (by decide) Nat.card_pos

private theorem weighted_error {d : ℕ} (hd : 8≤d) :
    (exceptionalWords d).card*rootOrder d*2^d≤6^numberEdges d :=
  (Nat.mul_le_mul_right _ (Nat.mul_le_mul (exceptional_words_bound d) (root_frames_card d))).trans
    (scaled_exceptional_bound hd)

private theorem ratio_range {d x t a : ℕ} (ht : 0<t) (lower : t≤x+a) (upper : x≤t+a)
    (err : a*2^d≤t) :
    1-(1/2:ℝ)^d≤(x:ℝ)/t ∧ (x:ℝ)/t≤1+(1/2:ℝ)^d := by
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hlow : (t:ℝ)≤x+a := by exact_mod_cast lower
  have hupp : (x:ℝ)≤t+a := by exact_mod_cast upper
  have herr : (a:ℝ)*2^d≤t := by exact_mod_cast err
  have ha : (a:ℝ)≤(1/2:ℝ)^d*t := by
    rw [div_pow,one_pow,one_div,← div_eq_inv_mul]
    exact (le_div_iff₀ (by positivity)).mpr herr
  constructor
  · apply (le_div_iff₀ ht').mpr
    nlinarith only [hlow,ha]
  · apply (div_le_iff₀ ht').mpr
    nlinarith only [hupp,ha]

/-- Relative error at most 2⁻ᵈ for the full unlabelled count in this family. -/
theorem split_class_fraction {d : ℕ} (hd : 8≤d) :
    let R := (((splitClasses d).card*rootOrder d : ℕ):ℝ)/(6^numberEdges d : ℕ)
    1-(1/2:ℝ)^d≤R ∧ R≤1+(1/2:ℝ)^d := by
  have g := root_pos d
  have h := split_class_range (d:=d) (by omega)
  have more : (exceptionalWords d).card≤(exceptionalWords d).card*rootOrder d := Nat.le_mul_of_pos_right _ g
  exact ratio_range (by positivity) (h.1.trans (Nat.add_le_add_left more _)) h.2 (weighted_error hd)

/-- Proportion of distinct labelled systems satisfying the pinned design
predicate, top split rank and minimum full automorphism order. -/
theorem minimum_systems_fraction {d : ℕ} (hd : 8≤d) :
    let R := ((minimumSystems d).card:ℝ)/(6^numberEdges d : ℕ)
    1-(1/2:ℝ)^d≤R ∧ R≤1 := by
  have g := root_pos d
  have h := minimum_systems_range (d:=d) (by omega)
  have more : (exceptionalWords d).card≤(exceptionalWords d).card*rootOrder d := Nat.le_mul_of_pos_right _ g
  have err := (Nat.mul_le_mul_right (2^d) more).trans (weighted_error hd)
  refine ⟨(ratio_range (by positivity) h.1 (h.2.trans (Nat.le_add_right ..)) err).1,?_⟩
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast h.2

private theorem asymptotic_one {f : ℕ → ℝ}
    (h : ∀ d,8≤d → 1-(1/2:ℝ)^d≤f d ∧ f d≤1+(1/2:ℝ)^d) : Tendsto f atTop (𝓝 1) := by
  have decay := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ)) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub decay)
    (by simpa using tendsto_const_nhds.add decay)
  · exact (eventually_ge_atTop 8).mono fun d hd => by simpa using (h d hd).1
  · exact (eventually_ge_atTop 8).mono fun d hd => by simpa using (h d hd).2

theorem split_class_asymptotic :
    Tendsto (fun d => (((splitClasses d).card*rootOrder d : ℕ):ℝ)/(6^numberEdges d : ℕ)) atTop (𝓝 1) :=
  asymptotic_one fun _ hd => split_class_fraction hd

theorem minimum_systems_density_one :
    Tendsto (fun d => ((minimumSystems d).card:ℝ)/(6^numberEdges d : ℕ)) atTop (𝓝 1) :=
  asymptotic_one fun _ hd => ⟨(minimum_systems_fraction hd).1,
    (minimum_systems_fraction hd).2.trans (le_add_of_nonneg_right (by positivity))⟩

#print axioms split_class_fraction
#print axioms minimum_systems_fraction
#print axioms split_class_asymptotic
#print axioms minimum_systems_density_one
end
end Erdos722.FourPoint
