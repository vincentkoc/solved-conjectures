import Erdos478CubicGapTransitivity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Frequent dyadic intervals rich in selected prime lengths

Dirichlet's non-summability of the prime-supported von Mangoldt series in
the class 11 modulo 21 forces infinitely many dyadic blocks with more than
any fixed multiple of 2^j/j³ selected primes.
-/

namespace Erdos478.BinaryGap
open Finset Filter Topology ArithmeticFunction
noncomputable section

def lengths (j : ℕ) : Finset ℕ := by
  classical exact (Ico (2^j) (2^(j+1))).filter (fun l => l.Prime ∧ selected l)

def family (j : ℕ) : Finset Nat.Primes := (lengths j).subtype Nat.Prime

theorem family_mem {j : ℕ} {l : Nat.Primes} : l∈family j ↔ 2^j≤l.val ∧ l.val<2^(j+1) ∧ selected l.val := by
  classical
  apply (mem_subtype (a:=⟨l.val,l.property⟩) (p:=Nat.Prime) (s:=lengths j)).trans
  simp [lengths,l.property,and_assoc]

theorem family_card (j : ℕ) : (family j).card=(lengths j).card := by
  classical
  change ((lengths j).subtype Nat.Prime).card=_
  have h : (lengths j).filter Nat.Prime=lengths j := filter_eq_self.mpr (fun _ hl => (mem_filter.mp hl).2.1)
  rw [card_subtype,h]

def scale (j : ℕ) : ℝ := (2:ℝ)^j/(j:ℝ)^3

private def weight (n : ℕ) : ℝ := Real.log n/n

private theorem ap_diverges : ¬Summable (fun p : ℕ => if p.Prime ∧ p%21=11 then weight p else 0) := by
  have hunit : IsUnit (11 : ZMod 21) := by decide
  intro h
  apply vonMangoldt.not_summable_residueClass_prime_div hunit
  apply h.congr
  intro n
  have mod : (n : ZMod 21)=11 ↔ n%21=11 :=
    (ZMod.natCast_eq_natCast_iff n 11 21).trans Iff.rfl
  by_cases hp : n.Prime
  · by_cases hr : (n:ZMod 21)=11
    · simp [hp,mod.mp hr,vonMangoldt.residueClass,Set.indicator_of_mem,hr,weight,vonMangoldt_apply_prime hp]
    · simp [hp,mt mod.mpr hr,vonMangoldt.residueClass,Set.indicator_of_notMem,hr]
  · simp [hp]

private def blockMass (j : ℕ) : ℝ := ∑ p ∈ lengths j, weight p

private theorem mass_nonneg (j : ℕ) : 0≤blockMass j :=
  sum_nonneg (fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))

private theorem blocks_diverge : ¬Summable blockMass := by
  classical
  intro h
  apply ap_diverges
  apply summable_of_sum_le (c:=∑' j,blockMass j)
  · intro p
    change 0 ≤ (if p.Prime ∧ p%21=11 then weight p else 0)
    split_ifs
    · exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    · exact le_rfl
  intro s
  let u := s.filter (fun p => p.Prime ∧ p%21=11)
  let b := u.image (Nat.log 2)
  have maps (i : ℕ) (hi : i∈u) : Nat.log 2 i∈b := mem_image_of_mem _ hi
  rw [← sum_filter]
  change ∑ p ∈ u, weight p≤_
  rw [← sum_fiberwise_of_maps_to maps]
  apply (sum_le_sum (g:=fun j => blockMass j) ?_).trans (h.sum_le_tsum b (fun j _ => mass_nonneg j))
  intro j _
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
  intro p hp
  obtain ⟨hu,rfl⟩ := mem_filter.mp hp
  obtain ⟨hp,hr⟩ := (mem_filter.mp hu).2
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.pow_log_le_self _ hp.ne_zero,Nat.lt_pow_succ_log_self (by decide : 1<2) _⟩,
    hp,Or.inl hr⟩

private theorem mass_le (j : ℕ) : blockMass j≤(lengths j).card*((j:ℝ)+1)/(2:ℝ)^j := by
  classical
  have ht (p : ℕ) (hp : p∈lengths j) : weight p≤((j:ℝ)+1)/(2:ℝ)^j := by
    obtain ⟨lo,hi⟩ := mem_Ico.mp (mem_filter.mp hp).1
    have pp := (mem_filter.mp hp).2.1.pos
    have le : Real.log p≤(j:ℝ)+1 := by
      have h₁ : (p:ℝ)≤(2:ℝ)^(j+1) := by exact_mod_cast hi.le
      have h₂ := Real.log_le_log (by exact_mod_cast pp) h₁
      rw [Real.log_pow] at h₂
      push_cast at h₂
      exact h₂.trans (by nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))) (show 0≤(j:ℝ)+1 by positivity)])
    exact div_le_div₀ (by positivity) le (by positivity) (by exact_mod_cast lo)
  simpa [blockMass,mul_div_assoc] using sum_le_sum ht

/-- Infinitely often, the number of usable lengths exceeds C times 2^j/j³. -/
theorem frequently_many_lengths {C : ℝ} (hC : 0<C) :
    ∃ᶠ j : ℕ in atTop, C*scale j<(family j).card := by
  by_contra h
  have hev := not_frequently.mp h
  apply blocks_diverge
  apply Summable.of_norm_bounded_eventually_nat ((Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left (2*C))
  filter_upwards [hev,eventually_ge_atTop 1] with j hj hj₁
  have jr : 1≤(j:ℝ) := by exact_mod_cast hj₁
  have jp : 0<(j:ℝ) := by linarith
  have hpow : 0<(2:ℝ)^j := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg _)]
  apply (mass_le j).trans
  rw [family_card] at hj
  have hcard := le_of_not_gt hj
  have hmul := mul_le_mul_of_nonneg_right hcard (show 0≤(j:ℝ)+1 by positivity)
  apply (div_le_iff₀ hpow).mpr
  apply hmul.trans
  dsimp [scale]
  field_simp
  linarith only [jr]

#print axioms family_mem
#print axioms family_card
#print axioms frequently_many_lengths
end
end Erdos478.BinaryGap
