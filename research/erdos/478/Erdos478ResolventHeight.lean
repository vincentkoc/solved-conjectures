import Erdos478PermutationResolvent
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Bounds for a permutation resolvent and its exceptional primes

The size of each conjugate of a weighted sum controls both integer values
of its monic polynomial and the resultant with its derivative.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial
open scoped Polynomial

theorem gap_root_norm {n : ℕ} (hn : 0<n) {z : ℂ}
    (hz : (descPochhammer ℂ n-1).IsRoot z) : ‖z‖ ≤ n+1 := by
  by_contra! h
  have hx (i : ℕ) (hi : i ∈ range n) : 1 < ‖z-(i:ℂ)‖ := by
    have := norm_sub_norm_le z (i:ℂ)
    rw [Complex.norm_natCast] at this
    have hi' : (i:ℝ) < n := by exact_mod_cast mem_range.mp hi
    linarith
  have hh := prod_lt_prod (s := range n) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_lt_one)
    (fun i hi => (hx i hi).le) ⟨0,mem_range.mpr hn,hx 0 (mem_range.mpr hn)⟩
  have hp : ∏ i ∈ range n, (z-(i:ℂ)) = 1 := by
    simpa only [IsRoot.def,eval_sub,eval_one,sub_eq_zero,descPochhammer_eval_eq_prod_range] using hz
  have eqn := congrArg (fun w : ℂ => ‖w‖) hp
  simp only [norm_prod,norm_one] at eqn
  simp [eqn] at hh

theorem tag_norm {n M U : ℕ} (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ ≤ U) (σ : Equiv.Perm (Fin n)) :
    ‖tag a σ (M:ℂ)‖ ≤ (n*U*(M+1)^n : ℕ) := by
  classical
  unfold tag
  rw [ofFn_eq_sum_monomial,eval_finsetSum]
  calc
    _ ≤ ∑ i : Fin n, ‖(monomial i ((a ∘ σ) i)).eval (M:ℂ)‖ := norm_sum_le ..
    _ ≤ ∑ _i : Fin n, (U:ℝ)*(M+1)^n := by
      apply sum_le_sum
      intro i _
      simp only [eval_monomial,norm_mul,norm_pow,Complex.norm_natCast,Function.comp_apply]
      apply mul_le_mul (ha _) _ (by positivity) (by positivity)
      calc (M:ℝ)^i.val ≤ (M+1)^i.val := by gcongr; linarith
           _ ≤ (M+1)^n := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) M]) i.isLt.le
    _ = _ := by simp; ring

/-- The resultant detecting repeated roots after reduction. -/
noncomputable def bad (f : ℤ[X]) := f.resultant f.derivative

private theorem diff_product {I : Type*} [Fintype I] [DecidableEq I] (a : I → ℂ) (i : I) :
    (∏ j, (X-C (a j))).derivative.eval (a i) = ∏ j ∈ univ.erase i, (a i-a j) := by
  rw [← prod_erase_mul univ (fun j => X-C (a j)) (mem_univ i),derivative_mul]
  simp [eval_prod]

private theorem result_product {I : Type*} [Fintype I] [DecidableEq I] (f : ℤ[X]) (a : I → ℂ)
    (h : f.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i))) :
    ((bad f : ℤ) : ℂ) = ∏ i, ∏ j ∈ univ.erase i, (a i-a j) := by
  let g := f.map (Int.castRingHom ℂ)
  have hg : g = ∏ i, (X-C (a i)) := h
  have hm : g.Monic := hg.symm ▸ monic_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))
  have hs : g.Splits := hg.symm ▸ Splits.prod (fun i _ => Splits.X_sub_C (a i))
  have hdeg : g.natDegree = f.natDegree := natDegree_map_eq_of_injective Int.cast_injective f
  have hdeg' : g.derivative.natDegree = f.derivative.natDegree := by
    rw [show g.derivative = f.derivative.map (Int.castRingHom ℂ) from derivative_map _ _]
    exact natDegree_map_eq_of_injective Int.cast_injective _
  have hroots : g.roots = univ.val.map a := by
    have hprod : g = ((univ.val.map a).map (fun z => X-C z)).prod := by
      rw [hg,Multiset.map_map]
      rfl
    rw [hprod,roots_multiset_prod_X_sub_C]
  change (Int.castRingHom ℂ) (resultant f f.derivative _ _) = _
  rw [← resultant_map_map,← derivative_map]
  change resultant g g.derivative _ _ = _
  rw [← hdeg,← hdeg',resultant_eq_prod_eval _ _ _ le_rfl hs,hm.leadingCoeff,one_pow,one_mul,hroots]
  rw [Multiset.map_map]
  change (univ.val.map (fun i => g.derivative.eval (a i))).prod = _
  apply prod_congr rfl
  intro i _
  change f.map (Int.castRingHom ℂ) = _ at h
  dsimp only [g]
  rw [h,diff_product]

/-- Distinct complex roots give a nonzero integer resultant whose size
is bounded in terms of their common radius and their number. -/
theorem bad_bound {I : Type*} [Fintype I] (f : ℤ[X]) (a : I ↪ ℂ)
    (h : f.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i))) (U : ℕ) (hU : 0<U)
    (ha : ∀ i, ‖a i‖ ≤ U) :
    0 < (bad f).natAbs ∧ (bad f).natAbs ≤ (2*U)^(Fintype.card I)^2 := by
  classical
  have eqn := result_product f a h
  constructor
  · apply Int.natAbs_pos.mpr
    intro hz
    rw [hz,Int.cast_zero] at eqn
    exact (prod_ne_zero_iff.mpr (fun i _ => prod_ne_zero_iff.mpr (fun j hj =>
      sub_ne_zero.mpr (fun he => (mem_erase.mp hj).1 (a.injective he).symm)))) eqn.symm
  · have hrad (i j : I) : ‖a i-a j‖ ≤ 2*(U:ℝ) := (norm_sub_le ..).trans (by linarith [ha i,ha j])
    have hprod (i : I) : ∏ j ∈ univ.erase i, ‖a i-a j‖ ≤ (2*(U:ℝ))^(Fintype.card I) := calc
      _ ≤ ∏ _j ∈ univ.erase i, (2*(U:ℝ)) := prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hrad i j)
      _ ≤ _ := by
        simp only [prod_const]
        apply pow_le_pow_right₀ _ (card_le_univ _)
        exact_mod_cast (by omega : 1 ≤ 2*U)
    have hn := congrArg (fun w : ℂ => ‖w‖) eqn
    simp only [norm_prod,Complex.norm_intCast] at hn
    have H : |((bad f : ℤ):ℝ)| ≤ (2*(U:ℝ))^(Fintype.card I)^2 := calc
      _ = _ := hn
      _ ≤ ∏ _i : I, (2*(U:ℝ))^(Fintype.card I) :=
        prod_le_prod (fun _ _ => prod_nonneg (fun _ _ => norm_nonneg _)) (fun i _ => hprod i)
      _ = _ := by simp [pow_two,pow_mul]
    rw [← Int.cast_abs,← Int.natCast_natAbs] at H
    exact_mod_cast H

#print axioms gap_root_norm
#print axioms tag_norm
#print axioms bad_bound
end Erdos478.EffectiveResolvent
