import HosoyaDivisibilityDensities
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! Finite Möbius inversion for the upper-value gcd on a progression. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

def divisorSieve (m a d B n : ℕ) : Prop :=
  let G := n.gcd (lucasFibonacciSum n)
  n ≡ a [MOD m] ∧ d ∣ G ∧ (G/d).Coprime B
instance (m a d B n : ℕ) : Decidable (divisorSieve m a d B n) := by
  unfold divisorSieve
  infer_instance

private lemma sum_mu (N : ℕ) : ∑ j ∈ N.divisors, (μ j : ℝ) = if N=1 then 1 else 0 := by
  have z : ∑ j ∈ N.divisors, μ j = if N=1 then 1 else 0 := by
    rw [←coe_zeta_mul_apply,coe_zeta_mul_moebius,one_apply]
  split_ifs at z ⊢ with eq <;> exact_mod_cast z

private lemma multiple_iff (m a h n : ℕ) :
    multipleFiber m a h n ↔ n ≡ a [MOD m] ∧ h ∣ n.gcd (lucasFibonacciSum n) := by
  simp only [multipleFiber,Nat.dvd_gcd_iff]

theorem divisorSieve_indicator {m a d B : ℕ} (hd : 0 < d) (hb : 0 < B) (n : ℕ) :
    (if divisorSieve m a d B n then (1:ℝ) else 0) =
      ∑ j ∈ B.divisors, (μ j:ℝ)*(if multipleFiber m a (d*j) n then 1 else 0) := by
  let G := n.gcd (lucasFibonacciSum n)
  by_cases ap : n ≡ a [MOD m]
  · by_cases dv : d ∣ G
    · obtain ⟨t,ht⟩ := dv
      have g : n.gcd (lucasFibonacciSum n)=d*t := ht
      have filter_eq : B.divisors.filter (· ∣ t)=(B.gcd t).divisors := by
        ext j
        simp only [mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
        exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,(Nat.gcd_pos_of_pos_left t hb).ne'⟩,
          fun h => ⟨⟨h.1.1,hb.ne'⟩,h.1.2⟩⟩
      have test (j : ℕ) : multipleFiber m a (d*j) n ↔ j ∣ t := by
        simp only [multiple_iff,ap,true_and,g,Nat.mul_dvd_mul_iff_left hd]
      simp only [divisorSieve,g,Nat.dvd_mul_right,Nat.mul_div_cancel_left _ hd,ap,true_and,test,
        mul_ite,mul_one,mul_zero,←sum_filter,filter_eq,sum_mu,Nat.Coprime,Nat.gcd_comm t B]
    · have test (j : ℕ) : ¬ multipleFiber m a (d*j) n :=
        fun h => dv ((dvd_mul_right d j).trans ((multiple_iff ..).mp h).2)
      simp [divisorSieve,G] at dv ⊢
      simp_all
  · have test (j : ℕ) : ¬ multipleFiber m a (d*j) n := fun h => ap h.1
    simp [divisorSieve,ap,test]

noncomputable def divisorSum (m a d B : ℕ) : ℝ :=
  ∑ j ∈ B.divisors, (μ j:ℝ)*intersectionMass m a (d*j)

theorem divisorSieve_limit {m a d B : ℕ} (hm : 0 < m) (hd : 0 < d) (hb : 0 < B) :
    Tendsto (sampleFreq (divisorSieve m a d B)) atTop (𝓝 (divisorSum m a d B)) := by
  have eq (X : ℕ) : sampleFreq (divisorSieve m a d B) X =
      ∑ j ∈ B.divisors, (μ j:ℝ)*sampleFreq (multipleFiber m a (d*j)) X := by
    unfold sampleFreq sample
    simp only [natCast_card_filter,divisorSieve_indicator hd hb]
    rw [sum_comm,Finset.sum_div]
    apply sum_congr rfl
    intro j _
    rw [←mul_sum,mul_div_assoc]
  rw [funext eq]
  exact tendsto_finsetSum _ fun j hj => tendsto_const_nhds.mul
    (intersection_limit hm (Nat.mul_pos hd (Nat.pos_of_mem_divisors hj)))

#print axioms divisorSieve_indicator
#print axioms divisorSieve_limit

end Arxiv.«2211.10788».IndexDivisors
