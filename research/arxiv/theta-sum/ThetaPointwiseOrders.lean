import ThetaCharacterTorsion
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The divisor bound and a count of low-order characters at a prime. -/
namespace Arxiv.«2501.03234».ThetaPointwiseOrders
open Finset Filter Real DirichletCharacter
open scoped Topology
noncomputable section

theorem divisor_bound {ε : ℝ} (he : 0< ε) : ∃ C : ℝ, 0< C ∧ ∀ n : ℕ, 0< n →
    (n.divisors.card:ℝ)≤ C*(n:ℝ)^ε := by
  classical
  have hh := ((tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 2
  obtain ⟨N,hN⟩ := eventually_atTop.1 hh
  let t := (2:ℝ)^ε-1
  have ht : 0< t := sub_pos.mpr (Real.one_lt_rpow (by norm_num) he)
  let c := max 1 (1/t)
  have hc : 1≤ c := le_max_left ..
  have hct : 1≤ c*t := (div_le_iff₀ ht).mp (le_max_right ..)
  let G (n : ℕ) := n.primeFactors.filter (·< N)
  have per (p e : ℕ) (hp : p.Prime) :
      (e:ℝ)+1≤ (if p< N then c else 1)*((p:ℝ)^ε)^e := by
    have hp2 : (2:ℝ)≤ p := by exact_mod_cast hp.two_le
    have hpr := Real.rpow_le_rpow (by norm_num : (0:ℝ)≤ 2) hp2 he.le
    by_cases h : p< N
    · rw [if_pos h]
      have hh := one_add_mul_le_pow (show -2≤ t by linarith) e
      have ht1 : 1+t=(2:ℝ)^ε := by dsimp [t]; ring
      rw [ht1] at hh
      have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hpr e
      have h1 := mul_le_mul_of_nonneg_left (hh.trans hpow) (by linarith : 0≤ c)
      nlinarith only [hc,h1,mul_le_mul_of_nonneg_right hct (Nat.cast_nonneg e : (0:ℝ)≤ e)]
    · rw [if_neg h,one_mul]
      have h₁ := one_add_mul_le_pow (show (-2:ℝ)≤ 1 by norm_num) e
      norm_num only [one_mul,mul_one,one_add_one_eq_two] at h₁
      exact (add_comm (e:ℝ) 1).le.trans (h₁.trans (pow_le_pow_left₀ (by norm_num) (hN p (le_of_not_gt h)) _))
  have aux (n : ℕ) (hn : 0< n) : (n.divisors.card:ℝ)≤ c^(G n).card*(n:ℝ)^ε := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => omega
    | one => simp [G]
    | prime_pow p e hp he' =>
      have h := per p e hp
      rw [Nat.divisors_prime_pow hp,card_map,card_range]
      simp only [G,Nat.primeFactors_prime_pow he'.ne' hp,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
      have heq : ((p:ℝ)^e)^ε=((p:ℝ)^ε)^e := by
        rw [←Real.rpow_natCast_mul (Nat.cast_nonneg p),←Real.rpow_mul_natCast (Nat.cast_nonneg p),mul_comm]
      rw [heq]
      by_cases hl : p < N <;> simpa [hl,Finset.filter_singleton] using h
    | coprime a b ha hb hab ia ib =>
      have hG : G (a*b)=G a∪G b := by simp [G,Nat.primeFactors_mul (by omega : a≠0) (by omega : b≠0),filter_union]
      have hdis : Disjoint (G a) (G b) := hab.disjoint_primeFactors.mono (filter_subset ..) (filter_subset ..)
      rw [hab.card_divisors_mul,Nat.cast_mul,Nat.cast_mul,hG,card_union_of_disjoint hdis,
        pow_add,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      exact (mul_le_mul (ia (by omega)) (ib (by omega)) (Nat.cast_nonneg _) (by positivity [hc])).trans_eq (by ring)
  refine ⟨c^N,by positivity [hc],fun n hn => (aux n hn).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  apply pow_le_pow_right₀ hc
  rw [←card_range N]; apply card_le_card; intro p hp; exact mem_range.mpr (mem_filter.mp hp).2

/-- All orders up to a real cutoff, counted using the divisors of p−1. -/
theorem count_orders {p : ℕ} [Fact p.Prime] (hp : _root_.Odd p) (B : ℝ) (hB : 0≤ B)
    (s : Finset (DirichletCharacter ℂ p)) (hs : ∀ χ∈s,(orderOf χ:ℝ)≤ B) :
    (s.card:ℝ)≤ B*(p-1).divisors.card := by
  classical
  let D := (p-1).divisors
  have hp' : p.Prime := Fact.out
  have hφ : Fintype.card (DirichletCharacter ℂ p)=p-1 :=
    by simpa only [Nat.card_eq_fintype_card] using (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p).trans (Nat.totient_prime hp')
  have hmap (χ : DirichletCharacter ℂ p) (_ : χ∈s) : orderOf χ∈D := by
    exact Nat.mem_divisors.mpr ⟨hφ ▸ orderOf_dvd_card,by have := hp'.two_le; omega⟩
  have layer (d) (hd : d∈D) : ((s.filter (fun χ => orderOf χ=d)).card:ℝ)≤ B := by
    by_cases h : (s.filter (fun χ => orderOf χ=d)).Nonempty
    · obtain ⟨ψ,hψ⟩ := h
      have hψ' := (mem_filter.mp hψ).2
      have hbound := ThetaCharacterTorsion.count (q:=p) (Nat.pos_of_mem_divisors hd) hp
      simp only [hp'.primeFactors,card_singleton,pow_one,ThetaCharacterTorsion.roots,
        Nat.card_eq_fintype_card,Fintype.card_subtype] at hbound
      have hsmall : s.filter (fun χ => orderOf χ=d) ⊆ univ.filter (fun χ : DirichletCharacter ℂ p => χ^d=1) := by
        intro χ hχ
        rw [←(mem_filter.mp hχ).2]
        exact mem_filter.mpr ⟨mem_univ _,pow_orderOf_eq_one χ⟩
      exact (Nat.cast_le.mpr ((card_le_card hsmall).trans hbound)).trans (hψ' ▸ hs ψ (mem_filter.mp hψ).1)
    · simpa [not_nonempty_iff_eq_empty.mp h] using hB
  have hsum := sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at hsum
  rw [←hsum]
  simpa only [sum_const,nsmul_eq_mul,mul_comm B] using sum_le_sum layer

#print axioms count_orders
#print axioms divisor_bound
end
end Arxiv.«2501.03234».ThetaPointwiseOrders
