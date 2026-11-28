import ThetaTotientTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Subpower growth of the number of bounded-order local choices relative
to the density of units. -/
namespace Arxiv.«2501.03234».ThetaTorsionMajorant
open Finset Filter Real
open scoped Topology
noncomputable section

theorem choices (k : ℕ) (hk : 0< k) {ε : ℝ} (he : 0< ε) :
    ∃ C : ℝ, 0< C ∧ ∀ q : ℕ, 0< q → (k:ℝ)^q.primeFactors.card≤ C*(q:ℝ)^ε := by
  classical
  have h := ((tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (k:ℝ)
  obtain ⟨N,hN⟩ := eventually_atTop.1 h
  have hk' : 1≤ (k:ℝ) := by exact_mod_cast hk
  refine ⟨(k:ℝ)^N,by positivity,?_⟩
  intro q hq
  let G := q.primeFactors.filter (·< N)
  let H := q.primeFactors.filter (fun p => ¬p< N)
  have heq : G.card+H.card=q.primeFactors.card := card_filter_add_card_filter_not ..
  have hg : G.card≤ N := by
    rw [←card_range N]; apply card_le_card
    intro p hp; exact mem_range.mpr (mem_filter.mp hp).2
  have hh : (k:ℝ)^H.card ≤ (q:ℝ)^ε := by
    have hmul : (k:ℝ)^H.card ≤ ∏ p∈H,(p:ℝ)^ε := by
      rw [←prod_const]; apply prod_le_prod (fun _ _ => Nat.cast_nonneg k)
      exact fun p hp => hN p (le_of_not_gt (mem_filter.mp hp).2)
    apply hmul.trans
    have prodpow (s : Finset ℕ) : ∏ p∈s,(p:ℝ)^ε = ((∏ p∈s,p : ℕ):ℝ)^ε := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [prod_insert ha,prod_insert ha,ih,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg _)]
    rw [prodpow]
    have hd : (∏ p∈H,p)∣q := (Finset.prod_dvd_prod_of_subset H q.primeFactors id (filter_subset ..)).trans (Nat.prod_primeFactors_dvd q)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.le_of_dvd hq hd)) he.le
  rw [←heq,pow_add]
  exact mul_le_mul (pow_le_pow_right₀ hk' hg) hh (by positivity) (by positivity)

theorem totient_cost {q : ℕ} (hq : 0< q) : (q:ℝ)/q.totient≤ 2^q.primeFactors.card := by
  rw [ThetaTotientTail.totient_product hq,←prod_const]
  apply prod_le_prod (fun p hp => div_nonneg (Nat.cast_nonneg _) (by
    have h : (2:ℝ)≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith))
  intro p hp
  have h : (2:ℝ)≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  rw [div_le_iff₀ (by linarith)]; linarith

theorem normalized_choices (k : ℕ) (hk : 0< k) {ε : ℝ} (he : 0< ε) :
    ∃ C : ℝ, 0< C ∧ ∀ q : ℕ, 0< q → (k:ℝ)^q.primeFactors.card*((q:ℝ)/q.totient)≤ C*(q:ℝ)^ε := by
  obtain ⟨C,hC,H⟩ := choices (2*k) (by omega) he
  refine ⟨C,hC,fun q hq => ?_⟩
  apply (mul_le_mul_of_nonneg_left (totient_cost hq) (by positivity : 0≤ (k:ℝ)^q.primeFactors.card)).trans
  rw [mul_comm]
  simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_pow] using H q hq

#print axioms normalized_choices
end
end Arxiv.«2501.03234».ThetaTorsionMajorant
