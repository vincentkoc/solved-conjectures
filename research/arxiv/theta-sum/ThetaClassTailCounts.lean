import ThetaDyadicTailCounts
import ThetaAllClassExcursions

/-! Double-exponential frequency inside any fixed reduced prime progression. -/
namespace Arxiv.«2501.03234».ThetaClassTailCounts
open Filter Finset Real ThetaNaturalPrimeMeans ThetaPrimeDensity ThetaDoubleExponentialTails
open ThetaDiagonalConstant ThetaDyadicTailCounts
noncomputable section

/-- The class count is between half and twice its asymptotic size in units of π(X)/φ(q). -/
private theorem counts_approx (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q)
    (hr : r.Coprime q) (hlt : r<q) :
    ∀ᶠ X : ℕ in atTop,
      0<((primeSet (fun p => p%q=r) X).card:ℝ) ∧
      (X.primeCounting:ℝ)≤2*q.totient*(primeSet (fun p => p%q=r) X).card ∧
      (q.totient:ℝ)*(primeSet (fun p => p%q=r) X).card≤2*X.primeCounting := by
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hd := class_prime_density hAP hq hr hlt
  have hl : 1/(2*(q.totient:ℝ))<1/q.totient := by
    rw [div_lt_div_iff₀ (by positivity) hφ];linarith
  have hu : 1/(q.totient:ℝ)<2/q.totient := div_lt_div_of_pos_right (by norm_num) hφ
  have hpi := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [hd.eventually_const_lt hl, hd.eventually_lt_const hu,hpi.eventually_gt_atTop 0]
    with X hlo hhi hX
  change 0<(X.primeCounting:ℝ) at hX
  have h₁ := (div_lt_div_iff₀ (by positivity : 0<2*(q.totient:ℝ)) hX).mp hlo
  have h₂ := (div_lt_div_iff₀ hX hφ).mp hhi
  have hp : 0<((primeSet (fun p => p%q=r) X).card:ℝ) := by
    by_contra! hz
    nlinarith only [h₁,hX,mul_nonpos_of_nonpos_of_nonneg hz (by positivity : 0≤2*(q.totient:ℝ))]
  exact ⟨hp,by linarith only [h₁],by linarith only [h₂]⟩

/-- The counts are relative to the primes in (q,r), with the same exponent
constants for every reduced class. The initial height may depend on the class. -/
theorem original (hAP : ProgressionMangoldt) : ∃ c : ℝ, 0<c ∧
    ∀ q r : ℕ, 0<q → r<q → r.Coprime q → ∀ᶠ b : ℝ in atTop, ∀ᶠ X : ℕ in atTop,
      let l := (q.totient:ℝ)/2*exp (-exp (32*π*sqrt b))
      let R := fun p : ℕ => (S p:ℝ)/p-log p/2-diagonalConstant
      l≤fraction q r X (fun p => b<R p) ∧ l≤fraction q r X (fun p => R p< -b) ∧
        fraction q r X (fun p => b < |R p|)≤2*q.totient*exp (-exp (c*sqrt b)) := by
  classical
  obtain ⟨c,hc,H⟩ := original_prime hAP
  refine ⟨c,hc,?_⟩
  intro q r hq hlt hr
  filter_upwards [H,ThetaAllClassExcursions.counts hAP hq hlt hr] with b hb hc'
  filter_upwards [hb,hc',counts_approx hAP hq hr hlt,
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting).eventually_gt_atTop 0]
    with X hu hlow happrox hX
  change 0<(X.primeCounting:ℝ) at hX
  let B := ((primeSet (fun p => p%q=r) X).card:ℝ)
  let l := exp (-exp (32*π*sqrt b))
  let u := exp (-exp (c*sqrt b))
  have hB : 0<B := happrox.1
  have h₁ := (div_le_iff₀ hX).mp hu
  let R := fun p : ℕ => (S p:ℝ)/p-log p/2-diagonalConstant
  have hs : primeSet (fun p => p%q=r ∧ b < |R p|) X ⊆ primeSet (fun p => b < |R p|) X := by
    intro p hp
    simp only [primeSet,mem_filter] at hp ⊢
    exact ⟨hp.1,hp.2.2⟩
  have hp : (fun p : ℕ => b<R p) = (fun p => diagonalConstant+b<(S p:ℝ)/p-log p/2) := by
    funext p;apply propext;dsimp [R];constructor <;> intro h <;> linarith
  have hm : (fun p : ℕ => R p< -b) = (fun p => (S p:ℝ)/p-log p/2<diagonalConstant-b) := by
    funext p;apply propext;dsimp [R];constructor <;> intro h <;> linarith
  have hl : ((q.totient:ℝ)/2*l)*B≤l*X.primeCounting := by
    have hh := mul_le_mul_of_nonneg_left happrox.2.2 (exp_pos (-exp (32*π*sqrt b))).le
    change l*(q.totient*B)≤l*(2*X.primeCounting) at hh
    linarith only [hh]
  have hupper : u*X.primeCounting≤(2*q.totient*u)*B := by
    have hh := mul_le_mul_of_nonneg_left happrox.2.1 (exp_pos (-exp (c*sqrt b))).le
    change u*X.primeCounting≤u*(2*q.totient*B) at hh
    linarith only [hh]
  change _≤fraction q r X (fun p => b<R p) ∧ _≤fraction q r X (fun p => R p< -b) ∧ _≤_
  rw [hp,hm]
  exact ⟨(le_div_iff₀ hB).mpr (hl.trans hlow.1),(le_div_iff₀ hB).mpr (hl.trans hlow.2),
    (div_le_iff₀ hB).mpr ((Nat.cast_le.mpr (card_le_card hs)).trans (h₁.trans hupper))⟩

#print axioms original
end
end Arxiv.«2501.03234».ThetaClassTailCounts
