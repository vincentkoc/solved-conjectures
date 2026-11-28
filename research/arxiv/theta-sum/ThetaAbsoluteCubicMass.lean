import ThetaRealCharacterMoment

/-! A lower bound for the absolute real cubic mass at every large prime. -/
namespace Arxiv.«2501.03234».ThetaAbsoluteCubicMass
open Filter Finset Real Complex DirichletCharacter ThetaFourier ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaRealCharacterMoment ThetaOddInverseCount
noncomputable section

def scale (p : ℕ) : ℝ := (p:ℝ)^2*Real.sqrt p

def mass {p : ℕ} [Fact p.Prime] (D : Finset (DirichletCharacter ℂ p)) : ℝ := ∑ χ∈D,|(cubic χ).re|

private lemma threshold {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) {T : ℝ} (hT : 0≤T) :
    T*((halfSum χ).re)^2 ≤ |(cubic χ).re|+T^3 := by
  rw [cubic_real,abs_mul,abs_of_nonneg (sq_nonneg _)]
  let x := |(halfSum χ).re|
  have hx : 0≤x := abs_nonneg _
  have hn : x≤‖halfSum χ‖ := abs_re_le_norm _
  have h2 : x^2=((halfSum χ).re)^2 := sq_abs _
  rw [←h2]
  change T*x^2 ≤ ‖halfSum χ‖^2*x+T^3
  rcases le_total x T with h|h
  · have h' := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx h 2) hT
    nlinarith only [h',mul_nonneg (sq_nonneg ‖halfSum χ‖) hx]
  · have h' := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx hn 2) hx
    nlinarith only [h',mul_le_mul_of_nonneg_right h (sq_nonneg x),pow_nonneg hT 3]

theorem lower {p : ℕ} [Fact p.Prime] (hp : _root_.Odd p) (hL : (p:ℝ)/8 ≤ (inverseCount p:ℝ)) :
    scale p/512 ≤ mass (nonprincipal p) := by
  classical
  let T := Real.sqrt p/8
  have hx : 0≤(p:ℝ) := Nat.cast_nonneg _
  have hT : 0≤T := by dsimp [T]; positivity
  have hs := sum_le_sum (s:=nonprincipal p) (fun χ _ => threshold χ hT)
  rw [←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul] at hs
  have hc : ((nonprincipal p).card:ℝ)≤p := by
    have h := card_le_card (filter_subset (fun χ : DirichletCharacter ℂ p => χ≠1) univ)
    have hφ := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p
    rw [Nat.card_eq_fintype_card] at hφ
    exact_mod_cast h.trans (by simp [hφ,Nat.totient_prime (Fact.out : p.Prime)])
  have hφ : (p:ℝ)/2≤p.totient := by
    have hp' : p.Prime := Fact.out
    rw [Nat.totient_prime hp',Nat.cast_sub hp'.one_le]; push_cast
    have : (2:ℝ)≤p := by exact_mod_cast hp'.two_le
    linarith
  have hm := real_second_moment hp
  have hsm : (p:ℝ)^2/32≤∑ χ∈nonprincipal p,((halfSum χ).re)^2 := by
    nlinarith only [hm,mul_le_mul hφ hL (by positivity) (Nat.cast_nonneg _)]
  have hs' := (mul_le_mul_of_nonneg_left hsm hT).trans hs
  change _ ≤ mass (nonprincipal p)+_ at hs'
  have hupper := mul_le_mul_of_nonneg_right hc (pow_nonneg hT 3)
  dsimp [T,scale] at *
  nlinarith only [hs',hupper,Real.sq_sqrt hx,
    congrArg (fun x : ℝ => x*(p:ℝ)*Real.sqrt p) (Real.sq_sqrt hx)]

theorem eventually_lower : ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
    letI : Fact p.Prime := ⟨hp⟩
    scale p/512 ≤ mass (nonprincipal p) := by
  filter_upwards [eventually_many] with p H
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact lower ho (H hp ho)

#print axioms lower
#print axioms eventually_lower
end
end Arxiv.«2501.03234».ThetaAbsoluteCubicMass
