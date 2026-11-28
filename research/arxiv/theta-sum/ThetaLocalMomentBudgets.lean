import ThetaLocalMomentScales

/-! The prime mass and denominator budgets for averaged errors in every
admissible short interval. -/
namespace Arxiv.«2501.03234».ThetaLocalMomentBudgets
open Real Finset Filter ThetaLocalPrimeCounts ThetaLocalMomentScales
noncomputable section

/-- The mass is positive and the number of sampled primes is at most twice it. -/
theorem count {θ : ℝ} (h : Ordinary θ) : ∀ᶠ X : ℕ in atTop,
    ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    0< mass X H ∧ ((sample X H).card:ℝ)≤2*mass X H := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [h 0 2,ht.eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)] with X ha hlog hX
  intro H hHX hθ
  let L := log (X:ℝ)
  change 2≤L at hlog
  have hLp : 0<L := by linarith
  have hx : 0<(X:ℝ) := by exact_mod_cast (by omega : 0<X)
  have hH := (rpow_pos_of_pos hx θ).trans_le hθ
  have hM := mass_lower hX hHX
  change (H:ℝ)/(2*L)≤ mass X H at hM
  have hd := ha H hHX hθ 1 (by decide) (by simp) 0 (by decide) (by decide)
  have hs : ((sample X H).filter (fun p => p%1=0))=sample X H :=
    filter_eq_self.mpr fun p _ => Nat.mod_one p
  rw [hs,Nat.totient_one,Nat.cast_one,div_one] at hd
  have hsmall : (H:ℝ)/L^2≤ mass X H := (div_le_div_of_nonneg_left hH.le (by positivity : 0<2*L)
    (by nlinarith only [mul_le_mul_of_nonneg_right hlog hLp.le] : 2*L≤L^2)).trans hM
  refine ⟨(by positivity : 0<(H:ℝ)/(2*L)).trans_le hM,?_⟩
  have hh := (le_abs_self _).trans hd
  change ((sample X H).card:ℝ)-mass X H≤(H:ℝ)/L^2 at hh
  linarith only [hh,hsmall]

private theorem numeric {L V Y J B H M : ℝ} (a : ℕ) (hB : 0<B) (hL : 2≤L) (hV : 0≤V)
    (hVL : V≤L) (hY : 0<Y) (hJ : 0≤J) (hH : 0≤H)
    (hconst : 2^10*B*(2^(a+12)+1)≤L)
    (hp : L^(a+12)≤2^(a+12)*Y) (hj : J*L^(a+12)≤H) (hM : H/(2*L)≤M) :
    B*(1+V)^9*(H/Y+J)≤M/L^a := by
  have hl : 0<L := by linarith
  have hpow : 0<L^(a+12) := pow_pos hl _
  have hh : H/Y≤2^(a+12)*H/L^(a+12) := by
    rw [div_le_div_iff₀ hY hpow]
    nlinarith only [mul_le_mul_of_nonneg_left hp hH]
  have hj' := (le_div_iff₀ hpow).mpr hj
  have hsum : H/Y+J≤(2^(a+12)+1)*H/L^(a+12) := by linarith only [hh,hj',show (2^(a+12)+1)*H/L^(a+12)=2^(a+12)*H/L^(a+12)+H/L^(a+12) by ring]
  have hV9 := pow_le_pow_left₀ (by linarith only [hV] : 0≤1+V) (by linarith only [hVL,hL] : 1+V≤2*L) 9
  apply (mul_le_mul (mul_le_mul_of_nonneg_left hV9 hB.le) hsum (add_nonneg (div_nonneg hH hY.le) hJ) (by positivity)).trans
  apply le_trans _ (div_le_div_of_nonneg_right hM (pow_nonneg hl.le a))
  rw [←mul_div_assoc,div_div,div_le_div_iff₀ hpow (by positivity : 0<2*L*L^a)]
  have hsmall : 2^10*B*(2^(a+12)+1)≤L^2 := hconst.trans (by nlinarith only [mul_le_mul_of_nonneg_right hL hl.le,hL])
  have huse := mul_le_mul_of_nonneg_right hsmall (show 0≤(H*L^a)*L^10 by positivity)
  rw [pow_add L a 12]
  nlinarith only [huse]

/-- Any fixed inverse logarithmic power is available for the discarded rows
by raising the logarithmic denominator exponent. -/
theorem scales {e : ℕ} {θ B : ℝ} (hθ : (e:ℝ)/64<θ) (hB : 0<B) (a : ℕ)
    (N₀ : ℕ) {η : ℝ} (hη : 0<η) :
    ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, let Y := den (a+12) X
    N₀≤N ∧ 2≤Y ∧ Y≤N ∧ N^56≤X ∧ 2*X≤N^64 ∧ (Y:ℝ)≤(log X)^(64*(a+12)) ∧
    3*(Y:ℝ)/N≤η ∧ ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
      B*(1+log N)^9*((H:ℝ)/(Y:ℝ)^(1/64:ℝ)+(N:ℝ)^e)≤ mass X H/(log X)^a := by
  have hm : 1≤a+12 := by omega
  have hy := den_large hm
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [band hθ hm,den_bounds hm,hy.eventually_ge_atTop N₀,
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hy).eventually_ge_atTop (3/η),ht.eventually_ge_atTop (2:ℝ),
    ht.eventually_ge_atTop (2^10*B*(2^(a+12)+1)),eventually_ge_atTop (2:ℕ)] with X hb hc h₀ hsmall hL hcst hx
  obtain ⟨N,hN,hl,hu,hsq,hlog,hJ⟩ := hb
  let Y := den (a+12) X
  obtain ⟨hY,hymax,_,hp⟩ := hc
  have hyn : Y≤N := (Nat.le_self_pow (by decide : 2≠0) Y).trans hsq
  have hypos : 0<(Y:ℝ) := by exact_mod_cast (show 0<Y by dsimp [Y];omega)
  refine ⟨N,h₀.trans hyn,hY,hyn,hl,hu,hymax,?_,?_⟩
  · rw [div_le_iff₀ (by exact_mod_cast (show 0<N by omega) : 0<(N:ℝ))]
    change 3/η≤(Y:ℝ) at hsmall
    have h₃ := (div_le_iff₀ hη).mp hsmall
    have hs : (Y:ℝ)^2≤N := by exact_mod_cast hsq
    nlinarith only [mul_le_mul_of_nonneg_right h₃ hypos.le,mul_le_mul_of_nonneg_left hs hη.le]
  · intro H hHX hh
    exact numeric a hB hL (log_nonneg (by exact_mod_cast (show 1≤N by omega))) hlog
      (rpow_pos_of_pos hypos _) (by positivity) (Nat.cast_nonneg _) hcst hp (hJ.trans hh) (mass_lower hx hHX)

#print axioms count
#print axioms scales
end
end Arxiv.«2501.03234».ThetaLocalMomentBudgets
