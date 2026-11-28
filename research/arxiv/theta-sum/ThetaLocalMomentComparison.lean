import ThetaLocalModelComparison

/-! At a common endpoint, every fixed shifted and periodically weighted
residual moment agrees asymptotically with its value on the dyadic window. -/
namespace Arxiv.«2501.03234».ThetaLocalMomentComparison
open Real Filter Finset ThetaLocalPrimeCounts ThetaLocalDyadicReference ThetaLocalModelComparison
open ThetaCharacterPrimeMeans ThetaPrimeLaw ThetaPeriodMeans ThetaLocalPowerStability ThetaCalibratedCone
noncomputable section

private theorem close {s : Finset ℕ} {M B δ t D : ℝ} (k : ℕ) (a b g : ℕ → ℝ)
    (hδ : 0≤δ) (ht : 0<t) (hD : 0≤D) (hg : ∀ n, |g n|≤1) (hcard : (s.card:ℝ)≤2*M)
    (hM : 0<M) (herr : (∑ n∈s,|a n-b n|^(2*k))≤t^2*M)
    (hb : (∑ n∈s,|b n|^(2*k))≤(B+1)*M)
    (hgap : ∀ a b : ℝ, |a^k-b^k|≤δ*(1+|b|^k)+D*|a-b|^k) :
    |(∑ n∈s,g n*(a n)^k)/M-(∑ n∈s,g n*(b n)^k)/M|≤δ*(B+5)+2*D*t := by
  have hs := sum_le_sum (s:=s) (fun n _ => show |b n|^k≤1+|b n|^(2*k) by
    rw [Nat.mul_comm 2 k,pow_mul];nlinarith only [sq_nonneg (|b n|^k-1/2)])
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at hs
  have hb' : (s.card:ℝ)+(∑ n∈s,|b n|^k)≤(B+5)*M := by linarith only [hs,hcard,hb]
  have h := mixed a b g k hg hgap (s:=s)
  rw [←sub_div,abs_div,abs_of_pos hM,div_le_iff₀ hM]
  apply h.trans
  nlinarith only [mul_le_mul_of_nonneg_left hb' hδ,mul_le_mul_of_nonneg_left (half_error a b k ht hcard herr) hD]

theorem original {e : ℕ} (he : 32≤e) (h48 : e≤48) (hk : Kernel e)
    {θ : ℝ} (hθ : (e:ℝ)/64<θ) (hθ₁ : θ≤1) (ordinary : Ordinary θ)
    {q : ℕ} (hq : 0<q) (g w : ℕ → ℝ) (hg : OnMod q g) (hw : OnMod q w)
    (hA : ∀ n, |g n|≤1) {D : ℝ} (hD : ∀ n, |w n|≤D) (k : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H →
    let f (p : ℕ) := g p*(w p+residual p)^k
    |avg X H f-avg X X f|≤ε := by
  by_cases hk₀ : k=0
  · subst k
    have hh := compare hθ₁ ordinary hq g w hg hw hA hD 0 0 hε
    filter_upwards [hh] with X h
    simpa only [pow_zero,mul_one] using h (Y:=1) le_rfl (by simp) 1
  obtain ⟨C,hC,hc⟩ := shifted_moments (2*k) w hD
  let B := (2:ℝ)^(2*k-1)*(C+1)
  have hB : 0<B := by dsimp [B]; positivity
  let δ := ε/(8*(B+5))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨d,hd,hgap⟩ := gap k hδ
  let t := min 1 (ε/(16*d))
  have ht : 0<t := lt_min zero_lt_one (by positivity)
  have ht1 : t≤1 := min_le_left ..
  have htδ : δ*(B+5)+2*d*t≤ε/4 := by
    have ht' := (le_div_iff₀ (by positivity : 0<16*d)).mp (min_le_right 1 (ε/(16*d)))
    change t*(16*d)≤ε at ht'
    have hdeq : δ*(B+5)=ε/8 := by dsimp [δ];field_simp
    linarith only [hdeq,ht']
  let j := 64*(2*(2*k)+13)
  have hcmp := compare hθ₁ ordinary hq g w hg hw hA hD k j (half_pos hε)
  have h2cmp := compare hθ₁ ordinary hq (fun _ => (1:ℝ)) w (fun _ => rfl) hw (fun _ => by norm_num)
    hD (2*k) j (by norm_num : (0:ℝ)<1)
  have happrox := ThetaLocalMomentApproximation.powers he h48 hk hθ ordinary (show 1≤2*k by omega) (sq_pos_of_pos ht)
  filter_upwards [hc,hcmp,h2cmp,happrox,ThetaLocalMomentBudgets.count ordinary,eventually_ge_atTop (1:ℕ)]
    with X hCfull hmodel hsquare ha hcount hx
  obtain ⟨N,h₂,hY,hE⟩ := ha
  let Y := ThetaLocalMomentScales.den (2*(2*k)+13) X
  let a (p : ℕ) := w p+residual p
  let b (p : ℕ) := w p+residualModel Y N p
  let Q (H : ℕ) := ∑ n∈sample X H,|b n|^(2*k)
  have hfull := full_length hx hθ₁
  have herror {H : ℕ} (hh : H≤X) (hl : (X:ℝ)^θ≤H) :
      (∑ n∈sample X H,|a n-b n|^(2*k))≤t^2*mass X H := by
    simpa only [a,b,add_sub_add_left_eq_sub] using hE H hh hl
  have hM := (hcount X le_rfl hfull).1
  have htop : Q X≤B*mass X X := by
    have hb := upper (s:=sample X X) a b (2*k)
    have het := (herror le_rfl hfull).trans (mul_le_of_le_one_left hM.le (by simpa using pow_le_pow_left₀ ht.le ht1 2))
    change _≤B*mass X X
    apply hb.trans
    dsimp only [B]
    have H := mul_le_mul_of_nonneg_left (add_le_add hCfull het) (by positivity : 0≤(2:ℝ)^(2*k-1))
    change (∑ n∈sample X X,|a n|^(2*k))≤_ at hCfull
    nlinarith only [H]
  have hnorm (n : ℕ) : (b n)^(2*k)=|b n|^(2*k) := by
    rw [Nat.mul_comm 2 k,pow_mul,pow_mul,pow_abs,sq_abs]
  have hevery (H : ℕ) (hh : H≤X) (hl : (X:ℝ)^θ≤H) : Q H≤(B+1)*mass X H := by
    have hh' := hsquare (Y:=Y) (by omega) hY N H hh hl
    change |avg X H (fun n => 1*(b n)^(2*k))-avg X X (fun n => 1*(b n)^(2*k))|≤1 at hh'
    simp only [avg,one_mul,hnorm] at hh'
    have hdiff := (le_abs_self _).trans hh'
    change Q H/mass X H-Q X/mass X X≤1 at hdiff
    exact (div_le_iff₀ (hcount H hh hl).1).mp (by linarith only [hdiff,(div_le_iff₀ hM).mpr htop])
  have hclose (H : ℕ) (hh : H≤X) (hl : (X:ℝ)^θ≤H) :
      |avg X H (fun n => g n*(a n)^k)-avg X H (fun n => g n*(b n)^k)|≤ε/4 :=
    (close k a b g hδ.le ht hd.le hA (hcount H hh hl).2 (hcount H hh hl).1
      (herror hh hl) (hevery H hh hl) hgap).trans htδ
  intro H hh hl f
  let A (H : ℕ) := avg X H (fun n => g n*(a n)^k)
  let V (H : ℕ) := avg X H (fun n => g n*(b n)^k)
  have hc₁ : |A H-V H|≤ε/4 := hclose H hh hl
  have hc₂ : |A X-V X|≤ε/4 := hclose X le_rfl hfull
  have hc₃ : |V H-V X|≤ε/2 := hmodel (Y:=Y) (by omega) hY N H hh hl
  change |A H-A X|≤ε
  rw [abs_sub_comm (A X)] at hc₂
  linarith only [abs_sub_le (A H) (V H) (A X),abs_sub_le (V H) (V X) (A X),hc₁,hc₂,hc₃]

#print axioms original
end
end Arxiv.«2501.03234».ThetaLocalMomentComparison
