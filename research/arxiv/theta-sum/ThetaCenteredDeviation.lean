import ThetaCenteredScales

/-! A three-quarter-power logarithmic saving for deviations on a prime band. -/
namespace Arxiv.«2501.03234».ThetaCenteredDeviation
open Real Finset Filter ThetaIdentityModels
noncomputable section

def root (x : ℝ) := exp (log (log x)/4)
def rate (x : ℝ) := root x ^ 3
theorem rate_pos (x : ℝ) : 0<rate x := pow_pos (exp_pos _) _
theorem fourth {x : ℝ} (h : 0<log x) : root x ^ 4=log x := by
  rw [root,←exp_nat_mul,show ((4:ℕ):ℝ)*(log (log x)/4)=log (log x) by ring,exp_log h]
theorem rate_le {x : ℝ} (h : 1≤log x) : rate x≤log x := by
  have hr : 1≤root x := one_le_exp (by exact div_nonneg (Real.log_nonneg h) (by norm_num))
  rw [←fourth (by linarith : 0<log x)]
  exact pow_le_pow_right₀ hr (by decide)
theorem rate_eq {x : ℝ} (h : 0<log x) : rate x=(log x)^(3/4:ℝ) := by
  rw [Real.rpow_def_of_pos h,rate,root,←exp_nat_mul]
  congr 1
  ring

/-- One exponent works for all translations, truncation constants and starting
levels of the centered filtration. -/
theorem calibrated {ε : ℝ} (hε : 0<ε) : ∃ a : ℝ, 0<a ∧ a≤1/64 ∧
    ∀ (C : ℝ) (U₀ : ℕ), ∀ᶠ N : ℕ in atTop, ∃ U T k : ℕ, ∃ u : ℝ,
    U₀≤U ∧ 2≤T ∧ T≤N^2 ∧ 0<u ∧
    (∀ p : ℕ, N≤p → C+(8/Real.pi^2)*(u+ThetaModelExponentialMoment.height U+1)≤ε*log p) ∧
    1/(T:ℝ)^(1/64:ℝ)≤exp (-a*rate N) ∧
    (((2*k:ℕ):ℝ)/(ThetaTiltBudget.tilt U*u))^(2*k)≤exp (-a*rate N) ∧
    (12*Z*(T:ℝ)^2/u)^(2*k)≤exp (16*log N) := by
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c];positivity
  let b := ε/(4*c)
  have hb : 0<b := div_pos hε (by positivity)
  have hec : c*b=ε/4 := by dsimp [b];field_simp
  have hz : 0≤Z := tsum_nonneg (fun _ => by positivity)
  obtain ⟨a,ha,ha64,hpar⟩ := ThetaCenteredScales.parameters hb (show 0≤12*Z by positivity)
  refine ⟨a,ha,ha64,?_⟩
  intro C U₀
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hr : Tendsto (fun N : ℕ => root N) atTop atTop :=
    tendsto_exp_atTop.comp ((tendsto_log_atTop.comp hlog).atTop_div_const (by norm_num : (0:ℝ)<4))
  filter_upwards [hr.eventually (hpar U₀),hlog.eventually_ge_atTop 1,
    hlog.eventually_ge_atTop ((2*C+2*c)/ε),eventually_ge_atTop 2] with N hpar hL1 hth hN
  simp only [Function.comp_apply] at hL1 hth
  let L := log (N:ℝ)
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hL : 0<L := lt_of_lt_of_le zero_lt_one hL1
  have heL : exp L=N := exp_log hNp
  obtain ⟨U,T,k,hU,hT,hheight,hTlo,hTtop,hk,hep⟩ := hpar
  have heq := fourth hL
  rw [heq] at hheight hTtop hk hep
  rw [show 2*L=L+L by ring,exp_add,heL] at hTtop
  have hTY : T≤N^2 := by rw [sq];exact_mod_cast hTtop
  change exp (rate N)≤(T:ℝ) at hTlo
  change _ ≤ exp (-a*rate N) at hk
  let u := b*L
  have hu : 0<u := mul_pos hb hL
  have hval : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hd : 1/(T:ℝ)^(1/64:ℝ) ≤ exp (-rate N/64) := by
    calc
      _ ≤ 1/exp (rate N)^(1/64:ℝ) := one_div_le_one_div_of_le (rpow_pos_of_pos (exp_pos _) _) (rpow_le_rpow (exp_pos _).le hTlo (by norm_num))
      _ = _ := by rw [← exp_mul,one_div,← exp_neg];congr 1;ring
  have hR := rate_pos (N:ℝ)
  have hd' : 1/(T:ℝ)^(1/64:ℝ) ≤ exp (-a*rate N) := hd.trans (exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right ha64 hR.le]))
  refine ⟨U,T,k,u,hU,hT,hTY,hu,?_,hd',hk,hep⟩
  intro p hNp'
  have he := mul_le_mul_of_nonneg_left (log_le_log hNp (show (N:ℝ)≤(p:ℝ) by exact_mod_cast hNp')) hε.le
  have ht : 2*C+2*c≤L*ε := (div_le_iff₀ hε).mp hth
  change C+c*(u+ThetaModelExponentialMoment.height U+1)≤_
  dsimp [u]
  nlinarith only [ht,he,congrArg (·*L) hec,mul_le_mul_of_nonneg_left hheight hc.le]


theorem band {ε : ℝ} (hε : 0<ε) : ∃ a D : ℝ, 0<a ∧ a≤1/64 ∧ 0<D ∧
    ∀ᶠ N : ℕ in atTop, ∀ s : Finset ℕ,
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64 ∧ ε*log p≤|(S p:ℝ)/p-log p/2|) →
    (s.card:ℝ) ≤ D*(N:ℝ)^64*exp (-a*rate N) := by
  obtain ⟨C,B,hC,hB,h⟩ := ThetaCenteredPrimeBand.prime_band
  obtain ⟨U₀,hband⟩ := eventually_atTop.mp h
  obtain ⟨a,ha,ha64,hp⟩ := calibrated hε
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨a,B+2*(2*exp ThetaTiltBudget.total)+2,ha,ha64,by positivity,?_⟩
  filter_upwards [hp C U₀,hlog.eventually_ge_atTop 1,eventually_ge_atTop 2] with N hpar hL1 hN
  obtain ⟨U,T,k,u,hU,hT,hTY,hu,gate,hd',hk,hep⟩ := hpar
  let L := log (N:ℝ)
  have hL : 0<L := lt_of_lt_of_le zero_lt_one hL1
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have heL : exp L=N := exp_log hNp
  have hR := rate_pos (N:ℝ)
  have hTY' : T≤2*N^52 := hTY.trans ((Nat.pow_le_pow_right (by omega : 1≤N) (by decide : 2≤52)).trans (by omega))
  intro s hs
  have H := hband U hU hN hT hTY' k hu s (by
    intro p hps
    obtain ⟨hpr,hlo,hhi,hdev⟩ := hs p hps
    exact ⟨hpr,hlo,hhi,(gate p ((Nat.le_self_pow (by norm_num : 56≠0) N).trans hlo)).trans hdev⟩)
  let K := 2*exp ThetaTiltBudget.total
  have hK : 0<K := by dsimp [K]; positivity
  have hK' : (((2*k:ℕ):ℝ)/(ThetaTiltBudget.tilt U*u))^(2*k)≤exp (-a*rate N) := hk
  have hRN : rate N≤L := rate_le hL1
  have hpN : (N:ℝ)^64=exp (64*L) := by rw [show (64:ℝ)=(64:ℕ) by norm_num,exp_nat_mul,heL]
  have hsmall : exp (16*L)≤(N:ℝ)^64*exp (-a*rate N) := by
    rw [hpN,←exp_add,exp_le_exp];nlinarith only [mul_le_mul_of_nonneg_right ha64 hR.le,hRN,hL.le]
  let M := ((N^64+1:ℕ):ℝ)
  have hM : M≤2*(N:ℝ)^64 := by
    have hpow : 1≤(N:ℝ)^64 := one_le_pow₀ (by exact_mod_cast (show 1≤N by omega))
    dsimp [M];push_cast;linarith
  have hdiv : ((M*K*(((2*k:ℕ):ℝ)/ThetaTiltBudget.tilt U)^(2*k)+2*(12*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) =
      M*K*(((2*k:ℕ):ℝ)/(ThetaTiltBudget.tilt U*u))^(2*k)+2*(12*Z*(T:ℝ)^2/u)^(2*k) := by
    rw [add_div,mul_div_assoc,mul_div_assoc 2,← div_pow,← div_pow,div_div]
  apply H.trans
  change B*(N:ℝ)^64/(T:ℝ)^(1/64:ℝ)+_≤_
  rw [hdiv,div_eq_mul_one_div]
  have hmain := mul_le_mul (mul_le_mul_of_nonneg_right hM hK.le) hK' (by positivity [show 0≤ThetaTiltBudget.tilt U by unfold ThetaTiltBudget.tilt; positivity])
    (by positivity : 0≤2*(N:ℝ)^64*K)
  nlinarith only [hmain,hep.trans hsmall,mul_le_mul_of_nonneg_left hd' (by positivity : 0≤B*(N:ℝ)^64)]

#print axioms calibrated
#print axioms band
end
end Arxiv.«2501.03234».ThetaCenteredDeviation
