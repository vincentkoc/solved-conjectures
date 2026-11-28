import ThetaGrowingWindowScales

/-! A stretched-exponential exceptional set for the original sum on one band. -/
namespace Arxiv.«2501.03234».ThetaStrongDeviation
open Finset Real Filter ThetaGrowingWindowScales ThetaIdentityModels
noncomputable section

def rate (x : ℝ) := sqrt (log x*log (log x))

theorem height_eq {x : ℝ} (hx : 1≤log x) : height (log (log x))=rate x := by
  have hp : 0<log x := by linarith
  have he : exp (log (log x)/2)^2=log x := by
    rw [sq,← exp_add,show log (log x)/2+log (log x)/2=log (log x) by ring,exp_log hp]
  have hr : exp (log (log x)/2)=sqrt (log x) := by
    nlinarith only [he,sq_sqrt hp.le,sqrt_nonneg (log x),exp_pos (log (log x)/2)]
  simp only [height,rate,sqrt_mul hp.le,hr]

theorem rate_le {x : ℝ} (hx : 1≤log x) : rate x≤log x := by
  have hp : 0≤log x := by linarith
  have hs := sq_sqrt (mul_nonneg hp (log_nonneg hx))
  change sqrt (log x*log (log x))≤log x
  nlinarith only [hs,hp,mul_le_mul_of_nonneg_left (log_le_self hp) hp]

/-- One parameter choice controls the deleted rows, the complete moment, and the
finite endpoint at every eligible prime. -/
theorem calibrated {ε a : ℝ} (C : ℝ) (hε : 0<ε) (ha : 0<a) : ∀ᶠ N : ℕ in atTop,
    ∃ (T k : ℕ) (u : ℝ), 2≤T ∧ T≤N^2 ∧ 0<u ∧
      (∀ p : ℕ,N≤p → C+8/Real.pi^2*(u+1)≤ε*log p) ∧
      1/(T:ℝ)^(1/64:ℝ)≤exp (-rate N/64) ∧
      (((2*k:ℕ):ℝ)/(a*u))^(2*k)≤exp (-rate N/64) ∧
      (6*Z*(T:ℝ)^2/u)^(2*k)≤exp (16*log N) := by
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c];positivity
  let b := ε/(2*c)
  have hb : 0<b := div_pos hε (by positivity)
  have hec : c*b=ε/2 := by dsimp [b];field_simp
  have hz : 0≤Z := tsum_nonneg (fun _ => by positivity)
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hh := (tendsto_log_atTop.comp hlog).eventually (parameters ha hb (show 0≤6*Z by positivity))
  filter_upwards [hh,hlog.eventually_ge_atTop 1,hlog.eventually_ge_atTop ((2*C+2*c)/ε),
    eventually_ge_atTop 2] with N hpar hL1 hth hN
  simp only [Function.comp_apply] at hpar hL1 hth
  let L := log (N:ℝ)
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hL : 0<L := lt_of_lt_of_le zero_lt_one hL1
  have heL : exp L=N := exp_log hNp
  obtain ⟨T,k,hT,hTtop,hTlo,hk,hep⟩ := hpar
  change _≤exp (2*exp (log L)) at hTtop
  rw [exp_log hL,show 2*L=L+L by ring,exp_add,heL] at hTtop
  have hTY : T≤N^2 := by rw [sq];exact_mod_cast hTtop
  rw [height_eq hL1] at hTlo hk
  rw [show exp (log (log (N:ℝ)))=L from exp_log hL] at hk hep
  let u := b*L
  have hu : 0<u := mul_pos hb hL
  have hval : 0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hd : 1/(T:ℝ)^(1/64:ℝ) ≤ exp (-rate N/64) := by
    calc
      _ ≤ 1/exp (rate N)^(1/64:ℝ) := one_div_le_one_div_of_le (rpow_pos_of_pos (exp_pos _) _) (rpow_le_rpow (exp_pos _).le hTlo (by norm_num))
      _ = _ := by rw [← exp_mul,one_div,← exp_neg];congr 1;ring
  refine ⟨T,k,u,hT,hTY,hu,?_,hd,?_,hep⟩
  · intro p hNp'
    have he := mul_le_mul_of_nonneg_left (log_le_log hNp (show (N:ℝ)≤(p:ℝ) by exact_mod_cast hNp')) hε.le
    have ht : 2*C+2*c≤L*ε := (div_le_iff₀ hε).mp hth
    change C+c*(u+1)≤_
    dsimp [u]
    nlinarith only [ht,he,congrArg (·*L) hec]
  · exact hk.trans (exp_le_exp.mpr (by dsimp [rate];linarith only [sqrt_nonneg (log (N:ℝ)*log (log (N:ℝ)))]))

theorem band {ε : ℝ} (hε : 0<ε) : ∃ D : ℝ, 0<D ∧ ∀ᶠ N : ℕ in atTop, ∀ s : Finset ℕ,
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64 ∧ ε*log p≤|(S p:ℝ)/p-log p/2|) →
    (s.card:ℝ) ≤ D*(N:ℝ)^64*exp (-rate N/64) := by
  obtain ⟨C,a,K,B,hC,ha,hK,hB,band⟩ := ThetaWindowPrimeBand.prime_band
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨B+2*K+2,by positivity,?_⟩
  filter_upwards [calibrated C hε ha,hlog.eventually_ge_atTop 1,eventually_ge_atTop 2] with N hpar hL1 hN
  let L := log (N:ℝ)
  have hL : 0<L := lt_of_lt_of_le zero_lt_one hL1
  have heL : exp L=N := exp_log (by exact_mod_cast (show 0<N by omega))
  obtain ⟨T,k,u,hT,hTY,hu,gate,hd,hK',hep⟩ := hpar
  intro s hs
  have hcap : T≤2*N^52 := (hTY.trans (Nat.pow_le_pow_right (by omega : 0<N) (by decide : 2≤52))).trans (by omega)
  have H := band hN hT hcap k hu s (by
    intro p hps
    obtain ⟨hpr,hlo,hhi,hdev⟩ := hs p hps
    exact ⟨hpr,hlo,hhi,(gate p ((Nat.le_self_pow (by norm_num : 56≠0) N).trans hlo)).trans hdev⟩)
  have hR := rate_le hL1
  have hpN : (N:ℝ)^64=exp (64*L) := by rw [show (64:ℝ)=(64:ℕ) by norm_num,exp_nat_mul,heL]
  have hsmall : exp (16*L)≤(N:ℝ)^64*exp (-rate N/64) := by
    rw [hpN,←exp_add,exp_le_exp];linarith only [hR,hL.le]
  let M := ((N^64+1:ℕ):ℝ)
  have hM : M≤2*(N:ℝ)^64 := by
    have hpow : 1≤(N:ℝ)^64 := one_le_pow₀ (by exact_mod_cast (show 1≤N by omega))
    dsimp [M];push_cast;linarith
  have hdiv : ((M*K*(((2*k:ℕ):ℝ)/a)^(2*k)+2*(6*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) =
      M*K*(((2*k:ℕ):ℝ)/(a*u))^(2*k)+2*(6*Z*(T:ℝ)^2/u)^(2*k) := by
    rw [add_div,mul_div_assoc,mul_div_assoc 2,← div_pow,← div_pow,div_div]
  apply H.trans
  change B*(N:ℝ)^64/(T:ℝ)^(1/64:ℝ)+_≤_
  rw [hdiv,div_eq_mul_one_div]
  have hmain := mul_le_mul (mul_le_mul_of_nonneg_right hM hK.le) hK' (by positivity)
    (by positivity : 0≤2*(N:ℝ)^64*K)
  nlinarith only [hmain,hep.trans hsmall,mul_le_mul_of_nonneg_left hd (by positivity : 0≤B*(N:ℝ)^64)]

#print axioms calibrated
#print axioms band
end
end Arxiv.«2501.03234».ThetaStrongDeviation
