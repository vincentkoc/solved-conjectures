import ThetaShortCenteredBand
import ThetaCenteredDeviation

/-! A high-moment deviation estimate on an arbitrary translated interval. -/
namespace Arxiv.«2501.03234».ThetaShortCenteredDeviation
open Finset Filter Real ThetaCenteredDeviation ThetaIdentityModels
noncomputable section

theorem band {e : ℕ} (h32 : 32≤e) (h48 : e≤48) (kernel : ThetaCalibratedCone.Kernel e) {ε : ℝ} (hε : 0<ε) : ∃ a D : ℝ, 0<a ∧ a≤1/64 ∧ 0<D ∧ ∀ᶠ N : ℕ in atTop, ∀ M H : ℕ, ∀ s : Finset ℕ,
    (∀ i∈s,i<H ∧ (M+i).Prime ∧ N^56≤M+i ∧ M+i≤N^64 ∧
      ε*log (M+i:ℕ)≤|(S (M+i):ℝ)/(M+i:ℕ)-log (M+i:ℕ)/2|) →
    (s.card:ℝ) ≤ D*(1+log N)^8*((H:ℝ)*exp (-a*rate N)+(N:ℝ)^e) := by
  obtain ⟨C,B,hC,hB,hh⟩ := ThetaShortCenteredBand.prime_band h32 h48 kernel
  obtain ⟨U₀,band⟩ := eventually_atTop.mp hh
  obtain ⟨a,ha,ha64,hpar⟩ := calibrated hε
  let K := 2*exp ThetaTiltBudget.total
  have hK : 0<K := by dsimp [K];positivity
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  refine ⟨a,B+K+2,ha,ha64,by positivity,?_⟩
  filter_upwards [hpar C U₀,hlog.eventually_ge_atTop 1,eventually_ge_atTop 2] with N hpar hL hN
  obtain ⟨U,T,k,u,hU,hT,hTY,hu,gate,hd,hk,hep⟩ := hpar
  have hnp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let V := (1+log (N:ℝ))^8
  let W := (N:ℝ)^e
  let E := exp (-a*rate N)
  have hE : 0≤E := (exp_pos _).le
  have hW : 0≤W := by dsimp [W];positivity
  have hV : 1≤V := one_le_pow₀ (n:=8) (show 1≤1+log (N:ℝ) by change 1≤log (N:ℝ) at hL;linarith)
  have hsmall : exp (16*log N)≤W := by
    change _≤(N:ℝ)^e
    rw [show (N:ℝ)^e=exp ((e:ℝ)*log N) by rw [exp_nat_mul,exp_log hnp],exp_le_exp]
    change 1≤log (N:ℝ) at hL
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show 16≤e by omega)) (by linarith)
  intro M H s hs
  have h := band U hU hN hT hTY M H k hu s (by
    intro i hi
    obtain ⟨hi',hp,hlo,hhi,hdev⟩ := hs i hi
    exact ⟨hi',hp,hlo,hhi,(gate _ ((Nat.le_self_pow (by norm_num : 56≠0) N).trans hlo)).trans hdev⟩)
  have hdiv : (((H:ℝ)*K*(((2*k:ℕ):ℝ)/ThetaTiltBudget.tilt U)^(2*k)+2*(12*Z*(T:ℝ)^2)^(2*k))/u^(2*k)) =
      (H:ℝ)*K*(((2*k:ℕ):ℝ)/(ThetaTiltBudget.tilt U*u))^(2*k)+2*(12*Z*(T:ℝ)^2/u)^(2*k) := by
    rw [add_div,mul_div_assoc,mul_div_assoc 2,←div_pow,←div_pow,div_div]
  apply h.trans
  rw [hdiv,div_eq_mul_one_div (H:ℝ)]
  change B*V*((H:ℝ)*(1/(T:ℝ)^(1/64:ℝ))+W)+_≤(B+K+2)*V*((H:ℝ)*E+W)
  have hE' : 0≤(H:ℝ)*E := mul_nonneg (Nat.cast_nonneg H) hE
  have hf := add_le_add (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg H (α:=ℝ))) (le_refl W)
  have high := mul_le_mul_of_nonneg_left hf (show 0≤B*V by positivity)
  have low := mul_le_mul_of_nonneg_left hk (show 0≤(H:ℝ)*K by positivity)
  change _≤(H:ℝ)*K*E at low
  change _≤B*V*((H:ℝ)*E+W) at high
  have hvh := mul_le_mul_of_nonneg_right hV hE'
  have hvw := mul_le_mul_of_nonneg_right hV hW
  nlinarith only [high,low,hep.trans hsmall,mul_le_mul_of_nonneg_left hvh hK.le,
    hvw,mul_nonneg hK.le (mul_nonneg (by linarith only [hV] : 0≤V) hW),
    mul_nonneg (by linarith only [hV] : 0≤V) hE']

#print axioms band
end
end Arxiv.«2501.03234».ThetaShortCenteredDeviation
