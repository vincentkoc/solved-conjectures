import ThetaCenteredDeviation
import ThetaPrimeConcentration

/-! Transfer the centered band estimate to every endpoint. -/
namespace Arxiv.«2501.03234».ThetaCenteredEndpoint
open Finset Filter Real ThetaPrimeDensity ThetaCenteredDeviation
noncomputable section

theorem compare_rate {X N : ℕ} (hX : 0<X) (hlo : X≤N^64)
    (hNlog : 1≤log N) (hXlog : 1≤log X) : rate X≤64*rate N := by
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hl := log_le_log hx (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hlo)
  rw [log_pow] at hl
  rw [rate_eq (by linarith),rate_eq (by linarith)]
  calc _ ≤ (64*log (N:ℝ))^(3/4:ℝ) := rpow_le_rpow (by linarith) hl (by norm_num)
       _ = (64:ℝ)^(3/4:ℝ)*(log (N:ℝ))^(3/4:ℝ) := by rw [mul_rpow (by norm_num : (0:ℝ)≤64) (by linarith)]
       _ ≤ _ := mul_le_mul_of_nonneg_right (rpow_le_self_of_one_le (by norm_num) (by norm_num)) (rpow_nonneg (by linarith) _)

private theorem member {X p : ℕ} {P : ℕ → Prop} : p∈primeSet P X ↔ p≤X ∧ p.Prime ∧ P p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

theorem endpoint {ε : ℝ} (hε : 0<ε) : ∃ a D : ℝ, 0<a ∧ 0<D ∧ ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => ε*log p≤|(S p:ℝ)/p-log p/2|) X).card:ℝ) ≤
      D*X*exp (-(a*rate X)) := by
  classical
  obtain ⟨a,C,ha,ha64,hC,hband⟩ := band hε
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp (hband.and (hlog.eventually_ge_atTop 1))
  refine ⟨a/64,(1+C)*2^64,by positivity,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop ((256:ℕ)^64),eventually_ge_atTop (N₀^64),hlog.eventually_ge_atTop 1]
    with X hX hbig hXlog
  obtain ⟨N,hN,_,hlo,hhi⟩ := ThetaPrimeConcentration.dyadic_cover hX
  have hN₀ : N₀≤N := by
    by_contra! lt
    exact (Nat.pow_lt_pow_left lt (by norm_num : 64≠0)).not_ge (hbig.trans hlo)
  obtain ⟨hb,hNlog⟩ := h₀ N hN₀
  let E := primeSet (fun p => ε*log p≤|(S p:ℝ)/p-log p/2|) X
  let U := E.filter (N^56≤·)
  have hU := hb U (by
    intro p hp
    obtain ⟨he,hh⟩ := mem_filter.mp hp
    obtain ⟨hx,hpr,hv⟩ := member.mp he
    exact ⟨hpr,hh,hx.trans hlo,hv⟩)
  have hsub : E⊆range (N^56) ∪ U := by
    intro p hp
    rcases lt_or_ge p (N^56) with hl|hu
    · exact mem_union_left _ (mem_range.mpr hl)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,hu⟩)
  have hc : (E.card:ℝ)≤(N:ℝ)^56+U.card := by
    exact_mod_cast (card_le_card hsub).trans ((card_union_le ..).trans_eq (by rw [card_range]))
  have hr : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hn : (N:ℝ)^56≤(N:ℝ)^64*exp (-a*rate N) := by
    have he (k : ℕ) : (N:ℝ)^k=exp ((k:ℝ)*log N) := by rw [exp_nat_mul,exp_log hr]
    rw [he 56,he 64,←exp_add,exp_le_exp]
    norm_num
    have hl := rate_le hNlog
    change 1≤log (N:ℝ) at hNlog
    nlinarith only [hl,mul_le_mul_of_nonneg_right ha64 (rate_pos (N:ℝ)).le,hNlog]
  have hx : 0<X := (show 0<(256:ℕ)^64 by positivity).trans_le hX
  have hcomp := compare_rate hx hlo hNlog hXlog
  have hfrac : exp (-a*rate N)≤exp (-(a/64*rate X)) := exp_le_exp.mpr (by linarith only [mul_le_mul_of_nonneg_left hcomp ha.le])
  have hscale : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hhi
  change (E.card:ℝ)≤_
  calc
    _ ≤ (1+C)*((N:ℝ)^64*exp (-a*rate N)) := by linarith only [hc,hU,hn]
    _ ≤ (1+C)*((2^64*(X:ℝ))*exp (-(a/64*rate X))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hscale hfrac (exp_pos _).le (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms endpoint
end
end Arxiv.«2501.03234».ThetaCenteredEndpoint
