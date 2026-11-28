import ThetaStrongDeviation
import ThetaPrimeConcentration

/-! Transfer of the one-band estimate to the original prime count at every endpoint. -/
namespace Arxiv.«2501.03234».ThetaStrongPrimeTail
open Finset Filter Real ThetaPrimeDensity ThetaStrongDeviation
noncomputable section

theorem compare_rate {X N : ℕ} (hN : 0<N) (hX : 0<X) (hlo : X≤N^64)
    (hNlog : 1≤log N) (hXlog : 1≤log X) (h64 : log 64≤log (log N)) :
    rate X≤16*rate N := by
  have hr : 0<(N:ℝ) := by exact_mod_cast hN
  have hx : 0<(X:ℝ) := by exact_mod_cast hX
  have hl := log_le_log hx (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hlo)
  rw [log_pow] at hl
  have hL : 0<log (N:ℝ) := by linarith
  have hLx : 0<log (X:ℝ) := by linarith
  have hl' := log_le_log hLx hl
  rw [log_mul (by norm_num) hL.ne'] at hl'
  norm_num1 at hl hl'
  have hn := log_nonneg hNlog
  have hp := log_nonneg hXlog
  have hprod := mul_le_mul hl (show log (log (X:ℝ))≤2*log (log (N:ℝ)) by linarith) hp (by positivity)
  have h1 := sq_sqrt (mul_nonneg hLx.le hp)
  have h2 := sq_sqrt (mul_nonneg hL.le hn)
  unfold rate
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  nlinarith only [h2,hprod,mul_nonneg hL.le hn]

private theorem member {X p : ℕ} {P : ℕ → Prop} : p∈primeSet P X ↔ p≤X ∧ p.Prime ∧ P p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

theorem endpoint {ε : ℝ} (hε : 0<ε) : ∃ D : ℝ, 0<D ∧ ∀ᶠ X : ℕ in atTop,
    ((primeSet (fun p => ε*log p≤|(S p:ℝ)/p-log p/2|) X).card:ℝ) ≤
      D*X*exp (-rate X/1024) := by
  classical
  obtain ⟨C,hC,hband⟩ := band hε
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨N₀,h₀⟩ := eventually_atTop.mp (hband.and ((hlog.eventually_ge_atTop 1).and
    ((tendsto_log_atTop.comp hlog).eventually_ge_atTop (log 64))))
  refine ⟨(1+C)*2^64,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop ((256:ℕ)^64),eventually_ge_atTop (N₀^64),hlog.eventually_ge_atTop 1]
    with X hX hbig hXlog
  obtain ⟨N,hN,_,hlo,hhi⟩ := ThetaPrimeConcentration.dyadic_cover hX
  have hN₀ : N₀≤N := by
    by_contra! lt
    exact (Nat.pow_lt_pow_left lt (by norm_num : 64≠0)).not_ge (hbig.trans hlo)
  obtain ⟨hb,hNlog,h64⟩ := h₀ N hN₀
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
  have hn : (N:ℝ)^56≤(N:ℝ)^64*exp (-rate N/64) := by
    have he (k : ℕ) : (N:ℝ)^k=exp ((k:ℝ)*log N) := by rw [exp_nat_mul,exp_log hr]
    rw [he 56,he 64,←exp_add,exp_le_exp]
    norm_num
    have hl := rate_le hNlog
    change 1≤log (N:ℝ) at hNlog
    linarith
  have hx : 0<X := (show 0<(256:ℕ)^64 by positivity).trans_le hX
  have hcomp := compare_rate (by omega : 0<N) hx hlo hNlog hXlog h64
  have hfrac : exp (-rate N/64)≤exp (-rate X/1024) := exp_le_exp.mpr (by linarith)
  have hscale : (N:ℝ)^64≤2^64*(X:ℝ) := by exact_mod_cast hhi
  change (E.card:ℝ)≤_
  calc
    _ ≤ (1+C)*((N:ℝ)^64*exp (-rate N/64)) := by linarith only [hc,hU,hn]
    _ ≤ (1+C)*((2^64*(X:ℝ))*exp (-rate X/1024)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hscale hfrac (exp_pos _).le (by positivity)) (by positivity)
    _ = _ := by ring

#print axioms endpoint
end
end Arxiv.«2501.03234».ThetaStrongPrimeTail
