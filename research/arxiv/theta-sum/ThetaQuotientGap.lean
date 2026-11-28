import ThetaQuadraticExcess

/-! Quantitative lower bounds on approximation by finite congruence classes. -/
namespace Arxiv.«2501.03234».ThetaQuotientGap
open Finset Filter Topology ThetaPrimeSpectrum ThetaLegendreFactors ThetaQuadraticExcess
open ThetaNaturalPrimeMeans

/-- The absolute Gauss sum suffices for a lower bound quadratic in the excess.
The sign of the Gauss sum is not required. -/
theorem excess_correlation_bound (hAP : ProgressionMangoldt) (q : ℕ) [Fact q.Prime]
    (hq : q%4=3) : ∃ C : ℝ, Tendsto (primeMean (fun p => (legendreSym q (p:ℤ):ℝ)*
      ((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 C) ∧
      Real.pi*(excess q:ℝ)^2/(Real.sqrt q*((q:ℝ)*q.totient)) ≤ |C| := by
  obtain ⟨L,C,hpos,hL,hC,_,_,hb,_⟩ := prime_correlation q hAP hq
  have hE := abs_excess q hq hpos hL
  have ho := Nat.odd_iff.mpr (show q%2=1 by omega)
  have hP := parityFactor_eq_excess q ho
  change parityFactor q= -2 * symbol q 2 * excess q at hP
  rw [hP,conductor_amplitude q ho] at hb
  have he (p : ℕ) : legendreSym q (p:ℤ)=symbol q p := by
    simp only [legendreSym,symbol,Int.cast_natCast]
  refine ⟨C,by simpa only [he,ThetaCharacterPrimeMeans.residual] using hC,?_⟩
  have hq0 : 0<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos
  have hs := Real.sqrt_pos.mpr hq0
  apply le_trans _ hb
  let E : ℝ := |(excess q:ℝ)|
  change E=_ at hE
  rw [show (excess q:ℝ)^2=E^2 from (sq_abs _).symm]
  have ht : (q.totient:ℝ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (Fact.out : q.Prime).pos).ne'
  have hn : ¬q∣2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  rcases symbol_unit q hn with h|h <;> rw [h] at hE ⊢ <;> push_cast at hE ⊢ <;>
    simp only [abs_mul,abs_neg,abs_of_pos hpos] <;> rw [show |(excess q:ℝ)|=E from rfl] <;>
    apply le_of_eq <;> field_simp [ht,hq0.ne',hs.ne',Real.pi_ne_zero] at hE ⊢ <;>
    norm_num at hE ⊢ <;> nlinarith only [congrArg (fun x : ℝ => x*E) hE]

private lemma prime_factor_three (n : ℕ) : n%4=3 → ∃ q : ℕ, q.Prime ∧ q%4=3 ∧ q∣n := by
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => exact fun h => ⟨p,hp,h,dvd_refl _⟩
  | mul a b ha hb =>
    intro h
    have hh : a%4=3 ∨ b%4=3 := by
      rw [Nat.mul_mod] at h
      have h₁ := Nat.mod_lt a (by decide : 0<4)
      have h₂ := Nat.mod_lt b (by decide : 0<4)
      interval_cases a%4 <;> interval_cases b%4 <;> first | decide | contradiction
    obtain h|h := hh
    · obtain ⟨q,hp,hq,hd⟩ := ha h
      exact ⟨q,hp,hq,dvd_mul_of_dvd_left hd b⟩
    · obtain ⟨q,hp,hq,hd⟩ := hb h
      exact ⟨q,hp,hq,dvd_mul_of_dvd_right hd a⟩

private lemma small_conductor (m : ℕ) [NeZero m] :
    ∃ q : ℕ, q.Prime ∧ q%4=3 ∧ q.Coprime m ∧ q≤4*m := by
  have hm := NeZero.pos m
  obtain ⟨q,hp,hq,hd⟩ := prime_factor_three (4*m-1) (by omega)
  refine ⟨q,hp,hq,hp.coprime_iff_not_dvd.mpr (fun h => ?_), (Nat.le_of_dvd (by omega) hd).trans (by omega)⟩
  have hx := dvd_mul_of_dvd_right h 4
  have H : q∣1 := by
    have he : 4*m=(4*m-1)+1 := by omega
    rwa [he,Nat.dvd_add_right hd] at hx
  exact hp.not_dvd_one H

private lemma period_gap_at_conductor (hAP : ProgressionMangoldt) {m q : ℕ} [NeZero m] (hp : q.Prime) (hq : q%4=3)
    (hcop : q.Coprime m) {B : ℝ} (hqB : (q:ℝ) ≤ B)
    {g : ℕ → ℝ} (hg : ThetaPeriodMeans.OnMod m g) {a : ℝ}
    (ha : a < Real.pi/(Real.sqrt B*B^2)) :
    ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g p|) X := by
  let : Fact q.Prime := ⟨hp⟩
  obtain ⟨C,hC,hbound⟩ := excess_correlation_bound hAP q hq
  have hE : excess q ≠ 0 := by
    intro hz
    have h := parityFactor_eq_excess q (Nat.odd_iff.mpr (by omega : q%2=1))
    change parityFactor q = -2 * symbol q 2 * excess q at h
    exact parityFactor_nonzero q hq (by simpa [hz] using h)
  have hE1 : (1:ℝ) ≤ (excess q:ℝ)^2 := by
    have h1 : (1:ℤ) ≤ (excess q)^2 := by have := sq_pos_of_ne_zero hE; omega
    exact_mod_cast h1
  have hφ : (q.totient:ℝ)≤q := by exact_mod_cast Nat.totient_le q
  have hB : 0 ≤ B := (Nat.cast_nonneg q).trans hqB
  have hden : Real.sqrt q*((q:ℝ)*q.totient) ≤ Real.sqrt (B)*B^2 := by
    rw [sq]
    gcongr
    exact hφ.trans hqB
  have hq0 : (0:ℝ)<q := by exact_mod_cast hp.pos
  have ht : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hf := div_le_div_of_nonneg_left Real.pi_pos.le (by positivity : 0<Real.sqrt q*((q:ℝ)*q.totient)) hden
  have hb : Real.pi/(Real.sqrt (B)*B^2) ≤ |C| := hf.trans ((div_le_div_of_nonneg_right
    (by simpa using mul_le_mul_of_nonneg_left hE1 Real.pi_pos.le) (by positivity)).trans hbound)
  apply periodic_error_of_correlation q hAP hcop (by omega) _ hg (ha.trans_le hb)
  simpa only [legendreSym,symbol,Int.cast_natCast,ThetaCharacterPrimeMeans.residual] using hC

/-- A numerical error floor for the original residual on every finite congruence quotient. -/
theorem effective_period_gap (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] (g : ZMod m → ℝ) {a : ℝ}
    (ha : a < Real.pi/(Real.sqrt (4*(m:ℝ))*(4*m)^2)) :
    ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g (p:ZMod m)|) X := by
  obtain ⟨q,hp,hq,hcop,hqm⟩ := small_conductor m
  exact period_gap_at_conductor hAP hp hq hcop (by exact_mod_cast hqm : (q:ℝ)≤4*m)
    (g:=fun p => g (p:ZMod m)) (fun n => by simp) ha

open ThetaPrimeDensity ArithmeticFunction

private theorem progression_weight_lower (hAP : ProgressionMangoldt) {c : ℝ} (hc : c<1/2) :
    ∀ᶠ N : ℕ in atTop, c*N < ∑ p ∈ primeSet (fun p => p%4=3) N, Real.log p := by
  classical
  obtain ⟨d,hcd,hd⟩ := exists_between hc
  have hlim := hAP (q:=4) (a:=3) (by decide) (by decide) (by decide)
  norm_num [show Nat.totient 4=2 by decide] at hlim
  obtain ⟨K,hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_gt_atTop 0,hlim.eventually_const_lt hd,
    hs.eventually_gt_atTop (K/(d-c))] with N hN hψ hsqrt
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hs0 := Real.sqrt_pos.mpr hN'
  have hh := (div_lt_iff₀ (sub_pos.mpr hcd)).mp hsqrt
  have hpow := mul_lt_mul_of_pos_right hh hs0
  have he := Real.sq_sqrt hN'.le
  have hmon : selectedPsi (fun p => p%4=3) N ≤ selectedPsi (fun p => p%4=3) (N+1) := by
    unfold selectedPsi
    rw [Finset.sum_range_succ]
    apply le_add_of_nonneg_right
    split_ifs <;> simp [vonMangoldt_nonneg]
  have hweight := (selected_prime_weight_bounds (fun p => p%4=3) N).2
  have hpsi' := (lt_div_iff₀ hN').mp hψ
  have hk := hK (N:ℝ)
  change K/(d-c)<Real.sqrt N at hsqrt
  change Real.sqrt N*(d-c)*Real.sqrt N > K*Real.sqrt N at hpow
  nlinarith only [hpsi',hmon,hweight,hk,hpow,congrArg (fun r : ℝ => r*(d-c)) he]

private theorem logarithmic_conductor (hAP : ProgressionMangoldt) {b : ℝ} (hb : 2<b) :
    ∀ᶠ m : ℕ in atTop, ∃ q : ℕ, q.Prime ∧ q%4=3 ∧ q.Coprime m ∧ (q:ℝ)≤b*Real.log m := by
  classical
  have hb0 : 0<b := by linarith
  have hb1 : 1/b<(1:ℝ)/2 := by rw [div_lt_div_iff₀ hb0 (by norm_num)]; linarith
  obtain ⟨c,hc,hc'⟩ := exists_between hb1
  have hc0 : 0<c := (one_div_pos.mpr hb0).trans hc
  have hcb := (div_lt_iff₀ hb0).mp hc
  have hl := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hN := tendsto_nat_floor_atTop.comp (hl.const_mul_atTop hb0)
  filter_upwards [eventually_gt_atTop 1, hN.eventually (progression_weight_lower hAP hc'),
    hl.eventually_gt_atTop (c/(c*b-1))] with m hm hθ hlm
  let N := ⌊b*Real.log m⌋₊
  let A := primeSet (fun p => p%4=3) N
  have hN0 : 0≤b*Real.log m := mul_nonneg hb0.le (Real.log_nonneg (by exact_mod_cast hm.le))
  change c/(c*b-1) < Real.log m at hlm
  have hlm' := (div_lt_iff₀ (sub_pos.mpr hcb)).mp hlm
  have hf := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one (b*Real.log m)) hc0
  have hlt : Real.log m < c*N := by dsimp only [N]; nlinarith only [hlm',hf]
  have hlog : Real.log m < ∑ p∈A,Real.log p := hlt.trans hθ
  have hmem {p : ℕ} (h : p∈A) : p∈Nat.primesLE N ∧ p%4=3 := by
    simpa only [A,primeSet,mem_filter] using h
  have hpr {p : ℕ} (h : p∈A) := Nat.prime_of_mem_primesLE (hmem h).1
  by_contra! h
  have hd : ∏ p∈A,p ∣ m := Finset.prod_primes_dvd m (fun _ hp => (hpr hp).prime) fun p hp => by
    by_contra H
    exact (not_le.mpr (h p (hpr hp) (hmem hp).2 ((hpr hp).coprime_iff_not_dvd.mpr H)))
      ((by exact_mod_cast Nat.le_of_mem_primesLE (hmem hp).1 : (p:ℝ)≤N).trans (Nat.floor_le hN0))
  have hpos : 0<∏ p∈A,p := prod_pos fun p hp => (hpr hp).pos
  have hp0 : (0:ℝ) < ((∏ p∈A,p):ℕ) := by exact_mod_cast hpos
  have hm0 : 0 < m := by omega
  have hnat := Nat.le_of_dvd hm0 hd
  have hle : (((∏ p∈A,p):ℕ):ℝ) ≤ m := by exact_mod_cast hnat
  push_cast at hp0 hle
  have H := Real.log_le_log hp0 hle
  rw [Real.log_prod (fun p hp => by exact_mod_cast (hpr hp).ne_zero)] at H
  exact hlog.not_ge H

/-- The approximation-error floor decreases at most as a power of the logarithm
of the fixed period. The endpoint cutoff may depend on the period and model. -/
theorem logarithmic_period_gap (hAP : ProgressionMangoldt) {b : ℝ} (hb : 2<b) :
    ∀ᶠ m : ℕ in atTop, ∀ g : ZMod m → ℝ, ∀ a < Real.pi/
      (Real.sqrt (b*Real.log m)*(b*Real.log m)^2), ∀ᶠ X : ℕ in atTop,
      a < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g (p:ZMod m)|) X := by
  filter_upwards [eventually_gt_atTop 0,logarithmic_conductor hAP hb] with m hm H
  let : NeZero m := ⟨hm.ne'⟩
  obtain ⟨q,hp,hq,hcop,hqm⟩ := H
  intro g a ha
  exact period_gap_at_conductor hAP hp hq hcop hqm (g:=fun p => g (p:ZMod m)) (fun n => by simp) ha

/-- The coefficient two in the missing-conductor argument is sharp. For any
smaller positive coefficient, arbitrarily large periods contain every prime
of the required class up to that multiple of their logarithm. -/
theorem sharp_conductor_threshold (hAP : ProgressionMangoldt) {b : ℝ}
    (hb : 0<b) (hb2 : b<2) :
    ∃ᶠ m : ℕ in atTop, ∀ q : ℕ, q.Prime → q%4=3 → (q:ℝ)≤b*Real.log m → q∣m := by
  classical
  have hroom : (1:ℝ)/2 < 1/b := by rw [div_lt_div_iff₀ (by norm_num) hb]; linarith
  obtain ⟨d,hd,hd'⟩ := exists_between hroom
  have hdb : b*d<1 := by simpa [mul_comm] using (lt_div_iff₀ hb).mp hd'
  have hlim := hAP (q:=4) (a:=3) (by decide) (by decide) (by decide)
  norm_num [show Nat.totient 4=2 by decide] at hlim
  have hshift := (hlim.comp (tendsto_add_atTop_nat 1)).eventually_lt_const hd
  apply frequently_atTop.mpr
  intro m₀
  obtain ⟨N,hlo,hup,hsize,hroomN⟩ := ((progression_weight_lower hAP (by norm_num : (1:ℝ)/4 < 1/2)).and
    (hshift.and ((eventually_ge_atTop (4*(m₀+1))).and
      ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_gt_atTop (b*d/(1-b*d)))))).exists
  let A := primeSet (fun p => p%4=3) N
  let M := ∏ p∈A,p
  have hmem (p : ℕ) : p∈A ↔ p∈Nat.primesLE N ∧ p%4=3 := by simp only [A, primeSet, mem_filter]
  have hpr (p : ℕ) (h : p∈A) := Nat.prime_of_mem_primesLE ((hmem p).mp h).1
  have hm : 0<M := prod_pos fun p hp => (hpr p hp).pos
  have hlog : Real.log M=∑ p∈A,Real.log p := by
    simp only [M,Nat.cast_prod]
    exact Real.log_prod (fun p hp => by exact_mod_cast (hpr p hp).ne_zero)
  have hlarge : m₀ ≤ M := by
    change (1:ℝ)/4*N < ∑ p∈A,Real.log p at hlo
    rw [← hlog] at hlo
    have hx : (4:ℝ)*(m₀+1) ≤ N := by exact_mod_cast hsize
    exact_mod_cast (show (m₀:ℝ) ≤ M by linarith [Real.log_le_self (Nat.cast_nonneg M)])
  refine ⟨M,hlarge,fun q hp hq hqm => ?_⟩
  have hu := (selected_prime_weight_bounds (fun p => p%4=3) N).1
  change selectedPsi (fun p => p%4=3) (N+1)/((N+1:ℕ):ℝ)<d at hup
  have hup' := (div_lt_iff₀ (by positivity : (0:ℝ)<((N+1:ℕ):ℝ))).mp hup
  push_cast at hup'
  have hbnd := mul_lt_mul_of_pos_left (hu.trans_lt hup') hb
  change b*d/(1-b*d) < (N:ℝ) at hroomN
  have hr := (div_lt_iff₀ (sub_pos.mpr hdb)).mp hroomN
  have hle : (q:ℝ) ≤ N := by rw [hlog] at hqm; change b*(∑ p∈A,Real.log p) < _ at hbnd; nlinarith
  exact dvd_prod_of_mem _ ((hmem q).mpr ⟨Nat.mem_primesLE.mpr ⟨by exact_mod_cast hle,hp⟩,hq⟩)

#print axioms sharp_conductor_threshold

#print axioms logarithmic_period_gap

#print axioms effective_period_gap
#print axioms excess_correlation_bound
end Arxiv.«2501.03234».ThetaQuotientGap
