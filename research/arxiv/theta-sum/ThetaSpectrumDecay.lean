import ThetaConductorProduct
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Decay and sum of the prime-conductor quadratic spectrum. -/
namespace Arxiv.«2501.03234».ThetaSpectrumDecay
open Finset Filter Topology ThetaLegendreFactors ThetaQuadraticExcess ThetaConductorProduct
open ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans
variable (q : ℕ) [Fact q.Prime]

private lemma normalizer (hq : q%4=3) {L : ℝ} (hpos : 0<L)
    (hL : Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L)) :
    |(parityFactor q:ℝ)*L*(1-(symbol q 2:ℝ)/2)|=Real.pi*(excess q:ℝ)^2/Real.sqrt q := by
  have he := abs_excess q hq hpos hL
  have hP := parityFactor_eq_excess q (Nat.odd_iff.mpr (by omega : q%2=1))
  change parityFactor q= -2 * symbol q 2 * excess q at hP
  rw [hP]
  let E : ℝ := |(excess q:ℝ)|
  change E=_ at he
  rw [show (excess q:ℝ)^2=E^2 from (sq_abs _).symm]
  have hq0 := (Fact.out : q.Prime).pos
  have hs : 0 < Real.sqrt (q:ℝ) := by positivity
  have hn : ¬q∣2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  rcases symbol_unit q hn with h|h <;> rw [h] at he ⊢ <;> push_cast at he ⊢ <;>
    simp only [abs_mul,abs_neg,abs_of_pos hpos] <;> rw [show |(excess q:ℝ)|=E from rfl] <;>
    field_simp [hs.ne',Real.pi_ne_zero] at he ⊢ <;> norm_num at he ⊢ <;>
    nlinarith only [congrArg (fun x : ℝ => x*E) he]

/-- Exact magnitude in terms of a finite integer and an explicitly approximable
Euler product over inert odd primes. -/
theorem correlation_size (hAP : ProgressionMangoldt) (hq : q%4=3) :
    ∃ C : ℝ, Tendsto (primeMean (fun p => (symbol q p:ℝ)*residual p)) atTop (𝓝 C) ∧
      |C| = Real.pi*(excess q:ℝ)^2/Real.sqrt q*((q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)))*inertProduct q ∧
      ∀ n : ℕ, inertPrefix q n ≤ inertProduct q ∧
        inertProduct q ≤ inertPrefix q n*(((n:ℝ)+2)/(n+1))^2 := by
  obtain ⟨L,hpos,hL,hC⟩ := correlation_product q hAP hq
  obtain ⟨_,_,_,_,_,hA⟩ := amplitude_sum q hAP hq
  have H := inertProduct_bounds q (by omega) hA.summable
  have hp1 : (1:ℝ)<q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hs : 0≤(q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)) := by apply div_nonneg (by positivity); apply mul_nonneg (by linarith); nlinarith
  refine ⟨_,hC,?_,product_interval q (by omega) hA.summable⟩
  rw [abs_mul,abs_of_nonneg (zero_le_one.trans H.1),abs_mul,abs_of_nonneg hs,normalizer q hq hpos hL]

private theorem harmonic_upper (hq : q≠2) {L : ℝ}
    (hL : Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L)) : L≤2+Real.log q := by
  have hp := (Fact.out : q.Prime)
  have H := (abs_le.mp (reciprocal_error q hq hL hp.pos)).2
  rw [div_self (by exact_mod_cast hp.ne_zero)] at H
  have hc (n : ℕ) : term q n ≤ (n:ℝ)⁻¹ := by
    have hh : (symbol q n:ℝ) ≤ 1 := by
      by_cases h : q∣n
      · simp [symbol_zero q h]
      · rcases symbol_unit q h with h|h <;> norm_num [h]
    simpa only [term,one_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg n)
  have hsum := sum_le_sum (s:=range q) (fun n _ => hc n)
  have he : ∑ n∈range (q+1),(n:ℝ)⁻¹ = (harmonic q:ℝ) := by
    rw [sum_range_succ',harmonic]
    push_cast
    simp
  have ha := (sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => (n:ℝ)⁻¹)
    (Finset.range_mono (Nat.le_succ q)) (fun n _ _ => by positivity)).trans_eq he
  linarith [harmonic_le_one_add_log q]

/-- An explicit uniform upper bound on each nonzero correlation. -/
theorem correlation_decay (hAP : ProgressionMangoldt) (hq : q%4=3) {C : ℝ}
    (hC : Tendsto (primeMean (fun p => (symbol q p:ℝ)*residual p)) atTop (𝓝 C)) :
    |C| ≤ 144*(2+Real.log q)^2/((q:ℝ)*Real.sqrt q) := by
  obtain ⟨L,hpos,hL⟩ := reciprocal_limit q (by omega)
  obtain ⟨D,hD,hsize,_⟩ := correlation_size q hAP hq
  have HCD := tendsto_nhds_unique hC hD
  rw [HCD,hsize]
  have he := abs_excess q hq hpos hL
  have hp := (Fact.out : q.Prime)
  have hq2 : (2:ℝ)≤q := by exact_mod_cast hp.two_le
  have hq0 : (0:ℝ)<q := by linarith
  have hs := Real.sqrt_pos.mpr hq0
  have hsq := Real.sq_sqrt hq0.le
  have hn : ¬q∣2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have hex : |(excess q:ℝ)| ≤ 3*Real.sqrt q*L/Real.pi := by
    rw [he]
    gcongr
    rcases symbol_unit q hn with h|h <;> norm_num [h]
  have hmass : Real.pi*(excess q:ℝ)^2/Real.sqrt q ≤ 9*Real.sqrt q*L^2 := by
    calc Real.pi*(excess q:ℝ)^2/Real.sqrt q = Real.pi*|(excess q:ℝ)|^2/Real.sqrt q := by rw [sq_abs]
         _ ≤ Real.pi*(3*Real.sqrt q*L/Real.pi)^2/Real.sqrt q := by gcongr
         _ = 9*Real.sqrt q*L^2/Real.pi := by field_simp; ring
         _ ≤ _ := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
  have hh₁ : (q:ℝ)/2 ≤ q-1 := by linarith
  have hh₂ : (q:ℝ)^2/2 ≤ (q:ℝ)^2-1 := by nlinarith
  have hden : (q:ℝ)/2*((q:ℝ)^2/2) ≤ ((q:ℝ)-1)*((q:ℝ)^2-1) :=
    mul_le_mul hh₁ hh₂ (by positivity) (by linarith)
  have hr : (q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)) ≤ 4/(q:ℝ)^2 := by
    apply (div_le_div_iff₀ (mul_pos (by linarith) (by nlinarith)) (by positivity)).2
    nlinarith only [hden]
  have hr0 : 0≤(q:ℝ)/(((q:ℝ)-1)*((q:ℝ)^2-1)) :=
    div_nonneg hq0.le (mul_nonneg (by linarith) (by nlinarith))
  obtain ⟨_,_,_,_,_,hA⟩ := amplitude_sum q hAP hq
  have hZ := inertProduct_bounds q (by omega) hA.summable
  have hLmax := harmonic_upper q (by omega) hL
  have HM := mul_le_mul (mul_le_mul hmass hr hr0 (by positivity)) hZ.2
    (zero_le_one.trans hZ.1) (by positivity)
  apply HM.trans
  calc _ = 144*L^2/((q:ℝ)*Real.sqrt q) := by
          field_simp
          nlinarith only [hsq]
       _ ≤ _ := by gcongr

private theorem summable_envelope : Summable (fun n : ℕ => 144*(2+Real.log n)^2/((n:ℝ)*Real.sqrt n)) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(-(5:ℝ)/4)) := Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (hs.mul_left 1296)
  have hlog := (isLittleO_log_rpow_atTop (show 0<(1:ℝ)/8 by norm_num)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop 1,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hlog] with n hn h
  have hx : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hx1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hL := Real.log_nonneg hx1
  have ha := Real.rpow_nonneg hx.le ((1:ℝ)/8)
  have hA := Real.one_le_rpow hx1 (by norm_num : 0≤(1:ℝ)/8)
  simp only [Real.norm_eq_abs,abs_of_nonneg hL,abs_of_nonneg ha,one_mul] at h
  have h₁ : 2+Real.log n ≤ 3*(n:ℝ)^((1:ℝ)/8) := by linarith
  have h₂ : (2+Real.log n)^2 ≤ (3*(n:ℝ)^((1:ℝ)/8))^2 := by gcongr
  have hd : (n:ℝ)*Real.sqrt n = (n:ℝ)^((3:ℝ)/2) := by
    calc (n:ℝ)*Real.sqrt n = (n:ℝ)^(1:ℝ)*(n:ℝ)^((1:ℝ)/2) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
         _ = _ := by rw [← Real.rpow_add hx]; norm_num
  have he : ((n:ℝ)^((1:ℝ)/8))^2 = (n:ℝ)^((1:ℝ)/4) := by
    rw [← Real.rpow_two,← Real.rpow_mul hx.le]; norm_num
  have h5 : (n:ℝ)^((1:ℝ)/4)/(n:ℝ)^((3:ℝ)/2)=(n:ℝ)^(-(5:ℝ)/4) := by
    rw [← Real.rpow_sub hx]; norm_num
  rw [Real.norm_of_nonneg (by positivity)]
  change _ ≤ 1296*(n:ℝ)^(-(5:ℝ)/4)
  rw [hd,← h5]
  calc _ ≤ 144*(3*(n:ℝ)^((1:ℝ)/8))^2/(n:ℝ)^((3:ℝ)/2) := by gcongr
       _ = _ := by rw [mul_pow,he]; ring

/-- Odd prime conductors for the Legendre coefficients of the original residual. -/
abbrev OddPrime := {q : ℕ // q.Prime ∧ Odd q}

instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩

noncomputable def coefficient (q : OddPrime) : ℝ :=
  limUnder atTop (primeMean (fun p => (legendreSym q.val (p:ℤ):ℝ)*((S p:ℝ)/p-Real.log p/2)))

theorem coefficient_limit (hAP : ProgressionMangoldt) (r : OddPrime) :
    Tendsto (primeMean (fun p => (legendreSym r.val (p:ℤ):ℝ)*((S p:ℝ)/p-Real.log p/2)))
      atTop (𝓝 (coefficient r)) := by
  have he (p : ℕ) : legendreSym r.val (p:ℤ)=symbol r.val p := by
    simp only [legendreSym,symbol,Int.cast_natCast]
  simp only [coefficient,he]
  let f := primeMean (fun p => (symbol r.val p:ℝ)*ThetaCharacterPrimeMeans.residual p)
  change Tendsto f atTop (𝓝 (limUnder atTop f))
  dsimp only [f]
  rcases (show r.val%4=1 ∨ r.val%4=3 by have h := Nat.odd_iff.mp r.property.2; omega) with h|h
  · have H := ThetaPrimeSpectrum.even_character_mean r.val hAP h
    rwa [H.limUnder_eq]
  · obtain ⟨C,H,_⟩ := correlation_size r.val hAP h
    rwa [H.limUnder_eq]

/-- Pointwise decay for the canonical prime-conductor coefficient. -/
theorem coefficient_bound (hAP : ProgressionMangoldt) (r : OddPrime) :
    |coefficient r| ≤ 144*(2+Real.log r.val)^2/((r.val:ℝ)*Real.sqrt r.val) := by
  have h := coefficient_limit hAP r
  have he (p : ℕ) : legendreSym r.val (p:ℤ)=symbol r.val p := by simp only [legendreSym,symbol,Int.cast_natCast]
  simp only [he] at h
  change Tendsto (primeMean (fun p => (symbol r.val p:ℝ)*ThetaCharacterPrimeMeans.residual p)) atTop (𝓝 (coefficient r)) at h
  rcases (show r.val%4=1 ∨ r.val%4=3 by have hn := Nat.odd_iff.mp r.property.2; omega) with hq|hq
  · have h0 := tendsto_nhds_unique h (ThetaPrimeSpectrum.even_character_mean r.val hAP hq)
    rw [h0,abs_zero]
    positivity
  · exact correlation_decay r.val hAP hq h

/-- Absolute summability across all prime quadratic conductors. -/
theorem summable_coefficients (hAP : ProgressionMangoldt) :
    Summable (fun r : OddPrime => |coefficient r|) := by
  apply Summable.of_nonneg_of_le (fun r => abs_nonneg _) _ (summable_envelope.comp_injective Subtype.val_injective)
  exact coefficient_bound hAP

/-- The prime quadratic component converges uniformly in the integer argument. -/
theorem uniform_quadratic_series (hAP : ProgressionMangoldt) :
    TendstoUniformly (fun (s : Finset OddPrime) (n : ℕ) =>
      ∑ r∈s, coefficient r*(legendreSym r.val (n:ℤ):ℝ))
      (fun n => ∑' r : OddPrime,coefficient r*(legendreSym r.val (n:ℤ):ℝ)) atTop := by
  apply tendstoUniformly_tsum (summable_coefficients hAP)
  intro r n
  simp only [Real.norm_eq_abs,abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  have he : legendreSym r.val (n:ℤ)=symbol r.val n := by simp only [legendreSym,symbol,Int.cast_natCast]
  rw [he]
  by_cases h : r.val∣n
  · simp [symbol_zero r.val h]
  · rcases symbol_unit r.val h with h|h <;> simp [h]

/-- The uniformly convergent sum of the individual prime-conductor quadratic modes. -/
noncomputable def quadraticPart (n : ℕ) : ℝ :=
  ∑' r : OddPrime, coefficient r*(legendreSym r.val (n:ℤ):ℝ)

private noncomputable abbrev character (q : OddPrime) (n : ℕ) : ℝ := (legendreSym q.val (n:ℤ):ℝ)

private lemma char_bound (r : OddPrime) (n : ℕ) : |character r n| ≤ 1 := by
  have he : legendreSym r.val (n:ℤ) = symbol r.val n := by simp only [legendreSym,symbol,Int.cast_natCast]
  by_cases h : r.val∣n
  · simp [character,he,symbol_zero r.val h]
  · rcases symbol_unit r.val h with h|h <;> simp [character,he,h]

private lemma finite_projection (hAP : ProgressionMangoldt) (q : OddPrime)
    (s : Finset OddPrime) (hs : q∈s) :
    Tendsto (primeMean (fun p => character q p*∑ r∈s,coefficient r*character r p))
      atTop (𝓝 (coefficient q)) := by
  have hpair (r : OddPrime) := ThetaPrimeSpectrum.prime_character_pair q.val hAP
    (fun h => by have := q.property.2; rw [h] at this; exact (by decide : ¬ Odd 2) this) r.val
  have hh (r : OddPrime) : Tendsto (fun X => coefficient r * primeMean (fun p => character q p*character r p) X)
        atTop (𝓝 (coefficient r*(if q=r then 1 else 0))) := by
    simpa only [character,legendreSym,symbol,Int.cast_natCast,Subtype.val_inj] using (hpair r).const_mul (coefficient r)
  have H := tendsto_finsetSum s (fun r _ => hh r)
  simp only [mul_ite,mul_one,mul_zero,sum_ite_eq,if_pos hs] at H
  apply H.congr'
  filter_upwards with X
  simp only [primeMean,mul_sum,← mul_div_assoc,← sum_div]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro r hr
  ring

/-- Subtracting the uniformly convergent quadratic series removes every odd
prime-conductor Legendre correlation of the original residual. -/
theorem orthogonal_remainder (hAP : ProgressionMangoldt) (q : OddPrime) :
    Tendsto (primeMean (fun p => (legendreSym q.val (p:ℤ):ℝ)*
      ((S p:ℝ)/p-Real.log p/2-quadraticPart p))) atTop (𝓝 0) := by
  have hcomponent : Tendsto (primeMean (fun p => character q p*quadraticPart p)) atTop (𝓝 (coefficient q)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu := Metric.tendstoUniformly_iff.mp (uniform_quadratic_series hAP) (ε/2) (half_pos hε)
    obtain ⟨s,hs,hU⟩ := ((eventually_ge_atTop ({q}:Finset OddPrime)).and hu).exists
    let f (p : ℕ) := ∑ r∈s,coefficient r*character r p
    have H := finite_projection hAP q s (hs (mem_singleton_self q))
    have hx := (Metric.tendsto_nhds.mp H) (ε/2) (half_pos hε)
    have hπ : Tendsto (fun X : ℕ => (X.primeCounting:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
    filter_upwards [hx,hπ.eventually_gt_atTop 0] with X hX hpos
    change dist (primeMean (fun p => character q p*f p) X) (coefficient q) < ε/2 at hX
    apply lt_of_le_of_lt (dist_triangle _ (primeMean (fun p => character q p*f p) X) _)
    have hb : dist (primeMean (fun p => character q p*quadraticPart p) X)
        (primeMean (fun p => character q p*f p) X) ≤ ε/2 := by
      rw [Real.dist_eq,primeMean,primeMean,← sub_div,← sum_sub_distrib,abs_div,abs_of_pos hpos,div_le_iff₀ hpos]
      apply (abs_sum_le_sum_abs ..).trans
      calc _ ≤ ∑ _p∈X.primesLE, ε/2 := sum_le_sum (fun p _ => by
              rw [← mul_sub,abs_mul]
              apply (mul_le_of_le_one_left (abs_nonneg _) (char_bound q p)).trans
              exact (hU p).le)
           _ = _ := by simp [Nat.primesLE_card_eq_primeCounting,mul_comm]
    linarith
  have H := (coefficient_limit hAP q).sub hcomponent
  rw [sub_self] at H
  apply H.congr'
  filter_upwards with X
  simp only [primeMean,character,mul_sub,sum_sub_distrib,sub_div]

#print axioms orthogonal_remainder

#print axioms coefficient_bound
#print axioms coefficient_limit
#print axioms summable_coefficients
#print axioms uniform_quadratic_series

#print axioms correlation_decay
#print axioms harmonic_upper
#print axioms correlation_size
end Arxiv.«2501.03234».ThetaSpectrumDecay
