import ThetaAbelPrimes
import ThetaPrimeVariance

/-! Prime-scale approximation of the off-diagonal by finite reciprocal rows. -/
namespace Arxiv.«2501.03234».ThetaPrimeTailTransfer
open Finset Filter ThetaPrimeAsymptotic ThetaNondivisibleCone ThetaDivisibleDiagonal ThetaPrimeMeanSquare

/-- The deterministic cone error divided by p vanishes uniformly on the
prime scale N^56 ≤ p ≤ N^64. -/
theorem normalized_cone_error {N p : ℕ} (hN : 2≤N) (hp : p.Prime) (hl : N^56≤p) (hh : p≤N^64) :
    |offDiagonal p/p-(8/Real.pi^2)*(rationalCone p (N^52) (coneWidth N):ℝ)| ≤
      (2265642+4*(1+64*Real.log N))/N := by
  let : Fact p.Prime := ⟨hp⟩
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hK : coneWidth N%2=1 := by unfold coneWidth; omega
  have hk : 0<(coneWidth N:ℝ) := by exact_mod_cast (show 0<coneWidth N by unfold coneWidth; omega)
  have hKN : coneWidth N≤N := by unfold coneWidth; omega
  have hNK : (N:ℝ)≤2*(coneWidth N:ℝ) := by exact_mod_cast (show N≤2*coneWidth N by unfold coneWidth; omega)
  have ho : p%2=1 := by
    rcases hp.eq_two_or_odd with h|h
    · have := ThetaPrimeDensity.cutoff_inside hN hl; have := Nat.one_le_pow 52 N (by omega); omega
    · exact h
  have hlog : Real.log p≤64*Real.log N := by
    have h := Real.log_le_log hp' (show (p:ℝ)≤(N:ℝ)^64 by exact_mod_cast hh)
    simpa only [Real.log_pow,Nat.cast_ofNat] using h
  have hln : 0≤1+Real.log p := by linarith [Real.log_nonneg (by exact_mod_cast hp.one_le : (1:ℝ)≤p)]
  have hbound : 2*(1+Real.log p)/coneWidth N≤4*(1+64*Real.log N)/N := by
    rw [div_le_div_iff₀ hk hn]
    nlinarith only [mul_le_mul_of_nonneg_left hNK hln,mul_le_mul_of_nonneg_right hlog hk.le]
  have h := vanishing_cone_error hN hK hKN hl hh ho
  rw [show offDiagonal p/p-(8/Real.pi^2)*(rationalCone p (N^52) (coneWidth N):ℝ)=
    (offDiagonal p-(8*p/Real.pi^2)*(rationalCone p (N^52) (coneWidth N):ℝ))/p by field_simp,
    abs_div,abs_of_pos hp']
  apply (div_le_div_of_nonneg_right h hp'.le).trans
  calc
    _ = 2265642/N+2*(1+Real.log p)/coneWidth N := by field_simp
    _ ≤ 2265642/N+4*(1+64*Real.log N)/N := add_le_add le_rfl hbound
    _ = _ := by ring

open ThetaRowCorrelations ThetaReciprocalInversion ThetaReciprocalBlocks ThetaConditionalRows
open ThetaPeriodMeans

/-- The denominator-truncated window at the prime scale N. -/
noncomputable def model (T N n : ℕ) : ℝ :=
  low T (coneWindow (coneWidth N)) (commonWeight (2*N^52)) n

private lemma commonWeight_mono (d : ℕ) : Monotone (fun Y => commonWeight Y d) := by
  intro Y Z h
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro g hg
  obtain ⟨hd,ho⟩ := mem_filter.mp hg
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2.trans (Nat.div_le_div_right h)⟩,ho⟩

private lemma model_cauchy (T n : ℕ) : CauchySeq (fun N => model T N n) := by
  let w (d N : ℕ) := commonWeight (2*N^52) d
  have hrow (d) (hd : d∈Icc 2 T) :
      ∃ z : ℝ, Tendsto (fun N => row d (coneWindow (coneWidth N) d) n) atTop (nhds z) := by
    obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (row_cauchy (mem_Icc.mp hd).1 n)
    refine ⟨z,hz.comp (tendsto_atTop.mpr (fun B => ?_))⟩
    filter_upwards [eventually_ge_atTop (B+3)] with N hN
    have h₁ : d≠1 := by have := (mem_Icc.mp hd).1; omega
    have hd' : 1≤d := by have := (mem_Icc.mp hd).1; omega
    have h₂ := Nat.le_mul_of_pos_right (coneWidth N) hd'
    simp only [coneWindow,if_neg h₁]
    unfold coneWidth at *; omega
  have hw (d) : Tendsto (w d) atTop (nhds (⨆ N, w d N)) := by
    apply tendsto_atTop_ciSup
    · intro N M h; exact commonWeight_mono d (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 52))
    · refine ⟨∑' g : ℕ,((g:ℝ)^2)⁻¹,?_⟩
      rintro _ ⟨N,rfl⟩; exact (commonWeight_bounds _ d).2
  classical
  let z (d : ℕ) := if hd : d∈Icc 2 T then (hrow d hd).choose else 0
  have hz (d) (hd : d∈Icc 2 T) : Tendsto (fun N => row d (coneWindow (coneWidth N) d) n) atTop (nhds (z d)) := by
    simpa only [z,dif_pos hd] using (hrow d hd).choose_spec
  have H := tendsto_finsetSum (Icc 2 T) (fun d hd => ((hw d).div_const d).mul (hz d hd))
  exact H.cauchySeq

/-- A single fixed scale approximates all sufficiently large windows through
denominator T, simultaneously on every residue and every prime. -/
theorem freeze_model (T : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ V : ℕ, 2≤V ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, |model T N n-model T V n| ≤ ε := by
  let P := T.factorial
  have hmod (N) : OnMod P (model T N) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  have h (j : ℕ) : ∀ᶠ b : ℕ in atTop, ∀ N≥b, ∀ V≥b, |model T N j-model T V j|≤ε := by
    obtain ⟨b,hb⟩ := Metric.cauchySeq_iff.mp (model_cauchy T j) ε hε
    exact eventually_atTop.mpr ⟨b,fun B hB N hN V hV => (hb N (hB.trans hN) V (hB.trans hV)).le⟩
  obtain ⟨V,hV,hA⟩ := ((eventually_ge_atTop 2).and ((eventually_all_finset (range P)).mpr (fun j _ => h j))).exists
  refine ⟨V,hV,?_⟩; filter_upwards [eventually_ge_atTop V] with N hN
  intro n
  rw [← hmod N n,← hmod V n]
  exact hA _ (mem_range.mpr (Nat.mod_lt n (Nat.factorial_pos _))) N hN V le_rfl

open ThetaDivisibleDiagonal ThetaDenominatorTails ThetaPrimeDensity

/-- The off-diagonal on the scale of the rational cone. -/
noncomputable def scaledOff (p : ℕ) : ℝ := (Real.pi^2/8)*(offDiagonal p/p)

private lemma cone_error_vanishes {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p : ℕ, p.Prime → N^56≤p → p≤N^64 →
      |scaledOff p-(rationalCone p (N^52) (coneWidth N):ℝ)|≤ε := by
  let A := Real.pi^2/8
  have hlog : Tendsto (fun N : ℕ => Real.log N/(N:ℝ)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => A*((2265642+4*(1+64*Real.log N))/N)) atTop (nhds 0) := by
    have H := ((hi.const_mul 2265646).add (hlog.const_mul 256)).const_mul A
    simp only [mul_zero,add_zero] at H
    apply H.congr'; filter_upwards with N; simp only [div_eq_mul_inv]; ring
  filter_upwards [eventually_ge_atTop 2,hlim.eventually_le_const hε] with N hN hbound
  intro p hp hl hh
  have hc : A*(8/Real.pi^2)=1 := by dsimp [A]; field_simp
  calc
    _ = A*|offDiagonal p/p-(8/Real.pi^2)*(rationalCone p (N^52) (coneWidth N):ℝ)| := by
      rw [← abs_of_nonneg (show 0≤A by dsimp [A]; positivity),← abs_mul]
      congr 1; rw [mul_sub,← mul_assoc,hc,one_mul]; rfl
    _ ≤ ε := (mul_le_mul_of_nonneg_left (normalized_cone_error hN hp hl hh)
      (by dsimp [A]; positivity)).trans hbound

private lemma low_split {T N : ℕ} (h : T≤N) (K : ℕ → ℕ) (a : ℕ → ℝ) (p : ℕ) :
    low N K a p=low T K a p+low N K (fun d => if T<d then a d else 0) p := by
  classical
  let f d := (a d/d)*row d (K d) p
  have hs : (Icc 2 N).filter (·≤T)=Icc 2 T := by ext d; simp; omega
  have hcut (d : ℕ) : (if T<d then a d else 0)/d*row d (K d) p=
      if ¬d≤T then f d else 0 := by
    by_cases hd : d≤T <;> simp [f,hd,not_lt_of_ge,lt_of_not_ge]
  unfold low; simp_rw [hcut]; rw [← sum_filter,← hs]
  exact (sum_filter_add_sum_filter_not (Icc 2 N) (·≤T) f).symm

private lemma fixed_bound (T V : ℕ) : ∃ F : ℝ, 0≤F ∧ ∀ n, |model T V n|≤F := by
  let P := T.factorial
  have hm : OnMod P (model T V) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  refine ⟨∑ j∈range P,|model T V j|,sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro n; rw [← hm n]; exact single_le_sum (f:=fun j => |model T V j|) (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.mod_lt n (Nat.factorial_pos _)))

private lemma small_error_bound (T V : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ {N p : ℕ}, 2≤N → p.Prime → p≤N^64 →
    |scaledOff p-model T V p|≤C*(N:ℝ)^2 := by
  obtain ⟨D,hD,h⟩ := S_sub_offDiagonal_asymptotic
  obtain ⟨F,hF,hf⟩ := fixed_bound T V
  let A := Real.pi^2/8
  let M := |(S 2:ℝ)/2-Real.log 2/2|+17000
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨|scaledOff 2|+A*(M+D)+F,by dsimp [A,M]; positivity,?_⟩
  intro N p hN hp hhi
  have h1 : (1:ℝ)≤(N:ℝ)^2 := one_le_pow₀ (by exact_mod_cast (show 1≤N by omega))
  apply (abs_sub _ _).trans
  by_cases htwo : p=2
  · subst p
    apply (add_le_add le_rfl (hf 2)).trans
    apply le_trans _ (le_mul_of_one_le_right (by dsimp [M,A]; positivity) h1)
    have hMD : 0≤A*(M+D) := by dsimp [M,A]; positivity
    linarith
  · let : Fact p.Prime := ⟨hp⟩
    have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
    have H := (div_le_iff₀ hp').mpr (h p (Nat.odd_iff.mp (hp.odd_of_ne_two htwo)))
    have H' : |(S p:ℝ)/p-Real.log p/2-offDiagonal p/p|≤D := by
      rw [show (S p:ℝ)/p-Real.log p/2-offDiagonal p/p=((S p:ℝ)-offDiagonal p-(p:ℝ)*Real.log p/2)/p by field_simp; ring]
      rwa [abs_div,abs_of_pos hp']
    have Ht := abs_sub_le (offDiagonal p/p) ((S p:ℝ)/p-Real.log p/2) 0
    simp only [sub_zero] at Ht
    rw [abs_sub_comm (offDiagonal p/p)] at Ht
    have ho : |offDiagonal p/p|≤M*(N:ℝ)^2+D := by dsimp [M]; linarith [small_scale_error hN hp hhi]
    rw [scaledOff,abs_mul,abs_of_nonneg hA]
    apply (add_le_add (mul_le_mul_of_nonneg_left ho hA) (hf p)).trans
    have hdf := mul_le_mul_of_nonneg_left h1 (show 0≤A*D+F by positivity)
    have hnn := mul_nonneg (abs_nonneg (scaledOff 2)) (sq_nonneg (N:ℝ))
    nlinarith only [hdf,hnn]

private noncomputable def middle (T N p : ℕ) := low N (coneWindow (coneWidth N))
  (fun d => if T<d then commonWeight (2*N^52) d else 0) p

private noncomputable def upper (N p : ℕ) :=
  windowExtension (above N (coneWindow (coneWidth N))) (2*N^52) p

private lemma band_point {N T V p : ℕ} (hN : 2≤N) (hTN : T≤N) (hp : p.Prime) (hlo : N^56≤p)
    {δ : ℝ} (hc : |scaledOff p-(rationalCone p (N^52) (coneWidth N):ℝ)|≤δ)
    (hf : |model T N p-model T V p|≤δ) :
    (scaledOff p-model T V p)^2 ≤ 12*δ^2+3*(middle T N p^2+‖upper N p‖^2) := by
  let K := coneWindow (coneWidth N)
  let a := commonWeight (2*N^52)
  let C : ℝ := rationalCone p (N^52) (coneWidth N)
  have hYp := cutoff_inside hN hlo
  have hY : N≤2*N^52 := by have := Nat.le_self_pow (by decide : 52≠0) N; omega
  have hu (d : ℕ) (hd : d∈Icc 1 (2*N^52)) : p.Coprime d := hp.coprime_iff_not_dvd.mpr
    (fun h => ((mem_Icc.mp hd).2.trans_lt hYp).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 h))
  have he := window_split hY K (by simp [K,coneWindow]) hu
  rw [cone_interpolation (show coneWidth N%2=1 by unfold coneWidth; omega) hp hYp] at he
  have hz : ((C:ℂ)-(model N N p:ℂ))=upper N p := by
    change ((↑(rationalCone p (N^52) (coneWidth N)):ℝ):ℂ)-(low N K a p:ℂ)=_
    change ((↑(rationalCone p (N^52) (coneWidth N)):ℝ):ℂ)-(low N K a p:ℂ)=windowExtension (above N K) (2*N^52) p
    rw [Complex.ofReal_ratCast]; linear_combination he
  have hhi : |C-model N N p|=‖upper N p‖ := by
    rw [← Real.norm_eq_abs,← Complex.norm_real,Complex.ofReal_sub,hz]
  have hm : model N N p=model T N p+middle T N p := low_split hTN K a p
  have ht₁ := abs_sub_le (scaledOff p) C (model N N p)
  have ht₂ := abs_sub_le (scaledOff p) (model N N p) (model T N p)
  have ht₃ := abs_sub_le (scaledOff p) (model T N p) (model T V p)
  rw [hhi] at ht₁
  rw [show model N N p-model T N p=middle T N p by rw [hm]; ring] at ht₂
  change |scaledOff p-C|≤δ at hc
  have ht : |scaledOff p-model T V p|≤2*δ+|middle T N p|+‖upper N p‖ := by linarith
  have H := pow_le_pow_left₀ (abs_nonneg _) ht 2
  rw [sq_abs] at H
  nlinarith only [H,sq_nonneg (2*δ-|middle T N p|),sq_nonneg (2*δ-‖upper N p‖),
    sq_nonneg (|middle T N p|-‖upper N p‖),sq_abs (middle T N p)]

private lemma log_decay {r : ℝ} (hr : 0<r) :
    Tendsto (fun N : ℕ => Real.log N/(N:ℝ)^r) atTop (nhds 0) :=
  (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

private lemma choose_tail {U Z ε : ℝ} (hε : 0<ε) :
    ∃ T : ℕ, 3≤T ∧ U*(Z/denominatorWeight T)^2≤ε := by
  have ht : Tendsto (fun T : ℕ => denominatorWeight T) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/16)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun T : ℕ => Z/denominatorWeight T) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp ht).const_mul Z
  have hlim := (hzero.pow 2).const_mul U
  simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero] at hlim
  exact ((eventually_ge_atTop 3).and (hlim.eventually_le_const hε)).exists

private lemma scale_approximation {ε : ℝ} (hε : 0<ε) :
    ∃ T V : ℕ, 3≤T ∧ 2≤V ∧ ∀ᶠ N : ℕ in atTop,
      ∑ p∈Nat.primesLE (N^64),(scaledOff p-model T V p)^2 ≤ ε*(N:ℝ)^64/Real.log N := by
  obtain ⟨U,hU,hm⟩ := ThetaSievedWindows.tail_prime_band
  obtain ⟨W,hW,hu⟩ := cut_variance
  let Z := ∑' g : ℕ,((g:ℝ)^2)⁻¹
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  let η := ε/(12*Real.log 4+7)
  have hη : 0<η := by dsimp [η]; positivity
  let δ := Real.sqrt η
  have hδ : 0<δ := Real.sqrt_pos.mpr hη
  have hsδ : δ^2=η := Real.sq_sqrt hη.le
  obtain ⟨T,hT,hcut⟩ := choose_tail (U:=U) (Z:=Z) hη
  obtain ⟨V,hV,hfreeze⟩ := freeze_model T hδ
  obtain ⟨D,hD,hs⟩ := small_error_bound T V
  have hhigh := (log_decay (by norm_num : (0:ℝ)<1/64)).const_mul W
  have hsmall := (log_decay (by norm_num : (0:ℝ)<4)).const_mul (D^2)
  rw [mul_zero] at hhigh hsmall
  refine ⟨T,V,hT,hV,?_⟩
  filter_upwards [eventually_ge_atTop T,hfreeze,cone_error_vanishes hδ,
    hhigh.eventually_le_const hη,hsmall.eventually_le_const hη] with N hTN hf hcone hh hsmall
  have hN : 2≤N := by omega
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  let P := Nat.primesLE (N^64)
  let Q := P.filter (fun p => N^56≤p)
  let R := P.filter (fun p => ¬N^56≤p)
  let μ : ℝ := (N:ℝ)^64/Real.log N
  have hμ : 0≤μ := by dsimp [μ]; positivity
  have hQ (p) (hp : p∈Q) : p.Prime ∧ N<p ∧ p≤N^64 := by
    obtain ⟨hp',hlo⟩ := mem_filter.mp hp
    have hY := cutoff_inside hN hlo
    have hNY := Nat.le_self_pow (by decide : 52≠0) N
    exact ⟨Nat.prime_of_mem_primesLE hp',by omega,Nat.le_of_mem_primesLE hp'⟩
  have hsumM : ∑ p∈Q,(middle T N p)^2 ≤ η*μ := by
    have H := hm N T hN (by omega) (coneWindow (coneWidth N)) (commonWeight (2*N^52)) Z hZ
      (fun d _ => by rw [abs_of_nonneg (commonWeight_bounds _ d).1]; exact (commonWeight_bounds _ d).2) Q hQ
    apply H.trans; dsimp [μ]; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hcut hμ
  have hsumH : ∑ p∈Q,‖upper N p‖^2≤η*μ := by
    have hsub : Q⊆range (N^64+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hQ p hp).2.2)
    have H := hu (show 1≤N by omega) (above N (coneWindow (coneWidth N))) (fun d hd => if_pos hd) N (by omega)
    apply (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans (H.trans ?_)
    have ht : 0<(N:ℝ)^(1/64:ℝ) := Real.rpow_pos_of_pos hn _
    change W*(Real.log N/(N:ℝ)^(1/64:ℝ))≤η at hh
    have hb := (div_le_iff₀ ht).mp (show W*Real.log N/(N:ℝ)^(1/64:ℝ)≤η by rwa [mul_div_assoc])
    change W*(N:ℝ)^64/(N:ℝ)^(1/64:ℝ)≤η*((N:ℝ)^64/Real.log N)
    rw [← mul_div_assoc,div_le_div_iff₀ ht hl]
    nlinarith only [mul_le_mul_of_nonneg_right hb (show 0≤(N:ℝ)^64 by positivity)]
  have hsumQ : ∑ p∈Q,(scaledOff p-model T V p)^2≤(12*Real.log 4+6)*η*μ := by
    have hcard := ThetaPrimeVariance.band_card hN Q hQ
    have H := sum_le_sum (s:=Q) (fun p hp => band_point hN hTN (hQ p hp).1 (mem_filter.mp hp).2
      (hcone p (hQ p hp).1 (mem_filter.mp hp).2 (hQ p hp).2.2) (hf p))
    apply H.trans
    rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,sum_add_distrib,hsδ]
    change (Q.card:ℝ)≤Real.log 4*(N:ℝ)^64/Real.log N at hcard
    rw [mul_div_assoc] at hcard
    change (Q.card:ℝ)≤Real.log 4*μ at hcard
    nlinarith only [mul_le_mul_of_nonneg_right hcard hη.le,hsumM,hsumH]
  have hsumR : ∑ p∈R,(scaledOff p-model T V p)^2 ≤ η*μ := by
    have hsub : R⊆range (N^56) := fun p hp => mem_range.mpr (lt_of_not_ge (mem_filter.mp hp).2)
    have hcard := card_le_card hsub
    rw [card_range] at hcard
    have hcard' : (R.card:ℝ)≤(N:ℝ)^56 := by exact_mod_cast hcard
    have he (p) (hp : p∈R) : (scaledOff p-model T V p)^2≤(D*(N:ℝ)^2)^2 := by
      have hp' := (mem_filter.mp hp).1
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hs hN (Nat.prime_of_mem_primesLE hp')
        (Nat.le_of_mem_primesLE hp')) 2
    apply (sum_le_sum he).trans
    rw [sum_const,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right hcard' (sq_nonneg _)).trans
    change D^2*(Real.log N/(N:ℝ)^(4:ℝ))≤η at hsmall
    rw [show (4:ℝ)=(4:ℕ) by norm_num,Real.rpow_natCast,← mul_div_assoc,div_le_iff₀ (by positivity)] at hsmall
    dsimp [μ]; rw [← mul_div_assoc,le_div_iff₀ hl]
    nlinarith only [mul_le_mul_of_nonneg_right hsmall (show 0≤(N:ℝ)^60 by positivity)]
  have H := sum_filter_add_sum_filter_not P (fun p => N^56≤p) (fun p => (scaledOff p-model T V p)^2)
  change ∑ p∈Q,(scaledOff p-model T V p)^2+∑ p∈R,(scaledOff p-model T V p)^2=_ at H
  rw [← H]
  apply (add_le_add hsumQ hsumR).trans_eq
  have hcancel : (12*Real.log 4+7)*η=ε := by dsimp [η]; field_simp
  calc
    _ = ((12*Real.log 4+7)*η)*μ := by ring
    _ = _ := by rw [hcancel]; dsimp [μ]; ring

private lemma from_scales (f : ℕ → ℝ) (hf : ∀ n, 0≤f n) {η : ℝ} (hη : 0≤η)
    (h : ∀ᶠ N : ℕ in atTop, ∑ p∈Nat.primesLE (N^64),f p≤η*(N:ℝ)^64/Real.log N) :
    ∀ᶠ X : ℕ in atTop, ∑ p∈Nat.primesLE X,f p≤(64*2^64)*η*(X:ℝ)/Real.log X := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop 2,eventually_ge_atTop (B^64)] with X hX hXB
  let r := Nat.nthRoot 64 X
  let N := r+1
  have hr : 1≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr (by simpa using (show 1≤X by omega))
  have hb : B≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr hXB
  have hN : 2≤N := by dsimp [N]; omega
  have hL : X<N^64 := Nat.lt_pow_nthRoot_add_one (by decide) X
  have hl : r^64≤X := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hnr : N^64≤2^64*X := calc
    _ ≤ (2*r)^64 := Nat.pow_le_pow_left (by dsimp [N]; omega) _
    _ = _ := Nat.mul_pow ..
    _ ≤ _ := Nat.mul_le_mul_left _ hl
  have hsub : Nat.primesLE X⊆Nat.primesLE (N^64) := by
    intro p hp; obtain ⟨hh,hp'⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hh.trans hL.le,hp'⟩
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf p)).trans ((hB N (by dsimp [N]; omega)).trans ?_)
  have hx : (1:ℝ)<X := by exact_mod_cast hX
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hsize : (N:ℝ)^64≤(2:ℝ)^64*X := by exact_mod_cast hnr
  have hlog := Real.log_le_log (by linarith : (0:ℝ)<X) (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hL.le)
  rw [Real.log_pow] at hlog
  rw [div_le_div_iff₀ (Real.log_pos hn) (Real.log_pos hx)]
  have H := mul_le_mul hsize hlog (Real.log_pos hx).le (by positivity)
  have hmul := mul_le_mul_of_nonneg_left H hη
  norm_num only [Nat.cast_ofNat] at hmul
  linarith only [hmul]

/-- The scaled full off-diagonal is approximated in mean square over actual
primes by one periodic window fixed before X tends to infinity. -/
theorem prime_model_approximation {ε : ℝ} (hε : 0<ε) :
    ∃ T V : ℕ, 3≤T ∧ 2≤V ∧ ∀ᶠ X : ℕ in atTop,
      ∑ p∈Nat.primesLE X,(scaledOff p-model T V p)^2≤ε*Nat.primeCounting X := by
  let b := Real.log 2/2
  have hb : 0<b := by dsimp [b]; positivity
  let η := ε*b/(64*2^64)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨T,V,hT,hV,h⟩ := scale_approximation hη
  refine ⟨T,V,hT,hV,?_⟩
  filter_upwards [from_scales _ (fun _ => sq_nonneg _) hη.le h,prime_count_lower,eventually_ge_atTop 2]
    with X H hcount hX
  apply H.trans; rw [div_le_iff₀ (Real.log_pos (by exact_mod_cast hX))]
  have hh : (64*2^64)*η=ε*b := by dsimp [η]; ring
  rw [hh]; change b*(X:ℝ)≤Nat.primeCounting X*Real.log X at hcount
  linarith only [mul_le_mul_of_nonneg_left hcount hε.le]

/-- The finite model can also be frozen with arbitrarily small mean
absolute discrepancy. The normalization counts primes up to X. -/
theorem prime_model_absolute {ε : ℝ} (hε : 0<ε) :
    ∃ T V : ℕ, 3≤T ∧ 2≤V ∧ ∀ᶠ X : ℕ in atTop,
      ∑ p∈Nat.primesLE X,|scaledOff p-model T V p|≤ε*Nat.primeCounting X := by
  obtain ⟨T,V,hT,hV,H⟩ := prime_model_approximation (sq_pos_of_pos hε)
  refine ⟨T,V,hT,hV,?_⟩; filter_upwards [H] with X h
  have hcs := sum_mul_sq_le_sq_mul_sq (Nat.primesLE X) (fun _ => (1:ℝ)) (fun p => |scaledOff p-model T V p|)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs,Nat.primesLE_card_eq_primeCounting] at hcs
  have hs := hcs.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))
  have hpos : 0≤ε*Nat.primeCounting X := by positivity
  nlinarith only [hs,hpos,sq_nonneg ((∑ p∈Nat.primesLE X,|scaledOff p-model T V p|)-ε*Nat.primeCounting X)]

end Arxiv.«2501.03234».ThetaPrimeTailTransfer
#print axioms Arxiv.«2501.03234».ThetaPrimeTailTransfer.prime_model_approximation
#print axioms Arxiv.«2501.03234».ThetaPrimeTailTransfer.prime_model_absolute
#print axioms Arxiv.«2501.03234».ThetaPrimeTailTransfer.freeze_model
#print axioms Arxiv.«2501.03234».ThetaPrimeTailTransfer.normalized_cone_error
