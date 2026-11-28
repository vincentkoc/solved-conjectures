import ThetaFifteenOrthogonality
import ThetaQuadraticEnergy

/-! A composite quadratic character survives removing every prime-conductor mode. -/
namespace Arxiv.«2501.03234».ThetaCompositeVariance
open Finset Filter Topology ThetaJacobiRows ThetaJacobiFifteen ThetaFifteenOrthogonality
open ThetaCharacterSeven (siftedSum)
open ThetaConditionalRows ThetaNaturalPrimeMeans ThetaPeriodMeans ThetaRowCorrelations ThetaCharacterPrimeMeans
open ThetaSpectrumDecay ThetaQuadraticEnergy

private noncomputable def amplitude (d : ℕ) : ℝ :=
  if Odd d ∧ 15∣d then
    (∏ p∈sieve 15 d,(1-w 15 p)) * (∏ p∈insert 2 (sieve 15 d),(1-w 15 p/p)) /
      ((d:ℝ)*d.totient) else 0

private lemma amplitude_nonneg (d : ℕ) : 0≤amplitude d := by
  unfold amplitude
  split_ifs
  · apply div_nonneg _ (by positivity)
    apply mul_nonneg
    · exact prod_nonneg (fun p _ => sub_nonneg.mpr ((le_abs_self _).trans (bounded 15 p)))
    · apply prod_nonneg
      intro p hp
      have hpr : p.Prime := (mem_insert.mp hp).elim (fun h => h ▸ Nat.prime_two)
        (fun h => Nat.prime_of_mem_primeFactors (mem_filter.mp h).1)
      have hp1 : (1:ℝ)≤p := by exact_mod_cast hpr.one_le
      apply sub_nonneg.mpr
      rw [div_le_iff₀ (by positivity : (0:ℝ)<p),one_mul]
      exact ((le_abs_self _).trans (bounded 15 p)).trans hp1
  · exact le_rfl

private lemma conductor_amplitude : amplitude 15=1/240 := by
  have hs : sieve 15 15=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpr,hc⟩ := mem_filter.mp hp
    have hg := hc.gcd_eq_one
    rw [Nat.gcd_eq_left (Nat.dvd_of_mem_primeFactors hpr)] at hg
    exact (Nat.prime_of_mem_primeFactors hpr).ne_one hg
  have hφ : Nat.totient 15=8 := by decide
  norm_num [amplitude,show Odd 15 by decide,hs,hφ,w,symbol]

private theorem row_lim {P d : ℕ} [NeZero P] [NeZero d]
    (hP : 15∣P) (hd : d∣P) {L : ℝ} (hL : Tendsto (siftedSum (term 15) ∅) atTop (𝓝 L)) :
    Tendsto (fun K => unitMean P (fun n => w 15 n*row d K n)/(d:ℝ)) atTop
      (𝓝 (((parityFactor 15:ℝ)*L)*amplitude d)) := by
  by_cases H : Odd d ∧ 15∣d
  · have he (K : ℕ) : unitMean P (fun n => w 15 n*row d K n) = unitMean d (fun n => w 15 n*row d K n) :=
      unitMean_lift hd (fun n => congrArg₂ (·*·) (onMod_lift H.2 (periodic 15) n) (row_onMod d K n))
    simp_rw [he,unitMean]
    have h := ((row_limit 15 (by decide) H.1 H.2 hL).div_const (d.totient:ℝ)).div_const (d:ℝ)
    convert h using 1
    congr 1
    simp only [amplitude,if_pos H,Int.cast_mul,Int.cast_prod,Int.cast_sub,Int.cast_one,w]
    ring
  · rw [amplitude,if_neg H,mul_zero]
    have he (K : ℕ) : unitMean P (fun n => w 15 n*row d K n)=0 := by
      by_cases ho : Odd d
      · exact missing_modulus hP hd (fun h => H ⟨ho,h⟩) (row_onMod d K)
      · simp [even_row ho,unitMean]
    simpa only [he,zero_div] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=atTop (α:=ℕ)))

/-- A signed correlation of the original centered theta sum at composite conductor fifteen. -/
theorem composite_correlation (hAP : ProgressionMangoldt) :
    ∃ C : ℝ, C < -(1/60) ∧
      Tendsto (primeMean (fun n => w 15 n*((S n:ℝ)/n-Real.log n/2))) atTop (𝓝 C) := by
  obtain ⟨L,hpos,hL⟩ := harmonic_fifteen
  obtain ⟨C,hC,hlim⟩ := ThetaPrimeSpectrum.mean_from_rows hAP (w 15) (fun n => bounded 15 n) (periodic 15)
    fifteen_center ((parityFactor 15:ℝ)*L) amplitude (fun hP hd => row_lim hP hd hL)
  rw [fifteen_parity] at hlim
  have hc : C ≤ -L/60 := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop 15] with T hT
    have h := single_le_sum (f:=amplitude) (fun d _ => amplitude_nonneg d)
      (mem_Icc.mpr ⟨by decide,hT⟩ : 15∈Icc 2 T)
    rw [conductor_amplitude] at h
    push_cast
    nlinarith [mul_nonneg (show 0≤L by linarith) (sub_nonneg.mpr h)]
  exact ⟨C,by linarith,hC⟩

private theorem against_quadratic (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => w 15 p*quadraticPart p)) atTop (𝓝 0) := by
  have h1 : Tendsto (primeMean (fun _ => (1:ℝ))) atTop (𝓝 1) :=
    prime_mean_of_convergence (by intro ε he; simp [he])
  have hb : ∀ᶠ X : ℕ in atTop, primeMean (fun p => |w 15 p|) X ≤ 2 := by
    filter_upwards [h1.eventually_le_const (by norm_num : (1:ℝ)<2)] with X hX
    exact (div_le_div_of_nonneg_right (sum_le_sum (fun p _ => bounded 15 p)) (Nat.cast_nonneg (α:=ℝ) X.primeCounting)).trans hX
  have hpair (r : OddPrime) :
      Tendsto (primeMean (fun p => (legendreSym r.val (p:ℤ):ℝ)*w 15 p)) atTop (𝓝 0) := by
    have hmiss : ¬15∣r.val := by
      intro h
      have he := (Nat.dvd_prime_two_le r.property.1 (by decide : 2≤15)).mp h
      exact (show ¬Nat.Prime 15 by decide) (he.symm ▸ r.property.1)
    have h := against_period hAP hmiss (periodic r.val)
    have he (n : ℕ) : w r.val n=(legendreSym r.val (n:ℤ):ℝ) := by
      simp only [w,symbol,←jacobiSym.legendreSym.to_jacobiSym]
    simpa only [he,mul_comm] using h
  have H := quadratic_pairing hAP (f:=w 15) (b:=fun _ => 0) (by norm_num : (0:ℝ)≤2)
    hb hpair (by simp)
  simpa using H

/-- A bounded centered twist lower-bounds empirical variance whenever all three prime limits exist. -/
theorem variance_of_twist {v f : ℕ → ℝ} {C B W : ℝ} (hb : ∀ p, |v p|≤1)
    (hv : Tendsto (primeMean v) atTop (𝓝 0))
    (hf : Tendsto (primeMean f) atTop (𝓝 B))
    (hC : Tendsto (primeMean (fun p => v p*f p)) atTop (𝓝 C))
    (hW : Tendsto (sampleVariance f) atTop (𝓝 W)) : C^2 ≤ W := by
  let z p := f p-B
  have hz : Tendsto (primeMean (fun p => v p*z p)) atTop (𝓝 C) := by
    have H := hC.sub (hv.mul_const B)
    rw [zero_mul,sub_zero] at H
    apply H.congr'
    filter_upwards with X
    simp only [primeMean,z,mul_sub,sum_sub_distrib,←sum_mul,sub_div,div_mul_eq_mul_div]
  have hπ : Tendsto (fun X : ℕ => (X.primeCounting:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting
  have hZ : Tendsto (primeMean (fun p => (z p)^2)) atTop (𝓝 W) := by
    have H := hW.add ((hf.sub_const B).pow 2)
    rw [sub_self,zero_pow (by decide : 2≠0),add_zero] at H
    apply H.congr'
    filter_upwards [hπ.eventually_gt_atTop 0] with X hX
    rw [variance_recentering f B hX]
    dsimp only [z]
    ring
  have h1 : Tendsto (primeMean (fun _ => (1:ℝ))) atTop (𝓝 1) :=
    prime_mean_of_convergence (by intro ε he; simp [he])
  have Hl := (hz.const_mul (2*C)).sub (h1.const_mul (C^2))
  have H : 2*C*C-C^2*1≤W := le_of_tendsto_of_tendsto' Hl hZ (fun X => by
    change 2*C*primeMean _ X-C^2*primeMean _ X ≤ primeMean _ X
    simp only [primeMean,← mul_div_assoc,← sub_div,mul_sum,←sum_sub_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro p _
    have hsq : (v p)^2≤1 := by
      rw [←sq_abs]
      nlinarith only [mul_nonneg (sub_nonneg.mpr (hb p)) (show 0≤1+|v p| by positivity)]
    nlinarith only [sq_nonneg (z p-C*v p),mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hsq)])
  linarith

/-- The composite twist is orthogonal to every prime-conductor mode. Its negative
correlation certifies a positive variance even after subtracting their whole series. -/
theorem residual_variance (hAP : ProgressionMangoldt) :
    ∃ C V W : ℝ, C < -(1/60) ∧ C^2≤W ∧ 1/3600<W ∧ V=quadraticEnergy+W ∧
      Tendsto (primeMean (fun p => w 15 p*((S p:ℝ)/p-Real.log p/2-quadraticPart p))) atTop (𝓝 C) ∧
      Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2)) atTop (𝓝 V) ∧
      Tendsto (sampleVariance (fun p => (S p:ℝ)/p-Real.log p/2-quadraticPart p)) atTop (𝓝 W) := by
  let R := ThetaCharacterPrimeMeans.residual
  let f p := R p-quadraticPart p
  obtain ⟨C,hneg,hC⟩ := composite_correlation hAP
  obtain ⟨V,W,_,he,hV,hW,_⟩ := variance_decomposition hAP
  have hc : Tendsto (primeMean (fun p => w 15 p*f p)) atTop (𝓝 C) := by
    have H := hC.sub (against_quadratic hAP)
    rw [sub_zero] at H
    apply H.congr'
    filter_upwards with X
    simp only [primeMean,f,R,ThetaCharacterPrimeMeans.residual,mul_sub,←sub_div,←sum_sub_distrib]
  have hf : Tendsto (primeMean f) atTop (𝓝 ThetaDiagonalConstant.diagonalConstant) := by
    have H := (S_second_order_prime_mean hAP).sub (quadraticPart_mean hAP)
    rw [sub_zero] at H
    apply H.congr'
    filter_upwards with X
    simp only [primeMean,f,R,ThetaCharacterPrimeMeans.residual,←sub_div,←sum_sub_distrib]
  have hv := periodic_prime_mean hAP (periodic 15)
  rw [fifteen_center] at hv
  have hl := variance_of_twist (fun p => bounded 15 p) hv hf hc hW
  refine ⟨C,V,W,hneg,hl,?_,he,hc,hV,hW⟩
  nlinarith only [hl,mul_pos (show 0 < -C-1/60 by linarith) (show 0 < -C+1/60 by linarith)]

/-- Even after including the entire infinite prime quadratic series, an additional arbitrary
periodic correction without both 3 and 5 leaves an absolute prime mean error above 1/60. -/
theorem corrected_period_gap (hAP : ProgressionMangoldt) {m : ℕ} [NeZero m] (hm : ¬15∣m)
    {g : ℕ → ℝ} (hg : OnMod m g) :
    ∀ᶠ X : ℕ in atTop, 1/60 < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-quadraticPart p-g p|) X := by
  obtain ⟨C,_,_,hn,_,_,_,hc,_⟩ := residual_variance hAP
  apply ThetaPrimeSpectrum.error_of_twist (fun p => bounded 15 p) hc (against_period hAP hm hg)
  rw [abs_of_neg (by linarith : C<0)]
  linarith

#print axioms corrected_period_gap

#print axioms variance_of_twist
#print axioms residual_variance

#print axioms composite_correlation
end Arxiv.«2501.03234».ThetaCompositeVariance
