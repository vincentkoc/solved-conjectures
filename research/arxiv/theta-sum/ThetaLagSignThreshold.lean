import ThetaAsymmetricTails
import ThetaLogarithmicLags

/-! A single fixed positive threshold and a ternary signed residual mark
retain a nonzero prime correlation with a conductor outside the subtracted period. -/
namespace Arxiv.«2501.03234».ThetaLagSignThreshold
open Real Filter Finset MeasureTheory ThetaAsymmetricTails ThetaPeriodicCorrelationWitness
open ThetaPrimeLaw ThetaPrimeLagBounds ThetaPeriodMeans ThetaCharacterPrimeMeans ThetaNaturalPrimeMeans
open scoped Topology
noncomputable section

theorem transform {q m : ℕ} (hq : 0<q) (hm : 0 < m) {v g : ℕ → ℝ} (hv : OnMod q v)
    (hb : ∀ n,|v n|≤1) (hg : OnMod m g) : Approximable (fun n => v n*(residual n-g n)) := by
  intro ε he
  obtain ⟨T,b,hb',hh⟩ := residual_approximable ε he
  let U := max T (q*m)
  have hU : q*m∣U.factorial := Nat.dvd_factorial (Nat.mul_pos hq hm) (le_max_right ..)
  have h₁ := onMod_lift ((Nat.dvd_mul_right q m).trans hU) hv
  have h₂ := onMod_lift ((Nat.dvd_mul_left m q).trans hU) hg
  have h₃ := onMod_lift (Nat.factorial_dvd_factorial (le_max_left T (q*m))) hb'
  refine ⟨U,fun n => v n*(b n-g n),fun n => congrArg₂ (·*·) (h₁ n) (congrArg₂ (·-·) (h₃ n) (h₂ n)),?_⟩
  apply hh.mono;intro X hX;apply le_trans _ hX
  apply mean_mono;intro p
  rw [←mul_sub,sub_sub_sub_cancel_right,abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) (hb p)

theorem mark_mul (t : ℝ) (ht : 0≤t) {v : ℝ} (hv : v=0 ∨ v=1 ∨ v= -1) (x : ℝ) :
    mark t (v*x)=v*mark t x := by
  rcases hv with rfl|rfl|rfl
  · simp [mark,not_lt_of_ge ht,show ¬(0:ℝ)< -t by linarith]
  · simp
  · simp only [neg_one_mul,mark];split_ifs <;> norm_num <;> linarith

theorem signed (hAP : ProgressionMangoldt) (m : ℕ) [NeZero m] :
    ∃ q : ℕ,m<q ∧ q.Prime ∧ q%4=3 ∧ ∀ g : ℕ → ℝ,OnMod m g →
    ∀ P : ℝ → Prop,(∀ᵐ t : ℝ,P t) → ∃ t c : ℝ,0<t ∧ P t ∧ 0<c ∧
      ∀ b : ℝ,Scales q c (fun p => mark t (residual p-g p)-b) := by
  obtain ⟨q,hqm,hpr,hq₃,v,hv,hs,hz,C,hC,H⟩ := spectral hAP m
  refine ⟨q,hqm,hpr,hq₃,?_⟩
  intro g hg P hP
  let u (n : ℕ) := v n*(residual n-g n)
  have hbound (n : ℕ) : |v n|≤1 := by rcases hs n with h|h|h <;> simp [h]
  obtain ⟨F,hF⟩ := exists_haar_representative hAP (transform hpr.pos (NeZero.pos m) hv hbound hg)
  let μ := haarLaw F
  have hi : (∫ x : ℝ,x ∂(μ:Measure ℝ))=C := by
    have hh := prime_mean_lipschitz hAP hF LipschitzWith.id
    have ht : Tendsto (primeMean u) atTop (𝓝 (∫ x : ℝ,x ∂(μ:Measure ℝ))) := by
      rw [show (∫ x : ℝ,x ∂(μ:Measure ℝ))=∫ x,F x ∂ThetaProfiniteUnits.haar from haarLaw_integral F continuous_id]
      exact hh
    exact tendsto_nhds_unique ht (H g hg)
  obtain ⟨t,ht,hPt,ha,hb,hn⟩ := level μ hP (hi.trans_ne hC)
  let f (n : ℕ) := mark t (residual n-g n)
  have hh := limit (empirical_tendsto hAP hF) ha hb
  have hm : Tendsto (primeMean (fun p => v p*f p)) atTop
      (𝓝 ((μ:Measure ℝ).real (Set.Ioi t)-(μ:Measure ℝ).real (Set.Iio (-t)))) := by
    simpa only [mark_mul t ht.le (hs _) _,f] using hh
  let J := (μ:Measure ℝ).real (Set.Ioi t)-(μ:Measure ℝ).real (Set.Iio (-t))
  have hJ : 0 < |J|/4 := by have := abs_pos.mpr (sub_ne_zero.mpr hn);dsimp [J];positivity
  refine ⟨t,(|J|/4)^2/12,ht,hPt,by positivity,?_⟩
  intro b
  have hlim := hm.sub (hz.mul_const b)
  rw [zero_mul,sub_zero] at hlim
  have hlim' : Tendsto (primeMean (fun p => v p*(f p-b))) atTop (𝓝 J) := by
    change Tendsto (fun X : ℕ => primeMean (fun p => v p*(f p-b)) X) atTop (𝓝 J)
    simpa only [primeMean,mul_sub,sum_sub_distrib,sub_div,sum_mul,div_mul_eq_mul_div] using hlim
  have hd : 0<2*(1+|b|)^2 := by positivity
  apply of_witness hJ hd hbound (fun n j => by rw [←hv (n+q*j),Nat.add_mul_mod_self_left,hv])
    (mean_lower hAP (sub_ne_zero.mpr hn) hlim')
  filter_upwards [(pnt hAP).eventually_lt_const (by norm_num : (1:ℝ)<2),eventually_ge_atTop (2:ℕ)] with X hx hX
  have hX' : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hX)
  have hsq (p : ℕ) : (f p-b)^2≤(1+|b|)^2 := by
    have hf : |f p|≤1 := by dsimp [f,mark];split_ifs <;> norm_num
    have hh := (abs_sub (f p) b).trans (add_le_add_left hf |b|)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hsum := sum_le_sum (s:=Nat.primesLE X) (fun p _ => hsq p)
  simp only [sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting] at hsum
  have hp := (div_lt_iff₀ hX').mp hx
  nlinarith only [mul_le_mul_of_nonneg_right hsum hl.le,mul_le_mul_of_nonneg_right hp.le (sq_nonneg (1+|b|))]

#print axioms signed
end
end Arxiv.«2501.03234».ThetaLagSignThreshold
