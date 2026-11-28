import ThetaDensePredictors

/-! Every open interval of centered residual values recurs with positive
lower prime density in each fixed progression. The limiting law has full
support on the real line. -/
namespace Arxiv.«2501.03234».ThetaFullResidualSupport
open Real Finset Filter MeasureTheory ThetaDensePredictors ThetaClassConcentration ThetaUniformPrimePrediction
open ThetaDyadicLaw ThetaNaturalPrimeMeans ThetaPrimeLaw ThetaPrimeDensity ThetaCharacterPrimeMeans
open ThetaProfiniteUnits
open scoped Topology
noncomputable section

def hits (q r : ℕ) (y ε : ℝ) (X : ℕ) := primeSet (fun p => p%q=r ∧ |residual p-y|<ε) X

private theorem inside {s : Finset ℕ} (f : ℕ → ℝ) {a y d κ : ℝ}
    (hd : 0<d) (hκ : 0<κ) (ha : |a-y|≤d/4)
    (hmean : (∑ p∈s,|f p-a|)/(s.card:ℝ)≤κ*d/4) :
    (1-κ)*(s.card:ℝ)≤((s.filter (fun p => |f p-y|<d)).card:ℝ) := by
  classical
  by_cases he : s.Nonempty
  · let G := s.filter (fun p => |f p-y|<d)
    let E := s.filter (fun p => ¬|f p-y|<d)
    have hsum : (E.card:ℝ)*(d/2)≤∑ p∈s,|f p-a| := calc
      _ = ∑ _p∈E,d/2 := by simp
      _ ≤ ∑ p∈E,|f p-a| := sum_le_sum (fun p hp => by
        have h := le_of_not_gt (mem_filter.mp hp).2
        linarith only [h,abs_sub_le (f p) a y,ha,hd])
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => abs_nonneg _)
    have ht := (div_le_iff₀ (Nat.cast_pos.mpr (card_pos.mpr he) : (0:ℝ)<s.card)).mp hmean
    have hc : (G.card:ℝ)+(E.card:ℝ)=s.card := by exact_mod_cast card_filter_add_card_filter_not (s:=s) (fun p => |f p-y|<d)
    have H : (E.card:ℝ)≤κ*s.card := by
      by_contra! h
      nlinarith only [hsum,ht,mul_lt_mul_of_pos_right h hd,mul_nonneg (mul_nonneg hκ.le (Nat.cast_nonneg s.card)) hd.le]
    change _≤(G.card:ℝ); nlinarith only [hc,H]
  · rw [not_nonempty_iff_eq_empty.mp he]; simp

/-- An arbitrarily fine subprogression puts any prescribed fraction below
one inside the specified open interval. The denominator counts primes in
that subprogression itself. -/
theorem refinement (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q)
    (hc : r.Coprime q) (y : ℝ) {d κ : ℝ} (hd : 0<d) (hκ : 0<κ) (N : ℕ) :
    ∃ T≥N, q∣m T ∧ ∃ a< m T, a.Coprime (m T) ∧ a%q=r ∧ ∀ᶠ X : ℕ in atTop,
      (1-κ)*((primeSet (fun n => n%m T=a) X).card:ℝ)≤((hits (m T) a y d X).card:ℝ) := by
  classical
  have hδ : 0<κ*d/8 := by positivity
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ((original hAP).and (rate_zero.eventually_le_const hδ))
  obtain ⟨T,ht,hqT,a,ha,hu,har,hclose⟩ := dense hAP hq hr hc y (show 0<d/4 by positivity) (max N J)
  refine ⟨T,(le_max_left ..).trans ht,hqT,a,ha,hu,har,?_⟩
  obtain ⟨H,hrate⟩ := hJ T ((le_max_right ..).trans ht)
  filter_upwards [H _ hδ] with X hx
  have he := hx a ha hu
  have hh := inside (s:=primeSet (fun n => n%m T=a) X) residual hd hκ hclose
    (he.trans (show rate T+κ*d/8≤κ*d/4 by linarith only [hrate]))
  have eqn : (primeSet (fun n => n%m T=a) X).filter (fun n => |residual n-y|<d)=hits (m T) a y d X := by
    ext n; simp [hits,primeSet,and_assoc]
  rwa [eqn] at hh

/-- Positive lower density among all primes, even after imposing any fixed
reduced residue class. -/
theorem density (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q)
    (hc : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ X : ℕ in atTop, δ*X.primeCounting≤((hits q r y d X).card:ℝ) := by
  classical
  obtain ⟨T,_,hdiv,a,ha,hu,har,h⟩ := refinement hAP hq hr hc y hd (by norm_num : (0:ℝ)<1/2) 0
  let M := m T
  have hm := ThetaCompactModulus.positive T
  have ht : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hden := (class_prime_density hAP hm hu ha).eventually_const_lt
    (show 1/(2*(M.totient:ℝ))<1/M.totient by apply one_div_lt_one_div_of_lt ht;linarith)
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  refine ⟨1/(4*(M.totient:ℝ)),by positivity,?_⟩
  filter_upwards [h,hden,hπ.eventually_gt_atTop 0] with X H hd hx
  change 0<(X.primeCounting:ℝ) at hx
  have hl := (lt_div_iff₀ hx).mp hd
  have hsub : hits M a y d X⊆hits q r y d X := by
    intro p hp
    simp only [hits,primeSet,mem_filter] at hp ⊢
    exact ⟨hp.1,by rw [←Nat.mod_mod_of_dvd p hdiv,hp.2.1,har],hp.2.2⟩
  have hs : 1/(4*(M.totient:ℝ))=(1/(2*(M.totient:ℝ)))/2 := by ring
  rw [hs]; apply le_trans _ (Nat.cast_le.mpr (card_le_card hsub))
  change (1-1/2:ℝ)*_≤((hits M a y d X).card:ℝ) at H
  change 1/(2*(M.totient:ℝ))*X.primeCounting<((primeSet (fun n => n%m T=a) X).card:ℝ) at hl
  calc _ = (1-1/2:ℝ)*(1/(2*(M.totient:ℝ))*X.primeCounting) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hl.le (by norm_num : (0:ℝ)≤1-1/2)).trans H

theorem full_support (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    (y : ℝ) {d : ℝ} (hd : 0<d) : 0<(haarLaw F : Measure ℝ) (Metric.ball y d) := by
  obtain ⟨δ,hδ,H⟩ := density hAP (q:=1) (r:=0) (by decide) (by decide) (by decide) y (half_pos hd)
  have hl := mass_lower_of_count (f:=residual) (s:=Metric.closedBall y (d/2)) Metric.isClosed_closedBall
    (empirical_tendsto hAP hF) H (fun p _ hp => by
      change p%1=0 ∧ |residual p-y|<d/2 at hp
      exact (Metric.mem_closedBall.mpr (by simpa only [Real.dist_eq] using hp.2.le)))
  exact (ENNReal.ofReal_pos.mpr hδ).trans_le (hl.trans (measure_mono (Metric.closedBall_subset_ball (by linarith))))

#print axioms refinement
#print axioms density
#print axioms full_support
end
end Arxiv.«2501.03234».ThetaFullResidualSupport
