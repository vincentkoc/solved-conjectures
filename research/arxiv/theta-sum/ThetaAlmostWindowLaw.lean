import ThetaAlmostTransfer
import ThetaPrimeTestApproximation

/-! Weak convergence along triples consisting of a dyadic scale, a typical
starting integer and an arbitrary admissible window length. -/
namespace Arxiv.«2501.03234».ThetaAlmostWindowLaw
open Real Finset Filter MeasureTheory ThetaWindowApproximation ThetaAlmostPeriodicWindows
open ThetaPrimeLaw ThetaNaturalPrimeMeans ThetaLocalPrimeCounts ThetaCharacterPrimeMeans ThetaProfiniteUnits
open scoped Topology NNReal
noncomputable section

structure Window where
  base : ℕ
  start : ℕ
  len : ℕ

private theorem all {P : ℕ → ℕ → Prop} (h : ∀ᶠ X : ℕ in atTop,∀ n∈starts X,P X n) : Almost P := by
  intro ε hε
  filter_upwards [h] with X hh
  have he : exceptional X (P X)=∅ := eq_empty_iff_forall_notMem.mpr (by
    intro n hn;obtain ⟨hs,hh'⟩ := mem_exceptional.mp hn;exact hh' (hh n hs))
  rw [he,card_empty,Nat.cast_zero];positivity

def windows (θ : ℝ) : Filter Window where
  sets := {s | Almost (fun X n => ∀ H : ℕ, Admits θ X H → (⟨X,n,H⟩:Window)∈s)}
  univ_sets := all (Eventually.of_forall (by intros;trivial))
  sets_of_superset := fun hs h => mono hs (Eventually.of_forall (by intro X n _ hh H hH;exact h (hh H hH)))
  inter_sets := fun hs ht => mono (inter hs ht) (Eventually.of_forall (by
    intro X n _ hh H hH; exact ⟨hh.1 H hH,hh.2 H hH⟩))

theorem nontrivial {θ : ℝ} (ht : θ≤1) : (windows θ).NeBot := by
  apply Filter.neBot_iff.mpr
  intro hb
  have he : (∅:Set Window)∈windows θ := by rw [hb];trivial
  change Almost (fun X n => ∀ H : ℕ,Admits θ X H → (⟨X,n,H⟩:Window)∈(∅:Set Window)) at he
  obtain ⟨X,hbad,hX⟩ := ((he (1/2) (by norm_num)).and (eventually_ge_atTop (2:ℕ))).exists
  have hpos : 0<X := by omega
  have hpow : (X:ℝ)^θ≤X := (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤X by omega)) ht).trans_eq (rpow_one _)
  have hs : exceptional X (fun n => ∀ H : ℕ,Admits θ X H → (⟨X,n,H⟩:Window)∈(∅:Set Window))=starts X := by
    ext n;rw [mem_exceptional];exact and_iff_left (fun h => h X ⟨hpos,le_rfl,hpow⟩)
  rw [hs] at hbad
  have hcard : (starts X).card=X := by simp [starts];omega
  rw [hcard] at hbad;linarith only [hbad,(Nat.cast_pos.mpr hpos : (0:ℝ)<X)]

theorem scaled {θ : ℝ} (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {f : ℕ → ℝ} (hf : Approximable f) {a : ℝ} (ha : Tendsto (primeMean f) atTop (𝓝 a)) :
    Tendsto (fun w : Window => avg w.base w.start w.len f) (windows θ) (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr;intro ε hε
  change Almost (fun X n => ∀ H : ℕ,Admits θ X H → dist (avg X n H f) a<ε)
  apply mono (ThetaAlmostTransfer.limit h hAP hf ha (half_pos hε))
  filter_upwards with X
  intro n _ hh H hH
  exact (hh H hH).trans_lt (half_lt_self hε)

theorem mass {θ : ℝ} (h : Equidistributed θ) :
    Tendsto (fun w : Window => avg w.base w.start w.len (fun _ => 1)) (windows θ) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr;intro ε hε
  change Almost (fun X n => ∀ H : ℕ,Admits θ X H → dist (avg X n H (fun _ => (1:ℝ))) 1<ε)
  apply mono (h 1 (by decide) (ε/2) (half_pos hε))
  filter_upwards with X
  intro n _ hh H hH
  have hi := hh H hH 0 (by decide)
  simpa [scaledCount,avg,Real.dist_eq,Nat.mod_one] using hi.trans_lt (half_lt_self hε)

theorem populated {θ : ℝ} (h : Equidistributed θ) : ∀ᶠ w in windows θ,(sample w.start w.len).Nonempty := by
  apply ((mass h).eventually_const_lt (by norm_num : (0:ℝ)<1)).mono
  intro w hw
  by_contra hv;rw [not_nonempty_iff_eq_empty] at hv
  simp [avg,hv] at hw

theorem normalize {θ : ℝ} (h : Equidistributed θ) {f : ℕ → ℝ} {a : ℝ}
    (ht : Tendsto (fun w : Window => avg w.base w.start w.len f) (windows θ) (𝓝 a)) :
    Tendsto (fun w : Window => ThetaShortResidualLaw.actual w.start w.len f) (windows θ) (𝓝 a) := by
  have hdiv := ht.div (mass h) one_ne_zero
  rw [div_one] at hdiv
  apply hdiv.congr'
  filter_upwards [(mass h).eventually_const_lt (by norm_num : (0:ℝ)<1)] with w hw
  change 0<avg w.base w.start w.len (fun _ => 1) at hw
  simp only [avg,sum_const,nsmul_eq_mul,mul_one] at hw
  have hn : log (w.base:ℝ)/w.len≠0 := left_ne_zero_of_mul (ne_of_gt hw)
  change avg w.base w.start w.len f / avg w.base w.start w.len (fun _ => 1)=_
  simp only [avg,ThetaShortResidualLaw.actual,sum_const,nsmul_eq_mul,mul_one,mul_div_mul_left _ _ hn]

theorem polynomial_growth {θ : ℝ} (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {K : ℝ} (hK : 0≤K) (k : ℕ) (hg : ∀ x, |φ x|≤K*(1+|x|^k)) :
    Tendsto (fun w : Window => ThetaShortResidualLaw.actual w.start w.len (fun p => φ (residual p)))
      (windows θ) (𝓝 (∫ x, φ x ∂(haarLaw F : Measure ℝ))) :=
  normalize h (scaled h hAP (ThetaPrimeTestApproximation.original hAP hF hφ hK k hg)
    (ThetaResidualMoments.prime_polynomial_growth hAP hF hφ hg).2)

theorem weak {θ : ℝ} (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) :
    Tendsto (fun w : Window => ThetaShortResidualLaw.law w.start w.len residual)
      (windows θ) (𝓝 (haarLaw F)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have hg (x : ℝ) : |φ x|≤‖φ‖*(1+|x|^0) := by
    have h := φ.norm_coe_le_norm x
    rw [Real.norm_eq_abs] at h
    simp only [pow_zero,one_add_one_eq_two];linarith only [h,norm_nonneg φ]
  have hl := polynomial_growth h hAP hF φ.continuous (norm_nonneg φ) 0 hg
  exact hl.congr' ((populated h).mono fun w hw =>
    (ThetaShortResidualLaw.integral_eq hw residual φ.continuous.measurable).symm)

#print axioms polynomial_growth
#print axioms nontrivial
#print axioms weak
end
end Arxiv.«2501.03234».ThetaAlmostWindowLaw
