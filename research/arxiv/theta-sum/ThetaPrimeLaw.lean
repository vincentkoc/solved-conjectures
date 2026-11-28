import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.Portmanteau
import ThetaProfiniteUnits

/-! Prime limits of periodically approximable functions represented on Haar units. -/
namespace Arxiv.«2501.03234».ThetaPrimeLaw
open ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaPeriodMeans ThetaConditionalRows
open Filter MeasureTheory Finset
open scoped Topology NNReal
noncomputable section
local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos _).ne'⟩

/-- Approximation in ordinary prime mean absolute discrepancy by periodic
functions of a factorial modulus. -/
def Approximable (f : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∃ g : ℕ → ℝ, OnMod T.factorial g ∧
    ∀ᶠ X : ℕ in atTop, primeMean (fun p => |f p-g p|) X ≤ ε

/-- Linearity of the ordinary prime mean. -/
theorem mean_add (f g : ℕ → ℝ) (X : ℕ) :
    primeMean (fun p => f p+g p) X = primeMean f X+primeMean g X := by
  simp [primeMean,sum_add_distrib,add_div]

/-- Pointwise comparison passes to every ordinary prime mean. -/
theorem mean_mono {f g : ℕ → ℝ} (h : ∀ p, f p ≤ g p) (X : ℕ) :
    primeMean f X ≤ primeMean g X :=
  div_le_div_of_nonneg_right (sum_le_sum (fun p _ => h p)) (Nat.cast_nonneg _)

private theorem mean_triangle (f g h : ℕ → ℝ) (X : ℕ) :
    primeMean (fun p => |f p-h p|) X ≤
      primeMean (fun p => |g p-f p|) X + primeMean (fun p => |g p-h p|) X := by
  rw [← mean_add]
  apply mean_mono
  intro p
  simpa only [Real.dist_eq,abs_sub_comm (g p) (f p)] using dist_triangle (f p) (g p) (h p)

private theorem lift_integrable (n : ℕ) (f : ℕ → ℝ) : Integrable (cylinder n f) haar :=
  (continuous_cylinder n f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private def liftL1 (n : ℕ) (f : ℕ → ℝ) : G →₁[haar] ℝ :=
  (lift_integrable n f).toL1 _

private theorem lift_pair (hAP : ProgressionMangoldt) {i j : ℕ} {f g : ℕ → ℝ}
    (hf : OnMod i.factorial f) (hg : OnMod j.factorial g) :
    Tendsto (primeMean (fun p => |f p-g p|)) atTop (𝓝 (dist (liftL1 i f) (liftL1 j g))) := by
  let k := max i j
  let h (p : ℕ) := |f p-g p|
  have hfi := onMod_lift (Nat.factorial_dvd_factorial (le_max_left i j)) hf
  have hgj := onMod_lift (Nat.factorial_dvd_factorial (le_max_right i j)) hg
  have hper : OnMod k.factorial h := fun n => by simp only [h,k,hfi n,hgj n]
  have H := periodic_prime_mean hAP hper
  suffices dist (liftL1 i f) (liftL1 j g) = unitMean k.factorial h by rwa [this]
  rw [L1.dist_eq_integral_dist,← integral_cylinder]
  apply integral_congr_ae
  filter_upwards [(lift_integrable i f).coeFn_toL1,(lift_integrable j g).coeFn_toL1] with x hx hy
  change dist ((lift_integrable i f).toL1 _ x) ((lift_integrable j g).toL1 _ x) = _
  rw [hx,hy,Real.dist_eq,cylinder_lift (le_max_left i j) hf,cylinder_lift (le_max_right i j) hg]
  rfl

/-- The same factorial-periodic models approximate the prime data and a
single random variable on the profinite unit group with its Haar probability. -/
def Represents (f : ℕ → ℝ) (F : G →₁[haar] ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∃ g : ℕ → ℝ, OnMod T.factorial g ∧
    (∀ᶠ X : ℕ in atTop, primeMean (fun p => |f p-g p|) X ≤ ε) ∧
    (∫ x, |F x-cylinder T g x| ∂haar) ≤ ε

theorem exists_haar_representative (hAP : ProgressionMangoldt) {f : ℕ → ℝ}
    (ha : Approximable f) : ∃ F, Represents f F := by
  let δ (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hδ : Tendsto δ atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))).const_div_atTop 1
  have hpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  choose T g hper herr using (fun n : ℕ => ha (δ n) (hpos n))
  let F (n : ℕ) := liftL1 (T n) (g n)
  have hdist (i j : ℕ) : dist (F i) (F j) ≤ δ i + δ j := by
    apply le_of_tendsto (lift_pair hAP (hper i) (hper j))
    filter_upwards [herr i,herr j] with X hi hj
    exact (mean_triangle (g i) f (g j) X).trans (add_le_add hi hj)
  have hC : CauchySeq F := by
    apply Metric.cauchySeq_iff.mpr
    intro ε he
    obtain ⟨n,hn⟩ := eventually_atTop.mp (hδ.eventually_lt_const (half_pos he))
    exact ⟨n,fun i hi j hj => (hdist i j).trans_lt (by linarith only [hn i hi,hn j hj])⟩
  obtain ⟨A,hA⟩ := cauchySeq_tendsto_of_complete hC
  refine ⟨A,?_⟩
  intro ε he
  obtain ⟨n,hn,hclose⟩ := ((hδ.eventually_le_const he).and (Metric.tendsto_nhds.mp hA ε he)).exists
  refine ⟨T n,g n,hper n,(herr n).mono (fun X h => h.trans hn),?_⟩
  rw [dist_comm,L1.dist_eq_integral_dist] at hclose
  apply le_trans _ hclose.le
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [(lift_integrable (T n) (g n)).coeFn_toL1] with x hx
  change |A x - cylinder (T n) (g n) x| = dist (A x) ((lift_integrable (T n) (g n)).toL1 _ x)
  rw [hx,Real.dist_eq]

private lemma lipschitz_integrable {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    {f : G → ℝ} (hf : Integrable f haar) : Integrable (fun x => φ (f x)) haar := by
  have hg : Integrable (fun x => |φ 0|+(K:ℝ)*|f x|) haar :=
    (integrable_const _).add (hf.abs.const_mul _)
  apply hg.mono' (hφ.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  have h := hφ.dist_le_mul (f x) 0
  rw [Real.dist_eq,Real.dist_eq,sub_zero] at h
  rw [Real.norm_eq_abs]
  linarith only [h,abs_sub_abs_le_abs_sub (φ (f x)) (φ 0)]

/-- Lipschitz tests preserve the prime mean absolute approximation bound. -/
theorem lipschitz_mean {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (f g : ℕ → ℝ) (X : ℕ) :
    |primeMean (fun p => φ (f p)) X - primeMean (fun p => φ (g p)) X| ≤
      (K:ℝ)*primeMean (fun p => |f p-g p|) X := by
  unfold primeMean
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) X.primeCounting),← sum_sub_distrib,← mul_div_assoc, mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => hφ.dist_le_mul (f p) (g p))

private lemma lipschitz_integral {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    {f g : G → ℝ} (hf : Integrable f haar) (hg : Integrable g haar) :
    |(∫ x, φ (f x) ∂haar) - ∫ x, φ (g x) ∂haar| ≤ (K:ℝ)*∫ x, |f x-g x| ∂haar := by
  rw [← integral_sub (lipschitz_integrable hφ hf) (lipschitz_integrable hφ hg),← integral_const_mul]
  exact (norm_integral_le_integral_norm _).trans (integral_mono
    ((lipschitz_integrable hφ hf).sub (lipschitz_integrable hφ hg)).norm
    ((hf.sub hg).abs.const_mul _) (fun x => hφ.dist_le_mul (f x) (g x)))

/-- Ordinary prime averages converge to the Haar integral for every Lipschitz
real test, including unbounded tests of linear growth. -/
theorem prime_mean_lipschitz (hAP : ProgressionMangoldt) {f : ℕ → ℝ} {F : G →₁[haar] ℝ}
    (hF : Represents f F) {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    Tendsto (primeMean (fun p => φ (f p))) atTop (𝓝 (∫ x, φ (F x) ∂haar)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let η := ε/(2*(K:ℝ)+2)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨T,g,hp,hprime,hhaar⟩ := hF η hη
  have hper : OnMod T.factorial (fun p => φ (g p)) := fun n => congrArg φ (hp n)
  have hm := periodic_prime_mean hAP hper
  rw [← integral_cylinder] at hm
  have hlim := Metric.tendsto_nhds.mp hm η hη
  filter_upwards [hprime,hlim] with X he₁ he₂
  have h₁ := (lipschitz_mean hφ f g X).trans (mul_le_mul_of_nonneg_left he₁ K.2)
  have h₂ := (lipschitz_integral hφ (L1.integrable_coeFn F) (lift_integrable T g)).trans
    (mul_le_mul_of_nonneg_left hhaar K.2)
  have htri := dist_triangle (primeMean (fun p => φ (f p)) X) (primeMean (fun p => φ (g p)) X)
    (∫ x, φ (F x) ∂haar)
  have htri' := dist_triangle (primeMean (fun p => φ (g p)) X) (∫ x, φ (cylinder T g x) ∂haar)
    (∫ x, φ (F x) ∂haar)
  change dist (primeMean (fun p => φ (g p)) X) (∫ x, φ (cylinder T g x) ∂haar) < η at he₂
  rw [← Real.dist_eq] at h₁ h₂
  rw [dist_comm] at h₂
  have hcancel : (2*(K:ℝ)+2)*η=ε := by dsimp [η]; field_simp
  linarith only [htri,htri',h₁,h₂,he₂,hcancel,hη]




private abbrev PrimeSample (X : ℕ) := ↥(Nat.primesLE (max X 2))
private instance (X : ℕ) : Nonempty (PrimeSample X) :=
  ⟨⟨2,Nat.mem_primesLE.mpr ⟨le_max_right ..,Nat.prime_two⟩⟩⟩

private def uniformSample (X : ℕ) : ProbabilityMeasure (PrimeSample X) :=
  ⟨(PMF.uniformOfFintype (PrimeSample X)).toMeasure,inferInstance⟩

/-- The empirical law of f on primes up to X. At X < 2 its value is
the point mass at f(2). -/
def empirical (f : ℕ → ℝ) (X : ℕ) : ProbabilityMeasure ℝ :=
  (uniformSample X).map (f := fun p => f p.val) (measurable_of_countable _).aemeasurable

theorem empirical_integral {X : ℕ} (hX : 2 ≤ X) (f : ℕ → ℝ) {φ : ℝ → ℝ} (hp : Measurable φ) :
    (∫ x, φ x ∂(empirical f X)) = primeMean (fun p => φ (f p)) X := by
  rw [empirical,ProbabilityMeasure.toMeasure_map,integral_map (measurable_of_countable _).aemeasurable
    hp.aestronglyMeasurable]
  change (∫ p : PrimeSample X, φ (f p.val) ∂(PMF.uniformOfFintype _).toMeasure) = _
  rw [PMF.integral_eq_sum]
  have hs : (∑ p : PrimeSample X, φ (f p.val)) = ∑ p∈Nat.primesLE (max X 2),φ (f p) :=
    Finset.sum_attach (Nat.primesLE (max X 2)) (fun p => φ (f p))
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,
    ← mul_sum,hs,PrimeSample,Fintype.card_coe,max_eq_left hX,
    Nat.primesLE_card_eq_primeCounting,primeMean,div_eq_inv_mul]

#print axioms empirical_integral

/-- The limiting law is the pushforward of Haar probability by the representative. -/
def haarLaw (F : ThetaProfiniteUnits.G →₁[ThetaProfiniteUnits.haar] ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (⟨ThetaProfiniteUnits.haar,inferInstance⟩ : ProbabilityMeasure ThetaProfiniteUnits.G)
    (f := fun x => F x) (Lp.aestronglyMeasurable F).aemeasurable

theorem haarLaw_integral (F : ThetaProfiniteUnits.G →₁[ThetaProfiniteUnits.haar] ℝ)
    {φ : ℝ → ℝ} (hp : Continuous φ) : (∫ x, φ x ∂(haarLaw F)) = ∫ x, φ (F x) ∂ThetaProfiniteUnits.haar := by
  change (∫ x, φ x ∂(ThetaProfiniteUnits.haar.map (fun x => F x))) = _
  exact integral_map (Lp.aestronglyMeasurable F).aemeasurable hp.aestronglyMeasurable

theorem empirical_tendsto (hAP : ProgressionMangoldt) {f : ℕ → ℝ}
    {F : ThetaProfiniteUnits.G →₁[ThetaProfiniteUnits.haar] ℝ} (hr : Represents f F) :
    Tendsto (empirical f) atTop (𝓝 (haarLaw F)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ _ ⟨K,hK⟩
  rw [haarLaw_integral F hK.continuous]
  exact (prime_mean_lipschitz hAP hr hK).congr' ((eventually_ge_atTop 2).mono fun X hX =>
    (empirical_integral hX f hK.continuous.measurable).symm)


#print axioms exists_haar_representative
#print axioms prime_mean_lipschitz
#print axioms empirical_tendsto

end
end Arxiv.«2501.03234».ThetaPrimeLaw
