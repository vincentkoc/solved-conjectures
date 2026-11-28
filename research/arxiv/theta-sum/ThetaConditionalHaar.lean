import ThetaShortClassMeans
import Mathlib.Probability.ConditionalProbability

/-! Conditioning the profinite Haar representative on an arbitrary reduced
progression gives its prime law and all fixed short-window Lipschitz limits. -/
namespace Arxiv.«2501.03234».ThetaConditionalHaar
open Real Filter Finset MeasureTheory ProbabilityTheory ThetaProfiniteUnits ThetaPrimeLaw
open ThetaCharacterPrimeMeans ThetaIdentityFiber ThetaLocalIntervalTests ThetaNaturalPrimeMeans
open ThetaPrimeDensity ThetaPeriodMeans ThetaShortClassMeans
open scoped Topology NNReal
noncomputable section

def fibre (q r : ℕ) : Set G := {x | cylinder q (selectClass r q) x=1}

theorem measurable (q r : ℕ) : MeasurableSet (fibre q r) :=
  measurableSet_eq_fun (continuous_cylinder _ _).measurable measurable_const

theorem indicator_one (q r : ℕ) (x : G) :
    (fibre q r).indicator (fun _ => (1:ℝ)) x=cylinder q (selectClass r q) x := by
  simp only [fibre,ThetaProfiniteUnits.cylinder,selectClass,Set.indicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem mass (hAP : ProgressionMangoldt) {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) :
    haar.real (fibre q r)=1/(q.totient:ℝ) := by
  let : NeZero q.factorial := ⟨(Nat.factorial_pos _).ne'⟩
  have hper := onMod_lift (Nat.dvd_factorial hq (le_refl q)) (selectClass_mod r q)
  have hm := periodic_prime_mean hAP hper
  have hd := class_prime_density hAP hq hu hr
  have hh : Tendsto (primeMean (selectClass r q)) atTop (𝓝 (1/(q.totient:ℝ))) := by
    apply hd.congr;intro X
    simp only [primeMean,selectClass,sum_boole]
    congr 2
    exact congrArg Finset.card (by ext p;simp [primeSet])
  have hs : ∫ x, (fibre q r).indicator (fun _ => (1:ℝ)) x ∂haar=haar.real (fibre q r) := by
    rw [integral_indicator (measurable q r),setIntegral_const,smul_eq_mul,mul_one]
  simp_rw [indicator_one] at hs
  rw [←hs,integral_cylinder]
  exact tendsto_nhds_unique hm hh

private theorem int_cylinder (n : ℕ) (g : ℕ → ℝ) : Integrable (cylinder n g) haar :=
  (continuous_cylinder n g).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem masked {f : ℕ → ℝ} {F : G →₁[haar] ℝ} (hF : Represents f F)
    {q : ℕ} (hq : 0<q) (r : ℕ) : ∃ Y : G →₁[haar] ℝ,
      Represents (fun p => selectClass r q p*f p) Y ∧
      (fun x => Y x)=ᵐ[haar](fibre q r).indicator (fun x => F x) := by
  let C := fibre q r
  have hi := (L1.integrable_coeFn F).indicator (measurable q r)
  let Y := hi.toL1 _
  refine ⟨Y,?_,hi.coeFn_toL1⟩
  intro ε hε
  obtain ⟨n,g,hg,hp,ha⟩ := hF ε hε
  let U := max q n
  let w := selectClass r q
  have hw := onMod_lift (Nat.dvd_factorial hq (le_refl q)) (selectClass_mod r q)
  have hwU := onMod_lift (Nat.factorial_dvd_factorial (le_max_left q n)) hw
  have hgU := onMod_lift (Nat.factorial_dvd_factorial (le_max_right q n)) hg
  let b (p : ℕ) := w p*g p
  have hcy (x : G) : cylinder U b x=cylinder q w x*cylinder n g x := by
    rw [cylinder_lift (le_max_left q n) hw,cylinder_lift (le_max_right q n) hg];rfl
  refine ⟨U,b,fun p => congrArg₂ (·*·) (hwU p) (hgU p),?_,?_⟩
  · apply hp.mono;intro X hx;apply le_trans _ hx
    apply mean_mono;intro p
    simp only [b,w,selectClass];split_ifs <;> simp [abs_nonneg]
  · apply le_trans _ ha
    apply integral_mono_ae ((L1.integrable_coeFn Y).sub (int_cylinder U b)).abs
      ((L1.integrable_coeFn F).sub (int_cylinder n g)).abs
    filter_upwards [hi.coeFn_toL1] with x hx
    change |Y x-cylinder U b x|≤_
    rw [show Y x=C.indicator (fun x => F x) x from hx,hcy,←indicator_one]
    by_cases hc : x∈C <;> simp [C] at hc <;> simp [C,hc,abs_nonneg]

theorem composed {f : ℕ → ℝ} {F : G →₁[haar] ℝ} (hF : Represents f F)
    {φ : ℝ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∃ Y : G →₁[haar] ℝ,Represents (fun p => φ (f p)) Y ∧ (fun x => Y x)=ᵐ[haar](fun x => φ (F x)) := by
  have hFi := L1.integrable_coeFn F
  have hi : Integrable (fun x => φ (F x)) haar := by
    apply ((integrable_const |φ 0|).add (hFi.abs.const_mul (K:ℝ))).mono'
      (hφ.continuous.comp_aestronglyMeasurable hFi.aestronglyMeasurable)
    apply Eventually.of_forall;intro x
    have hh := hφ.dist_le_mul (F x) 0
    simp only [Real.dist_eq,sub_zero] at hh
    change ‖φ (F x)‖≤|φ 0|+(K:ℝ)*|F x|
    rw [Real.norm_eq_abs]
    linarith only [hh,abs_sub_abs_le_abs_sub (φ (F x)) (φ 0)]
  let Y := hi.toL1 _
  refine ⟨Y,?_,hi.coeFn_toL1⟩
  intro ε hε
  let t := ε/((K:ℝ)+1)
  have ht : 0<t := by dsimp [t];positivity
  have he : (K:ℝ)*t≤ε := by
    have heq : ((K:ℝ)+1)*t=ε := by dsimp [t];field_simp
    linarith only [heq,ht]
  obtain ⟨n,g,hg,hp,hm⟩ := hF t ht
  refine ⟨n,fun p => φ (g p),fun p => congrArg φ (hg p),?_,?_⟩
  · filter_upwards [hp] with X hx
    have hd := mean_mono (fun p => hφ.dist_le_mul (f p) (g p)) X
    simp only [Real.dist_eq,primeMean,←mul_sum,mul_div_assoc] at hd
    exact hd.trans ((mul_le_mul_of_nonneg_left hx K.2).trans he)
  · have hh : (∫ x,|Y x-cylinder n (fun p => φ (g p)) x| ∂haar) ≤
        ∫ x,(K:ℝ)*|F x-cylinder n g x| ∂haar := by
      apply integral_mono_ae ((L1.integrable_coeFn Y).sub (int_cylinder _ _)).abs
        (((L1.integrable_coeFn F).sub (int_cylinder n g)).abs.const_mul _)
      filter_upwards [hi.coeFn_toL1] with x hx
      change |Y x-φ (cylinder n g x)|≤_
      rw [show Y x=φ (F x) from hx];exact hφ.dist_le_mul _ _
    rw [integral_const_mul] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hm K.2).trans he)

#print axioms mass
#print axioms masked
#print axioms composed
end
end Arxiv.«2501.03234».ThetaConditionalHaar
