import ThetaShortClassMeans

/-! An even-moment bound extends finite-sample weak convergence to every
integrable continuous test of the specified polynomial growth. -/
namespace Arxiv.«2501.03234».ThetaWindowTruncation
open Filter Finset Real MeasureTheory ThetaShortClassMeans
open scoped Topology
noncomputable section

def clamp (M y : ℝ) := max (-M) (min M y)

private theorem bounded {M : ℝ} (hM : 0≤M) (y : ℝ) : |clamp M y|≤M :=
  abs_le.mpr ⟨le_max_left ..,max_le (by linarith) (min_le_left ..)⟩

private theorem err {M : ℝ} (hM : 0<M) (y : ℝ) : |y-clamp M y| *M≤y^2 := by
  rcases le_or_gt y (-M) with hh|hh
  · have he : y≤M := by linarith
    simp only [clamp,min_eq_right he,max_eq_left hh,sub_neg_eq_add,abs_of_nonpos (by linarith : y+M≤0)]
    nlinarith only [mul_nonneg (show 0≤ -y-M by linarith) (show 0≤ -y by linarith),sq_nonneg M]
  rcases le_or_gt y M with he|he
  · simp [clamp,min_eq_right he,max_eq_right hh.le,sq_nonneg]
  · simp only [clamp,min_eq_left he.le,max_eq_right (by linarith : -M≤M),abs_of_nonneg (sub_nonneg.mpr he.le)]
    nlinarith only [sq_nonneg (y-M),mul_nonneg hM.le (sub_nonneg.mpr he.le)]

private theorem power {K : ℝ} {k : ℕ} {φ : ℝ → ℝ}
    (hg : ∀ x,|φ x|≤K*(1+|x|^k)) (x : ℝ) : (φ x)^2≤2*K^2*(1+x^(k*2)) := by
  have hs := pow_le_pow_left₀ (abs_nonneg _) (hg x) 2
  rw [sq_abs] at hs
  rw [pow_mul,←sq_abs (x^k),←pow_abs]
  nlinarith only [hs,mul_nonneg (sq_nonneg K) (sq_nonneg (1-|x|^k))]

theorem finite (s : Finset ℕ) (hs : s.Nonempty) (φ : ℝ → ℝ) (r : ℕ → ℝ)
    {K : ℝ} (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k)) {M : ℝ} (hM : 0<M) :
    |mean s (fun p => φ (r p))-mean s (fun p => clamp M (φ (r p)))| *M≤
      2*K^2*(1+mean s (fun p => (r p)^(k*2))) := by
  let u (p : ℕ) := φ (r p)-clamp M (φ (r p))
  have h₁ := abs_sum_le_sum_abs u s
  have h₂ := sum_le_sum (s:=s) (fun p _ =>
    (err hM (φ (r p))).trans (power hg (r p)))
  have hs' : 0<(s.card:ℝ) := by exact_mod_cast hs.card_pos
  change (∑ p∈s,|u p| *M)≤∑ p∈s,2*K^2*(1+(r p)^(k*2)) at h₂
  simp only [←sum_mul,←mul_sum,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at h₂
  dsimp only [mean]
  rw [←sub_div,←sum_sub_distrib,abs_div,abs_of_pos hs',div_mul_eq_mul_div,div_le_iff₀ hs']
  change |∑ p∈s,u p| *M≤_
  have heq : (1+(∑ p∈s,(r p)^(k*2))/(s.card:ℝ))*s.card=
      (s.card:ℝ)+(∑ p∈s,(r p)^(k*2)) := by field_simp
  nlinarith only [mul_le_mul_of_nonneg_right h₁ hM.le,h₂,congrArg (fun x : ℝ => 2*K^2*x) heq]

/-- A common even-moment bound makes weak convergence valid for a given
integrable continuous test of polynomial growth. -/
theorem limit {s : ℕ → Finset ℕ} {r : ℕ → ℝ} {μ : MeasureTheory.ProbabilityMeasure ℝ}
    {φ : ℝ → ℝ} (hp : Continuous φ) {K : ℝ} (k : ℕ) (hg : ∀ x,|φ x|≤K*(1+|x|^k))
    (hi : MeasureTheory.Integrable φ (μ:MeasureTheory.Measure ℝ))
    {B : ℝ} (hB : 0≤B) (hh : ∀ᶠ X : ℕ in atTop,(s X).Nonempty ∧ mean (s X) (fun p => (r p)^(k*2))≤B)
    (hw : ∀ ψ : BoundedContinuousFunction ℝ ℝ,Tendsto (fun X => mean (s X) (fun p => ψ (r p))) atTop
      (𝓝 (∫ x,ψ x ∂μ))) :
    Tendsto (fun X => mean (s X) (fun p => φ (r p))) atTop (𝓝 (∫ x,φ x ∂μ)) := by
  let ψ (n : ℕ) : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => clamp n (φ x),by dsimp [clamp];fun_prop⟩ (2*n) (fun x y => by
      rw [Real.dist_eq];exact (abs_sub _ _).trans (by simpa [two_mul] using add_le_add (bounded (Nat.cast_nonneg n) (φ x)) (bounded (Nat.cast_nonneg n) (φ y))))
  have hd : Tendsto (fun n => ∫ x,ψ n x ∂μ) atTop (𝓝 (∫ x,φ x ∂μ)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => |φ x|)
      (fun n => (ψ n).continuous.aestronglyMeasurable) hi.abs
    · intro n;apply Eventually.of_forall;intro x
      change |clamp n (φ x)|≤|φ x|
      by_cases he : |φ x|≤n
      · simp [clamp,min_eq_right (abs_le.mp he).2,max_eq_right (abs_le.mp he).1]
      · exact (bounded (Nat.cast_nonneg n) _).trans (le_of_not_ge he)
    · apply Eventually.of_forall;intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop |φ x|] with n hn
      change φ x=clamp n (φ x)
      simp [clamp,min_eq_right (abs_le.mp hn).2,max_eq_right (abs_le.mp hn).1]
  apply Metric.tendsto_nhds.mpr;intro ε hε
  let D := 2*K^2*(1+B)
  have hD : 0≤D := by dsimp [D];positivity
  obtain ⟨n,hn,hN⟩ := ((Metric.tendsto_nhds.mp hd (ε/3) (by positivity)).and
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1+3*D/ε))).exists
  change 1+3*D/ε≤(n:ℝ) at hN
  have hn' : 0<(n:ℝ) := (show 0<1+3*D/ε by positivity).trans_le hN
  have hsmall : D/n<ε/3 := by
    rw [div_lt_iff₀ hn']
    have hc := mul_le_mul_of_nonneg_right hN hε.le
    rw [add_mul,div_mul_cancel₀ _ hε.ne'] at hc
    linarith
  filter_upwards [hh,Metric.tendsto_nhds.mp (hw (ψ n)) (ε/3) (by positivity)] with X hX he
  have he' := (finite (s X) hX.1 φ r k hg hn').trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hX.2 1) (by positivity))
  have hcut : |mean (s X) (fun p => φ (r p))-mean (s X) (fun p => ψ n (r p))|≤D/n :=
    (le_div_iff₀ hn').mpr he'
  rw [Real.dist_eq] at he hn ⊢
  let v := mean (s X) (fun p => ψ n (r p))
  let a := mean (s X) (fun p => φ (r p))
  let b := ∫ x,ψ n x ∂μ
  let z := ∫ x,φ x ∂μ
  change |a-v|≤D/n at hcut
  change |v-b|<ε/3 at he
  change |b-z|<ε/3 at hn
  change |a-z|<ε
  linarith only [abs_sub_le a v z,abs_sub_le v b z,hcut,hsmall,he,hn]

#print axioms limit

end
end Arxiv.«2501.03234».ThetaWindowTruncation
