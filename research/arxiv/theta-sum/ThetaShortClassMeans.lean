import ThetaShortPrimeDistribution

/-! Short-window averages in a reduced class, normalized by its own prime count. -/
namespace Arxiv.«2501.03234».ThetaShortClassMeans
open Filter Real Finset MeasureTheory ThetaPrimeLaw ThetaProfiniteUnits ThetaIdentityFiber
open ThetaLocalIntervalTests ThetaDyadicLaw ThetaLocalDyadicReference ThetaLocalPrimeCounts
open ThetaNaturalPrimeMeans ThetaPrimeDensity ThetaCharacterPrimeMeans ThetaCalibratedCone
open scoped Topology NNReal
noncomputable section

def mean (s : Finset ℕ) (f : ℕ → ℝ) : ℝ := (∑ p∈s,f p)/s.card
def window (q r X H : ℕ) := cell q r (sample X H)

theorem dominated {s z : Finset ℕ} (hs : s.Nonempty) (hsub : s⊆z) {f : ℕ → ℝ}
    (hf : ∀ n,0≤f n) {D B : ℝ} (hD : (z.card:ℝ)≤D*s.card) (hB : 0≤B) (hm : mean z f≤B) :
    mean s f≤B*D := by
  have hc : 0<(s.card:ℝ) := by exact_mod_cast hs.card_pos
  have hz : 0<(z.card:ℝ) := by exact_mod_cast (hs.mono hsub).card_pos
  have hu := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf p)
  change (∑ p∈s,f p)/(s.card:ℝ)≤_
  apply (div_le_iff₀ hc).mpr
  nlinarith only [hu,(div_le_iff₀ hz).mp hm,mul_le_mul_of_nonneg_left hD hB]

theorem weighted_sum (s : Finset ℕ) (q r : ℕ) (f : ℕ → ℝ) :
    (∑ p∈s,selectClass r q p*f p)=∑ p∈cell q r s,f p := by
  classical
  simp only [selectClass,ite_mul,one_mul,zero_mul,cell,sum_filter]

theorem prefix_mean (q r X : ℕ) (f : ℕ → ℝ) :
    primeMean (fun p => selectClass r q p*f p) X=
      (((primeSet (fun n => n%q=r) X).card:ℝ)/X.primeCounting)*progressionMean q r f X := by
  classical
  let s := primeSet (fun n => n%q=r) X
  have eq : cell q r (Nat.primesLE X)=s := by ext p;simp [cell,s,primeSet]
  rw [primeMean,weighted_sum,eq,progressionMean]
  change (∑ p∈s,f p)/_=(s.card/_)*((∑ p∈s,f p)/s.card)
  by_cases hs : s.Nonempty
  · have hpos : (s.card:ℝ)≠0 := by exact_mod_cast hs.card_pos.ne'
    by_cases hπ : (X.primeCounting:ℝ)=0
    · simp [hπ]
    · field_simp
  · rw [not_nonempty_iff_eq_empty.mp hs];simp

theorem factor {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (hAP : ProgressionMangoldt) {f : ℕ → ℝ} {a : ℝ}
    (ha : Tendsto (progressionMean q r f) atTop (𝓝 a)) :
    Tendsto (primeMean (fun p => selectClass r q p*f p)) atTop (𝓝 (1/(q.totient:ℝ)*a)) :=
  ((class_prime_density hAP hq hu hr).mul ha).congr (fun X => (prefix_mean q r X f).symm)

theorem denominator {θ : ℝ} (h : Ordinary θ) (hAP : ProgressionMangoldt)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X) :
    Tendsto (fun X => ((window q r X (H X)).card:ℝ)/mass X (H X)) atTop (𝓝 (1/(q.totient:ℝ))) := by
  let : NeZero q := ⟨hq.ne'⟩
  let w := selectClass r q
  have eq (s : Finset ℕ) : (∑ p∈s,w p)=((cell q r s).card:ℝ) := by
    simpa only [w,mul_one,sum_const,nsmul_eq_mul] using weighted_sum s q r (fun _ => (1:ℝ))
  have hg := class_prime_density hAP hq hu hr
  have hper := ThetaNaturalPrimeMeans.periodic_prime_mean hAP (selectClass_mod r q)
  have heq : ThetaConditionalRows.unitMean q w=1/(q.totient:ℝ) := by
    apply tendsto_nhds_unique hper
    apply hg.congr
    intro X
    change _=(∑ p∈Nat.primesLE X,w p)/_
    rw [eq]
    rw [show primeSet (fun n => n%q=r) X=cell q r (Nat.primesLE X) by ext p;simp [primeSet,cell]]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [ThetaLocalLipschitzTransfer.periodic_mean h (selectClass_mod r q) (half_pos hε),hh] with X h₁ h₂
  have ha := h₁ (H X) h₂.1 h₂.2
  change |(∑ p∈sample X (H X),w p)/mass X (H X)-ThetaConditionalRows.unitMean q w|≤ε/2 at ha
  rw [eq,heq] at ha
  exact ha.trans_lt (half_lt_self hε)

theorem normalize {θ : ℝ} (h : Ordinary θ) (hAP : ProgressionMangoldt) {q r : ℕ}
    (hq : 0<q) (hr : r<q) (hu : r.Coprime q) {H : ℕ → ℕ}
    (hh : ∀ᶠ X : ℕ in atTop,H X≤X ∧ (X:ℝ)^θ≤H X) {f : ℕ → ℝ} {a : ℝ}
    (ha : Tendsto (fun X => avg X (H X) (fun p => selectClass r q p*f p)) atTop (𝓝 (1/(q.totient:ℝ)*a))) :
    Tendsto (fun X => mean (window q r X (H X)) f) atTop (𝓝 a) := by
  have hpos : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hden := denominator h hAP hq hr hu hh
  have hr := ha.div hden (by positivity)
  rw [mul_comm (1/(q.totient:ℝ)),mul_div_cancel_right₀ _ (by positivity)] at hr
  apply hr.congr'
  filter_upwards [hh,ThetaLocalMomentBudgets.count h] with X hx hc
  dsimp [avg,mean,window]
  rw [weighted_sum,div_div_div_cancel_right₀ (hc _ hx.1 hx.2).1.ne']

#print axioms normalize
end
end Arxiv.«2501.03234».ThetaShortClassMeans
