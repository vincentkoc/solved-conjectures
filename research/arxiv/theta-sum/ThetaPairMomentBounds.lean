import ThetaPairMarginals

/-! Uniform integrability budgets for both class-conditioned marginals. -/
namespace Arxiv.«2501.03234».ThetaPairMomentBounds
open Filter Finset Real MeasureTheory ThetaClassPairLaws ThetaPairMarginals ThetaPrimeLaw ThetaProfiniteUnits
open ThetaLocalPrimeCounts ThetaNaturalPrimeMeans ThetaPairDyadic ThetaCharacterPrimeMeans ThetaClassResidualLaws
open ThetaIdentityFiber ThetaConditionalHaar ThetaShortConditionalLaw ThetaAlmostPeriodicWindows
open ThetaPairEmpirical ThetaShortClassMeans ThetaLocalIntervalTests
open scoped Topology
noncomputable section

theorem box_bound (hAP : ProgressionMangoldt) {f : ℕ → ℝ} (hf : ∀ p,0≤f p) {a : ℝ}
    (hlim : Tendsto (primeMean f) atTop (𝓝 a)) :
    ∀ᶠ X : ℕ in atTop,log X/X*(∑ p∈box X,f p)≤4*(|a|+1) := by
  have hc := (cumulative hAP hlim).comp (show Tendsto (fun X : ℕ => 4*X) atTop atTop by
    apply tendsto_atTop_mono (fun x => by change x≤4*x;omega) tendsto_id)
  filter_upwards [eventually_ge_atTop (2:ℕ),hc.eventually_lt_const (show a < |a|+1 by linarith only [le_abs_self a])]
    with X hx ht
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_le_log hX (show (X:ℝ)≤4*X by linarith)
  change log ((4*X:ℕ):ℝ)/((4*X:ℕ):ℝ)*(∑ p∈box X,f p)<_ at ht
  simp only [Nat.cast_mul,Nat.cast_ofNat] at ht
  have hsum : 0≤∑ p∈box X,f p := sum_nonneg (fun p _ => hf p)
  rw [div_mul_eq_mul_div,div_lt_iff₀ (by positivity : 0<4*(X:ℝ))] at ht
  rw [div_mul_eq_mul_div,div_le_iff₀ hX]
  nlinarith only [ht,mul_le_mul_of_nonneg_right hl hsum]

theorem subset (q r s t X H : ℕ) : selected q r s t X H⊆pairs X H := by
  intro z hz
  obtain ⟨hp,hl⟩ := mem_sigma.mp hz
  exact mem_sigma.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hl).1⟩

theorem budgets {θ : ℝ} (hθ : 0<θ) (hθ' : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {q r s t : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (hs : 0<s) (ht : t<s) (hv : t.Coprime s)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X))
    {f : ℕ → ℝ} (hf : ∀ p,0≤f p) {a : ℝ} (ha : Tendsto (primeMean f) atTop (𝓝 a)) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ X : ℕ in atTop,let z := selected q r s t X (H X)
      z.Nonempty ∧ (∑ p∈z,f p.1)/(z.card:ℝ)≤B ∧ (∑ p∈z,f p.2)/(z.card:ℝ)≤B := by
  obtain ⟨C,hC,hdeg⟩ := degrees hθ
  have hq₀ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hs₀ : 0<(s.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hs
  have hd : 0<weight q s := by dsimp [weight];positivity
  let D := 4*(|a|+1)
  have hD : 0<D := by dsimp [D];positivity
  refine ⟨C*D/(weight q s/2),by positivity,?_⟩
  have hc := pair_count hθ hθ' h hAP hq hr hu hs ht hv hF hH
  filter_upwards [hc.eventually_const_lt (half_lt_self hd),hH,box_bound hAP hf ha,hdeg,eventually_ge_atTop (2:ℕ)] with X hm hh hb hdeg hx
  let z := selected q r s t X (H X)
  let L := log (X:ℝ)/X*(log X/(H X:ℝ))
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show 1<(X:ℝ) by exact_mod_cast hx)
  have hH₀ : 0<(H X:ℝ) := by exact_mod_cast hh.1
  have hL : 0<L := by dsimp [L];positivity
  change weight q s/2<L*(z.card:ℝ) at hm
  have hn : z.Nonempty := by
    by_contra he;rw [not_nonempty_iff_eq_empty.mp he] at hm;simp at hm;linarith only [hd,hm]
  have hz : 0<(z.card:ℝ) := by exact_mod_cast hn.card_pos
  obtain ⟨d₁,d₂⟩ := hdeg _ hh f hf
  have aux (g : (Σ _ : ℕ,ℕ) → ℝ) (hg : ∀ p,0≤g p)
      (hh' : (∑ p∈pairs X (H X),g p)*log X≤C*(H X)*(∑ p∈box X,f p)) :
      (∑ p∈z,g p)/(z.card:ℝ)≤C*D/(weight q s/2) := by
    have hu₁ := sum_le_sum_of_subset_of_nonneg (subset q r s t X (H X)) (fun p _ _ => hg p)
    have hs' := ((mul_le_mul_of_nonneg_right hu₁ hl.le).trans hh')
    have hscaled : L*(∑ p∈z,g p)≤C*D := by
      dsimp only [L]
      calc
        _ = (log X/X)*(((∑ p∈z,g p)*log X)/(H X)) := by ring
        _ ≤ (log X/X)*(C*(∑ p∈box X,f p)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply (div_le_iff₀ hH₀).mpr
          linarith only [hs']
        _ ≤ C*D := by
          rw [mul_left_comm];exact mul_le_mul_of_nonneg_left hb hC.le
    rw [div_le_div_iff₀ hz (half_pos hd)]
    have h₁ := mul_le_mul_of_nonneg_left hm.le (sum_nonneg (s:=z) (fun p _ => hg p))
    nlinarith only [h₁,mul_le_mul_of_nonneg_right hscaled hz.le]
  exact ⟨hn,aux _ (fun p => hf p.1) d₁,aux _ (fun p => hf p.2) d₂⟩

#print axioms budgets
end
end Arxiv.«2501.03234».ThetaPairMomentBounds
