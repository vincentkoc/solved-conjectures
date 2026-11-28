import ThetaAlmostPeriodicWindows

/-! Transfer global prime-mean approximations to almost every short-window
starting point. Only the ordinary fixed-modulus inputs involve the length. -/
namespace Arxiv.«2501.03234».ThetaAlmostTransfer
open Real Finset Filter ThetaWindowApproximation ThetaAlmostPeriodicWindows ThetaPrimeLaw
open ThetaNaturalPrimeMeans ThetaConditionalRows ThetaPeriodMeans
open scoped Topology
noncomputable section
local instance (n : ℕ) : NeZero n.factorial := ⟨Nat.factorial_ne_zero _⟩

private theorem compare {P Q : ℕ → ℕ → Prop} (hp : Almost P)
    {ε τ δ : ℝ} (he : 0<ε) (ht : 0<τ) (hd : 0≤δ) (hsmall : δ≤ε*τ/24)
    (e : ℕ → ℝ) (he₀ : ∀ p,0≤e p) (hm : ∀ᶠ Y : ℕ in atTop,primeMean e Y≤δ)
    (h : ∀ᶠ X : ℕ in atTop,∀ n∈starts X, P X n →
      (∀ H : ℕ,0<H → H≤X → avg X n H e≤τ) → Q X n) :
    ∀ᶠ X : ℕ in atTop, ((exceptional X (Q X)).card:ℝ)≤ε*X := by
  classical
  filter_upwards [hp (ε/2) (half_pos he),budget hd ht e he₀ hm,h] with X hP hE hx
  let E (n : ℕ) := ∀ H : ℕ,0<H → H≤X → avg X n H e≤τ
  have hu : exceptional X (Q X)⊆exceptional X (P X)∪exceptional X E := by
    intro n hn;obtain ⟨hn,hb⟩ := mem_exceptional.mp hn
    by_cases h₁ : P X n
    · exact mem_union_right _ (mem_exceptional.mpr ⟨hn,fun h₂ => hb (hx n hn h₁ h₂)⟩)
    · exact mem_union_left _ (mem_exceptional.mpr ⟨hn,h₁⟩)
  have hc := (Nat.cast_le (α:=ℝ)).mpr ((card_le_card hu).trans (card_union_le ..))
  push_cast at hc
  have hcoef : 12*δ/τ≤ε/2 := (div_le_iff₀ ht).mpr (by linarith only [hsmall])
  have hB := hE.trans (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg X))
  change ((exceptional X E).card:ℝ)≤_ at hB
  linarith only [hc,hB,hP]

private theorem mean_error (f g : ℕ → ℝ) (X : ℕ) :
    |primeMean f X-primeMean g X|≤primeMean (fun p => |f p-g p|) X := by
  simpa using lipschitz_mean (φ:=id) LipschitzWith.id f g X

theorem limit {θ : ℝ} (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {f : ℕ → ℝ} (hf : Approximable f) {a : ℝ} (ha : Tendsto (primeMean f) atTop (𝓝 a))
    {t : ℝ} (ht : 0<t) :
    Almost (fun X n => ∀ H : ℕ, Admits θ X H → |avg X n H f-a|≤t) := by
  intro ε hε
  let τ := t/4
  have hτ : 0<τ := by dsimp [τ];positivity
  let δ := min τ (ε*τ/24)
  have hδ : 0<δ := lt_min hτ (by positivity)
  obtain ⟨T,g,hg,he⟩ := hf δ hδ
  have hl := periodic_prime_mean hAP hg
  have hc : |a-unitMean T.factorial g|≤δ := le_of_tendsto ((ha.sub hl).abs) <| he.mono
    (fun X hX => (mean_error f g X).trans hX)
  apply compare (ThetaAlmostPeriodicWindows.limit h hg hτ) hε hτ hδ.le (min_le_right ..)
    (fun p => |f p-g p|) (fun _ => abs_nonneg _) he
  filter_upwards [eventually_ge_atTop (1:ℕ)] with X hX
  intro n _ h₁ h₂ H hH
  have he' := (difference (n:=n) (H:=H) hX f g).trans (h₂ H hH.1 hH.2.1)
  have hg' := h₁ H hH
  have hh := abs_sub_le (avg X n H f) (avg X n H g) a
  have hh' := abs_sub_le (avg X n H g) (unitMean T.factorial g) a
  rw [abs_sub_comm (a:=unitMean T.factorial g) (b:=a)] at hh'
  have hd : δ≤τ := min_le_left ..
  dsimp only [τ] at he' hg' hd
  linarith

theorem lower {θ c : ℝ} (h : Lower θ c) (hc : 0<c) (hAP : ProgressionMangoldt)
    {f : ℕ → ℝ} (hf : Approximable f) (hf₀ : ∀ n,0≤f n) {m : ℝ} (hm : 0 < m)
    (hl : ∀ᶠ X : ℕ in atTop,m≤primeMean f X) :
    Almost (fun X n => ∀ H : ℕ, Admits θ X H → c*m/4≤avg X n H f) := by
  intro ε hε
  let τ := c*m/4
  have hτ : 0<τ := by dsimp [τ];positivity
  let δ := min (m/2) (ε*τ/24)
  have hδ : 0<δ := lt_min (half_pos hm) (by positivity)
  obtain ⟨T,g,hg,he⟩ := hf δ hδ
  let b (p : ℕ) := max (g p) 0
  have hpos (p : ℕ) : 0≤b p := le_max_right ..
  have hb : OnMod T.factorial b := fun n => congrArg (fun x : ℝ => max x 0) (hg n)
  have herr : ∀ᶠ X : ℕ in atTop,primeMean (fun p => |f p-b p|) X≤δ := by
    apply he.mono;intro X hx;apply le_trans _ hx
    apply mean_mono;intro p
    by_cases h : 0≤g p
    · simp [b,max_eq_left h]
    · have hg' := le_of_not_ge h
      change |f p-max (g p) 0|≤|f p-g p|
      rw [max_eq_right hg',sub_zero,abs_of_nonneg (hf₀ p),abs_of_nonneg (by linarith [hf₀ p] : 0≤f p-g p)]
      linarith
  have hmass : m/2≤unitMean T.factorial b := by
    apply ge_of_tendsto (periodic_prime_mean hAP hb)
    filter_upwards [herr,hl] with X he' hm'
    have hh := (le_abs_self _).trans ((mean_error f b X).trans he')
    have hsmall : δ≤ m/2 := min_le_left ..
    linarith
  apply compare (ThetaAlmostPeriodicWindows.lower h hb hpos) hε hτ hδ.le (min_le_right ..)
    (fun p => |f p-b p|) (fun _ => abs_nonneg _) herr
  filter_upwards [eventually_ge_atTop (1:ℕ)] with X hX
  intro n _ h₁ h₂ H hH
  have hbound := (difference (n:=n) (H:=H) hX f b).trans (h₂ H hH.1 hH.2.1)
  have hb' := (mul_le_mul_of_nonneg_left hmass hc.le).trans (h₁ H hH)
  have h₃ := (abs_le.mp hbound).1
  dsimp only [τ] at h₃;linarith only [h₃,hb']

#print axioms limit
#print axioms lower
end
end Arxiv.«2501.03234».ThetaAlmostTransfer
