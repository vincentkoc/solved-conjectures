import ThetaPairExcursionDensity
import ThetaPairDyadic

/-! Positive joint counts at the lower almost-all prime threshold, for
independently specified residue classes and residual intervals. -/
namespace Arxiv.«2501.03234».ThetaNearbyPrimeExcursions
open Real Finset Filter ThetaWindowApproximation ThetaAlmostPeriodicWindows ThetaLocalPrimeCounts
open ThetaShortPrimeInterval ThetaPrimeStartDensity ThetaPairExcursionDensity ThetaNaturalPrimeMeans
open ThetaAlmostPrimeDistribution
noncomputable section
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def count (X H : ℕ) (P Q : ℕ → Prop) :=
  ∑ p∈(sample X X).filter P,((sample p H).filter Q).card

theorem combine {θ a b : ℝ} (ha : 0<a) (hb : 0<b) {P Q : ℕ → Prop}
    (h₁ : ∀ᶠ X : ℕ in atTop, a*X≤(((sample X X).filter P).card:ℝ)*log X)
    (h₂ : Typical (fun X n => ∀ H : ℕ,Admits θ X H → b≤avg X n H (mark Q))) :
    ∀ᶠ X : ℕ in atTop,∀ H : ℕ,Admits θ X H → (a*b/2)*X*H≤(count X H P Q:ℝ)*(log X)^2 := by
  filter_upwards [h₁,h₂ (a/2) (half_pos ha),eventually_ge_atTop (2:ℕ)] with X hS hE hX
  let S := (sample X X).filter P
  let good (p : ℕ) := ∀ H : ℕ,Admits θ X H → b≤avg X p H (mark Q)
  let E := missed X good
  let T := S \ E
  have ht : a/2*X≤(T.card:ℝ)*log X := by
    have hcount := card_sdiff_add_card_inter S E
    have hc : S.card≤T.card+E.card := by
      have hi := card_le_card (inter_subset_right (s₁:=S) (s₂:=E))
      change S.card≤(S \ E).card+E.card;omega
    have hc' : (S.card:ℝ)≤T.card+E.card := by exact_mod_cast hc
    have hl := log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
    change a*X≤(S.card:ℝ)*log X at hS
    change (E.card:ℝ)*log X≤a/2*X at hE
    linarith only [mul_le_mul_of_nonneg_right hc' hl,hS,hE]
  intro H hH
  let f (p : ℕ) : ℝ := ((sample p H).filter Q).card
  have hh : ∀ p∈T, b*H≤f p*log X := by
    intro p hp
    obtain ⟨hs,hm⟩ := mem_sdiff.mp hp
    have hg : good p := by
      by_contra hn
      exact hm (mem_missed.mpr ⟨ThetaPairDyadic.subset hX (mem_filter.mp hs).1,hn⟩)
    have hc := hg H hH
    rw [avg_mark,div_mul_eq_mul_div,le_div_iff₀ (Nat.cast_pos.mpr hH.1)] at hc
    rwa [mul_comm (log (X:ℝ))] at hc
  have hsum := sum_le_sum hh
  simp only [sum_const,nsmul_eq_mul,←sum_mul] at hsum
  have hcnt : (∑ p∈T,f p)≤(count X H P Q:ℝ) := by
    have hs := sum_le_sum_of_subset_of_nonneg (sdiff_subset (s:=S) (t:=E)) (fun p _ _ => (Nat.cast_nonneg _ : 0≤f p))
    simpa only [count,Nat.cast_sum,S,f,T] using hs
  have hl := log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have hmain := hsum.trans (mul_le_mul_of_nonneg_right hcnt hl)
  have hpos : 0≤b*(H:ℝ) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right ht hpos,mul_le_mul_of_nonneg_right hmain hl]

def selected (q r : ℕ) (y d : ℝ) (p : ℕ) := p%q=r ∧ |(S p:ℝ)/p-log p/2-y|<d

private theorem intervals (h : LowerInput) (hAP : ProgressionMangoldt) {θ : ℝ} (hθ : 1/15<θ) (ht : θ≤1)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (y : ℝ) {d : ℝ} (hd : 0<d) :
    ∃ a : ℝ,0<a ∧ Almost (fun X n => ∀ H : ℕ,Admits θ X H → a*H/log X≤
      (((sample n H).filter (selected q r y d)).card:ℝ)) := by
  obtain ⟨a,ha,hh⟩ := excursions h hAP hθ ht hq hr hu y hd
  refine ⟨a,ha,ThetaWindowApproximation.mono hh (Eventually.of_forall ?_)⟩
  intro X n _ hv H hH
  apply (hv H hH).trans_eq
  congr 2
  ext p
  simp only [mem_filter,selected]

theorem joint (h : LowerInput) (hAP : ProgressionMangoldt) {θ : ℝ} (hθ : 1/15<θ) (ht : θ≤1)
    {q r q' r' : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (hq' : 0<q') (hr' : r'<q') (hu' : r'.Coprime q') (y z : ℝ) {d e : ℝ} (hd : 0<d) (he : 0<e) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,Admits θ X H →
      δ*X*H≤(count X H (selected q r y d) (selected q' r' z e):ℝ)*(log X)^2 := by
  obtain ⟨a,ha,h₁⟩ := intervals h hAP (by norm_num : (1:ℝ)/15<1/2) (by norm_num) hq hr hu y hd
  obtain ⟨b,hb,h₂⟩ := intervals h hAP hθ ht hq' hr' hu' z he
  exact ⟨(a/3)*(b/2)/2,by positivity,combine (by positivity : 0<a/3) (half_pos hb)
    (dyadic (P:=selected q r y d) ha h₁)
    (anchored (P:=selected q' r' z e) (by linarith) ht hb h₂)⟩

#print axioms joint
end
end Arxiv.«2501.03234».ThetaNearbyPrimeExcursions
