import ThetaLagSieveWeights
import ThetaLogPrimeCorrelations

/-! A uniform ordinary upper-bound sieve and a finite second moment make
a positive proportion of the available displacements popular. -/
namespace Arxiv.«2501.03234».ThetaPopularLagCounts
open Real Filter Finset ThetaPrimeLagBounds ThetaPositiveLag ThetaLagSieveWeights
open ThetaDistinctPrimeQuadruples
noncomputable section

/-- Ordinary unweighted prime-pair upper sieve, including the single possible pair at odd lag. -/
def Upper := ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,∀ h : ℕ,0<h → h≤X →
  ((pairs X h).card:ℝ)*(log X)^2≤C*X*weight 3 h

theorem select {s : Finset ℕ} {L : ℕ} (hL : 0<L) (hs : s.card≤L) (f : ℕ → ℝ)
    {c B : ℝ} (hc : 0<c) (hB : 0<B) (hm : c*L≤∑ k∈s,f k)
    (h₂ : (∑ k∈s,(f k)^2)≤B*L) :
    c^2/(4*B)*L≤((s.filter (fun k => c/2≤f k)).card:ℝ) := by
  classical
  let P := s.filter (fun k => c/2≤f k)
  let Q := s.filter (fun k => ¬c/2≤f k)
  have hcap : (Q.card:ℝ)≤L := by exact_mod_cast (card_le_card (filter_subset _ s)).trans hs
  have hh := sum_le_sum (s:=Q) (g:=fun _ => c/2) (fun k hk => (lt_of_not_ge (mem_filter.mp hk).2).le)
  simp only [sum_const,nsmul_eq_mul] at hh
  have ht : (∑ k∈P,f k)+(∑ k∈Q,f k)=∑ k∈s,f k := sum_filter_add_sum_filter_not ..
  have hmain : c/2*L≤∑ k∈P,f k := by nlinarith only [hm,hh,ht,mul_le_mul_of_nonneg_right hcap (half_pos hc).le]
  have H := sum_mul_sq_le_sq_mul_sq P (fun _ => (1:ℝ)) f
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at H
  have hen := (sum_le_sum_of_subset_of_nonneg (show P⊆s from filter_subset ..) (fun k _ _ => sq_nonneg (f k))).trans h₂
  have hL' : 0<(L:ℝ) := by exact_mod_cast hL
  have hh₂ := pow_le_pow_left₀ (mul_nonneg (half_pos hc).le hL'.le) hmain 2
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<4*B)]
  apply (mul_le_mul_iff_left₀ hL').mp
  nlinarith only [hh₂,H,mul_le_mul_of_nonneg_left hen (Nat.cast_nonneg P.card)]

def value (D X k : ℕ) (f : ℕ → ℝ) := max 0 (corr X (D*k) f)*(log X)^2/X

theorem dispersion (U : Upper) {D : ℕ} (hD : 0<D) {f : ℕ → ℝ} (hf : ∀ p,|f p|≤1) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ X : ℕ in atTop,∀ L : ℕ,D*L≤X →
      (∑ k∈offsets L,(value D X k f)^2)≤B*L := by
  obtain ⟨C,hC,H⟩ := U
  refine ⟨C^2*exp 12*D,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (1:ℕ)] with X hx hX
  intro L hL
  have hx' : 0<(X:ℝ) := by exact_mod_cast hX
  have hb (k : ℕ) (hk : k∈offsets L) : value D X k f≤C*weight 3 (D*k) := by
    obtain ⟨h₀,hl⟩ := mem_erase.mp hk
    let d := D*k
    have HH := hx d (Nat.mul_pos hD (Nat.pos_of_ne_zero h₀)) ((Nat.mul_le_mul_left D (mem_range.mp hl).le).trans hL)
    have hu (p : ℕ) : f p*f (p+d)≤1 := by
      exact (le_abs_self _).trans (by rw [abs_mul];exact (mul_le_mul (hf _) (hf _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
    have hc := sum_le_sum (s:=pairs X d) (fun p _ => hu p)
    simp only [sum_const,nsmul_eq_mul,mul_one] at hc
    have hb : max 0 (corr X d f)≤((pairs X d).card:ℝ) := max_le (Nat.cast_nonneg _) hc
    apply (div_le_iff₀ hx').mpr
    nlinarith only [mul_le_mul_of_nonneg_right hb (sq_nonneg (log X)),HH]
  have hs := sum_le_sum (s:=offsets L) (fun k hk => pow_le_pow_left₀
    (show 0≤value D X k f by dsimp [value];positivity) (hb k hk) 2)
  simp only [mul_pow,←mul_sum] at hs
  nlinarith only [hs,mul_le_mul_of_nonneg_left (mean_square hD L) (sq_nonneg C)]

def popular (X D L : ℕ) (f : ℕ → ℝ) (b : ℝ) := (offsets L).filter
  (fun k => b*X≤corr X (D*k) f*(log X)^2)

theorem many (U : Upper) {D : ℕ} (hD : 0<D) {c : ℝ} (hc : 0<c) {f : ℕ → ℝ}
    (hf : ∀ p,|f p|≤1) (s : Scales D c f) :
    ∃ δ K : ℝ,0<δ ∧ 0<K ∧ ∀ᶠ X : ℕ in atTop,∀ L : ℕ,K*log X≤L → D*L≤X →
      δ*L≤((popular X D L f (c/2)).card:ℝ) := by
  obtain ⟨K,hK,H⟩ := s
  obtain ⟨B,hB,HB⟩ := dispersion U hD hf
  refine ⟨c^2/(4*B),K,by positivity,hK,?_⟩
  filter_upwards [H,HB,eventually_ge_atTop (2:ℕ)] with X hh hb hx
  intro L hL hcap
  have hx' : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
  have hpos : 0<L := Nat.cast_pos.mp ((mul_pos hK hl).trans_le hL)
  have hcard : (offsets L).card≤L := (card_le_card (erase_subset ..)).trans (by simp)
  have hm : c*L≤∑ k∈offsets L,value D X k f := by
    simp only [value,←sum_div,←sum_mul]
    apply (le_div_iff₀ hx').mpr
    nlinarith only [hh L hL hcap]
  apply le_trans (select hpos hcard _ hc hB hm (hb L hcap))
  apply Nat.cast_le.mpr
  apply card_le_card
  intro k hk
  obtain ⟨hk,he⟩ := mem_filter.mp hk
  apply mem_filter.mpr
  refine ⟨hk,?_⟩
  have he' := (le_div_iff₀ hx').mp he
  by_cases hn : 0≤corr X (D*k) f
  · rwa [max_eq_right hn] at he'
  · rw [max_eq_left (le_of_not_ge hn),zero_mul] at he'
    exact False.elim ((mul_pos (half_pos hc) hx').not_ge he')

#print axioms select
#print axioms many

#print axioms dispersion
end
end Arxiv.«2501.03234».ThetaPopularLagCounts
