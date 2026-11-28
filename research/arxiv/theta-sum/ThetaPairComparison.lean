import ThetaPrimeAnchorTests
import ThetaPairDyadic

/-! A bounded test on each member of a nearby directed prime pair. Uniform
upper-sieve control allows the exceptional prime starts to be discarded. -/
namespace Arxiv.«2501.03234».ThetaPairComparison
open Real Filter Finset ThetaPrimeStartDensity ThetaPrimeIntervalSieve ThetaShortPrimeInterval
open ThetaWindowApproximation ThetaAlmostPeriodicWindows ThetaLocalPrimeCounts ThetaNaturalPrimeMeans
open scoped Topology
noncomputable section

def scaled (X H : ℕ) (f g : ℕ → ℝ) := avg X X X (fun p => f p*avg X p H g)

theorem shift_marks (n H : ℕ) : sample n H=marks (n+1) H := by
  classical
  ext p
  simp only [sample,mem_primes,marks,mem_filter,mem_Ioc,mem_Ico,and_true]
  aesop (add safe (by omega))

theorem inner {θ : ℝ} (ht : 0<θ) {g : ℕ → ℝ} {B : ℝ} (hB : 0≤B) (hg : ∀ n,|g n|≤B) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop, ∀ n H : ℕ,X≤n → Admits θ X H → |avg X n H g|≤C := by
  obtain ⟨D,hD,hd⟩ := sieve ht
  refine ⟨D*B+1,by positivity,?_⟩
  filter_upwards [hd,eventually_ge_atTop (1:ℕ)] with X hd hx
  intro n H hn hH
  have hl := log_nonneg (Nat.one_le_cast.mpr hx)
  have hh := hd H (n+1) (by have := hH.2.1;omega) hH.2.2
  rw [←shift_marks] at hh
  have hr := (abs_sum_le_sum_abs g (sample n H)).trans (sum_le_sum (s:=sample n H) (fun i _ => hg i))
  simp only [sum_const,nsmul_eq_mul] at hr
  rw [avg,abs_mul,abs_of_nonneg (div_nonneg hl (Nat.cast_nonneg _))]
  apply (mul_le_mul_of_nonneg_left hr (div_nonneg hl (Nat.cast_nonneg _))).trans
  rw [div_mul_eq_mul_div,div_le_iff₀ (Nat.cast_pos.mpr hH.1)]
  nlinarith only [mul_le_mul_of_nonneg_right hh hB,Nat.cast_nonneg (α:=ℝ) H]

private theorem sum_bound (s E : Finset ℕ) (u : ℕ → ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (ha : ∀ p∈s,p∉E → |u p|≤A) (hb : ∀ p∈s,|u p|≤B) :
    |(∑ p∈s,u p)| ≤ (s.card:ℝ)*A+(E.card:ℝ)*B := by
  classical
  apply (abs_sum_le_sum_abs ..).trans
  rw [←sum_filter_add_sum_filter_not s (fun p => p∈E)]
  have h₁ := sum_le_sum (s:=s.filter (fun p => p∈E)) (fun p hp => hb p (mem_filter.mp hp).1)
  have h₂ := sum_le_sum (s:=s.filter (fun p => p∉E)) (fun p hp => ha p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
  simp only [sum_const,nsmul_eq_mul] at h₁ h₂
  have hs : s.filter (fun p => p∈E)⊆E := fun _ hp => (mem_filter.mp hp).2
  have HC := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hs)) hB
  have HD := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card (filter_subset (fun p => p∉E) s))) hA
  linarith only [h₁,h₂,HC,HD]


theorem compare {θ : ℝ} (ht : 0<θ) (hAP : ProgressionMangoldt) {f g : ℕ → ℝ}
    {B D : ℝ} (hB : 0<B) (hf : ∀ p,|f p|≤B) (hD : 0≤D) (hg : ∀ p,|g p|≤D)
    {b : ℝ} (htyp : ∀ t : ℝ,0<t → Typical (fun X n => ∀ H : ℕ,Admits θ X H → |avg X n H g-b|≤t))
    {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X)) :
    Tendsto (fun X : ℕ => scaled X (H X) f g-avg X X X f*b) atTop (𝓝 0) := by
  obtain ⟨C,hC,hinner⟩ := inner ht hD hg
  have hm := (ThetaPairDyadic.mass hAP).eventually_lt_const (by norm_num : (1:ℝ)<2)
  apply Metric.tendsto_nhds.mpr;intro ε he
  let t := ε/(8*B)
  let v := ε/(4*(B*(C+|b|)+1))
  have ht' : 0<t := by dsimp [t];positivity
  have hv : 0<v := by dsimp [v];positivity
  filter_upwards [hH,hinner,htyp t ht' v hv,hm,eventually_ge_atTop (2:ℕ)] with X hH hinner hE hm hx
  let s := sample X X
  let P (p : ℕ) := ∀ K : ℕ,Admits θ X K → |avg X p K g-b|≤t
  let E := missed X P
  let u (p : ℕ) := f p*(avg X p (H X) g-b)
  have hbound := sum_bound s E u (A:=B*t) (B:=B*(C+|b|)) (by positivity) (by positivity) (by
    intro p hp hgood
    have hp' : P p := by
      by_contra hm
      exact hgood (mem_missed.mpr ⟨ThetaPairDyadic.subset hx hp,hm⟩)
    exact (abs_mul ..).le.trans (mul_le_mul (hf p) (hp' _ hH) (abs_nonneg _) hB.le)) (by
    intro p hp
    have hs := (mem_Ioc.mp (mem_primes.mp hp).1).1
    exact (abs_mul ..).le.trans (mul_le_mul (hf p) ((abs_sub ..).trans (add_le_add_left (hinner p _ hs.le hH) _)) (abs_nonneg _) hB.le))
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  have eqn : scaled X (H X) f g-avg X X X f*b=log X/X*(∑ p∈s,u p) := by
    simp only [scaled,avg,s,u,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    ring
  rw [Real.dist_eq,sub_zero,eqn,abs_mul,abs_of_nonneg (div_nonneg hl hX.le)]
  apply (mul_le_mul_of_nonneg_left hbound (div_nonneg hl hX.le)).trans_lt
  change ((s.card:ℝ)*log X/X)<2 at hm
  change (E.card:ℝ)*log X≤v*X at hE
  have hE' := (div_le_iff₀ hX).mpr hE
  have hsmall : 8*B*t=ε := by dsimp [t];field_simp
  have hv' : 4*(B*(C+|b|)+1)*v=ε := by dsimp [v];field_simp
  have ha := mul_le_mul_of_nonneg_right hm.le (mul_nonneg hB.le ht'.le)
  have hb := mul_le_mul_of_nonneg_right hE' (show 0≤B*(C+|b|) by positivity)
  rw [show log X/X*(s.card*(B*t)+E.card*(B*(C+|b|)))=
    ((s.card:ℝ)*log X/X)*(B*t)+((E.card:ℝ)*log X/X)*(B*(C+|b|)) by ring]
  linarith only [ha,hb,hsmall,hv',hv,he]

#print axioms compare
end
end Arxiv.«2501.03234».ThetaPairComparison
