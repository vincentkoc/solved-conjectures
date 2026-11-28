import ThetaPairBiasThree

/-! The signed second-order bias for the actual gap of two nearby primes. -/
namespace Arxiv.«2501.03234».ThetaGapBiasThree
open Filter Finset Real MeasureTheory ThetaPairEmpirical ThetaClassPairLaws ThetaPairBiasThree
open ThetaLocalPrimeCounts ThetaShortPrimeInterval ThetaShortClassMeans
open ThetaConditionalHaar ThetaShortConditionalLaw ThetaPairTestTruncation ThetaCharacterCoefficient
open ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaAlmostPeriodicWindows
open scoped Topology
noncomputable section

def gap (d X H : ℕ) := (pairs X H).filter (fun z => (z.2-z.1)%3=d)
def total (Z : Finset (Σ _ : ℕ,ℕ)) (g : ℝ×ℝ → ℝ) := ∑ z∈Z,g (observe z)
def scale (X H : ℕ) : ℝ := log X/X*(log X/H)

private theorem units {p : ℕ} (hp : p.Prime) (h : 3<p) : p%3=1 ∨ p%3=2 := by
  by_contra! H
  have h0 : p%3=0 := by omega
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero h0) with hh|hh <;> omega

private theorem cell_mem (q r s t X H : ℕ) (z : Σ _ : ℕ,ℕ) :
    z∈selected q r s t X H ↔ z∈pairs X H ∧ z.1%q=r ∧ z.2%s=t := by
  simp only [selected,pairs,mem_sigma,window,ThetaLocalIntervalTests.cell,mem_filter];tauto

theorem split {X : ℕ} (hX : 3≤X) (H : ℕ) :
    gap 0 X H=selected 3 1 3 1 X H ∪ selected 3 2 3 2 X H ∧
    gap 1 X H=selected 3 1 3 2 X H ∧ gap 2 X H=selected 3 2 3 1 X H := by
  have hr (z : Σ _ : ℕ,ℕ) (hz : z∈pairs X H) :
      z.1<z.2 ∧ (z.1%3=1 ∨ z.1%3=2) ∧ (z.2%3=1 ∨ z.2%3=2) := by
    obtain ⟨hp,hl⟩ := mem_sigma.mp hz
    simp only [sample,mem_primes,mem_Ioc,and_true] at hp hl
    exact ⟨hl.1.1,units hp.2 (lt_of_le_of_lt hX hp.1.1),units hl.2 (by have := hp.1.1;have := hl.1.1;omega)⟩
  refine ⟨?_,?_,?_⟩ <;> ext z <;> simp only [gap,mem_filter,mem_union,cell_mem] <;>
    by_cases hz : z∈pairs X H <;> simp only [hz,true_and,false_and,or_self] <;>
    first | rfl | (obtain ⟨hp,ha,hb⟩ := hr z hz;omega)

private theorem disj (X H : ℕ) : Disjoint (selected 3 1 3 1 X H) (selected 3 2 3 2 X H) := by
  rw [disjoint_left]
  intro z ha hb
  have h₁ := ((cell_mem ..).mp ha).2.1
  have h₂ := ((cell_mem ..).mp hb).2.1
  omega

theorem cell_total {θ : ℝ} (hθ : 0<θ) (ht : θ≤1) (h : Equidistributed θ) (hAP : ProgressionMangoldt)
    {r t : ℕ} (hr : r<3) (hu : r.Coprime 3) (ht₀ : t<3) (hv : t.Coprime 3)
    {F : G →₁[haar] ℝ} (hF : Represents residual F) {H : ℕ → ℕ} (hH : ∀ᶠ X : ℕ in atTop,Admits θ X (H X))
    {g : ℝ×ℝ → ℝ} (hg : Measurable g) {a : ℝ}
    (hh : Tendsto (fun X => ∫ z,g z ∂(empirical (selected 3 r 3 t X (H X)))) atTop (𝓝 a)) :
    Tendsto (fun X => scale X (H X)*total (selected 3 r 3 t X (H X)) g) atTop (𝓝 (a/4)) := by
  have hc := pair_count hθ ht h hAP (by decide) hr hu (by decide) ht₀ hv hF hH
  rw [show weight 3 3=1/4 by norm_num [weight,show Nat.totient 3=2 by decide]] at hc
  have L := hc.mul hh
  rw [show (1/4:ℝ)*a=a/4 by ring] at L
  apply L.congr'
  filter_upwards [hc.eventually_const_lt (by norm_num : (0:ℝ)<1/4)] with X hx
  let z := selected 3 r 3 t X (H X)
  have hn : z.Nonempty := by by_contra he;change 0<_*(z.card:ℝ) at hx;rw [not_nonempty_iff_eq_empty.mp he] at hx;simp at hx
  have hne : (z.card:ℝ)≠0 := by exact_mod_cast hn.card_pos.ne'
  rw [integral_empirical hn hg]
  change (scale X (H X)*(z.card:ℝ))*(total z g/z.card)=_
  field_simp
  rfl

def Limits (H : ℕ → ℕ) (g : ℝ×ℝ → ℝ) (v₀ v₁ v₂ : ℝ) : Prop :=
  Tendsto (fun X => scale X (H X)*total (gap 0 X (H X)) g) atTop (𝓝 v₀) ∧
  Tendsto (fun X => scale X (H X)*total (gap 1 X (H X)) g) atTop (𝓝 v₁) ∧
  Tendsto (fun X => scale X (H X)*total (gap 2 X (H X)) g) atTop (𝓝 v₂)

private theorem combine {H : ℕ → ℕ} {g : ℝ×ℝ → ℝ} {a b c d : ℝ}
    (h₁ : Tendsto (fun X => scale X (H X)*total (selected 3 1 3 1 X (H X)) g) atTop (𝓝 a))
    (h₂ : Tendsto (fun X => scale X (H X)*total (selected 3 2 3 2 X (H X)) g) atTop (𝓝 b))
    (h₃ : Tendsto (fun X => scale X (H X)*total (selected 3 1 3 2 X (H X)) g) atTop (𝓝 c))
    (h₄ : Tendsto (fun X => scale X (H X)*total (selected 3 2 3 1 X (H X)) g) atTop (𝓝 d)) :
    Limits H g (a+b) c d := by
  refine ⟨(h₁.add h₂).congr' ?_,h₃.congr' ?_,h₄.congr' ?_⟩ <;>
    filter_upwards [eventually_ge_atTop (3:ℕ)] with X hx
  · simp only [(split hx _).1,total,sum_union (disj ..),mul_add]
  · rw [(split hx _).2.1]
  · rw [(split hx _).2.2]

def actual (d X H : ℕ) := total (gap d X H) test/(gap d X H).card

private theorem ratio {H : ℕ → ℕ} {d : ℕ} {a b : ℝ} (hb : 0<b)
    (h₁ : Tendsto (fun X => scale X (H X)*total (gap d X (H X)) test) atTop (𝓝 a))
    (h₂ : Tendsto (fun X => scale X (H X)*total (gap d X (H X)) (fun _ => 1)) atTop (𝓝 b)) :
    Tendsto (fun X => actual d X (H X)) atTop (𝓝 (a/b)) := by
  apply (h₁.div h₂ hb.ne').congr'
  filter_upwards [h₂.eventually_const_lt hb] with X hx
  have hn := left_ne_zero_of_mul hx.ne'
  simp only [total,sum_const,nsmul_eq_mul,mul_one] at *
  exact mul_div_mul_left _ _ hn

def Statement (θ : ℝ) : Prop := 0<characterConstant ∧ ∀ H : ℕ → ℕ,(∀ᶠ X : ℕ in atTop,Admits θ X (H X)) →
  Limits H (fun _ => 1) (1/2) (1/4) (1/4) ∧
  Limits H test (characterConstant^2/2) (-(characterConstant^2)/4) (-(characterConstant^2)/4) ∧
  ∀ d : ℕ,d<3 → Tendsto (fun X => actual d X (H X)) atTop
    (𝓝 (if d=0 then characterConstant^2 else -(characterConstant^2)))

theorem original (h : ThetaAlmostPrimeDistribution.DistributionInput) (hAP : ProgressionMangoldt)
    {θ : ℝ} (hθ : 1/6<θ) (ht : θ≤1) : Statement θ := by
  let β := (1/6+θ)/2
  have h₀ : 0<θ := by linarith
  have hh := ThetaAlmostPrimeCounts.limit h₀ (show β<θ by dsimp [β];linarith)
    (h β (by dsimp [β];linarith) (by dsimp [β];linarith))
  obtain ⟨F,hF⟩ := exists_haar_representative hAP residual_approximable
  refine ⟨positive_constant hAP,?_⟩
  intro H hH
  have ct {r t : ℕ} (hr : r<3) (hu : r.Coprime 3) (hr' : t<3) (hu' : t.Coprime 3) :=
    cell_total h₀ ht hh hAP hr hu hr' hu' hF hH (g:=fun _ => (1:ℝ)) measurable_const
      (a:=1) (by simpa only [integral_const,probReal_univ,one_smul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  have wt {r t : ℕ} (hr : r<3) (hu : r.Coprime 3) (hr' : t<3) (hu' : t.Coprime 3) :=
    cell_total h₀ ht hh hAP hr hu hr' hu' hF hH (g:=test) (by unfold test ThetaPairBiasThree.center;fun_prop)
      (cell_test h₀ ht hh hAP hr hu hr' hu' hF hH)
  have c : Limits H (fun _ => 1) (1/2) (1/4) (1/4) := by
    convert combine (ct (r:=1) (t:=1) (by decide) (by decide) (by decide) (by decide))
      (ct (r:=2) (t:=2) (by decide) (by decide) (by decide) (by decide))
      (ct (r:=1) (t:=2) (by decide) (by decide) (by decide) (by decide))
      (ct (r:=2) (t:=1) (by decide) (by decide) (by decide) (by decide)) using 1 <;> norm_num
  have w : Limits H test (characterConstant^2/2) (-(characterConstant^2)/4) (-(characterConstant^2)/4) := by
    convert combine (wt (r:=1) (t:=1) (by decide) (by decide) (by decide) (by decide))
      (wt (r:=2) (t:=2) (by decide) (by decide) (by decide) (by decide))
      (wt (r:=1) (t:=2) (by decide) (by decide) (by decide) (by decide))
      (wt (r:=2) (t:=1) (by decide) (by decide) (by decide) (by decide)) using 1 <;> norm_num [signedBias] <;> ring
  refine ⟨c,w,?_⟩
  intro d hd
  interval_cases d
  · convert ratio (by norm_num) w.1 c.1 using 1 <;> norm_num <;> ring
  · convert ratio (by norm_num) w.2.1 c.2.1 using 1 <;> norm_num <;> ring
  · convert ratio (by norm_num) w.2.2 c.2.2 using 1 <;> norm_num <;> ring

#print axioms original

#print axioms split
end
end Arxiv.«2501.03234».ThetaGapBiasThree
