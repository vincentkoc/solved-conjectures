import ThetaFrequentSignedGaps

/-! Counting the compatible even gaps gives the exact mean-per-eligible-gap
threshold for the positive-proportion argument. -/
namespace Arxiv.«2501.03234».ThetaCompatibleSignedGaps
open Filter Finset Real ThetaGapFibres ThetaFrequentSignedGaps ThetaSignedGapEnergy
open ThetaLocalPrimeCounts ThetaShortPrimeInterval ThetaPopularLagCounts
noncomputable section

def compatible (d H : ℕ) := (shifts d H).filter Even

theorem cap (d H : ℕ) : (compatible d H).card≤H/6+1 := by
  calc
    _ ≤ (range (H/6+1)).card := by
      apply card_le_card_of_injOn (fun h : ℕ => h/6)
      · intro h hh
        have hle := (mem_Icc.mp (mem_filter.mp (mem_filter.mp hh).1).1).2
        exact mem_range.mpr (by change h/6<H/6+1;omega)
      · intro h hh k hk he
        obtain ⟨h₁,h₂⟩ := mem_filter.mp hh
        obtain ⟨k₁,k₂⟩ := mem_filter.mp hk
        have hm := (mem_filter.mp h₁).2
        have km := (mem_filter.mp k₁).2
        change h%3=d at hm;change k%3=d at km
        rw [Nat.even_iff] at h₂ k₂
        change h/6=k/6 at he
        omega
    _ = _ := card_range _

theorem empty_of_odd {X H h : ℕ} (hX : 2≤X) (he : ¬Even h) : fibre X H h=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨h₁,hgap⟩ := mem_filter.mp hz
  obtain ⟨hp,hl⟩ := mem_sigma.mp h₁
  simp only [sample,mem_primes,mem_Ioc,and_true] at hp hl
  have ha := Nat.odd_iff.mp (hp.2.odd_of_ne_two (by have := hp.1.1;omega))
  have hb := Nat.odd_iff.mp (hl.2.odd_of_ne_two (by have := hp.1.1;have := hl.1.1;omega))
  apply he
  exact Nat.even_iff.mpr (by have := hl.1.1;omega)

theorem all_sum {X : ℕ} (hX : 2≤X) (d H : ℕ) :
    (∑ h∈compatible d H,oriented d X H h)=∑ h∈shifts d H,oriented d X H h := by
  apply sum_subset (filter_subset ..)
  intro h hh he
  have hn : ¬Even h := fun ha => he (mem_filter.mpr ⟨hh,ha⟩)
  simp [oriented,score,ThetaGapFibres.value,empty_of_odd (H:=H) hX hn]

/-- A subthreshold population has density at most one sixth among all shifts.
A surplus in its signed first moment and an upper second moment force many
individual displacements to exceed the requested level. -/
theorem select_at {X H d : ℕ} (hX : 2≤X) (hH : 0<H) {g b s D : ℝ} (hb : 0≤b) (hs : 0<s) (hD : 0<D)
    (hg : b/6+2*s≤g) (hlarge : b≤ s*H)
    (hmean : g*H≤∑ h∈shifts d H,oriented d X H h)
    (henergy : (∑ h∈shifts d H,(oriented d X H h)^2)≤D*H) :
    s^2/(4*(2*D+2*b^2))*H≤(((compatible d H).filter (fun h => b≤oriented d X H h)).card:ℝ) := by
  let I := compatible d H
  let f := oriented d X H
  have hi : I.card≤H := (card_le_card (filter_subset ..)).trans ThetaGapFibres.size
  have hc' := cap d H
  have hc : (I.card:ℝ)≤(H:ℝ)/6+1 := by
    have hc₁ : (I.card:ℝ)≤(H/6:ℕ)+1 := by exact_mod_cast hc'
    have hc₂ : 6*(H/6)≤H := by omega
    have hc₃ : 6*((H/6:ℕ):ℝ)≤H := by exact_mod_cast hc₂
    linarith
  rw [←all_sum hX] at hmean
  have hr := mul_le_mul_of_nonneg_right hc hb
  have hm : s*H≤∑ l∈I,(f l-b) := by
    rw [sum_sub_distrib,sum_const,nsmul_eq_mul]
    change g*(H:ℝ)≤∑ l∈I,f l at hmean
    nlinarith only [hmean,hr,hlarge,mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg H)]
  have hE := (sum_le_sum_of_subset_of_nonneg (show I⊆shifts d H from filter_subset ..) (fun l _ _ => sq_nonneg (f l))).trans henergy
  have hs₂ := sum_le_sum (s:=I) (fun l _ => (show (f l-b)^2≤2*(f l)^2+2*b^2 by nlinarith only [sq_nonneg (f l+b)]))
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul] at hs₂
  have hcap : (I.card:ℝ)≤H := by exact_mod_cast hi
  have hn : (∑ l∈I,(f l-b)^2)≤(2*D+2*b^2)*H := by
    nlinarith only [hs₂,hE,mul_le_mul_of_nonneg_right hcap (sq_nonneg b)]
  have hh := select hH hi (fun l => f l-b) hs (by positivity) hm hn
  apply hh.trans
  exact_mod_cast card_le_card (show I.filter (fun l => s/2≤f l-b)⊆I.filter (fun l => b≤f l) by
    intro l hl;obtain ⟨h₀,h₁⟩ := mem_filter.mp hl;exact mem_filter.mpr ⟨h₀,by linarith⟩)

#print axioms select_at
end
end Arxiv.«2501.03234».ThetaCompatibleSignedGaps
