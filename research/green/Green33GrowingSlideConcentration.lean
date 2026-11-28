import Green33SlideProbability
import Green33GrowingQuotientSlides

/-! Concentration of sumset coverage under independent odd quotient translations. -/
open Finset Filter Green33LayerSlides
open scoped Pointwise Topology
namespace Green33SlideConcentration
variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
open Green33StrictReduction
private theorem select_witness (green:OrdinaryLimit) (r:ℕ) (ε:ℝ) (eps:0<ε) (R:ℕ) :
    let m:ℕ+:=⟨2*r+1,by omega⟩
    ∃ n:ℕ+,R≤n.val ∧ ∃ div:m.val∣n.val,∃ T:Finset (ZMod n),T+T=univ ∧
      |(T.card:ℝ)/Real.sqrt n-Real.sqrt 2|<ε ∧ slideTail (cyclicProjection div) T (oddCoverage r) ε<ε := by
  classical
  intro m
  obtain ⟨N,div,T,grow,full,crit,_⟩:=green_iff_growing_quotient_slides.mp green
  let u (j:ℕ):=r+(2*r+1)*j
  have ge (j:ℕ):j≤u j:=by dsimp [u];nlinarith
  have big:Tendsto u atTop atTop:=tendsto_atTop_mono ge tendsto_id
  have divides (j:ℕ):m.val∣(N (u j)).val:=
    dvd_trans (show 2*r+1∣2*(u j)+1 from ⟨2*j+1,by dsimp [u];ring⟩) (div (u j))
  have law:=fixed_quotient_concentration (m:=m) (show Odd m.val from ⟨r,rfl⟩) (fun j=>N (u j)) (fun j=>T (u j))
    (fun j=>cyclicProjection (divides j)) (fun j=>ZMod.castHom_surjective (divides j))
    (grow.comp big) (fun j=>full (u j)) (crit.comp big) ε eps
  have id:(m.val-1)/2=r:=by dsimp [m];omega
  rw [id] at law
  obtain ⟨j,hR,hs,hp⟩:=(((grow.comp big).eventually (eventually_ge_atTop R)).and
    ((Metric.tendsto_nhds.mp (crit.comp big) ε eps).and (law.eventually_lt_const eps))).exists
  exact ⟨N (u j),hR,divides j,T (u j),full _,hs,hp⟩

/-- On selected full witnesses with quotient indices 1,3,5,… the covered
fraction converges in probability to 1−exp(−1). -/
theorem green_iff_growing_slide_concentration : OrdinaryLimit ↔
    ∃ n:ℕ→ℕ+, ∃ div:∀ i,2*i+1∣(n i).val, ∃ T:∀ i,Finset (ZMod (n i)),
      Tendsto (fun i => (n i).val) atTop atTop ∧ (∀ i,T i+T i=univ) ∧
      Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) atTop (𝓝 (Real.sqrt 2)) ∧
      ∀ ε:ℝ,0<ε → Tendsto (fun i => slideTail (cyclicProjection (m:=⟨2*i+1,by omega⟩) (div i))
        (T i) (1-Real.exp (-1)) ε) atTop (𝓝 0) := by
  constructor
  · intro green
    let δ (i:ℕ):ℝ:=1/((i:ℝ)+1)
    have ex (i:ℕ):=select_witness green i (δ i) (by unfold δ;positivity) i
    choose n big div T full size score using ex
    refine ⟨n,div,T,tendsto_atTop_mono big tendsto_id,full,?_,?_⟩
    · apply tendsto_iff_dist_tendsto_zero.mpr
      simpa only [Real.dist_eq] using squeeze_zero (fun _=>abs_nonneg _) (fun i=>(size i).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    · intro ε ep
      let x:=1-Real.exp (-1)
      have close:Tendsto (fun i => |oddCoverage i-x|) atTop (𝓝 0):=by
        simpa only [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.mp oddCoverage_limit
      have small:Tendsto δ atTop (𝓝 0):=tendsto_one_div_add_atTop_nhds_zero_nat
      have gap:∀ᶠ i in atTop,δ i+|oddCoverage i-x|<ε:=(small.add close).eventually_lt_const (by simpa using ep)
      apply squeeze_zero' (Eventually.of_forall fun i => by unfold slideTail;positivity) _ small
      filter_upwards [gap] with i hi
      apply le_trans _ (score i).le
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Nat.cast_le.mpr
      apply card_le_card
      intro h bad
      refine mem_filter.mpr ⟨(mem_filter.mp bad).1,?_⟩
      set y:=coverage (cyclicProjection (m:=⟨2*i+1,by omega⟩) (div i)) (T i) h
      have old:ε≤|y-x|:=(mem_filter.mp bad).2
      have triangle:|y-x|≤|y-oddCoverage i|+|oddCoverage i-x|:=abs_sub_le y _ x
      change δ i≤|y-oddCoverage i|
      linarith
  · rintro ⟨n,_,T,grow,full,size,_⟩ ε hε
    apply frequently_atTop.mpr
    intro R
    obtain ⟨i,big,small⟩:=((grow.eventually (eventually_ge_atTop R.val)).and
      (Metric.tendsto_nhds.mp size ε hε)).exists
    exact ⟨n i,big,T i,full i,small⟩
#print axioms green_iff_growing_slide_concentration

end Green33SlideConcentration
