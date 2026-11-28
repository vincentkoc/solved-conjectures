import Green33OddQuotientSlides
import Green33DivisibleOrder

/-! Growing odd quotients of the full cyclic bases in the pinned Green 33 predicate. -/
open Filter Finset Green33StrictReduction
open scoped Pointwise Topology
namespace Green33LayerSlides

noncomputable def cyclicProjection {m n:ℕ+} (divides:m.val∣n.val) : ZMod n→+ZMod m :=
  (ZMod.castHom divides (ZMod m)).toAddMonoidHom

private theorem fixed_witnesses (green:OrdinaryLimit) (m:ℕ+) (odd:Odd m.val) (ε:ℝ) (pos:0<ε) (R:ℕ) :
    ∃ n:ℕ+,R≤n.val ∧ ∃ div:m.val∣n.val,∃ T:Finset (ZMod n), T+T=univ ∧
      |(T.card:ℝ)/Real.sqrt n-Real.sqrt 2|<ε ∧
      |meanCoverage (cyclicProjection div) T-oddCoverage ((m.val-1)/2)|<ε := by
  classical
  have ex (i:ℕ):∃ n:ℕ+,i≤n.val ∧ ∃ div:m.val∣n.val,∃ T:Finset (ZMod n),
      StrictCover T ∧ |(T.card:ℝ)/Real.sqrt n-Real.sqrt 2|<1/((i:ℝ)+1) := by
    obtain ⟨n,big,div,T,basis,close⟩:=frequently_atTop.mp
      (Green33DivisibleOrder.green_iff_divisible_strict.mp green m (1/((i:ℝ)+1)) (by positivity)) (Nat.succPNat i)
    exact ⟨n,(Nat.le_succ i).trans big,div,T,basis,close⟩
  choose n big div T basis close using ex
  have grow:Tendsto (fun i => (n i).val) atTop atTop:=tendsto_atTop_mono big tendsto_id
  have full (i:ℕ):T i+T i=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a,ha,b,hb,_,eq⟩:=basis i x
    exact mem_add.mpr ⟨a,ha,b,hb,eq⟩
  have crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) atTop (𝓝 (Real.sqrt 2)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using squeeze_zero (fun _ => abs_nonneg _) (fun i => (close i).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have avg:=critical_mean_coverage odd n T (fun i => cyclicProjection (div i))
    (fun i => ZMod.castHom_surjective (div i)) grow full crit
  obtain ⟨i,hR,hk,hp⟩:=((grow.eventually (eventually_ge_atTop R)).and
    ((Metric.tendsto_nhds.mp crit ε pos).and (Metric.tendsto_nhds.mp avg ε pos))).exists
  exact ⟨n i,hR,div i,T i,full i,hk,hp⟩

/-- The quotient orders here are exactly 1,3,5,… . Each basis is full
before translation; the second limit averages the physical sumset size
after the layers move independently inside their original residue classes. -/
theorem green_iff_growing_quotient_slides : OrdinaryLimit ↔
    ∃ n:ℕ→ℕ+, ∃ div:∀ i,2*i+1∣(n i).val, ∃ T:∀ i,Finset (ZMod (n i)),
      Tendsto (fun i => (n i).val) atTop atTop ∧ (∀ i,T i+T i=univ) ∧
      Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun i => meanCoverage (cyclicProjection (m:=⟨2*i+1,by omega⟩) (div i)) (T i))
        atTop (𝓝 (1-Real.exp (-1))) := by
  constructor
  · intro green
    let m (i:ℕ):ℕ+:=⟨2*i+1,by omega⟩
    have ex (i:ℕ):=fixed_witnesses green (m i) (show Odd (m i).val from ⟨i,rfl⟩)
      (1/((i:ℝ)+1)) (by positivity) i
    choose n big div T full size avg using ex
    refine ⟨n,div,T,tendsto_atTop_mono big tendsto_id,full,?_,?_⟩
    · apply tendsto_iff_dist_tendsto_zero.mpr
      simpa only [Real.dist_eq] using squeeze_zero (fun _ => abs_nonneg _) (fun i => (size i).le) tendsto_one_div_add_atTop_nhds_zero_nat
    · have id (i:ℕ):((m i).val-1)/2=i:=by change (2*i+1-1)/2=i;omega
      simp_rw [id] at avg
      let f (i:ℕ):=meanCoverage (cyclicProjection (div i)) (T i)
      have err:Tendsto (fun i => f i-oddCoverage i) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simpa only [Real.norm_eq_abs,f] using squeeze_zero (fun _ => abs_nonneg _) (fun i => (avg i).le) tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [sub_add_cancel,zero_add] using err.add oddCoverage_limit
  · rintro ⟨n,_,T,grow,full,size,_⟩ ε hε
    apply frequently_atTop.mpr
    intro R
    obtain ⟨i,big,small⟩:=((grow.eventually (eventually_ge_atTop R.val)).and
      (Metric.tendsto_nhds.mp size ε hε)).exists
    exact ⟨n i,big,T i,full i,small⟩
#print axioms green_iff_growing_quotient_slides
end Green33LayerSlides
