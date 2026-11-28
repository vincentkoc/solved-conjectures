import Green33FullSlideVariance

/-! Concentration of sumset coverage under independent odd quotient translations. -/
open Finset Filter Green33LayerSlides
open scoped Pointwise Topology
namespace Green33SlideConcentration
variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
noncomputable def slideTail {m:ℕ+} (π:H→+ZMod m) (T:Finset H) (x ε:ℝ):ℝ :=
  ((univ.filter fun h:ZMod m→π.ker => ε≤|coverage π T h-x|).card:ℝ)/(Fintype.card π.ker:ℝ)^m.val

/-- A finite bound at any reference value, accounting separately for the
variance and the squared displacement of the mean. -/
theorem tail_bound {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (onto:Function.Surjective π)
    (T:Finset H) (full:T+T=univ) (x ε:ℝ) (ep:0≤ε) :
    slideTail π T x ε*ε^2 ≤ ((positiveHalf m).card:ℝ)*(m:ℝ)*slideCost T.card (Fintype.card H)/Fintype.card H+
      (meanCoverage π T-x)^2 := by
  classical
  let X:=coverage π T
  let μ:=meanCoverage π T
  let d:ℝ:=(Fintype.card π.ker:ℝ)^m.val
  have dp:0<d:=by dsimp [d];positivity
  have howmany:((Fintype.card (ZMod m→π.ker):ℕ):ℝ)=d:=by simp [d,ZMod.card]
  have mean:(∑ h,X h)/d=μ:=by simp only [X,coverage,μ,meanCoverage,d,←sum_div,div_div]
  have sumX:∑ h,X h=μ*d:=(div_eq_iff dp.ne').mp mean
  have shift (y:ℝ) :
      (∑ h,(X h-y)^2)/d=(∑ h,(X h)^2)/d-2*μ*y+y^2 := by
    simp only [sub_sq,sum_add_distrib,sum_sub_distrib,mul_assoc,←sum_mul,←mul_sum,sum_const,card_univ,nsmul_eq_mul,howmany,sumX]
    field_simp [dp.ne']
  have bound:=full_coverage_variance odd π onto T full
  let bad:Finset (ZMod m→π.ker):=univ.filter fun h => ε≤|X h-x|
  have le: (bad.card:ℝ)*ε^2≤∑ h,(X h-x)^2 := by
    calc
      _ = ∑ _h∈bad,ε^2 := by simp
      _ ≤ ∑ h∈bad,(X h-x)^2 := by
        apply sum_le_sum
        intro h hh
        simpa only [sq_abs] using pow_le_pow_left₀ ep (mem_filter.mp hh).2 2
      _ ≤ ∑ h,(X h-x)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros;positivity)
  change (bad.card:ℝ)/d*ε^2≤_+(μ-x)^2
  rw [div_mul_eq_mul_div]
  apply (div_le_div_of_nonneg_right le dp.le).trans
  have v:(∑ h,(X h-μ)^2)/d≤_:=bound
  rw [shift] at v ⊢
  linarith

variable {ι:Type*} {l:Filter ι}
theorem cost_limit (n:ι→ℕ+) (k:ι→ℕ) (grow:Tendsto (fun i => (n i).val) l atTop)
    (crit:Tendsto (fun i => (k i:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => slideCost (k i) (n i).val/(n i:ℝ)) l (𝓝 0) := by
  have lin:=(Green33TailEnergy.card_limits n k grow crit).1
  have slots:=choose_limit n k grow crit
  norm_num at slots
  have lim:=lin.add ((slots.sub_const 1).const_mul 3)
  simp only [sub_self,mul_zero,add_zero] at lim
  apply lim.congr
  intro i
  have p:(n i:ℝ)≠0:=by exact_mod_cast (n i).pos.ne'
  dsimp only [slideCost]
  field_simp

/-- Typical slides of every full critical basis have the fixed odd-quotient
coverage predicted by the first moment. -/
theorem fixed_quotient_concentration {m:ℕ+} (odd:Odd m.val) (n:ι→ℕ+) (T:∀ i,Finset (ZMod (n i)))
    (π:∀ i,ZMod (n i)→+ZMod m) (onto:∀ i,Function.Surjective (π i))
    (grow:Tendsto (fun i => (n i).val) l atTop) (full:∀ i,T i+T i=univ)
    (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2)))
    (ε:ℝ) (eps:0<ε) :
    Tendsto (fun i => slideTail (π i) (T i) (oddCoverage ((m.val-1)/2)) ε) l (𝓝 0) := by
  let c:=oddCoverage ((m.val-1)/2)
  let a:ℝ:=((positiveHalf m).card:ℝ)*(m:ℝ)
  have cost:=cost_limit n _ grow crit
  have avg:=critical_mean_coverage odd n T π onto grow full crit
  have tiny:=((cost.const_mul a).add ((avg.sub_const c).pow 2)).div_const (ε^2)
  simp only [mul_zero,show oddCoverage ((m.val-1)/2)=c from rfl,sub_self,zero_pow (by decide : 2≠0),add_zero,zero_div] at tiny
  apply squeeze_zero (fun i => by unfold slideTail;positivity) _ tiny
  intro i
  apply (le_div_iff₀ (sq_pos_of_pos eps)).mpr
  have b:=tail_bound odd (π i) (onto i) (T i) (full i) c ε eps.le
  rw [ZMod.card] at b
  simpa only [a,mul_div_assoc] using b
#print axioms tail_bound
#print axioms cost_limit
#print axioms fixed_quotient_concentration
/-- At any fixed odd index at least three, the fraction of independent
residue-class shifts that preserve full coverage tends to zero. -/
theorem surviving_full_slides {m:ℕ+} (odd:Odd m.val) (three:3 ≤ m.val) (n:ι→ℕ+)
    (T:∀ i,Finset (ZMod (n i))) (π:∀ i,ZMod (n i)→+ZMod m)
    (onto:∀ i,Function.Surjective (π i)) (grow:Tendsto (fun i => (n i).val) l atTop)
    (full:∀ i,T i+T i=univ) (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => ((univ.filter fun h:ZMod m→(π i).ker =>
      displaced (π i) (T i) h+displaced (π i) (T i) h=univ).card:ℝ)/(Fintype.card (π i).ker:ℝ)^m.val)
      l (𝓝 0) := by
  let r:=(m.val-1)/2
  have rp:1 ≤ r:=by dsimp [r];omega
  let p:=oddCoverage r
  have denom:2<(2*(r:ℝ)+1):=by
    have h:(1:ℝ) ≤ (r:ℝ):=by exact_mod_cast rp
    linarith
  have ep:0<1-p:=by
    change 0<1-(1-(1-1/(2*(r:ℝ)+1))*(1-2/(2*(r:ℝ)+1))^r)
    rw [sub_sub_cancel]
    apply mul_pos
    · apply sub_pos.mpr;apply (div_lt_one (by positivity)).mpr;linarith
    · apply pow_pos;apply sub_pos.mpr;exact (div_lt_one (by positivity)).mpr denom
  have tail:=fixed_quotient_concentration odd n T π onto grow full crit _ ep
  apply squeeze_zero (fun i => by positivity) _ tail
  intro i
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro h hit
  have cover:= (mem_filter.mp hit).2
  apply mem_filter.mpr ⟨mem_univ _,?_⟩
  have eq:coverage (π i) (T i) h=1:=by
    simp only [coverage,cover,card_univ]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)
  exact le_trans (by rw [eq]) (le_abs_self _)
#print axioms surviving_full_slides

end Green33SlideConcentration
