import Green33ParitySlideCoordinates
open Finset Filter Green33SingerBlockingLayers Green33ParityConvolution Green33TailEnergy
open scoped Pointwise Topology
namespace Green33ParitySlides

/-- Criticality balances the two parities for arbitrary bases of even order. -/
theorem balance {v : ℕ→ℕ+} (A B : ∀ i, Finset (ZMod (v i)))
    (full : ∀ i, split (A i) (B i)+split (A i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1) ∧
    Tendsto (fun i => ((B i).card:ℝ)/Real.sqrt (v i).val) atTop (𝓝 1) := by
  let a i := ((A i).card:ℝ)/Real.sqrt (v i).val
  let b i := ((B i).card:ℝ)/Real.sqrt (v i).val
  have vp (i) : (0:ℝ)<(v i).val := by exact_mod_cast (v i).property
  have total : Tendsto (fun i => a i+b i) atTop (𝓝 2) := by
    have h:=critical.mul_const (Real.sqrt 2)
    rw [Real.mul_self_sqrt (by norm_num)] at h
    apply h.congr
    intro i
    simp only [a,b,split_card,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    field_simp [(Real.sqrt_pos.mpr (vp i)).ne',Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)]
  have prod (i) : 1≤a i*b i := by
    have h:=card_add_le (s:=A i) (t:=B i)
    rw [(full_layers _ _ (full i)).1,card_univ,ZMod.card] at h
    change 1≤(_/_)*(_/_)
    rw [div_mul_div_comm,Real.mul_self_sqrt (vp i).le,le_div_iff₀ (vp i),one_mul]
    exact_mod_cast h
  have square:= (total.pow 2).sub_const 4
  norm_num only [Nat.reducePow,show (2:ℝ)^2-4=0 by norm_num] at square
  have diff : Tendsto (fun i => (a i-b i)^2) atTop (𝓝 0) :=
    squeeze_zero (fun i => sq_nonneg _) (fun i => by nlinarith only [prod i]) square
  have ab : Tendsto (fun i => a i-b i) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs,Real.sqrt_sq_eq_abs,Real.sqrt_zero] using diff.sqrt
  constructor
  · have h:=(total.add ab).div_const 2
    norm_num at h
    exact h
  · have h:=(total.sub ab).div_const 2
    norm_num at h
    exact h

private def scaledCost (aa bb ab u a b : ℝ) : ℝ :=
  (aa-2*u+2*a)*(2*u+aa) + (aa+bb-2+2*(a+b))*aa +
    (ab-1)*(ab+1) + |2*aa-2|

private theorem scale_cost (a b u n : ℝ) (hn : 0<n) :
    slideCost a b u n/n^2 = scaledCost (a^2/n) (b^2/n) (a*b/n) (u/n) (a/n) (b/n) := by
  unfold scaledCost slideCost
  rw [show 2*(a^2/n)-2=(2*a^2-2*n)/n by field_simp,abs_div,abs_of_pos hn]
  field_simp

/-- The two even-sum supports have half density and vanishing overlap, and
the normalized finite deviation bound tends to zero. -/
theorem critical_support {v : ℕ→ℕ+} (A B : ∀ i, Finset (ZMod (v i)))
    (grow : Tendsto (fun i => (v i).val) atTop atTop)
    (full : ∀ i, split (A i) (B i)+split (A i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2))) :
    let n i : ℝ := (v i).val
    let U i := A i+A i
    let W i := ({1}:Finset (ZMod (v i)))+(B i+B i)
    Tendsto (fun i => ((U i).card:ℝ)/n i) atTop (𝓝 (1/2)) ∧
    Tendsto (fun i => ((U i∩W i).card:ℝ)/n i) atTop (𝓝 0) ∧
    Tendsto (fun i => slideCost (A i).card (B i).card (U i).card (n i)/(n i)^2) atTop (𝓝 0) := by
  intro n U W
  let a (i:ℕ) : ℝ := (A i).card
  let b (i:ℕ) : ℝ := (B i).card
  have pos (i) : 0<n i := by dsimp only [n];exact_mod_cast (v i).property
  have top : Tendsto n atTop atTop := tendsto_natCast_atTop_atTop.comp grow
  obtain ⟨ha,hb⟩:=balance A B full critical
  change Tendsto (fun i => a i/Real.sqrt (n i)) _ _ at ha
  change Tendsto (fun i => b i/Real.sqrt (n i)) _ _ at hb
  have scale (x:ℕ→ℝ) (h:Tendsto (fun i => x i/Real.sqrt (n i)) atTop (𝓝 1)) :
      Tendsto (fun i => x i^2/n i) atTop (𝓝 1) ∧ Tendsto (fun i => x i/n i) atTop (𝓝 0) := by
    constructor
    · simpa only [div_pow,Real.sq_sqrt (pos _).le,one_pow] using h.pow 2
    · have small:=h.div_atTop (Real.tendsto_sqrt_atTop.comp top)
      simpa only [Function.comp_apply,div_div,Real.mul_self_sqrt (pos _).le] using small
  obtain ⟨aa,atiny⟩:=scale a ha
  obtain ⟨bb,btiny⟩:=scale b hb
  have ab : Tendsto (fun i => a i*b i/n i) atTop (𝓝 1) := by
    simpa only [div_mul_div_comm,Real.mul_self_sqrt (pos _).le,one_mul] using ha.mul hb
  let u (i:ℕ) := ((U i).card:ℝ)/n i
  let w (i:ℕ) := ((W i).card:ℝ)/n i
  let halfA (i:ℕ) := (a i^2/n i+a i/n i)/2
  let halfB (i:ℕ) := (b i^2/n i+b i/n i)/2
  have upp (i:ℕ) : u i ≤ halfA i ∧ w i ≤ halfB i := by
    have p:=Green33SidonLayerRepairs.sum_upper (A i)
    have r:=Green33SidonLayerRepairs.sum_upper (B i)
    have p' : 2*((U i).card:ℝ) ≤ a i^2+a i := by dsimp only [U,a];exact_mod_cast p
    have r' : 2*((W i).card:ℝ) ≤ b i^2+b i := by
      dsimp only [W,b];rw [card_singleton_add];exact_mod_cast r
    constructor <;> dsimp only [u,w,halfA,halfB] <;>
      rw [le_div_iff₀ (by norm_num),←add_div,div_mul_eq_mul_div,div_le_div_iff_of_pos_right (pos i)] <;> linarith
  have joints (i:ℕ) :
      1 + ((U i∩W i).card:ℝ)/n i = u i+w i := by
    have h:=card_union_add_card_inter (U i) (W i)
    rw [(full_layers _ _ (full i)).2,card_univ,ZMod.card] at h
    dsimp only [u,w]
    rw [←add_div,←div_self (pos i).ne',←add_div,div_left_inj' (pos i).ne']
    dsimp only [n];exact_mod_cast h
  have total (i:ℕ) : 1≤u i+w i := by
    have h:=div_nonneg (Nat.cast_nonneg (α:=ℝ) (U i∩W i).card) (pos i).le
    linarith only [h,joints i]
  have hA:Tendsto halfA atTop (𝓝 (1/2)) := by simpa [halfA] using (aa.add atiny).div_const 2
  have hB:Tendsto halfB atTop (𝓝 (1/2)) := by simpa [halfB] using (bb.add btiny).div_const 2
  have us:Tendsto u atTop (𝓝 (1/2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le _ hA (fun i => sub_le_iff_le_add.mpr ((total i).trans (add_le_add le_rfl (upp i).2))) (fun i => (upp i).1)
    convert hB.const_sub 1 using 1; norm_num
  have both : Tendsto (fun i => ((U i∩W i).card:ℝ)/n i) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (pos i).le)
      (fun i => show _ ≤ halfA i + halfB i - 1 by linarith only [joints i,(upp i).1,(upp i).2])
    convert (hA.add hB).sub_const 1 using 1; norm_num
  refine ⟨us,both,?_⟩
  simp_rw [scale_cost _ _ _ _ (pos _)]
  change Tendsto (fun i => scaledCost (a i^2/n i) (b i^2/n i) (a i*b i/n i) (u i) (a i/n i) (b i/n i)) _ _
  have c : Continuous (fun p : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ =>
    scaledCost p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by unfold scaledCost;fun_prop
  have h:=c.continuousAt.tendsto.comp (aa.prodMk_nhds (bb.prodMk_nhds (ab.prodMk_nhds (us.prodMk_nhds (atiny.prodMk_nhds btiny)))))
  norm_num only [Prod.fst,Prod.snd,show scaledCost 1 1 1 (1/2) 0 0=0 by norm_num [scaledCost]] at h
  exact h


private noncomputable def corrBad {v : ℕ+} (U : Finset (ZMod v)) (ε:ℝ) : Finset (ZMod v) := by
  classical
  exact univ.filter fun z => ε ≤ |(diffReps U z:ℝ)/(v.val:ℝ)-1/4|

private theorem corrBad_bound {v : ℕ+} (A B : Finset (ZMod v)) (ε:ℝ) (hp:0<ε)
    (full : split A B+split A B=univ) :
    ((corrBad (A+A) ε).card:ℝ)/v.val ≤ (3/(16*ε^2))*
      (slideCost A.card B.card (A+A).card v.val/(v.val:ℝ)^2) := by
  classical
  let U := A+A
  let n : ℝ := v.val
  let T := corrBad U ε
  have hn : 0<n := by dsimp [n];exact_mod_cast v.property
  obtain ⟨mixed,even⟩:=full_layers A B full
  have cover (g : ZMod v) : g∈A+A ∨ -(1:ZMod v)+g∈B+B := by
    have h : g∈(A+A)∪({1}+(B+B)) := even ▸ mem_univ _
    rcases mem_union.mp h with h|h
    · exact Or.inl h
    · obtain ⟨a,ha,b,hb,eq⟩:=mem_add.mp h
      obtain rfl : a=1 := mem_singleton.mp ha
      exact Or.inr (by simpa [←eq] using hb)
  have s:=support_deviation A B 1 mixed cover
  have d:=overlap_error U
  rw [ZMod.card] at s d
  have lo (g : ZMod v) (hg:g∈T) :
      (ε*n)^2 ≤ ((diffReps U g:ℝ)-n/4)^2 := by
    have h : ε≤|(diffReps U g:ℝ)/n-1/4| := (mem_filter.mp hg).2
    have eq : (diffReps U g:ℝ)/n-1/4=((diffReps U g:ℝ)-n/4)/n := by field_simp
    rw [eq,abs_div,abs_of_pos hn,le_div_iff₀ hn] at h
    simpa only [sq_abs] using pow_le_pow_left₀ (mul_nonneg hp.le hn.le) h 2
  have small:=sum_le_sum (s:=T) fun g hg => lo g hg
  rw [sum_const,nsmul_eq_mul] at small
  have big:=sum_le_sum_of_subset_of_nonneg (subset_univ T)
    (fun g _ _ => sq_nonneg ((diffReps U g:ℝ)-n/4))
  have h : (T.card:ℝ)*(ε*n)^2 ≤ (3*n/16)*slideCost A.card B.card U.card n := by
    apply (small.trans big).trans
    apply d.trans
    change 3*n/4 * _ ≤ _
    have bound:=mul_le_mul_of_nonneg_left s (show 0≤3*n/16 by positivity)
    dsimp only [U,n] at *
    linarith only [bound]
  change (T.card:ℝ)/n ≤ (3/(16*ε^2))*(slideCost A.card B.card U.card n/n^2)
  rw [div_mul_div_comm,div_le_div_iff₀ hn (by positivity)]
  linarith only [h]

/-- The fraction of odd-layer slides whose coverage differs from 7/8 by
at least the indicated tolerance. The denominator counts all v slides. -/
noncomputable def exceptionalFraction {v : ℕ+} (A B : Finset (ZMod v)) (ε:ℝ) : ℝ := by
  classical
  exact ((univ.filter fun h : ZMod v =>
    ε ≤ |(((slide A B h+slide A B h).card:ℝ)/(2*v.val))-7/8|).card:ℝ)/v.val

/-- For every sequence of full, asymptotically optimal bases of cyclic
groups of even order tending to infinity, almost every odd-layer slide
covers a fraction tending to seven eighths of the entire double. -/
theorem seven_eighths {v : ℕ→ℕ+} (A B : ∀ i, Finset (ZMod (v i)))
    (grow : Tendsto (fun i => (v i).val) atTop atTop)
    (full : ∀ i, split (A i) (B i)+split (A i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (A i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2))) (ε:ℝ) (hp : 0<ε) :
    Tendsto (fun i => exceptionalFraction (A i) (B i) ε) atTop (𝓝 0) := by
  classical
  let n (i:ℕ) : ℝ := (v i).val
  let U i := A i+A i
  let W i := ({1}:Finset (ZMod (v i)))+(B i+B i)
  have hn (i) : 0<n i := by dsimp [n];exact_mod_cast (v i).property
  obtain ⟨us,overlap,cost⟩ := critical_support A B grow full critical
  change Tendsto (fun i => ((U i).card:ℝ)/n i) _ _ at us
  change Tendsto (fun i => ((U i∩W i).card:ℝ)/n i) _ _ at overlap
  have slack : ∀ᶠ i in atTop, |((U i).card:ℝ)/n i-1/2|+((U i∩W i).card:ℝ)/n i < ε := by
    have h:=((us.sub_const (1/2)).abs).add overlap
    apply h.eventually_lt_const
    simpa using hp
  have high:=cost.const_mul (2*(3/(16*ε^2)))
  rw [mul_zero] at high
  apply squeeze_zero' (Eventually.of_forall fun i => by unfold exceptionalFraction;positivity) _ high
  filter_upwards [slack] with i hi
  let T := corrBad (U i) ε
  let X := univ.filter fun h : ZMod (v i) =>
    ε ≤ |((slide (A i) (B i) h+slide (A i) (B i) h).card:ℝ)/(2*n i)-7/8|
  have sub : X ⊆ univ.filter fun h : ZMod (v i) => h+h∈T := by
    intro h hh
    have bad:= (mem_filter.mp hh).2
    apply mem_filter.mpr
    refine ⟨mem_univ _, mem_filter.mpr ⟨mem_univ _,?_⟩⟩
    change ε ≤ |(diffReps (U i) (h+h):ℝ)/n i-1/4|
    obtain ⟨low,upp⟩:=slide_card (A i) (B i) h (full i)
    let S:=slide (A i) (B i) h
    have l : 2*n i+(diffReps (U i) (h+h):ℝ)≤(S+S).card+((U i).card:ℝ) := by
      dsimp only [n,U,S];exact_mod_cast low
    have u : (S+S).card+((U i).card:ℝ) ≤
        2*n i+(diffReps (U i) (h+h):ℝ)+(U i∩W i).card := by
      dsimp only [n,U,W,S];exact_mod_cast upp
    have l' := (div_le_div_iff_of_pos_right (hn i)).mpr l
    have u' := (div_le_div_iff_of_pos_right (hn i)).mpr u
    simp only [add_div,mul_div_cancel_right₀ _ (hn i).ne'] at l' u'
    change ε ≤ |((S+S).card:ℝ)/(2*n i)-7/8| at bad
    rw [mul_comm (2:ℝ),←div_div] at bad
    rw [le_abs] at bad
    have slack₁:=le_abs_self (((U i).card:ℝ)/n i-1/2)
    have slack₂:=neg_abs_le (((U i).card:ℝ)/n i-1/2)
    have nn:=div_nonneg (Nat.cast_nonneg (α:=ℝ) (U i∩W i).card) (hn i).le
    have right:=le_abs_self ((diffReps (U i) (h+h):ℝ)/n i-1/4)
    have left:=neg_abs_le ((diffReps (U i) (h+h):ℝ)/n i-1/4)
    rcases bad with bad|bad <;> linarith
  have count:= (card_le_card sub).trans (double_bad T)
  have c : (X.card:ℝ)≤2*T.card := by exact_mod_cast count
  have cb:=corrBad_bound (A i) (B i) ε hp (full i)
  change ((X.card:ℝ)/n i) ≤ _
  calc
    _ ≤ 2*((T.card:ℝ)/n i) := by rw [←mul_div_assoc];exact div_le_div_of_nonneg_right c (hn i).le
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left cb (by norm_num)
#print axioms critical_support
#print axioms balance
#print axioms seven_eighths

end Green33ParitySlides
