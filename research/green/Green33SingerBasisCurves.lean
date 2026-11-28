import Green33SingerCurveSupport
/-! Curves in an otherwise arbitrary cyclic basis containing an even Singer line. -/
open Finset Green33PerfectDifferenceCenters Green33SingerBlockingLayers
open Filter
open scoped Pointwise Topology
namespace Green33SingerBasisCurves

private theorem scale_orders (v : ℕ→ℕ+) (q : ℕ→ℕ) (D : ∀ i, Finset (ZMod (v i)))
    (perf : ∀ i, Perfect (D i)) (size : ∀ i,(D i).card=q i+1) (pos : ∀ i,0<q i)
    (grow : Tendsto q atTop atTop) :
    Tendsto (fun i => Real.sqrt ((2*(v i).val:ℕ):ℝ)/(q i:ℝ)) atTop (𝓝 (Real.sqrt 2)) := by
  have tiny:=(tendsto_const_nhds (x:=(1:ℝ))).div_atTop ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have one:=tendsto_const_nhds (f:=atTop (α:=ℕ)) (x:=(1:ℝ))
  have h:=(((one.add tiny).add (tiny.pow 2)).const_mul 2).sqrt
  simp only [add_zero,zero_pow (by decide : 2≠0),mul_one] at h
  apply h.congr
  intro i
  have hp : (0:ℝ)<q i := by exact_mod_cast pos i
  have ord:=parameters (D i) (perf i)
  rw [size i,ZMod.card,Nat.cast_add,Nat.cast_one] at ord
  have vq : ((v i).val:ℝ)=(q i:ℝ)^2+q i+1 := by nlinarith only [ord]
  rw [Nat.cast_mul,Nat.cast_ofNat,←Real.sqrt_sq hp.le,←Real.sqrt_div (by positivity),vq]
  congr 1
  simp only [Function.comp_apply]
  field_simp [hp.ne']

private theorem split_full_mixed {v : ℕ+} (E B : Finset (ZMod v))
    (full : split E B+split E B=univ) : E+B=univ := by
  have cap:=odd_holes E B
  rw [full,compl_univ,card_empty] at cap
  have z:=card_eq_zero.mp (Nat.eq_zero_of_le_zero cap)
  simpa using congrArg (fun S:Finset (ZMod v) => Sᶜ) z

/-- An optimal full basis containing an even planar layer has q+o(q) labels in
each parity class, even when no hypothesis on the opposite support is made. -/
theorem parity_balance {v : ℕ→ℕ+} (D E B : ∀ i, Finset (ZMod (v i))) (q : ℕ→ℕ)
    (perf : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=q i+1) (pos : ∀ i,0<q i)
    (grow : Tendsto q atTop atTop) (full : ∀ i,split (E i) (B i)+split (E i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (E i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => ((E i).card:ℝ)/(q i:ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun i => ((B i).card:ℝ)/(q i:ℝ)) atTop (𝓝 1) := by
  let a (i : ℕ) : ℝ := (E i).card/(q i:ℝ)
  let b (i : ℕ) : ℝ := (B i).card/(q i:ℝ)
  have qp (i) : (0:ℝ)<q i := by exact_mod_cast pos i
  have total : Tendsto (fun i => a i+b i) atTop (𝓝 2) := by
    have h:=critical.mul (scale_orders _ q D perf size pos grow)
    rw [Real.mul_self_sqrt (by norm_num)] at h
    apply h.congr
    intro i
    dsimp only [a,b]
    rw [split_card,Nat.cast_add,←add_div]
    have vp : (0:ℝ)<(v i).val := by exact_mod_cast (v i).property
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity : (0:ℝ)<(2*(v i).val:ℕ))]
  have prod (i) : 1≤a i*b i := by
    have cap:=card_add_le (s:=E i) (t:=B i)
    rw [split_full_mixed _ _ (full i),card_univ,ZMod.card] at cap
    have h : ((v i).val:ℝ)≤(E i).card*((B i).card:ℝ) := by exact_mod_cast cap
    have ord:=parameters (D i) (perf i)
    rw [size i,Nat.cast_add,Nat.cast_one,ZMod.card] at ord
    dsimp only [a,b]
    rw [div_mul_div_comm,le_div_iff₀ (mul_pos (qp i) (qp i))]
    nlinarith only [ord,h,Nat.cast_nonneg (α:=ℝ) (q i)]
  have square:= (total.pow 2).sub_const 4
  norm_num only [Nat.reducePow,show (2:ℝ)^2-4=0 by norm_num] at square
  have diff : Tendsto (fun i => (a i-b i)^2) atTop (𝓝 0) := by
    exact squeeze_zero' (Eventually.of_forall fun i => sq_nonneg _) (Eventually.of_forall fun i =>
      by nlinarith only [prod i]) square
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

#print axioms parity_balance

open Green33SingerCurveChart Green33SingerCurveSupport

private theorem split_mono {v : ℕ+} {A B E T : Finset (ZMod v)} (a : A⊆E) (b : B⊆T) :
    split A B⊆split E T :=
  union_subset_union (image_subset_image a) (image_subset_image b)

/-- The even layer may omit o(q) points of the Singer line, and may contain
arbitrary additional points. A full critical basis has o(q) opposite labels on
each bounded-degree curve, in coordinates allowed to vary with the field. -/
theorem stable_basis_escape {F : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [∀ i, DecidableEq (F i)] {v : ℕ→ℕ+} (D E B : ∀ i,Finset (ZMod (v i)))
    (q : ℕ→ℕ) (A : ∀ i,Chart (F i) (ZMod (v i)) (D i))
    (f : ∀ i,Polynomial (Polynomial (F i))) (d : ℕ) (ne : ∀ i,f i≠0)
    (dx : ∀ i m,((f i).coeff m).natDegree≤d) (dy : ∀ i,(f i).natDegree≤d)
    (perf : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=q i+1) (pos : ∀ i,0<q i)
    (grow : Tendsto q atTop atTop)
    (reflects : ∀ a : ∀ i,ZMod (v i),Tendsto (fun i =>
      ((doubled (D i) (a i)+doubled (D i) (a i)).card:ℝ)/(2*(v i).val)) atTop (𝓝 (7/8)))
    (full : ∀ i,split (E i) (B i)+split (E i) (B i)=univ)
    (critical : Tendsto (fun i => ((split (E i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ))
      atTop (𝓝 (Real.sqrt 2)))
    (retain : Tendsto (fun i => (((D i)\(E i)).card:ℝ)/(q i)) atTop (𝓝 0)) :
    Tendsto (fun i => ((B i∩locus (A i) (f i)).card:ℝ)/(q i)) atTop (𝓝 0) := by
  classical
  obtain ⟨even,odd⟩:=parity_balance D E B q perf size pos grow full critical
  have qp (i) : (0:ℝ)<q i := by exact_mod_cast pos i
  have grow':= (tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have near : Tendsto (fun i => ((q i+1:ℕ):ℝ)/(q i)) atTop (𝓝 1) := by
    have h:=(tendsto_const_nhds (f:=atTop (α:=ℕ)) (x:=(1:ℝ))).add
      ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop grow')
    rw [add_zero] at h
    exact h.congr (fun i => by simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one];field_simp [(qp i).ne'])
  choose U sub cut using fun i => exists_subset_card_eq (s:=B i) (min_le_left (B i).card (q i+1))
  have trimmed : Tendsto (fun i => ((U i).card:ℝ)/(q i)) atTop (𝓝 1) := by
    have h:=odd.min near
    rw [min_self] at h
    exact h.congr (fun i => by rw [cut,Nat.cast_min, min_div_div_right (qp i).le])
  have cardeq {a b c : ℕ} (h : a+b=c) {s : ℝ} :
      (c:ℝ)/s-(a:ℝ)/s=(b:ℝ)/s := by rw [←h,Nat.cast_add,add_div];ring
  have kept : Tendsto (fun i => (((D i)∩(E i)).card:ℝ)/(q i)) atTop (𝓝 1) := by
    have h:=near.sub retain
    rw [sub_zero] at h
    exact h.congr (fun i => by rw [←size];exact cardeq (card_sdiff_add_card_inter _ _))
  have discarded : Tendsto (fun i => (((B i)\(U i)).card:ℝ)/(q i)) atTop (𝓝 0) := by
    have h:=odd.sub trimmed
    rw [sub_self] at h
    exact h.congr (fun i => cardeq ((Nat.add_comm ..).trans (card_sdiff_add_card_eq_card (sub i))))
  let S i:=split (E i) (B i)
  let J i:=split (D i∩E i) (U i)
  let R i:=split (D i) (U i)
  have inside i : J i⊆S i := split_mono inter_subset_right (sub i)
  have inside' i : J i⊆R i := split_mono inter_subset_left Subset.rfl
  have total : Tendsto (fun i => ((S i).card:ℝ)/(q i)) atTop (𝓝 2) := by
    simpa only [S,split_card,Nat.cast_add,add_div,one_add_one_eq_two] using even.add odd
  have common : Tendsto (fun i => ((J i).card:ℝ)/(q i)) atTop (𝓝 2) := by
    simpa only [J,split_card,Nat.cast_add,add_div,one_add_one_eq_two] using kept.add trimmed
  have removed : Tendsto (fun i => (((S i)\(J i)).card:ℝ)/(q i)) atTop (𝓝 0) := by
    have h:=total.sub common
    rw [sub_self] at h
    exact h.congr (fun i => cardeq ((Nat.add_comm ..).trans (card_sdiff_add_card_eq_card (inside i))))
  have holes : Tendsto (fun i => (((R i)+(R i))ᶜ.card:ℝ)/(q i:ℝ)^2) atTop (𝓝 0) := by
    have h:=removed.mul total
    rw [zero_mul] at h
    apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ h
    apply Eventually.of_forall
    intro i
    have cap:=changed_sums (S i) (R i)
    have fs : S i+S i=univ := full i
    rw [fs,compl_univ,card_empty,zero_add] at cap
    have sm : S i\R i⊆S i\J i := sdiff_subset_sdiff Subset.rfl (inside' i)
    have bound:=cap.trans (Nat.mul_le_mul_right _ (card_le_card sm))
    rw [div_mul_div_comm,←sq]
    exact div_le_div_of_nonneg_right (by exact_mod_cast bound) (sq_nonneg _)
  let w : ℕ:=1+d+d
  have low:=(tendsto_const_nhds (x:=(w:ℝ))).div_atTop grow'
  have cost:=holes.const_mul (w:ℝ)
  rw [mul_zero] at cost
  have escape:=curve_escape D U q A f (fun _ => d) (fun _ => d) ne dx dy perf size
    (fun i => (cut i).trans_le (min_le_right ..)) pos grow reflects low
    (cost.congr fun i => by rw [mul_div_assoc])
  have h:=escape.add discarded
  rw [add_zero] at h
  apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ h
  apply Eventually.of_forall
  intro i
  have incl : B i ∩ locus (A i) (f i) ⊆ (U i ∩ locus (A i) (f i)) ∪ (B i\U i) := by
    intro z hz
    by_cases u:z∈U i
    · exact mem_union_left _ (mem_inter.mpr ⟨u,(mem_inter.mp hz).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_inter.mp hz).1,u⟩)
  rw [←add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast (card_le_card incl).trans (card_union_le _ _)) (qp i).le

#print axioms stable_basis_escape

end Green33SingerBasisCurves
