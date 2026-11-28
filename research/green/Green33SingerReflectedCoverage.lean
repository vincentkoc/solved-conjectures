import Green33SingerProjectiveOverlap
import Green33PerfectDifferenceCenters

/-! The intersection of a Singer line with a nontrivial multiplicative translate. -/

open Green33SingerCoordinates Green33SingerProjectiveOverlap
open scoped Pointwise

namespace Green33SingerReflectedCoverage

variable {F K : Type*} [Field F] [CharP F 2] [Field K] [Algebra F K]

def OnLine (C : CubicFrame F K) (w : K) : Prop := ∃ a b : F, value C.theta (a,b,0)=w

omit [CharP F 2] in
private theorem line_coeff (C : CubicFrame F K) (v : Coords F) :
    OnLine C (value C.theta v) ↔ v.2.2=0 := by
  obtain ⟨a,b,c⟩ := v
  constructor
  · rintro ⟨x,y,eq⟩
    exact (congrArg (fun z : Coords F => z.2.2) (C.basis.injective eq)).symm
  · intro h
    exact ⟨a,b,by simp only at h;rw [h]⟩

omit [CharP F 2] in
private theorem line_scale (C : CubicFrame F K) (k : F) {w : K} (h : OnLine C w) :
    OnLine C (algebraMap F K k*w) := by
  obtain ⟨a,b,rfl⟩ := h
  exact ⟨k*a,k*b,by simp only [value,map_mul,map_zero,zero_mul,add_zero];ring⟩

omit [CharP F 2] in
theorem mem_seed (C : CubicFrame F K) (x : Kˣ) :
    QuotientGroup.mk' (scalars F K) x∈seed C ↔ OnLine C (x:K) := by
  constructor
  · rintro ⟨u,hu,eq⟩
    obtain ⟨s,hs⟩ := QuotientGroup.eq_iff_div_mem.mp eq.symm
    have t := congrArg (fun z : Kˣ => (z:K)) hs
    rw [Units.val_div_eq_div_val] at t
    exact (eq_div_iff u.ne_zero).mp t ▸ line_scale C (s:F) hu
  · intro h
    exact ⟨x,h,rfl⟩

/-- For a nonscalar element i+jθ+kθ², the unique direction of its line
intersection has coordinates (j,k). -/
theorem denominator_direction (C : CubicFrame F K) (i j k a b : F) (nz : j≠0 ∨ k≠0) :
    OnLine C (value C.theta (i,j,k)*value C.theta (a,b,0)) ↔
      ∃ s : F, a=s*j ∧ b=s*k := by
  rw [← value_product C,line_coeff]
  simp only [product,mul_zero,zero_add,add_zero]
  constructor
  · intro eq
    rcases nz with hj | hk
    · refine ⟨a/j,by field_simp,?_⟩
      field_simp
      linear_combination eq - (CharTwo.add_self_eq_zero (k*a))
    · refine ⟨b/k,?_,by field_simp⟩
      field_simp
      linear_combination eq - (CharTwo.add_self_eq_zero (j*b))
  · rintro ⟨s,rfl,rfl⟩
    ring_nf
    reduce_mod_char!

omit [CharP F 2] in
private theorem mk_scalar (x y : Kˣ) {r : F} (eq : (x:K)=algebraMap F K r*(y:K)) :
    QuotientGroup.mk' (scalars F K) x=QuotientGroup.mk' (scalars F K) y := by
  have rn : r≠0 := by
    intro h
    simp [h] at eq
  apply QuotientGroup.eq_iff_div_mem.mpr
  refine ⟨Units.mk0 r rn,Units.ext ?_⟩
  rw [Units.val_div_eq_div_val]
  exact (eq_div_iff y.ne_zero).mpr eq.symm

/-- Each nonidentity projective multiplier sends exactly one point of the
Singer line back into the line. -/
theorem unique_direction (C : CubicFrame F K) (w : Plane F K) (hw : w≠1) :
    ∃! z : Plane F K, z∈seed C ∧ w*z∈seed C := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (scalars F K) w
  obtain ⟨⟨i,j,k⟩,hu⟩ := C.basis.surjective (u:K)
  have nz : j≠0 ∨ k≠0 := by
    by_contra! h
    obtain ⟨rfl,rfl⟩ := h
    apply hw
    rw [← map_one (QuotientGroup.mk' (scalars F K))]
    apply mk_scalar (r:=i)
    simpa [value] using hu.symm
  have yn : value C.theta (j,k,0)≠0 := by
    intro eq
    have eq' : value C.theta (j,k,0)=value (F:=F) C.theta (0,0,0) := by simpa [value] using eq
    have all := C.basis.injective eq'
    rcases nz with h|h
    · exact h (congrArg Prod.fst all)
    · exact h (congrArg (fun x : Coords F => x.2.1) all)
  let v := Units.mk0 _ yn
  refine ⟨QuotientGroup.mk' (scalars F K) v,⟨(mem_seed C v).mpr ⟨j,k,rfl⟩,?_⟩,?_⟩
  · rw [← map_mul (QuotientGroup.mk' (scalars F K)),mem_seed]
    change OnLine C ((u:K)*value C.theta (j,k,0))
    rw [← hu,denominator_direction C i j k j k nz]
    exact ⟨1,by simp,by simp⟩
  · intro z ⟨hz,huz⟩
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (scalars F K) z
    obtain ⟨a,b,hx⟩ := (mem_seed C x).mp hz
    rw [← map_mul (QuotientGroup.mk' (scalars F K)),mem_seed] at huz
    change OnLine C ((u:K)*(x:K)) at huz
    rw [← hu,← hx,denominator_direction C i j k a b nz] at huz
    obtain ⟨s,rfl,rfl⟩ := huz
    apply mk_scalar x v (r:=s)
    rw [← hx]
    change value C.theta (s*j,s*k,0)=algebraMap F K s*value C.theta (j,k,0)
    simp only [value,map_mul,map_zero,zero_mul,add_zero]
    ring

#print axioms unique_direction

variable [Fintype F] [Fintype K]

/-- The actual cyclic labels used in the overlap theorem have one ordered
representation of every nonzero difference. -/
theorem perfect (C : CubicFrame F K) : Green33PerfectDifferenceCenters.Perfect (labels C) := by
  classical
  intro c hc
  let e := (cyclic C).toEquiv.trans Additive.toMul
  have add (a b) : e (a+b)=e a*e b := by simp [e]
  have zero : e 0=1 := by simp [e]
  have nonzero : e c≠1 := fun h => hc (e.injective (h.trans zero.symm))
  have mem (a) : a∈labels C ↔ e a∈seed C := by simp [labels,e]
  obtain ⟨z,⟨hz,hwz⟩,unique⟩ := unique_direction C (e c) nonzero
  let y := e.symm z
  have val : e y=z := e.apply_symm_apply _
  have hy : y∈labels C := mem _ |>.mpr (val ▸ hz)
  have hcy : c+y∈labels C := mem _ |>.mpr (by rwa [add,val])
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨(c+y,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hcy,hy⟩,add_sub_cancel_right ..⟩,?_⟩
  rintro ⟨a,b⟩ h
  obtain ⟨pair,eq⟩ := Finset.mem_filter.mp h
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp pair
  change a-b=c at eq
  have ab : a=c+b := sub_eq_iff_eq_add.mp eq
  have bz : e b=z := unique _ ⟨(mem _).mp hb,by rw [← add,← ab];exact (mem _).mp ha⟩
  have by' : b=y := e.injective (bz.trans val.symm)
  exact Prod.ext (ab.trans (congrArg (c+·) by')) by'

#print axioms perfect

open Finset Filter Green33PerfectDifferenceCenters Green33ReflectedLayers
open scoped Topology

/-- The number of projective line labels is exactly q+1. -/
theorem label_card (C : CubicFrame F K) : (labels C).card=Fintype.card F+1 := by
  have h := parameters _ (perfect C)
  rw [ZMod.card] at h
  push_cast at h
  have prod : (((labels C).card:ℝ)-(Fintype.card F+1))*((labels C).card+Fintype.card F)=0 := by
    nlinarith only [h]
  have nz : ((labels C).card:ℝ)+Fintype.card F≠0 := by positivity
  exact_mod_cast sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_right nz)

private theorem labels_nonempty (C : CubicFrame F K) : (labels C).Nonempty := by
  rw [← card_pos,label_card]
  omega

abbrev order (F : Type*) [Fintype F] : ℕ+ := ⟨(Fintype.card F)^2+Fintype.card F+1,by omega⟩

/-- The two cyclic layers consist of the even copies of the projective labels
and their reflections across the freely chosen odd residue 1+2t. -/
noncomputable def reflected (C : CubicFrame F K) (t : ZMod (order F)) :=
  doubled (m:=order F) (labels C) t

/-- The two complementary cosets retain both copies of each of the q+1 labels. -/
theorem reflected_card (C : CubicFrame F K) (t : ZMod (order F)) :
    (reflected C t).card=2*(Fintype.card F+1) := by
  let f := doubleHom (order F)
  let j := 1+f t
  let B : Finset (ZMod (order F)) := labels C
  obtain ⟨inj,dis,_⟩ := double_coordinates (order F) t
  have hf : Function.Injective f := inj
  have hd : Disjoint (B.image f) (B.image fun a => j-f a) := by
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    obtain ⟨b,_,h⟩ := mem_image.mp hz'
    exact dis (a+b) (by change f (a+b)=j;rw [map_add,← h];abel)
  change (B.image f ∪ B.image (fun a => j-f a)).card=_
  rw [card_union_of_disjoint hd,card_image_of_injective B hf,
    card_image_of_injective B (fun a b h => hf (sub_right_inj.mp h)),show B.card=_ from label_card C]
  omega

#print axioms reflected_card

theorem exact_count (C : CubicFrame F K) (t : ZMod (order F)) :
    (reflected C t+reflected C t).card+Green33ReflectedLayers.overlap (labels C) (((1:ZMod (order F))+t)+t)+1=
    2*(order F).val+2*(Fintype.card F+1) := by
  rw [← label_card C]
  exact doubled_count (m:=order F) (perfect C) (labels_nonempty C) t

section Limits
variable {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, CharP (F i) 2] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)]

omit [∀ i, Field (F i)] [∀ i, CharP (F i) 2] [∀ i, DecidableEq (F i)] in
private theorem order_grows (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => (order (F i)).val) atTop atTop :=
  tendsto_atTop_mono (fun i => by dsimp [order];omega) big

private theorem quarter (C : ∀ i, CubicFrame (F i) (K i)) (t : ∀ i, ZMod (order (F i)))
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => (Green33ReflectedLayers.overlap (labels (C i)) (((1:ZMod (order (F i)))+t i)+t i):ℝ)/
      Fintype.card (ZMod (order (F i)))) atTop (𝓝 (1/4)) := by
  have h := cyclic_limit C (fun i => ((1:ZMod (order (F i)))+t i)+t i) big
  apply h.congr
  intro i
  rw [ZMod.card]
  congr 1
  change (Fintype.card (F i):ℝ)^2+Fintype.card (F i)+1=(((Fintype.card (F i))^2+Fintype.card (F i)+1:ℕ):ℝ)
  push_cast
  rfl

/-- Every full cyclic basis containing the two layers has limiting lower
size coefficient at least (3+√3)/(2√2), on every choice of axes. -/
theorem repair_floor (C : ∀ i, CubicFrame (F i) (K i)) (t : ∀ i, ZMod (order (F i)))
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop)
    (B : ∀ i, Finset (ZMod (2*(order (F i)).val))) (sub : ∀ i, reflected (C i) (t i) ⊆ B i)
    (full : ∀ i, B i+B i=univ) {s : ℝ} (below : s<(3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, s<((B i).card:ℝ)/Real.sqrt (2*((order (F i)).val:ℝ)) := by
  let v i := order (F i)
  have largeV : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by
    simpa only [ZMod.card] using order_grows big
  have got := Green33SidonLayerRepairs.overlap_extension_lower (fun i => labels (C i))
    (fun i => (perfect (C i)).sidon) (fun i => labels_nonempty (C i))
    (fun i => doubleHom (v i)) (fun i => (double_coordinates _ (t i)).1)
    (fun i => 1+doubleHom _ (t i)) (fun i => (double_coordinates _ (t i)).2.1)
    (by intro i;simp only [ZMod.card];rfl)
    (fun i => ((1:ZMod (order (F i)))+t i)+t i) (fun i => (double_coordinates _ (t i)).2.2)
    largeV (perfect_size_limit _ (fun i => perfect (C i)) largeV) (quarter C t big)
    B sub full below
  simpa only [ZMod.card,Nat.cast_mul,Nat.cast_ofNat] using got

/-- The full doubled cyclic group is covered with limiting density 7/8, for
every sequence of odd reflection axes. -/
theorem coverage (C : ∀ i, CubicFrame (F i) (K i)) (t : ∀ i, ZMod (order (F i)))
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => ((reflected (C i) (t i)+reflected (C i) (t i)).card:ℝ)/
      (2*((order (F i)).val:ℝ))) atTop (𝓝 (7/8)) := by
  let q i : ℝ := Fintype.card (F i)
  let v i : ℝ := (order (F i)).val
  let A i : ℝ := (reflected (C i) (t i)+reflected (C i) (t i)).card
  let I i : ℝ := Green33ReflectedLayers.overlap (labels (C i)) (((1:ZMod (order (F i)))+t i)+t i)
  have grow : Tendsto q atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have growV : Tendsto v atTop atTop := tendsto_natCast_atTop_atTop.comp (order_grows big)
  have one := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop grow
  have tiny := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop growV
  have small : Tendsto (fun i => (q i+1)/v i) atTop (𝓝 0) := by
    have h := (one.add (one.pow 2)).div (((tendsto_const_nhds (x:=(1:ℝ))).add one).add (one.pow 2))
      (by norm_num)
    norm_num only [zero_pow (by decide : 2 ≠ 0),add_zero,zero_div] at h
    apply h.congr
    intro i
    have qp : 0<q i := by dsimp [q];exact_mod_cast Fintype.card_pos
    have vp : v i=q i^2+q i+1 := by simp [v,q,order]
    change (1/q i+(1/q i)^2)/(1+1/q i+(1/q i)^2)=(q i+1)/v i
    rw [vp]
    have den : q i^2+q i+1≠0 := by positivity
    field_simp [qp.ne',den]
  have inter : Tendsto (fun i => I i/v i) atTop (𝓝 (1/4)) := by
    simpa only [ZMod.card] using quarter C t big
  have h := (((tendsto_const_nhds (x:=(1:ℝ))).add small).sub (inter.div_const 2)).sub (tiny.div_const 2)
  norm_num1 at h
  apply h.congr
  intro i
  have eq := congrArg (Nat.cast (R:=ℝ)) (exact_count (C i) (t i))
  push_cast at eq
  change A i+I i+1=2*v i+2*(q i+1) at eq
  have vp : 0<v i := by dsimp only [v];exact_mod_cast (order (F i)).pos
  change 1+(q i+1)/v i-I i/v i/2-(1/v i)/2=A i/(2*v i)
  field_simp [vp.ne']
  nlinarith only [eq]

#print axioms coverage

end Limits
#print axioms label_card
#print axioms exact_count
#print axioms repair_floor

end Green33SingerReflectedCoverage
