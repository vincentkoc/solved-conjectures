import Green33SingerCoordinates
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Finite.Basic

/-! The split-product estimate on the actual scalar quotient of a cubic field. -/

open Finset Green33SingerCoordinates Green33SplitPencils Green33ReciprocalCharts
open scoped Pointwise BigOperators

namespace Green33SingerProjectiveOverlap

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The scalar subgroup of the multiplicative group of the extension. -/
def scalars (F K : Type*) [Field F] [Field K] [Algebra F K] : Subgroup Kˣ :=
  (Units.map (algebraMap F K).toMonoidHom).range

abbrev Plane (F K : Type*) [Field F] [Field K] [Algebra F K] := Kˣ ⧸ scalars F K

/-- The projectivization of the line span(1,θ) in the Singer group. -/
def seed (C : CubicFrame F K) : Set (Plane F K) :=
  (QuotientGroup.mk' (scalars F K)) '' {u : Kˣ | ∃ a b : F, value C.theta (a,b,0)=u}

private theorem scalar_product (C : CubicFrame F K) (x y : Kˣ)
    (h : (QuotientGroup.mk' (scalars F K)) x=(QuotientGroup.mk' (scalars F K)) y) :
    LineProduct C (x:K) ↔ LineProduct C (y:K) := by
  obtain ⟨a,ha⟩ := QuotientGroup.eq_iff_div_mem.mp h
  have eq : algebraMap F K (a:F)*(y:K)=(x:K) := by
    have t := congrArg (fun u : Kˣ => (u:K)) ha
    rw [Units.val_div_eq_div_val] at t
    exact (eq_div_iff y.ne_zero).mp t
  rw [← eq,lineProduct_scalar C a.ne_zero]

theorem mem_seed_product (C : CubicFrame F K) (x : Kˣ) :
    (QuotientGroup.mk' (scalars F K)) x∈seed C*seed C ↔ LineProduct C (x:K) := by
  classical
  constructor
  · rintro ⟨_,⟨u,⟨a,b,hu⟩,rfl⟩,_,⟨v,⟨c,d,hv⟩,rfl⟩,he⟩
    dsimp only at he
    rw [← map_mul (QuotientGroup.mk' (scalars F K))] at he
    exact (scalar_product C _ _ he).mp ⟨a,b,c,d,by rw [hu,hv];rfl⟩
  · rintro ⟨a,b,c,d,h⟩
    have nz : value C.theta (a,b,0)*value C.theta (c,d,0)≠0 := h ▸ x.ne_zero
    let u := Units.mk0 _ (left_ne_zero_of_mul nz)
    let v := Units.mk0 _ (right_ne_zero_of_mul nz)
    have uv : u*v=x := Units.ext h
    exact ⟨_,⟨u,⟨a,b,rfl⟩,rfl⟩,_,⟨v,⟨c,d,rfl⟩,rfl⟩,(map_mul _ u v).symm.trans (congrArg _ uv)⟩

/-- Projective points in the line product and its multiplicative reflection. -/
def common (C : CubicFrame F K) (w : Plane F K) : Set (Plane F K) :=
  {z | z∈seed C*seed C ∧ w/z∈seed C*seed C}

private theorem mk_common (C : CubicFrame F K) (w z : Kˣ) :
    QuotientGroup.mk' (scalars F K) z ∈ common C (QuotientGroup.mk' (scalars F K) w) ↔
    LineProduct C (z:K) ∧ LineProduct C ((w:K)/(z:K)) := by
  change _∈seed C*seed C ∧ _/_∈seed C*seed C ↔ _
  rw [← map_div (QuotientGroup.mk' (scalars F K)),mem_seed_product,mem_seed_product,Units.val_div_eq_div_val]

variable [Fintype F] [Fintype K]

omit [Fintype K] in
theorem scalar_card : Nat.card (scalars F K)=Fintype.card F-1 := by
  classical
  have inj : Function.Injective (Units.map (algebraMap F K).toMonoidHom) := by
    intro a b eq
    exact Units.ext ((algebraMap F K).injective (congrArg (fun x : Kˣ => (x:K)) eq))
  rw [scalars,← Nat.card_congr (MonoidHom.ofInjective inj).toEquiv,Nat.card_eq_fintype_card,Fintype.card_units]

/-- Exact conversion of the full-field count. Each nonzero scalar orbit has
q−1 representatives, and the origin contributes one. -/
theorem orbit_count (C : CubicFrame F K) (w : Kˣ) :
    (overlap C (w:K)).card =
      (Fintype.card F-1)*Nat.card (common C (QuotientGroup.mk' (scalars F K) w))+1 := by
  classical
  let T := overlap C (w:K)
  let U := common C (QuotientGroup.mk' (scalars F K) w)
  let S := (QuotientGroup.mk (s:=scalars F K) ⁻¹' U : Set Kˣ)
  have zero : (0:K)∈T := by
    have p : LineProduct C 0 := ⟨0,0,0,0,by simp [value]⟩
    simp [T,overlap,p]
  let e : S ≃ (T.erase 0 : Finset K) := {
    toFun := fun z => ⟨(z.val:K), by
      apply mem_erase.mpr
      exact ⟨z.val.ne_zero,mem_filter.mpr ⟨mem_univ _,(mk_common C w z.val).mp z.property⟩⟩⟩
    invFun := fun z => ⟨Units.mk0 z.val (mem_erase.mp z.property).1, by
      apply (mk_common C w _).mpr
      exact (mem_filter.mp (mem_erase.mp z.property).2).2⟩
    left_inv := fun _ => Subtype.ext (Units.ext rfl)
    right_inv := fun _ => Subtype.ext rfl }
  have a : Nat.card S=(T.erase 0).card := (Nat.card_congr e).trans (by rw [Nat.card_eq_fintype_card,Fintype.card_coe])
  have b : Nat.card S=Nat.card (scalars F K)*Nat.card U := QuotientGroup.card_preimage_mk _ _
  change T.card=_*Nat.card U+1
  rw [← card_erase_add_one zero,← a,b,scalar_card]

#print axioms mem_seed_product
#print axioms orbit_count

/-- Order of the actual scalar quotient of the degree-three multiplicative group. -/
theorem plane_card (C : CubicFrame F K) :
    Nat.card (Plane F K)=(Fintype.card F)^2+Fintype.card F+1 := by
  classical
  let q := Fintype.card F
  have p : 1<q := Fintype.one_lt_card
  have size : Fintype.card K=q^3 := by
    have e := (Fintype.card_congr (Equiv.ofBijective _ C.basis)).symm
    simp only [Fintype.card_prod] at e
    exact e.trans (by dsimp [q];ring)
  have e := (scalars F K).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_units,Nat.card_eq_fintype_card,size,scalar_card] at e
  change q^3-1=Nat.card (Plane F K)*(q-1) at e
  have chk : (q^2+q+1)*(q-1)=q^3-1 := by
    apply Nat.sub_eq_of_eq_add (by
      have h := Nat.sub_add_cancel (show 1≤q by omega)
      nlinarith only [congrArg (fun x => (q^2+q+1)*x) h]) |>.symm
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0<q-1) (e.symm.trans chk.symm)

open Filter
open scoped Topology

/-- All reflection centers have normalized projective overlap tending to 1/4. -/
theorem projective_limit {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, CharP (F i) 2] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)] (C : ∀ i, CubicFrame (F i) (K i)) (t : ∀ i, Plane (F i) (K i))
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => (Nat.card (common (C i) (t i)):ℝ)/Nat.card (Plane (F i) (K i)))
      atTop (𝓝 (1/4)) := by
  classical
  choose w hw using fun i => QuotientGroup.mk'_surjective (scalars (F i) (K i)) (t i)
  let q i : ℝ := Fintype.card (F i)
  let a i : ℝ := (overlap (C i) (w i:K i)).card
  let b i : ℝ := Nat.card (common (C i) (t i))
  have p i : 1<q i := by dsimp [q];exact_mod_cast (Fintype.one_lt_card (α:=F i))
  have large : Tendsto q atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have one : Tendsto (fun i => 1/q i^3) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow,zero_pow (by decide : 3 ≠ 0)] using
      (((tendsto_const_nhds (x:=(1:ℝ))).div_atTop large).pow 3)
  have full := field_overlap_limit C (fun i => (w i:K i)) (fun i => (w i).ne_zero) big
  have lim := (full.sub one).div ((tendsto_const_nhds (x:=(1:ℝ))).sub one) (by norm_num)
  rw [sub_zero,sub_zero,div_one] at lim
  apply lim.congr
  intro i
  have h := orbit_count (C i) (w i)
  rw [hw i] at h
  have iden : a i=(q i-1)*b i+1 := by
    change ((overlap (C i) (w i:K i)).card:ℝ)=((Fintype.card (F i):ℝ)-1)*(Nat.card (common (C i) (t i)):ℝ)+1
    have cast := congrArg (Nat.cast (R:=ℝ)) h
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sub (by exact Nat.succ_le_of_lt Fintype.card_pos : 1≤Fintype.card (F i))] using cast
  rw [plane_card (C i)]
  push_cast
  change (a i/q i^3-1/q i^3)/(1-1/q i^3)=b i/(q i^2+q i+1)
  rw [iden]
  have pos := p i
  have nz : q i^3-1≠0 := by nlinarith only [pos,pow_lt_pow_left₀ pos (by norm_num : (0:ℝ)≤1) (by decide : 3 ≠ 0)]
  have qn : q i≠0 := by linarith
  have dn : q i^2+q i+1≠0 := by nlinarith only [pos,sq_nonneg (q i)]
  field_simp [qn,dn,nz]
  ring

#print axioms plane_card
#print axioms projective_limit

/-- Choose cyclic coordinates for the scalar quotient of order q²+q+1. -/
noncomputable def cyclic (C : CubicFrame F K) :
    ZMod ((Fintype.card F)^2+Fintype.card F+1) ≃+ Additive (Plane F K) := by
  letI : IsCyclic (Plane F K) := isCyclic_of_surjective (QuotientGroup.mk' (scalars F K))
    (QuotientGroup.mk'_surjective _)
  exact (ZMod.ringEquivCongr (plane_card C).symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (G:=Additive (Plane F K)) inferInstance)

/-- Singer line labels in additive cyclic coordinates. -/
noncomputable def labels (C : CubicFrame F K) : Finset (ZMod ((Fintype.card F)^2+Fintype.card F+1)) := by
  classical exact univ.filter fun x => (cyclic C x).toMul∈seed C

private theorem label_sum (C : CubicFrame F K) (x : ZMod ((Fintype.card F)^2+Fintype.card F+1)) :
    x∈labels C+labels C ↔ (cyclic C x).toMul∈seed C*seed C := by
  classical
  constructor
  · intro h
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp h
    rw [map_add,toMul_add]
    exact ⟨_,(mem_filter.mp ha).2,_,(mem_filter.mp hb).2,rfl⟩
  · rintro ⟨u,hu,v,hv,eq⟩
    let a := (cyclic C).symm (Additive.ofMul u)
    let b := (cyclic C).symm (Additive.ofMul v)
    have au : (cyclic C a).toMul=u := by simp [a]
    have bv : (cyclic C b).toMul=v := by simp [b]
    apply Finset.mem_add.mpr
    refine ⟨a,mem_filter.mpr ⟨mem_univ _,au ▸ hu⟩,b,mem_filter.mpr ⟨mem_univ _,bv ▸ hv⟩,?_⟩
    apply (cyclic C).injective
    apply Additive.toMul.injective
    rwa [map_add,toMul_add,au,bv]

/-- The literal cyclic sumset/reflection cardinal matches the projective product count. -/
theorem cyclic_count (C : CubicFrame F K) (c : ZMod ((Fintype.card F)^2+Fintype.card F+1)) :
    ((labels C+labels C).filter fun x => c-x∈labels C+labels C).card =
      Nat.card (common C (cyclic C c).toMul) := by
  classical
  let A := (labels C+labels C).filter fun x => c-x∈labels C+labels C
  let e := (cyclic C).toEquiv.trans Additive.toMul
  have prop (x) : x∈ A ↔ e x∈common C (e c) := by
    simp only [A,mem_filter,label_sum,map_sub,toMul_sub]
    rfl
  let eq : A ≃ common C (e c) := {
    toFun := fun x => ⟨e x,(prop _).mp x.property⟩
    invFun := fun x => ⟨e.symm x,(prop _).mpr (by simp)⟩
    left_inv := fun _ => Subtype.ext (e.symm_apply_apply _)
    right_inv := fun _ => Subtype.ext (e.apply_symm_apply _) }
  exact (by rw [Nat.card_eq_fintype_card,Fintype.card_coe] : Nat.card A=A.card).symm.trans (Nat.card_congr eq)

/-- For any choice of centers, the overlap of the Singer cyclic sumsets has
limiting density 1/4 in Z/(q²+q+1) as q grows through powers of two. -/
theorem cyclic_limit {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, CharP (F i) 2] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)] (C : ∀ i, CubicFrame (F i) (K i))
    (c : ∀ i, ZMod ((Fintype.card (F i))^2+Fintype.card (F i)+1))
    (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => (((labels (C i)+labels (C i)).filter fun x => c i-x∈labels (C i)+labels (C i)).card:ℝ)/
      ((Fintype.card (F i):ℝ)^2+Fintype.card (F i)+1)) atTop (𝓝 (1/4)) := by
  have h := projective_limit C (fun i => (cyclic (C i) (c i)).toMul) big
  simpa only [cyclic_count,plane_card (C _),Nat.cast_add,Nat.cast_pow,Nat.cast_one] using h

#print axioms cyclic_count
#print axioms cyclic_limit

end Green33SingerProjectiveOverlap
