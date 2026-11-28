import Green33SplitPencils

/-! Multiplication, inversion and binary splitting in a cubic Singer plane. -/

open Finset Green33ReciprocalCharts Green33SplitPencils
open scoped BigOperators

namespace Green33SingerCoordinates

abbrev Coords (F : Type*) := F × F × F

variable {F K : Type*} [Field F] [CharP F 2] [Field K] [Algebra F K]

/-- Value of the coefficient vector in the power basis. -/
def value (θ : K) (x : Coords F) : K :=
  algebraMap F K x.1 + algebraMap F K x.2.1*θ + algebraMap F K x.2.2*θ^2

/-- A cubic power basis with the quadratic term removed in characteristic two. -/
structure CubicFrame (F K : Type*) [Field F] [Field K] [Algebra F K] where
  theta : K
  p : F
  d : F
  rel : theta^3=algebraMap F K p*theta+algebraMap F K d
  basis : Function.Bijective (value (F:=F) theta)

/-- Multiplication modulo T³+pT+d in the coefficient basis. -/
def product (p d : F) (x y : Coords F) : Coords F :=
  (x.1*y.1+d*(x.2.1*y.2.2+x.2.2*y.2.1),
   x.1*y.2.1+x.2.1*y.1+p*(x.2.1*y.2.2+x.2.2*y.2.1)+d*x.2.2*y.2.2,
   x.1*y.2.2+x.2.1*y.2.1+x.2.2*y.1+p*x.2.2*y.2.2)

/-- Numerators of the reciprocal coordinates. -/
def adj (p d : F) (x : Coords F) : Coords F :=
  (x.1^2+p^2*x.2.2^2+p*x.2.1^2+d*x.2.1*x.2.2,
   x.1*x.2.1+d*x.2.2^2, x.2.1^2+x.1*x.2.2+p*x.2.2^2)

def normForm (p d : F) (x : Coords F) := (product p d x (adj p d x)).1

omit [CharP F 2] in
theorem value_product (C : CubicFrame F K) (x y : Coords F) :
    value C.theta (product C.p C.d x y)=value C.theta x*value C.theta y := by
  obtain ⟨i,j,k⟩ := x
  obtain ⟨a,b,c⟩ := y
  simp only [value,product,map_add,map_mul]
  linear_combination
    -(algebraMap F K j*algebraMap F K c+algebraMap F K k*algebraMap F K b+
      algebraMap F K k*algebraMap F K c*C.theta)*C.rel

theorem product_adj (p d : F) (x : Coords F) :
    product p d x (adj p d x)=(normForm p d x,0,0) := by
  obtain ⟨a,b,c⟩ := x
  refine Prod.ext ?_ ?_
  · rfl
  apply Prod.ext <;> dsimp [product,adj] <;> ring_nf <;> reduce_mod_char!

theorem adj_product (p d : F) (x y : Coords F) :
    adj p d (product p d x y)=product p d (adj p d x) (adj p d y) := by
  obtain ⟨i,j,k⟩ := x
  obtain ⟨a,b,c⟩ := y
  apply Prod.ext
  · dsimp [product,adj]; ring_nf; reduce_mod_char!
  · apply Prod.ext <;> dsimp [product,adj] <;> ring_nf <;> reduce_mod_char!

omit [CharP F 2] in
private theorem value_zero (θ : K) : value (F:=F) θ (0,0,0)=0 := by simp [value]

omit [CharP F 2] in
private theorem value_one (θ : K) : value (F:=F) θ (1,0,0)=1 := by simp [value]

omit [CharP F 2] in
theorem constant_ne (C : CubicFrame F K) : C.d≠0 := by
  intro h
  have θn : C.theta≠0 := by
    intro z
    have e := C.basis.injective (a₁:=(0,1,0)) (a₂:=(0,0,0)) (by simp [value,z])
    simpa using congrArg (fun t : Coords F => t.2.1) e
  have eq : C.theta^2=algebraMap F K C.p := by
    apply mul_right_cancel₀ θn
    simpa [pow_succ,h] using C.rel
  have e := C.basis.injective (a₁:=(0,0,1)) (a₂:=(C.p,0,0)) (by simp [value,eq])
  simpa using congrArg (fun t : Coords F => t.2.2) e

theorem norm_ne (C : CubicFrame F K) (x : Coords F) (hx : x≠(0,0,0)) :
    normForm C.p C.d x≠0 := by
  have nz : value C.theta x≠0 := fun h => hx (C.basis.injective (h.trans (value_zero _).symm))
  obtain ⟨y,hy⟩ := C.basis.surjective (value C.theta x)⁻¹
  have xy : product C.p C.d x y=(1,0,0) := by
    apply C.basis.injective
    rw [value_product,hy,mul_inv_cancel₀ nz,value_one]
  have an : adj C.p C.d x≠(0,0,0) := by
    intro h
    have e := adj_product C.p C.d x y
    rw [xy,h] at e
    simpa [adj,product] using congrArg Prod.fst e
  intro h
  have z := congrArg (value C.theta) (product_adj C.p C.d x)
  rw [value_product,h,value_zero,mul_eq_zero] at z
  exact an (C.basis.injective ((z.resolve_left nz).trans (value_zero _).symm))

#print axioms value_product
#print axioms norm_ne

/-- Coefficients of u·adj₀+v·adj₁+w·adj₂ on the chart (a,1,b). -/
def component (p d u v w : F) : PlaneQuad F :=
  ⟨u*p+w,v,u*d,u,w,u*p^2+v*d+w*p⟩

def first (p d : F) (t : Coords F) := component p d t.1 (d*t.2.2) (d*t.2.1)
def middle (p d : F) (t : Coords F) := component p d t.2.1 (t.1+p*t.2.2) (p*t.2.1+d*t.2.2)
def last (p d : F) (t : Coords F) := component p d t.2.2 t.2.1 (t.1+p*t.2.2)

omit [CharP F 2] in
theorem chart_product (p d : F) (t : Coords F) (a b : F) :
    product p d t (adj p d (a,1,b))=
      ((first p d t).eval a b,(middle p d t).eval a b,(last p d t).eval a b) := by
  obtain ⟨i,j,k⟩ := t
  apply Prod.ext
  · dsimp [first,component,PlaneQuad.eval,product,adj];ring
  · apply Prod.ext <;> dsimp [middle,last,component,PlaneQuad.eval,product,adj] <;> ring

/-- Every nonzero reflection center gives a nonsingular middle conic. -/
theorem middle_discriminant (p d : F) (t : Coords F) :
    (middle p d t).discriminant=d*normForm p d t := by
  obtain ⟨i,j,k⟩ := t
  dsimp [middle,component,PlaneQuad.discriminant,PlaneQuad.hom,normForm,product,adj]
  ring_nf
  reduce_mod_char!

theorem chart_incidence [Fintype F] [DecidableEq F] (C : CubicFrame F K)
    (t : Coords F) (ht : t≠(0,0,0)) :
    let P := first C.p C.d t
    let Q := middle C.p C.d t
    let R := last C.p C.d t
    |4*((common P Q R).card:ℝ)-2*(output P Q R).card-Fintype.card F| ≤
      (Fintype.card F:ℝ)*(radius (Fintype.card F)+8) := by
  apply split_incidence
  rw [middle_discriminant]
  exact mul_ne_zero (constant_ne C) (norm_ne C t ht)

#print axioms chart_product
#print axioms middle_discriminant
#print axioms chart_incidence

/-- Products of two elements of the line spanned by 1 and θ. The zero vector
is included so that complete field sums have no missing terms. -/
def LineProduct (C : CubicFrame F K) (z : K) : Prop :=
  ∃ r s t u : F, value C.theta (r,s,0)*value C.theta (t,u,0)=z

omit [CharP F 2] in
theorem lineProduct_value (C : CubicFrame F K) (x : Coords F) :
    LineProduct C (value C.theta x) ↔ Splits x.1 x.2.1 x.2.2 := by
  obtain ⟨a,b,c⟩ := x
  constructor
  · rintro ⟨r,s,t,u,eq⟩
    rw [← value_product C] at eq
    have h := C.basis.injective eq
    simp only [product,mul_zero,zero_mul,add_zero,zero_add] at h
    exact ⟨r,s,t,u,(congrArg Prod.fst h).symm,(congrArg (fun z : Coords F => z.2.1) h).symm,
      (congrArg (fun z : Coords F => z.2.2) h).symm⟩
  · rintro ⟨r,s,t,u,ar,br,cr⟩
    refine ⟨r,s,t,u,?_⟩
    rw [← value_product C]
    dsimp only at ar br cr
    simp [product,ar,br,cr]

omit [CharP F 2] in
private theorem lineProduct_mul (C : CubicFrame F K) (k : F) {z : K} (hz : LineProduct C z) :
    LineProduct C (algebraMap F K k*z) := by
  obtain ⟨r,s,t,u,rfl⟩ := hz
  refine ⟨k*r,k*s,t,u,?_⟩
  simp only [value,map_mul,map_zero,zero_mul,add_zero]
  ring

omit [CharP F 2] in
theorem lineProduct_scalar (C : CubicFrame F K) {k : F} (hk : k≠0) (z : K) :
    LineProduct C (algebraMap F K k*z) ↔ LineProduct C z := by
  refine ⟨fun h => ?_,lineProduct_mul C k⟩
  have e := lineProduct_mul C k⁻¹ h
  simpa [← mul_assoc,← map_mul,hk] using e

noncomputable def lineSign (C : CubicFrame F K) (z : K) : ℝ := by
  classical exact if LineProduct C z then 1 else -1

omit [CharP F 2] in
private theorem sign_value (C : CubicFrame F K) (x : Coords F) :
    lineSign C (value C.theta x)=sign x.1 x.2.1 x.2.2 := by
  classical simp only [lineSign,sign,lineProduct_value]

omit [CharP F 2] in
private theorem sign_scalar (C : CubicFrame F K) {k : F} (hk : k≠0) (z : K) :
    lineSign C (algebraMap F K k*z)=lineSign C z := by
  classical simp only [lineSign,lineProduct_scalar C hk]

omit [CharP F 2] in
private theorem sign_abs (C : CubicFrame F K) (z : K) : |lineSign C z|=1 := by
  classical by_cases h : LineProduct C z <;> simp [lineSign,h]

/-- Reciprocal in the extension is the adjugate divided by the scalar norm. -/
theorem reciprocal (C : CubicFrame F K) (x : Coords F) (hx : x≠(0,0,0)) (w : K) :
    algebraMap F K (normForm C.p C.d x)*(w/value C.theta x)=w*value C.theta (adj C.p C.d x) := by
  have nz : value C.theta x≠0 := fun h => hx (C.basis.injective (h.trans (value_zero _).symm))
  have h := congrArg (value C.theta) (product_adj C.p C.d x)
  rw [value_product] at h
  simp only [value,map_zero,zero_mul,add_zero] at h
  rw [← h]
  change (value C.theta x*value C.theta (adj C.p C.d x))*(w/value C.theta x)=_
  field_simp

theorem chart_reflection (C : CubicFrame F K) (t : Coords F) (a b : F) :
    lineSign C (value C.theta t/value C.theta (a,1,b))=
      sign ((first C.p C.d t).eval a b) ((middle C.p C.d t).eval a b) ((last C.p C.d t).eval a b) := by
  have nonzero : (a,(1:F),b)≠(0,0,0) := by simp
  rw [← sign_scalar C (norm_ne C _ nonzero),reciprocal C _ nonzero,← value_product C,
    sign_value,chart_product]

#print axioms lineProduct_value
#print axioms chart_reflection

variable [Fintype F] [Fintype K]

omit [CharP F 2] in
private theorem complete_bound (C : CubicFrame F K) (S : K→ℝ)
    (scal : ∀ k : F, k≠0 → ∀ z : K, S (algebraMap F K k*z)=S z)
    (unit : ∀ z, |S z|≤1) (H : ℝ) (chart : |∑ a : F, ∑ c : F, S (value C.theta (a,1,c))|≤H) :
    |∑ z : K, S z| ≤ (Fintype.card F:ℝ)*H+(Fintype.card F:ℝ)^2 := by
  classical
  let q : ℝ := Fintype.card F
  let T (b : F) := ∑ a : F, ∑ c : F, S (value C.theta (a,b,c))
  have eq (b : F) (hb : b≠0) : T b=T 1 := by
    have s (a c : F) : S (value C.theta (b*a,b,b*c))=S (value C.theta (a,1,c)) := by
      rw [← scal b hb (value C.theta (a,1,c))]
      congr 1
      simp only [value,map_mul,map_one,one_mul]
      ring
    calc
      T b = ∑ a : F, ∑ c : F, S (value C.theta (b*a,b,b*c)) := by
        unfold T
        rw [← Equiv.sum_comp (Equiv.mulLeft₀ b hb) (fun a => ∑ c : F, S (value C.theta (a,b,c)))]
        apply sum_congr rfl
        intro a _
        exact (Equiv.sum_comp (Equiv.mulLeft₀ b hb) (fun c => S (value C.theta (b*a,b,c)))).symm
      _ = T 1 := by simp only [s,T]
  have row (b : F) : |T b|≤H+(if b=0 then q^2 else 0) := by
    by_cases hb : b=0
    · subst b
      simp only [if_true]
      have pt (a : F) : |∑ c : F, S (value C.theta (a,0,c))|≤q :=
        (abs_sum_le_sum_abs ..).trans ((sum_le_sum fun c _ => unit _).trans_eq (by simp [q]))
      have tt : |T 0|≤q^2 := (abs_sum_le_sum_abs ..).trans
        ((sum_le_sum fun a _ => pt a).trans_eq (by simp [q,pow_two]))
      linarith [le_trans (abs_nonneg _) chart]
    · simpa only [if_neg hb,add_zero,eq b hb] using chart
  have allsum : (∑ z : K, S z)=∑ b : F, T b := by
    let e := Equiv.ofBijective _ C.basis
    calc
      _ = ∑ x : Coords F, S (value C.theta x) := (Equiv.sum_comp e S).symm
      _ = _ := by simp only [Fintype.sum_prod_type,T];rw [sum_comm]
  rw [allsum]
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum fun b _ => row b).trans_eq (by
    simp [sum_add_distrib,q]))

/-- Scalar representatives of the intersection of a line product with its
reflection. The origin belongs to both sets under totalized field inversion. -/
noncomputable def overlap (C : CubicFrame F K) (w : K) : Finset K := by
  classical exact univ.filter fun z => LineProduct C z ∧ LineProduct C (w/z)

theorem field_overlap [DecidableEq F] (C : CubicFrame F K) (w : K) (hw : w≠0) :
    |4*((overlap C w).card:ℝ)-(Fintype.card F:ℝ)^3| ≤
      (Fintype.card F:ℝ)^2*(radius (Fintype.card F)+13) := by
  classical
  let q : ℝ := Fintype.card F
  let s := lineSign C
  let H (z : K) := s z*s (w/z)
  obtain ⟨t,ht⟩ := C.basis.surjective w
  have tn : t≠(0,0,0) := fun h => hw (ht.symm.trans (h ▸ value_zero _))
  have pp := plane_bound (first C.p C.d t) (middle C.p C.d t) (last C.p C.d t)
    (by rw [middle_discriminant]; exact mul_ne_zero (constant_ne C) (norm_ne C t tn))
  have ps (a b : F) : H (value C.theta (a,1,b)) =
      weight (first C.p C.d t) (middle C.p C.d t) (last C.p C.d t) a b := by
    unfold H s weight
    rw [← ht,chart_reflection,sign_value]
  have hs (k : F) (hk : k≠0) (z : K) : H (algebraMap F K k*z)=H z := by
    have alg : w/(algebraMap F K k*z)=algebraMap F K k⁻¹*(w/z) := by
      rw [map_inv₀];simp only [div_eq_mul_inv,mul_inv_rev];ring
    unfold H s
    rw [sign_scalar C hk,alg,sign_scalar C (inv_ne_zero hk)]
  have pair := complete_bound C H hs (fun z => by simp [H,s,abs_mul,sign_abs]) _
    (by simpa only [ps] using pp)
  have src := complete_bound C s (fun _ h _ => sign_scalar C h _) (fun z => (sign_abs C z).le) q
    (by simp only [s,sign_value,source_total]; exact abs_of_nonneg (Nat.cast_nonneg _) |>.le)
  have perm : ∑ z : K, s (w/z)=∑ z : K, s z := by
    let e : K≃K := (Equiv.inv K).trans (Equiv.mulLeft₀ w hw)
    simpa only [e,Equiv.trans_apply,Equiv.inv_apply,Equiv.mulLeft₀_apply,div_eq_mul_inv] using Equiv.sum_comp e s
  have mark (z : K) :
      4*(if z∈overlap C w then (1:ℝ) else 0)=1+s z+s (w/z)+H z := by
    by_cases h : LineProduct C z <;> by_cases j : LineProduct C (w/z) <;>
      norm_num [overlap,s,H,lineSign,h,j]
  have count := sum_congr (s₁:=univ) rfl (fun z _ => mark z)
  have indicator : (∑ z : K, if z∈overlap C w then (1:ℝ) else 0)=(overlap C w).card := by
    rw [← sum_filter];simp
  have size : (Fintype.card K:ℝ)=q^3 := by
    have e := (Fintype.card_congr (Equiv.ofBijective _ C.basis)).symm
    simp only [Fintype.card_prod] at e
    dsimp [q];exact_mod_cast (e.trans (by ring))
  simp only [← mul_sum,indicator,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,perm,size] at count
  have val : 4*((overlap C w).card:ℝ)-q^3 = (∑ z : K, s z)+(∑ z : K, s z)+(∑ z : K,H z) := by linarith
  change |4*((overlap C w).card:ℝ)-q^3|≤q^2*(radius q+13)
  rw [val]
  calc
    _ ≤ (|∑ z : K, s z|+|∑ z : K, s z|)+|∑ z : K, H z| :=
      (abs_add_le ..).trans (add_le_add_left (abs_add_le ..) _)
    _ ≤ _ := by dsimp only [q] at *;nlinarith only [pair,src]

#print axioms field_overlap

open Filter
open scoped Topology

/-- A quarter of the extension elements, in the limit, belong to both the
line product and its reflection. Both the frame and the center may vary. -/
theorem field_overlap_limit {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)]
    [∀ i, Algebra (F i) (K i)] [∀ i, CharP (F i) 2] [∀ i, Fintype (F i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (F i)] (C : ∀ i, CubicFrame (F i) (K i)) (w : ∀ i, K i)
    (hw : ∀ i, w i≠0) (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => ((overlap (C i) (w i)).card:ℝ)/(Fintype.card (F i):ℝ)^3) atTop (𝓝 (1/4)) := by
  let q i : ℝ := Fintype.card (F i)
  let a i : ℝ := (overlap (C i) (w i)).card
  have qp i : 0<q i := by dsimp [q];exact_mod_cast Fintype.card_pos
  have large : Tendsto q atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have lim := (radius_ratio qp large).add ((tendsto_const_nhds (x:=(13:ℝ))).div_atTop large)
  rw [add_zero] at lim
  have lim0 : Tendsto (fun i => (4*a i-q i^3)/q i^3) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ lim
    filter_upwards with i
    have pos := qp i
    have est := field_overlap (C i) (w i) (hw i)
    change |4*a i-q i^3|≤q i^2*(radius (q i)+13) at est
    change ‖(4*a i-q i^3)/q i^3‖≤radius (q i)/q i+13/q i
    rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (pow_nonneg pos.le 3),← add_div]
    apply (div_le_div_iff₀ (pow_pos pos 3) pos).mpr
    nlinarith only [mul_le_mul_of_nonneg_right est pos.le]
  have done := (lim0.add (tendsto_const_nhds (x:=(1:ℝ)))).div_const 4
  rw [zero_add] at done
  apply done.congr
  intro i
  change ((4*a i-q i^3)/q i^3+1)/4=a i/q i^3
  field_simp [(qp i).ne']
  ring

#print axioms field_overlap_limit

end Green33SingerCoordinates
