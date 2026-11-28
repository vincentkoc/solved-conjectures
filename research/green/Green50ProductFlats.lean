import Green50QuadraticFlats

/-! # Product coordinates in binary quadratic sumsets

Each additional pair of graph summands reduces the number of unhandled rank-two planes
by a factor of four. The recovered output dimension pays for the input restriction.
-/

open Finset
open scoped Pointwise

namespace Green50ProductFlats
open Green50QuadraticGraphs Green50QuadraticFibres Green50QuadraticFlats
local notation "F₂" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]


variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The binary alternating form on a coordinate plane. -/
def planeForm (x y : F₂ × F₂) : F₂ := x.1*y.2 + x.2*y.1

private theorem common_orthogonal :
    ∀ t x y : F₂ × F₂, t ≠ 0 → planeForm t x = 0 → planeForm t y = 0 → planeForm x y = 0 := by
  decide

omit [Fintype U] [DecidableEq U] in
private theorem zero_of_proper_plane (C : U →ₗ[F₂] F₂ × F₂) (hc : ¬Function.Surjective C)
    (x y : U) : planeForm (C x) (C y) = 0 := by
  by_contra hn
  have spans : ∀ s t : F₂ × F₂, planeForm s t ≠ 0 → ∀ z : F₂ × F₂,
      ∃ a b : F₂, a • s + b • t = z := by decide
  apply hc
  intro z
  obtain ⟨a,b,he⟩ := spans _ _ hn z
  exact ⟨a • x + b • y, by simpa using he⟩

omit [DecidableEq U] [Fintype U] [DecidableEq V] in
private theorem projected_ranks {Z : Type*} [AddCommGroup Z] [Module F₂ Z]
    (W₀ : Submodule F₂ V) (A : U →ₗ[F₂] V) (P : V →ₗ[F₂] Z) (hz : ∀ v ∈ W₀, P v = 0) :
    Module.finrank F₂ W₀ + Module.finrank F₂ (P.comp A).range ≤
      Module.finrank F₂ (W₀ ⊔ A.range : Submodule F₂ V) := by
  let W := W₀ ⊔ A.range
  let D := P.comp W.subtype
  have h₀ : W₀ ≤ W := le_sup_left
  have hk : W₀.comap W.subtype ≤ D.ker := by
    intro x hx
    exact hz x hx
  have hr : (P.comp A).range ≤ D.range := by
    rintro _ ⟨u,rfl⟩
    exact ⟨⟨A u, (show A.range ≤ W from le_sup_right) (A.mem_range_self u)⟩,rfl⟩
  have h₁ := Submodule.finrank_mono hk
  rw [(Submodule.comapSubtypeEquivOfLe h₀).finrank_eq] at h₁
  have h₂ := Submodule.finrank_mono hr
  have h₃ := D.finrank_range_add_finrank_ker
  change _ ≤ Module.finrank F₂ W
  omega

omit [DecidableEq U] in
private theorem intersect_kernel {Z : Type*} [AddCommGroup Z] [Module F₂ Z]
    (H : Submodule F₂ U) (D : U →ₗ[F₂] Z) :
    Module.finrank F₂ H ≤ Module.finrank F₂ (H ⊓ D.ker : Submodule F₂ U) +
      Module.finrank F₂ D.range := by
  have h₁ := H.finrank_sup_add_finrank_inf_eq D.ker
  have h₂ := (H ⊔ D.ker : Submodule F₂ U).finrank_le
  have h₃ := D.finrank_range_add_finrank_ker
  omega


omit [DecidableEq U] [Fintype ι] [DecidableEq ι] in
private theorem quarter (C : ι → U →ₗ[F₂] F₂ × F₂) (s : Finset ι)
    (hs : ∀ i ∈ s, Function.Surjective (C i)) :
    ∃ a : U, 4 * (s.filter fun i => C i a = 0).card ≤ s.card := by
  classical
  have fibre (i : ι) (hi : i ∈ s) :
      4 * (univ.filter fun a => C i a = 0).card = Fintype.card U := by
    have he : (univ.filter fun a => C i a = 0).card = Fintype.card (C i).ker := by
      symm
      rw [Fintype.card_subtype]
      congr 1
      ext a
      simp [LinearMap.mem_ker]
    rw [he, Module.card_eq_pow_finrank (K := ZMod 2), Module.card_eq_pow_finrank (K := ZMod 2) (V := U)]
    have hd := (C i).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (hs i hi), finrank_top, Module.finrank_prod] at hd
    simp only [Module.finrank_self] at hd
    rw [← hd, pow_add]
    rfl
  obtain ⟨a,_,ha⟩ := exists_le_of_sum_le (s := univ) univ_nonempty
    (f := fun a : U => 4*(s.filter fun i => C i a = 0).card) (g := fun _ => s.card) (by
      apply le_of_eq
      calc
        _ = 4 * ∑ a : U, ∑ i ∈ s, if C i a = 0 then 1 else 0 := by
          simp only [card_filter, mul_sum]
        _ = 4 * ∑ i ∈ s, ∑ a : U, if C i a = 0 then 1 else 0 := by rw [sum_comm]
        _ = ∑ i ∈ s, Fintype.card U := by
          rw [mul_sum]
          apply sum_congr rfl
          intro i hi
          simpa only [sum_boole,Nat.cast_id] using fibre i hi
        _ = ∑ _a : U, s.card := by simp [Nat.mul_comm])
  exact ⟨a,ha⟩

private structure Slice (B : U →ₗ[F₂] U →ₗ[F₂] (ι → F₂)) (C : ι → U →ₗ[F₂] F₂ × F₂)
    (k : ℕ) where
  inputs : Submodule F₂ U
  outputs : Submodule F₂ (ι → F₂)
  remaining : Finset ι
  full : ∀ i ∈ remaining, Function.Surjective (C i)
  free : ∀ w ∈ outputs, ((0 : U),w) ∈ k • vertical B
  untouched : ∀ w ∈ outputs, ∀ i ∈ remaining, w i = 0
  isotropic : ∀ x ∈ inputs, ∀ y ∈ inputs, ∀ i ∉ remaining, B x y i = 0
  dimension : Module.finrank F₂ U ≤ Module.finrank F₂ inputs + Module.finrank F₂ outputs

variable (B : U →ₗ[F₂] U →ₗ[F₂] (ι → F₂)) (C : ι → U →ₗ[F₂] F₂ × F₂)
  (hC : ∀ x y i, B x y i = planeForm (C i x) (C i y))

private noncomputable def initialSlice : Slice B C 0 := by
  classical
  refine ⟨⊤,⊥,univ.filter fun i => Function.Surjective (C i),?_,?_,?_,?_,?_⟩
  · intro i hi; exact (mem_filter.mp hi).2
  · intro w hw; rw [Submodule.mem_bot] at hw; simp [hw]
  · intro w hw; rw [Submodule.mem_bot] at hw; simp [hw]
  · intro x _ y _ i hi
    rw [hC]
    exact zero_of_proper_plane _ (fun h => hi (mem_filter.mpr ⟨mem_univ _,h⟩)) _ _
  · simp

private noncomputable def advance {k : ℕ} (old : Slice B C k) (a : U) : Slice B C (k+1) := by
  classical
  let P : (ι → F₂) →ₗ[F₂] (old.remaining → F₂) := LinearMap.pi fun i => LinearMap.proj i.val
  let D := P.comp (B a)
  refine ⟨old.inputs ⊓ D.ker,old.outputs ⊔ (B a).range,
    old.remaining.filter fun i => C i a = 0,?_,?_,?_,?_,?_⟩
  · intro i hi; exact old.full i (mem_filter.mp hi).1
  · intro w hw
    obtain ⟨v,hv,_,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
    rw [succ_nsmul]
    exact mem_add.mpr ⟨(0,v),old.free _ hv,(0,B a x),
      mem_image.mpr ⟨(a,x),mem_univ _,rfl⟩,Prod.ext (zero_add _) rfl⟩
  · intro w hw i hi
    obtain ⟨v,hv,_,⟨x,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨hi,ha⟩ := mem_filter.mp hi
    change v i + B a x i = 0
    simp [old.untouched v hv i hi,hC,ha,planeForm]
  · intro x hx y hy i hi
    by_cases hi₀ : i ∈ old.remaining
    · have ha : C i a ≠ 0 := fun h => hi (mem_filter.mpr ⟨hi₀,h⟩)
      rw [hC]
      apply common_orthogonal (C i a) _ _ ha
      · rw [← hC]; exact congrFun (show D x = 0 from hx.2) ⟨i,hi₀⟩
      · rw [← hC]; exact congrFun (show D y = 0 from hy.2) ⟨i,hi₀⟩
    · exact old.isotropic x hx.1 y hy.1 i hi₀
  · have h₁ := intersect_kernel old.inputs D
    have h₂ := projected_ranks old.outputs (B a) P
      (fun w hw => funext fun i => old.untouched w hw i.val i.property)
    have h₃ := old.dimension
    change Module.finrank F₂ old.outputs + Module.finrank F₂ D.range ≤ _ at h₂
    omega

include hC

private theorem select_directions (k : ℕ) :
    ∃ st : Slice B C k, 4^k * st.remaining.card ≤ Fintype.card ι := by
  classical
  induction k with
  | zero =>
    refine ⟨initialSlice B C hC,?_⟩
    change 4^0 * (univ.filter fun i => Function.Surjective (C i)).card ≤ Fintype.card ι
    simpa using (card_filter_le (univ : Finset ι) (fun i => Function.Surjective (C i)))
  | succ k ih =>
    obtain ⟨old,hold⟩ := ih
    obtain ⟨a,ha⟩ := quarter C old.remaining old.full
    refine ⟨advance B C hC old a,?_⟩
    rw [pow_succ,mul_assoc]
    exact (Nat.mul_le_mul_left (4^k) ha).trans hold

private theorem finish_slice (f : U → ι → F₂) (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a))
    {k : ℕ} (st : Slice B C k) :
    ∃ (S : Submodule F₂ (U × (ι → F₂))) (t : U × (ι → F₂)),
      (∀ p ∈ S, t+p ∈ (2*k+1) • graph f) ∧
      Module.finrank F₂ U ≤ Module.finrank F₂ S + st.remaining.card := by
  classical
  let Y : U →ₗ[F₂] (st.remaining → F₂) :=
    LinearMap.pi fun i => (LinearMap.fst F₂ F₂ F₂).comp (C i.val)
  let H := st.inputs ⊓ Y.ker
  have hxy (x y : H) : B x.val y.val = 0 := by
    funext i
    by_cases hi : i ∈ st.remaining
    · have hx : (C i x.val).1 = 0 := congrFun (show Y x.val = 0 from x.property.2) ⟨i,hi⟩
      have hy : (C i y.val).1 = 0 := congrFun (show Y y.val = 0 from y.property.2) ⟨i,hi⟩
      simp [hC,planeForm,hx,hy]
    · exact st.isotropic x x.property.1 y y.property.1 i hi
  obtain ⟨S,t,hS,hd⟩ := flat_of_compression f B hf H st.outputs
    (fun x y => by rw [hxy]; exact st.outputs.zero_mem) k (fun w => st.free w w.property)
  refine ⟨S,t,hS,?_⟩
  have h₁ := intersect_kernel st.inputs Y
  change _ ≤ Module.finrank F₂ H + _ at h₁
  have h₂ := Y.range.finrank_le
  rw [Module.finrank_pi, Fintype.card_coe] at h₂
  have h₃ := st.dimension
  omega

/-- For product coordinates, each extra pair of summands cuts the dimension loss
beyond the output dimension by a factor of four. -/
theorem product_coordinate_flat (f : U → ι → F₂)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (k : ℕ) :
    ∃ (S : Submodule F₂ (U × (ι → F₂))) (t : U × (ι → F₂)),
      (∀ p ∈ S, t+p ∈ (2*k+1) • graph f) ∧
      Module.finrank F₂ U ≤ Module.finrank F₂ S + Fintype.card ι / 4^k := by
  obtain ⟨st, hs⟩ := select_directions B C hC k
  obtain ⟨S,t,hS,he⟩ := finish_slice B C hC f hf st
  exact ⟨S,t,hS,he.trans (Nat.add_le_add_left ((Nat.le_div_iff_mul_le (by positivity)).mpr
    (by simpa only [mul_comm st.remaining.card] using hs)) _)⟩

/-- If one direction meets all nonzero coordinate planes, three summands suffice for a flat
of at least the input dimension. -/
theorem threefold_of_transversal (f : U → ι → F₂)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (a : U)
    (ha : ∀ i, Function.Surjective (C i) → C i a ≠ 0) :
    ∃ (S : Submodule F₂ (U × (ι → F₂))) (t : U × (ι → F₂)),
      (∀ p ∈ S, t+p ∈ (3:ℕ) • graph f) ∧ Module.finrank F₂ U ≤ Module.finrank F₂ S := by
  classical
  let st := advance B C hC (initialSlice B C hC) a
  obtain ⟨S,t,hS,hd⟩ := finish_slice B C hC f hf st
  refine ⟨S,t,hS,?_⟩
  have hempty : st.remaining = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    change i ∈ (univ.filter fun i => Function.Surjective (C i)).filter (fun i => C i a = 0) at hi
    obtain ⟨hs,he⟩ := mem_filter.mp hi
    exact ha i (mem_filter.mp hs).2 he
  simpa [hempty] using hd

omit hC

/-- One product of linear forms per coordinate, with arbitrary affine terms. -/
def coordinateProducts (C : ι → U →ₗ[F₂] F₂ × F₂) (L : U →ₗ[F₂] (ι → F₂)) (c : ι → F₂)
    (x : U) (i : ι) : F₂ := (C i x).1 * (C i x).2 + L x i + c i

private def polarProducts (C : ι → U →ₗ[F₂] F₂ × F₂) : U →ₗ[F₂] U →ₗ[F₂] (ι → F₂) :=
  LinearMap.mk₂ F₂ (fun x y i => planeForm (C i x) (C i y))
    (by intro x y z; funext i; simp [planeForm,add_mul]; ring)
    (by intro r x y; funext i; simp [planeForm,smul_eq_mul]; ring)
    (by intro x y z; funext i; simp [planeForm,mul_add]; ring)
    (by intro r x y; funext i; simp [planeForm,smul_eq_mul]; ring)

omit [Fintype U] [DecidableEq U] [Fintype ι] [DecidableEq ι] in
private theorem product_difference (C : ι → U →ₗ[F₂] F₂ × F₂) (L : U →ₗ[F₂] (ι → F₂)) (c : ι → F₂)
    (a x : U) : coordinateProducts C L c x + coordinateProducts C L c (x+a) =
      polarProducts C a x + (coordinateProducts C L c 0 + coordinateProducts C L c a) := by
  funext i
  have ident : ∀ x y : F₂ × F₂, ∀ u v w : F₂,
      (x.1*x.2+u+w) + ((x+y).1*(x+y).2+(u+v)+w) =
        planeForm y x + (w + (y.1*y.2+v+w)) := by decide
  simpa [coordinateProducts,polarProducts] using ident (C i x) (C i a) (L x i) (L a i) (c i)

/-- Five sums of an affine product-coordinate graph contain a flat of codimension
at most d + floor(d/16), where d is the number of output coordinates. -/
theorem fivefold_products (C : ι → U →ₗ[F₂] F₂ × F₂) (L : U →ₗ[F₂] (ι → F₂)) (c : ι → F₂) :
    ∃ (S : Submodule F₂ (U × (ι → F₂))) (t : U × (ι → F₂)),
      (∀ p ∈ S, t+p ∈ (5:ℕ) • graph (coordinateProducts C L c)) ∧
      Module.finrank F₂ (U × (ι → F₂)) ≤ Module.finrank F₂ S + Fintype.card ι + Fintype.card ι / 16 := by
  obtain ⟨S,t,hS,hd⟩ := product_coordinate_flat (polarProducts C) C (fun _ _ _ => rfl)
    _ (product_difference C L c) 2
  refine ⟨S,t,hS,?_⟩
  rw [Module.finrank_prod, Module.finrank_pi]
  change Module.finrank F₂ U ≤ Module.finrank F₂ S + Fintype.card ι / 16 at hd
  omega

/-- Every family of coordinate monomials on the same input cube has an input-dimensional
flat already in three summands. Edges may repeat and may share either endpoint. -/
theorem threefold_monomials {J : Type*} [Fintype J] [DecidableEq J] (u v : ι → J)
    (L : (J → F₂) →ₗ[F₂] (ι → F₂)) (c : ι → F₂) :
    ∃ (S : Submodule F₂ ((J → F₂) × (ι → F₂))) (t : (J → F₂) × (ι → F₂)),
      (∀ p ∈ S, t+p ∈ (3:ℕ) • graph (fun x i => x (u i)*x (v i)+L x i+c i)) ∧
      Fintype.card J ≤ Module.finrank F₂ S := by
  classical
  let C (i : ι) : (J → F₂) →ₗ[F₂] F₂ × F₂ := (LinearMap.proj (u i)).prod (LinearMap.proj (v i))
  obtain ⟨S,t,hS,hd⟩ := threefold_of_transversal (polarProducts C) C (fun _ _ _ => rfl)
    _ (product_difference C L c) (fun _ => 1) (fun i _ h => one_ne_zero (congrArg Prod.fst h))
  exact ⟨S,t,hS,by simpa only [Module.finrank_pi] using hd⟩

/-- The tenfold sumset inherits the fivefold bound under an embedded product graph. -/
theorem tenfold_products {G : Type*} [AddCommGroup G] [Module F₂ G] [DecidableEq G]
    (A : Finset G) (e : (U × (ι → F₂)) ≃ₗ[F₂] G) (C : ι → U →ₗ[F₂] F₂ × F₂)
    (L : U →ₗ[F₂] (ι → F₂)) (c : ι → F₂) (hg : (graph (coordinateProducts C L c)).image e ⊆ A+A) :
    ∃ (W : Submodule F₂ G) (t : G), t +ᵥ (W : Set G) ⊆ (↑((10:ℕ) • A) : Set G) ∧
      Module.finrank F₂ G ≤ Module.finrank F₂ W + Fintype.card ι + Fintype.card ι / 16 := by
  classical
  obtain ⟨S,t,hS,hd⟩ := fivefold_products C L c
  have embed : ((5:ℕ) • graph (coordinateProducts C L c)).image e ⊆ (10:ℕ) • A := by
    rw [image_nsmul]
    simpa only [← two_nsmul, ← mul_smul, show (5:ℕ)*2=10 by decide] using
      (nsmul_subset_nsmul_left (n := 5) hg)
  refine ⟨S.map e.toLinearMap,e t,?_,?_⟩
  · rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
    apply embed
    change e t + e w ∈ _
    rw [← map_add]
    exact mem_image_of_mem _ (hS w hw)
  · rw [← e.finrank_eq, ← (S.equivMapOfInjective e.toLinearMap e.injective).finrank_eq]
    exact hd


end Green50ProductFlats

#print axioms Green50ProductFlats.product_coordinate_flat
#print axioms Green50ProductFlats.threefold_of_transversal
#print axioms Green50ProductFlats.fivefold_products
#print axioms Green50ProductFlats.threefold_monomials
#print axioms Green50ProductFlats.tenfold_products
