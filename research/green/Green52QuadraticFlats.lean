import Green50QuadraticFlats
import Green52Complements
import Green52AffineDerivatives

/-! # Quadratic bounds for twofold sums -/

open Finset
open scoped Pointwise
namespace Green52QuadraticFlats
local notation "K" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module K U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

omit [DecidableEq U] [DecidableEq V] in
/-- Freeze a right inverse at a direction of maximum rank. On the resulting affine
space every directional map has the same image. -/
theorem fixed_image (B : U →ₗ[K] U →ₗ[K] V) :
    ∃ (a : U) (H : Submodule K U) (W : Submodule K V),
      (∀ h : H, (B (a+h.val)).range = W) ∧
      (∀ h : H, ∀ x, B h.val x ∈ W) ∧
      Module.finrank K U ≤ Module.finrank K H + Module.finrank K W * Module.finrank K V := by
  classical
  obtain ⟨a,_,hmax⟩ := exists_max_image (univ : Finset U)
    (fun a => Module.finrank K (B a).range) univ_nonempty
  let W := (B a).range
  obtain ⟨j,hj⟩ := (B a).rangeRestrict.exists_rightInverse_of_surjective (B a).range_rangeRestrict
  have ident (w : W) : B a (j w) = w.val := congrArg Subtype.val (LinearMap.congr_fun hj w)
  let Q : U →ₗ[K] (W →ₗ[K] V) :=
    { toFun := fun h => (B h).comp j
      map_add' := by intro x y; ext w; simp
      map_smul' := by intro c x; ext w; simp }
  have same (h : Q.ker) : (B (a+h.val)).range = W := by
    symm
    apply Submodule.eq_of_le_of_finrank_le _ (hmax _ (mem_univ _))
    intro w hw
    let v : W := ⟨w,hw⟩
    refine ⟨j v,?_⟩
    have zero : B h.val (j v)=0 := LinearMap.congr_fun (show Q h.val=0 from h.property) v
    simpa only [map_add,LinearMap.add_apply,zero,add_zero] using ident v
  refine ⟨a,Q.ker,W,same,?_,?_⟩
  · intro h x
    have h₁ : B (a+h.val) x ∈ W := (same h).le (LinearMap.mem_range_self _ _)
    have h₂ : B a x ∈ W := LinearMap.mem_range_self _ _
    simpa only [map_add,LinearMap.add_apply,add_sub_cancel_left] using W.sub_mem h₁ h₂
  · have he := Q.finrank_range_add_finrank_ker
    have hd := Submodule.finrank_le Q.range
    rw [Module.finrank_linearMap] at hd
    omega

/-- For a d-dimensional output, two sums of a quadratic graph contain an affine
flat of codimension at most d squared. -/
theorem twofold_quadratic_square (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x+f (x+a)=B a x+(f 0+f a)) :
    ∃ (T : Submodule K (U × V)) (v : U × V),
      (∀ p ∈ T, v+p ∈ (2:ℕ) • Green50QuadraticGraphs.graph f) ∧
      Module.finrank K (U × V) ≤ Module.finrank K T + (Module.finrank K V)^2 := by
  classical
  obtain ⟨a,H,W,same,img,dim⟩ := fixed_image B
  let L := Green50QuadraticFlats.quotientSlope f B hf H W (fun x y => img x y)
  obtain ⟨T,hT,hsize⟩ := Green50QuadraticFlats.graph_lift H W L
  refine ⟨T,(a,f 0+f a),?_,?_⟩
  · rintro ⟨u,b⟩ hp
    obtain ⟨h,e,eq⟩ := hT _ hp
    change u=h.val at e
    subst u
    change W.mkQ b = W.mkQ (f h.val+f 0) at eq
    have hm : b - (f h.val+f 0) ∈ W := (Submodule.Quotient.eq W).mp eq
    have hb := hf h.val a
    have hi := img h a
    have hz : f 0+f a+b-(f 0+f (a+h.val)) ∈ W := by
      convert W.sub_mem hm hi using 1
      have ht (y : V) : y+y=0 := by rw [←two_smul K,show (2:K)=0 by decide,zero_smul]
      have hj : f (a+h.val) = B h.val a + (f 0+f h.val) - f a := by
        rw [←hb]; abel
      rw [hj]
      abel_nf
      rw [two_smul ℤ (f a),ht,zero_add]
    rw [←same h] at hz
    obtain ⟨x,hx⟩ := hz
    apply (Green50QuadraticGraphs.twofold_fibre _ _ _).mpr
    exact ⟨x,(hf (a+h.val) x).trans (add_eq_of_eq_sub hx)⟩
  · have le := Submodule.finrank_le W
    rw [Module.finrank_prod,hsize]
    cases hd : Module.finrank K V with
    | zero => simp [hd] at dim ⊢; omega
    | succ d =>
      have m := Nat.mul_le_mul_right d (show Module.finrank K W ≤ d+1 by omega)
      rw [hd] at dim
      nlinarith

section Embedded

open scoped Classical
open Green52Complements

private theorem embedded_flat {n c : ℕ} (A : Set (Cube n)) (U V : Submodule K (Cube n))
    (hc : IsCompl U V) (f : U → V) (hA : (Green50Graphs.graph U V f : Set (Cube n)) ⊆ A)
    (T : Submodule K (U × V)) (v : U × V)
    (hT : ∀ p ∈ T, v+p ∈ (2:ℕ) • Green50QuadraticGraphs.graph f)
    (hd : Module.finrank K (U × V) ≤ Module.finrank K T + c) : Flat n c A := by
  classical
  let e := U.prodEquivOfIsCompl V hc
  let W := T.map e.toLinearMap
  have eg : (Green50QuadraticGraphs.graph f).image e = Green50Graphs.graph U V f := by
    rw [Green50QuadraticGraphs.graph,Green50Graphs.graph,image_image]
    rfl
  refine ⟨AffineSubspace.mk' (e v) W,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,he⟩ := (AffineSubspace.mem_mk'.mp hx : x-e v ∈ W)
    change e p = x-e v at he
    have hsum := mem_image_of_mem e (hT p hp)
    rw [image_nsmul e,eg,two_nsmul] at hsum
    have hx' : e (v+p)=x := by rw [map_add,he]; abel
    rw [hx'] at hsum
    obtain ⟨y,hy,z,hz,h⟩ := mem_add.mp hsum
    exact ⟨y,hA hy,z,hA hz,h⟩
  · rw [AffineSubspace.direction_mk',← (T.equivMapOfInjective e.toLinearMap e.injective).finrank_eq]
    have en : Module.finrank K (U × V) = n := by simpa [Cube] using e.finrank_eq
    simpa only [en] using hd

/-- Green 52 for any set containing a quadratic transversal, with the better of
the bounds from scalar projections and a maximum-rank direction. -/
theorem quadratic_transversal_green52 {n : ℕ} (A : Set (Cube n)) (U V : Submodule K (Cube n))
    (hc : IsCompl U V) (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x+f (x+a)=B a x+(f 0+f a))
    (hA : (Green50Graphs.graph U V f : Set (Cube n)) ⊆ A) :
    Flat n (min (Nat.card V-1) ((Module.finrank K V)^2)) A := by
  classical
  by_cases hh : Nat.card V-1 ≤ (Module.finrank K V)^2
  · rw [min_eq_left hh,Nat.card_eq_fintype_card]
    obtain ⟨T,ht,hd⟩ := Green52AffineDerivatives.twofold_quadratic f B hf
    exact embedded_flat A U V hc f hA T 0 (fun p hp => by rw [zero_add]; exact ht hp) hd
  · rw [min_eq_right (le_of_not_ge hh)]
    obtain ⟨T,v,ht,hd⟩ := twofold_quadratic_square f B hf
    exact embedded_flat A U V hc f hA T v ht hd

end Embedded

end Green52QuadraticFlats

#print axioms Green52QuadraticFlats.fixed_image
#print axioms Green52QuadraticFlats.twofold_quadratic_square
#print axioms Green52QuadraticFlats.quadratic_transversal_green52
