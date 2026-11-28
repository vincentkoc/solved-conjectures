import Green50QuadraticFibres

/-! # Affine flats in sums of binary quadratic graphs

An input subspace on which the polarization takes values in an attainable vertical space
gives a flat in the corresponding odd sumset. Its dimension is the sum of the two dimensions.
-/

open Finset
open scoped Pointwise
namespace Green50QuadraticFlats
open Green50QuadraticGraphs Green50QuadraticFibres
local notation "K" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module K U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

private theorem twice {X : Type*} [AddCommGroup X] [Module K X] (x : X) : x+x=0 := by
  rw [← two_smul K x, show (2:K)=0 by decide, zero_smul]

/-- On an isotropic input subspace, subtracting the value at zero makes the quotient map linear. -/
noncomputable def quotientSlope (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (H : Submodule K U) (W : Submodule K V)
    (hiso : ∀ x y : H, B x.val y.val ∈ W) : H →ₗ[K] V ⧸ W :=
    { toFun := fun x => W.mkQ (f x.val+f 0)
      map_add' := by
        intro x a
        have he := congrArg W.mkQ (hf a.val x.val)
        simp only [map_add, show W.mkQ (B a.val x.val)=0 from (Submodule.Quotient.mk_eq_zero W).mpr
          (hiso a x), zero_add] at he
        have he' := congrArg (fun q => W.mkQ (f x.val)+q) he
        rw [← add_assoc,twice,zero_add] at he'
        simp only [Submodule.coe_add,map_add,he']
        abel
      map_smul' := by
        intro c x
        rcases (show ∀ z : K, z=0 ∨ z=1 from by decide) c with rfl | rfl <;> simp [twice] }

omit [DecidableEq U] [DecidableEq V] in
/-- The inverse image of a linear graph modulo the output subspace has dimension
equal to the input dimension plus the dimension of that output subspace. -/
theorem graph_lift (H : Submodule K U) (W : Submodule K V) (L : H →ₗ[K] V ⧸ W) :
    ∃ S : Submodule K (U × V),
      (∀ p ∈ S, ∃ x : H, p.1 = x.val ∧ W.mkQ p.2 = L x) ∧
      Module.finrank K S = Module.finrank K H + Module.finrank K W := by
  classical
  let P := W.mkQ.comp (LinearMap.snd K H V) - L.comp (LinearMap.fst K H V)
  have sur : Function.Surjective P := by
    intro q
    obtain ⟨v,rfl⟩ := W.mkQ_surjective q
    exact ⟨(0,v), by simp [P]⟩
  let e := H.subtype.prodMap (LinearMap.id (R:=K) (M:=V))
  have inj : Function.Injective e :=
    fun x y h => Prod.ext (Subtype.ext (congrArg (fun z : U × V => z.1) h))
      (congrArg (fun z : U × V => z.2) h)
  refine ⟨P.ker.map e,?_,?_⟩
  · rintro _ ⟨⟨x,v⟩,h,rfl⟩
    exact ⟨x,rfl,sub_eq_zero.mp (show W.mkQ v - L x = 0 from h)⟩
  · rw [← (P.ker.equivMapOfInjective e inj).finrank_eq]
    have h := P.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr sur, finrank_top,Module.finrank_prod] at h
    have := W.finrank_quotient_add_finrank
    omega

/-- An isotropic input subspace modulo attainable vertical outputs gives an affine flat
whose dimension is the sum of the two dimensions. -/
theorem flat_of_compression (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (H : Submodule K U) (W : Submodule K V)
    (hiso : ∀ x y : H, B x.val y.val ∈ W) (k : ℕ)
    (hw : ∀ w : W, ((0:U),w.val) ∈ k • vertical B) :
    ∃ (S : Submodule K (U × V)) (t : U × V),
      (∀ p ∈ S, t+p ∈ (2*k+1) • graph f) ∧
      Module.finrank K S = Module.finrank K H + Module.finrank K W := by
  classical
  obtain ⟨S,hS,hd⟩ := graph_lift H W (quotientSlope f B hf H W hiso)
  refine ⟨S,(0,f 0),?_,hd⟩
  rintro ⟨u,v⟩ hp
  obtain ⟨x,hx,eq⟩ := hS _ hp
  change u = x.val at hx
  subst u
  change W.mkQ v = W.mkQ (f x.val+f 0) at eq
  let w : W := ⟨v-(f x.val+f 0),(Submodule.Quotient.eq W).mp eq⟩
  rw [odd_sumset f B hf]
  apply mem_add.mpr
  refine ⟨(x.val,f x.val),mem_image_of_mem _ (mem_univ _),(0,w.val),hw w,Prod.ext ?_ ?_⟩
  · change x.val+0=0+x.val; simp
  · change f x.val + (v-(f x.val+f 0)) = f 0+v
    calc
      _ = v - f 0 := by abel
      _ = _ := sub_eq_iff_eq_add.mpr (by rw [add_right_comm,twice,zero_add])

end Green50QuadraticFlats

#print axioms Green50QuadraticFlats.graph_lift
#print axioms Green50QuadraticFlats.flat_of_compression
