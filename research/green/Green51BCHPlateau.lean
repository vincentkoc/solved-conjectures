import Green51BCHCompression
import Green51LocalFlats

/-! # Sparse affine plateau for Green 51 from a projected BCH coordinate -/

open Green50Downsets Green51BCH
open scoped Pointwise
namespace Green51BCHCompression
local notation "F" => ZMod 2

open Finset in
/-- Transport the projected curve and its double along a binary linear equivalence. -/
theorem transport_dimension {K H : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
    [AddCommGroup H] [Module F H] {n d : ℕ} (L : K →ₗ[F] H)
    (E : (Space K × H) ≃ₗ[F] Cube n)
    (avoid : ∀ (p : Space K × H) (W : Submodule F (Space K × H)),
      p+ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L) → Module.finrank F W≤d) :
    ∃ A : Finset (Cube n), A.card=Fintype.card K ∧
      ∀ (W : Submodule F (Cube n)) (p : Cube n),p+ᵥ (W:Set (Cube n)) ⊆ ↑(A+A) → Module.finrank F W≤d := by
  classical
  let v := fun x : K => E (lifted L x)
  let A := univ.image v
  have iv : Function.Injective v := fun x y eq => congrArg (fun z : Space K × H => z.1.1) (E.injective eq)
  refine ⟨A,(Finset.card_image_of_injective _ iv).trans Finset.card_univ,?_⟩
  intro W p within
  let V := W.comap E.toLinearMap
  have eq : V.map E.toLinearMap=W := Submodule.map_comap_eq_self (by rw [E.range];exact le_top)
  have rank := (V.equivMapOfInjective E.toLinearMap E.injective).finrank_eq
  rw [eq] at rank
  rw [←rank]
  apply avoid (E.symm p)
  rintro _ ⟨w,hw,rfl⟩
  have pre : p+E w∈A+A := within ⟨E w,hw,rfl⟩
  obtain ⟨_,ha,_,hb,sum⟩ := Finset.mem_add.mp pre
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
  refine ⟨_,⟨a,rfl⟩,_,⟨b,rfl⟩,E.injective ?_⟩
  change E (lifted L a+lifted L b)=E (E.symm p+w)
  rwa [map_add,map_add,LinearEquiv.apply_symm_apply]

open Finset in
/-- Transport the projected curve and its double along a binary linear equivalence. -/
theorem transport_curve {K H : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
    [AddCommGroup H] [Module F H] {n : ℕ} (L : K →ₗ[F] H)
    (E : (Space K × H) ≃ₗ[F] Cube n)
    (avoid : ∀ (p : Space K × H) (W : Submodule F (Space K × H)),
      p+ᵥ (W:Set (Space K × H)) ⊆ Set.range (lifted L)+Set.range (lifted L) → Module.finrank F W≤2) :
    ∃ A : Finset (Cube n), A.card=Fintype.card K ∧
      ∀ (W : Submodule F (Cube n)) (p : Cube n),p+ᵥ (W:Set (Cube n)) ⊆ ↑(A+A) → Module.finrank F W≤2 := transport_dimension L E avoid

open Finset in
/-- Two bits of the fourth BCH coordinate may be omitted. -/
theorem affine_examples (n : ℕ) (hn : 6≤n) :
    ∃ A : Finset (Cube n), A.card=2^((n+2)/4) ∧
      ∀ (W : Submodule F (Cube n)) (p : Cube n),
        p +ᵥ (W:Set (Cube n)) ⊆ ↑(A+A) → Module.finrank F W≤2 := by
  classical
  let m := (n+2)/4
  have hm : 2 ≤ m := by dsimp [m];omega
  let K := GaloisField 2 m
  let _ : Fintype K := Fintype.ofFinite K
  have dim : Module.finrank F K=m := GaloisField.finrank 2 (by omega)
  obtain ⟨j,inj⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank F (Cube 2) ≤ Module.finrank F K by simpa [Cube,dim] using hm)
  let U := j.range
  have two : Module.finrank F U=2 := by simpa [Cube] using j.finrank_range_of_inj inj
  let extra := n-(4*m-2)
  let H := (K ⧸ U) × Cube extra
  let L : K →ₗ[F] H := U.mkQ.prod 0
  have small : Module.finrank F L.ker≤2 := by
    have sub : L.ker≤U := by
      intro x hx
      have eq : U.mkQ x=0 := congrArg Prod.fst (show L x=0 from hx)
      exact (Submodule.Quotient.mk_eq_zero U).mp eq
    exact (Submodule.finrank_mono sub).trans two.le
  have rest := U.finrank_quotient_add_finrank
  rw [two,dim] at rest
  let E : (Space K × H) ≃ₗ[F] Cube n := LinearEquiv.ofFinrankEq _ _ (by
    simp only [Space,H,Cube,Module.finrank_prod,Module.finrank_fin_fun,dim]
    dsimp only [extra,m] at ⊢
    dsimp only [m] at rest
    omega)
  obtain ⟨A,card,avoid⟩ := transport_curve L E (excludes_three L small)
  exact ⟨A,card.trans (by rw [←Nat.card_eq_fintype_card];exact GaloisField.card 2 m (by omega)),avoid⟩

open Finset Green51SparseBounds Green51LocalFlats in
/-- A finite example excluding three-spaces certifies the affine two-dimensional plateau. -/
theorem plateau_of_example {n : ℕ} {α : ℝ} (A : Finset (Cube n))
    (avoid : ∀ (W : Submodule F (Cube n)) (p : Cube n),
      p+ᵥ (W:Set (Cube n)) ⊆ ↑(A+A) → Module.finrank F W≤2)
    (lo : 2/(2:ℝ)^n<α) (hi : α≤(A.card:ℝ)/2^n) :
    Green51.guaranteedMaxCosetDim n α=2 := by
  classical
  have admitted : α≤(A.dens:ℝ) := by
    rw [nnratCast_dens]
    simpa [Cube] using hi
  have upper : Green51.guaranteedMaxCosetDim n α ≤ maxCosetDim F (𝔽₂ n) ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,admitted,rfl⟩
  apply le_antisymm (upper.trans ?_) (two_above_two_points (admitted.trans (by exact_mod_cast A.dens_le_one)) lo)
  by_contra! big
  obtain ⟨W,p,rank,sub⟩ := (le_iff_coset (by decide : 0<3) _).mp big
  exact (by decide : ¬ 3 ≤ 2) (rank ▸ avoid W p sub)


open Finset Green51SparseBounds Green51LocalFlats in
/-- The pinned affine guarantee is two throughout the enlarged density interval. -/
theorem plateau {n : ℕ} (hn : 6≤n) {α : ℝ}
    (lo : 2/(2:ℝ)^n<α) (hi : α≤(2:ℝ)^((n+2)/4)/2^n) :
    Green51.guaranteedMaxCosetDim n α=2 := by
  classical
  obtain ⟨A,sz,avoid⟩ := Green51BCHCompression.affine_examples n hn
  apply plateau_of_example A avoid lo
  simpa [sz] using hi

end Green51BCHCompression
#print axioms Green51BCHCompression.transport_dimension
#print axioms Green51BCHCompression.transport_curve
#print axioms Green51BCHCompression.plateau_of_example
#print axioms Green51BCHCompression.affine_examples
#print axioms Green51BCHCompression.plateau
