import Green50QuadraticFlats

/-! # Mean rank and common isotropic subspaces

In a finite linear family of alternating forms, cutting to the kernel of a nonzero form
loses at most twice the drop in mean rank. Iterating gives a common isotropic subspace.
-/

open Finset
open scoped Pointwise
namespace Green50QuadraticRankDescent
open Green50QuadraticGraphs Green50QuadraticFibres Green50QuadraticFlats
local notation "F₂" => ZMod 2

section Rank
variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

private theorem quotient_dimension (S T : Submodule K V) :
    Module.finrank K (S.map T.mkQ) + Module.finrank K (S ⊓ T : Submodule K V) =
      Module.finrank K S := by
  let D := T.mkQ.comp S.subtype
  have hr : D.range = S.map T.mkQ := by
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have hk : D.ker = (S ⊓ T : Submodule K V).comap S.subtype := by
    ext x
    simp [D,LinearMap.mem_ker,Submodule.Quotient.mk_eq_zero]
  have he := D.finrank_range_add_finrank_ker
  rwa [hr,hk,(Submodule.comapSubtypeEquivOfLe (inf_le_left : S ⊓ T ≤ S)).finrank_eq] at he

/-- The ranks of X and A+X pay for the rank of A and twice the rank induced from
the kernel of A to its cokernel. -/
theorem kernel_cokernel_rank (A X : U →ₗ[K] V) :
    Module.finrank K A.range + 2 * Module.finrank K (A.range.mkQ.comp (X.comp A.ker.subtype)).range ≤
      Module.finrank K X.range + Module.finrank K (A+X).range := by
  let Z := A.ker.map X
  have zx : Z ≤ X.range := by
    rintro _ ⟨u,_,rfl⟩
    exact X.mem_range_self u
  have zy : Z ≤ (A+X).range := by
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,by simp [show A u = 0 from hu]⟩
  have aw : A.range ≤ (A+X).range ⊔ X.range := by
    rintro _ ⟨u,rfl⟩
    have h₁ := (show (A+X).range ≤ (A+X).range ⊔ X.range from le_sup_left) ((A+X).mem_range_self u)
    have h₂ := (show X.range ≤ (A+X).range ⊔ X.range from le_sup_right) (X.mem_range_self u)
    simpa using Submodule.sub_mem _ h₁ h₂
  have upper := Submodule.finrank_mono (sup_le aw (zx.trans (le_sup_right : X.range ≤ (A+X).range ⊔ X.range)))
  have lower := Submodule.finrank_mono (le_inf zy zx)
  have dims := (A+X).range.finrank_sup_add_finrank_inf_eq X.range
  have dims' := A.range.finrank_sup_add_finrank_inf_eq Z
  have q := quotient_dimension Z A.range
  rw [inf_comm] at q
  have zbound := Submodule.finrank_map_le A.range.mkQ Z
  rw [LinearMap.range_comp,LinearMap.range_comp,Submodule.range_subtype]
  change Module.finrank K A.range + 2 * Module.finrank K (Z.map A.range.mkQ) ≤ _
  omega
end Rank

section Scalar
universe uK uU uL
variable {K : Type uK} [Field K] {U : Type uU} [AddCommGroup U] [Module K U]
  [Module.Finite K U] {L : Type uL} [AddCommGroup L] [Module K L]

private def restrictFamily (Q : L →ₗ[K] LinearMap.BilinForm K U) (H : Submodule K U) :
    L →ₗ[K] LinearMap.BilinForm K H :=
  { toFun := fun t => (Q t).restrict H
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

private theorem restrict_pair (Q : L →ₗ[K] LinearMap.BilinForm K U) (a : L)
    (alt : (Q a).IsAlt) (x : L) :
    Module.finrank K (Q a).range + 2*Module.finrank K ((Q x).restrict (Q a).ker).range ≤
      Module.finrank K (Q x).range + Module.finrank K (Q (a+x)).range := by
  let A := Q a
  let H := A.ker
  let X := Q x
  let R := A.range.mkQ.comp (LinearMap.comp X H.subtype)
  have hz : A.range ≤ H.subtype.dualMap.ker := by
    rintro _ ⟨u,rfl⟩
    apply LinearMap.ext
    intro y
    change A u y.val = 0
    apply alt.eq_iff.mp
    exact LinearMap.congr_fun (show A y.val = 0 from y.property) u
  let F := A.range.liftQ H.subtype.dualMap hz
  have hr : X.restrict H = F.comp R := by ext; rfl
  have h := kernel_cokernel_rank A X
  rw [Q.map_add]
  change Module.finrank K A.range + 2*Module.finrank K (X.restrict H).range ≤ _
  rw [hr,LinearMap.range_comp]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Submodule.finrank_map_le F R.range)) _).trans h

private theorem mean_isotropic_aux [Fintype L] (N : ℕ) :
    ∀ {U : Type uU} [AddCommGroup U] [Module K U] [Module.Finite K U]
      (Q : L →ₗ[K] LinearMap.BilinForm K U), Module.finrank K U ≤ N → (∀ a, (Q a).IsAlt) →
      ∃ H : Submodule K U, (∀ z, ∀ x ∈ H, ∀ y ∈ H, Q z x y = 0) ∧
        (Module.finrank K U - Module.finrank K H)*Fintype.card L ≤ 2*∑ z, Module.finrank K (Q z).range := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro U _ _ _ Q hn alt
    classical
    by_cases hz : ∀ a, Q a = 0
    · exact ⟨⊤,fun z _ _ _ _ => by simp [hz z],by simp⟩
    · obtain ⟨a,ha⟩ := not_forall.mp hz
      let A := Q a
      let H := A.ker
      let r := Module.finrank K A.range
      have hpos : 0 < r := Nat.pos_of_ne_zero fun h => ha
        (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
      have dimA := A.finrank_range_add_finrank_ker
      change r + Module.finrank K H = Module.finrank K U at dimA
      let F := restrictFamily Q H
      obtain ⟨S,hiso,hs⟩ := ih (Module.finrank K H) (by omega) F (by rfl)
        (fun z x => alt z x.val)
      let full (z : L) := Module.finrank K (Q z).range
      let small (z : L) := Module.finrank K (F z).range
      have pair : ∑ z : L, (r + 2 * small z) ≤ ∑ z : L, (full z + full (a+z)) :=
        sum_le_sum (fun z _ => restrict_pair Q a (alt a) z)
      rw [sum_add_distrib,sum_add_distrib,← mul_sum] at pair
      have shift : (∑ z : L, full (a+z)) = ∑ z : L, full z := Equiv.sum_comp (Equiv.addLeft a) full
      rw [shift,sum_const,card_univ,nsmul_eq_mul] at pair
      refine ⟨S.map H.subtype,?_,?_⟩
      · rintro z _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
        exact hiso z x hx y hy
      · rw [← (S.equivMapOfInjective H.subtype Subtype.val_injective).finrank_eq]
        have dimS := S.finrank_le
        have heq : Module.finrank K U - Module.finrank K S =
            r + (Module.finrank K H - Module.finrank K S) := by omega
        rw [heq,Nat.add_mul]
        change _ ≤ 2 * ∑ z : L, full z
        change _ ≤ 2 * ∑ z : L, small z at hs
        change Fintype.card L * r + 2*(∑ z, small z) ≤ (∑ z, full z) + (∑ z, full z) at pair
        rw [Nat.mul_comm r]
        omega

/-- In a finite additive family of alternating forms there is a common totally isotropic
subspace with codimension at most twice the mean rank. This count uses no field-size bound. -/
theorem common_isotropic_mean [Fintype L] (Q : L →ₗ[K] LinearMap.BilinForm K U)
    (alt : ∀ z, (Q z).IsAlt) :
    ∃ H : Submodule K U, (∀ z, ∀ x ∈ H, ∀ y ∈ H, Q z x y = 0) ∧
      (Module.finrank K U - Module.finrank K H)*Fintype.card L ≤ 2*∑ z, Module.finrank K (Q z).range :=
  mean_isotropic_aux (Module.finrank K U) Q le_rfl alt

end Scalar

end Green50QuadraticRankDescent
#print axioms Green50QuadraticRankDescent.kernel_cokernel_rank

#print axioms Green50QuadraticRankDescent.common_isotropic_mean
