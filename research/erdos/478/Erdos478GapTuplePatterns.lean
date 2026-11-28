import Erdos478JointGapRootOrbits
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Equality patterns of factorial gap roots with single and double coordinates -/

namespace Erdos478.GapPatterns
open Polynomial Finset Function BinaryGap
open scoped Classical
noncomputable section

abbrev FieldOfRoots := AlgebraicClosure ℚ
abbrev R (l : Nat.Primes) := (rationalGap l.val).rootSet FieldOfRoots

/-- The two rational algebra instances on the algebraic closure agree. -/
theorem normal_fieldOfRoots : Normal ℚ FieldOfRoots := by
  let A := @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ)
  have hn : @Normal ℚ FieldOfRoots _ _ A := @IsAlgClosure.normal ℚ _ _ _ A (AlgebraicClosure.instIsAlgClosure ℚ)
  have he : A=(inferInstance : Algebra ℚ FieldOfRoots) := Subsingleton.elim _ _
  exact (congrArg (fun B => @Normal ℚ FieldOfRoots _ _ B) he).mp hn

/-- Transport the simultaneous action to any injective indexing of the lengths. -/
private theorem joint {I : Type*} [Fintype I] (l : I → Nat.Primes)
    (inj : Injective l) (good : ∀ i, broad (l i).val ∧ 3<(l i).val)
    (a b c d : (i : I) → R (l i)) (eq : ∀ i, a i=b i ↔ c i=d i) :
    ∃ σ : FieldOfRoots ≃ₐ[ℚ] FieldOfRoots, ∀ i,
      σ (a i : FieldOfRoots)=c i ∧ σ (b i : FieldOfRoots)=d i := by
  let : Normal ℚ FieldOfRoots := normal_fieldOfRoots
  let n (i : I) := (l i).val
  have ni : Injective n := Subtype.val_injective.comp inj
  let ext (v : (i : I) → R (l i)) := extend n (fun i => (v i : FieldOfRoots)) 0
  have hx (v : (i : I) → R (l i)) (i : I) : ext v (n i)=(v i : FieldOfRoots) :=
    ni.extend_apply _ _ _
  obtain ⟨σ,hσ⟩ := joint_gap_pairs FieldOfRoots (univ.image n) (ext a) (ext b) (ext c) (ext d) (by
    intro j hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp hj
    exact ⟨(l i).prop,(good i).1,(good i).2,IsAlgClosed.splits _⟩) (by
    intro j hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp hj
    simp only [hx]
    exact ⟨(a i).prop,(b i).prop,(c i).prop,(d i).prop,by simpa only [Subtype.ext_iff] using eq i⟩)
  exact ⟨σ,fun i => by simpa only [hx] using hσ (n i) (mem_image_of_mem _ (mem_univ i))⟩

variable (S T : Finset Nat.Primes)
def lengthAt : S ⊕ T → Nat.Primes := Sum.elim Subtype.val Subtype.val
abbrev Tuple := (i : S ⊕ T) → R (lengthAt S T i)
variable {S T} (sub : T⊆S)

def label (u : Tuple S T) : Finset T :=
  univ.filter fun j => (u (.inl ⟨j.val,sub j.prop⟩) : FieldOfRoots)=u (.inr j)

private theorem mem_label (u : Tuple S T) (j : T) :
    j∈label sub u ↔ (u (.inl ⟨j.val,sub j.prop⟩) : FieldOfRoots)=u (.inr j) := by
  simp [label]

theorem label_onto (good : ∀ l∈S, 3<l.val) : Surjective (label sub) := by
  intro D
  have distinct (i : S) : ∃ a b : R i.val, a≠b := by
    have hn := gap_card FieldOfRoots i.val.prop (IsAlgClosed.splits _)
    change Fintype.card (R i.val)=i.val.val at hn
    have hg := good i.val i.prop
    have : Nontrivial (R i.val) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_pair_ne _
  choose a b hab using distinct
  let u : Tuple S T := fun i => match i with
    | .inl j => a j
    | .inr j => if j∈D then a ⟨_,sub j.prop⟩ else b ⟨_,sub j.prop⟩
  refine ⟨u,Finset.ext fun j => ?_⟩
  rw [mem_label]
  by_cases hj : j∈D
  · simp [u,hj]
  · simpa [u,hj] using (Subtype.coe_injective.ne (hab ⟨j.val,sub j.prop⟩))

theorem label_orbit (good : ∀ l∈S, broad l.val ∧ 3<l.val) (u v : Tuple S T) :
    label sub u=label sub v ↔ ∃ σ : FieldOfRoots ≃ₐ[ℚ] FieldOfRoots,
      ∀ i, σ (u i : FieldOfRoots)=v i := by
  constructor
  · intro he
    let aux (w : Tuple S T) (i : S) : R i.val :=
      if h : i.val∈T then w (.inr ⟨i.val,h⟩) else w (.inl i)
    have yes (w : Tuple S T) (i : S) (hi : i.val∈T) : aux w i=w (.inr ⟨i.val,hi⟩) := dif_pos hi
    have no (w : Tuple S T) (i : S) (hi : i.val∉T) : aux w i=w (.inl i) := dif_neg hi
    obtain ⟨σ,hσ⟩ := joint (fun i : S => i.val) Subtype.val_injective (fun i => good i.val i.prop)
      (fun i => u (.inl i)) (aux u) (fun i => v (.inl i)) (aux v) (by
        intro i
        by_cases hi : i.val∈T
        · let j : T := ⟨i.val,hi⟩
          have h := Finset.ext_iff.mp he j
          rw [mem_label,mem_label] at h
          rw [yes u i hi,yes v i hi]
          exact Subtype.ext_iff.trans (h.trans Subtype.ext_iff.symm)
        · rw [no u i hi,no v i hi]
          exact ⟨fun _ => rfl,fun _ => rfl⟩)
    refine ⟨σ,fun i => ?_⟩
    cases i with
    | inl i => exact (hσ i).1
    | inr j =>
      have hh := (hσ ⟨j.val,sub j.prop⟩).2
      rw [yes u _ j.prop,yes v _ j.prop] at hh
      exact hh
  · rintro ⟨σ,hσ⟩
    ext j
    rw [mem_label,mem_label,← hσ,← hσ,σ.injective.eq_iff]

#print axioms normal_fieldOfRoots
#print axioms lengthAt
#print axioms Tuple
#print axioms label
#print axioms label_onto
#print axioms label_orbit
end
end Erdos478.GapPatterns
