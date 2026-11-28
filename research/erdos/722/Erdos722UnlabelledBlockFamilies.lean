import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Counting unlabelled block families

An isomorphism can be any permutation of the ground set. In particular it
need preserve neither a distinguished projection nor its two-point fibres.
-/

namespace Erdos722.QuadSwitch
open Finset
variable {V : Type*}

/-- Isomorphism by an arbitrary bijection of the labelled point set. -/
def Isomorphic (D E : Finset (Finset V)) : Prop :=
  ∃ e : Equiv.Perm V, e.finsetCongr.finsetCongr D = E

private def relabellings (F : Finset (Finset (Finset V))) : Setoid F where
  r D E := Isomorphic D.val E.val
  iseqv := {
    refl := fun D => ⟨Equiv.refl _,by simp⟩
    symm := by
      rintro D E ⟨e,he⟩
      exact ⟨e.symm, he ▸ e.finsetCongr.finsetCongr.symm_apply_apply D.val⟩
    trans := by
      rintro D E G ⟨e,he⟩ ⟨f,hf⟩
      refine ⟨e.trans f,?_⟩
      rw [← Equiv.finsetCongr_trans,← Equiv.finsetCongr_trans,Equiv.trans_apply,he,hf]
  }

/-- Select genuinely nonisomorphic members of any finite collection. -/
theorem representatives [Fintype V] (F : Finset (Finset (Finset V))) :
    ∃ R ⊆ F, (R : Set (Finset (Finset V))).Pairwise (fun D E => ¬Isomorphic D E) ∧
      F.card ≤ R.card * (Fintype.card V).factorial := by
  classical
  let Q := Quotient (relabellings F)
  let _ : Fintype Q := Fintype.ofFinite _
  let q : F → Q := Quotient.mk _
  let rep (x : Q) : F := Quotient.out x
  have hrep (x : Q) : q (rep x) = x := Quotient.out_eq x
  let R := univ.image (fun x : Q => (rep x).val)
  let orbit (D : Finset (Finset V)) := univ.image (fun e : Equiv.Perm V => e.finsetCongr.finsetCongr D)
  refine ⟨R,?_,?_,?_⟩
  · intro D hD
    obtain ⟨x,_,rfl⟩ := mem_image.mp hD
    exact (rep x).property
  · intro D hD E hE ne iso
    obtain ⟨x,_,rfl⟩ := mem_image.mp hD
    obtain ⟨y,_,rfl⟩ := mem_image.mp hE
    have eq : q (rep x) = q (rep y) := Quotient.sound iso
    rw [hrep,hrep] at eq
    exact ne (eq ▸ rfl)
  · have cover : F ⊆ R.biUnion orbit := by
      intro D hD
      let x : F := ⟨D,hD⟩
      have same : Isomorphic (rep (q x)).val x.val := Quotient.exact (hrep (q x))
      obtain ⟨e,he⟩ := same
      exact mem_biUnion.mpr ⟨_,mem_image.mpr ⟨q x,mem_univ _,rfl⟩,mem_image.mpr ⟨e,mem_univ _,he⟩⟩
    refine (card_le_card cover).trans (card_biUnion_le_card_mul R orbit _ (fun D _ => ?_))
    exact card_image_le.trans_eq (by rw [card_univ,Fintype.card_perm])

/-- A power-of-two lower bound after forgetting all vertex labels. -/
theorem unlabelled_exponent {n b m : ℕ} (bound : 2^b ≤ m * n.factorial) :
    2^(b - Nat.clog 2 n.factorial) ≤ m := by
  have hm : 0 < m := by
    by_contra! h
    have e : m = 0 := by omega
    simp [e] at bound
  let k := Nat.clog 2 n.factorial
  have hfac : n.factorial ≤ 2^k := Nat.le_pow_clog (by decide) _
  have hh := bound.trans (Nat.mul_le_mul_left m hfac)
  by_cases hb : k ≤ b
  · have eq : b-k+k = b := Nat.sub_add_cancel hb
    rw [← eq,pow_add] at hh
    exact Nat.le_of_mul_le_mul_right hh (by positivity)
  · have q : b-k = 0 := Nat.sub_eq_zero_of_le (by omega)
    change 2^(b-k) ≤ m
    rw [q,pow_zero]
    omega

#print axioms representatives
#print axioms unlabelled_exponent
end Erdos722.QuadSwitch
