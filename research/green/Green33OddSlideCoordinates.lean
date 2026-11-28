import Mathlib

/-! A change of variables for random shifts of an odd number of layers. -/
open Finset
open scoped BigOperators
namespace Green33LayerSlides
variable (G J : Type*) [AddCommGroup G]

/-- The first source coordinate is the target. One layer pairs with
itself; every other layer is one side of a distinct mixed pair. -/
def rowChange : (G × G × (J→G) × (J→G)) ≃ ((G × (J→G)) × (G × (J→G))) where
  toFun := fun ⟨x,a,l,r⟩ => ((x-(a+a),fun j => x-(l j+r j)),a,l)
  invFun := fun ⟨⟨s,t⟩,a,l⟩ => (s+(a+a),a,l,fun j => s+(a+a)-l j-t j)
  left_inv := by
    rintro ⟨x,a,l,r⟩
    simp only [sub_add_cancel,Prod.mk.injEq,true_and]
    funext j;abel
  right_inv := by
    rintro ⟨⟨s,t⟩,a,l⟩
    simp only [add_sub_cancel_right,Prod.mk.injEq,true_and,and_true]
    funext j;abel

variable [Fintype G] [Fintype J] [DecidableEq J]

/-- Every test on the unshifted target coordinates of the blocks has
the average of independent uniform targets. The diagonal needs no inverse of two. -/
theorem independent_targets {R:Type*} [AddCommMonoid R] (f:G×(J→G)→R) :
    (∑ p : G × G × (J→G) × (J→G), f ((rowChange G J p).1)) =
      (Fintype.card G)^(Fintype.card J+1) • ∑ s : G×(J→G),f s := by
  rw [Equiv.sum_comp (rowChange G J) (fun p => f p.1)]
  rw [Fintype.sum_prod_type]
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fun,←smul_sum,pow_succ,mul_comm]
#print axioms independent_targets

variable [DecidableEq G]

private def goodEquiv (D : Finset G) (M:J→Finset G) :
    {p : G×(J→G) // p.1∈D ∧ ∀ j,p.2 j∈M j} ≃ D × (∀ j,M j) where
  toFun p := (⟨p.val.1,p.property.1⟩,fun j => ⟨p.val.2 j,p.property.2 j⟩)
  invFun p := ⟨(p.1.val,fun j => (p.2 j).val),p.1.property,fun j => (p.2 j).property⟩
  left_inv := by intro p;rfl
  right_inv := by intro p;rfl

/-- Given a set of allowed target coordinates for every block, the number
of successful shift and target tuples factors as a product of cardinalities. -/
theorem row_hit_count (D:Finset G) (M:J→Finset G) :
    (univ.filter fun p : G×G×(J→G)×(J→G) =>
      (rowChange G J p).1.1∈D ∧ ∀ j,(rowChange G J p).1.2 j∈M j).card =
      (Fintype.card G)^(Fintype.card J+1)*D.card*∏ j,(M j).card := by
  classical
  let ok (s:G×(J→G)) := s.1∈D ∧ ∀ j,s.2 j∈M j
  have c : (univ.filter ok).card=D.card*∏ j,(M j).card := by
    rw [←Fintype.card_subtype]
    simpa [Fintype.card_prod,Fintype.card_pi] using Fintype.card_congr (goodEquiv G J D M)
  have law:=independent_targets G J (fun s => if ok s then (1:ℕ) else 0)
  rw [mul_assoc,←c,card_filter,card_filter]
  simpa only [nsmul_eq_mul,Nat.cast_id] using law
#print axioms row_hit_count


variable {C : Type*}
def splitShifts (e : Unit ⊕ (J ⊕ J) ≃ C) : (C→G) ≃ G × (J→G) × (J→G) where
  toFun f := (f (e (.inl ())),fun j => f (e (.inr (.inl j))),fun j => f (e (.inr (.inr j))))
  invFun := fun ⟨a,l,r⟩ c => (Sum.elim (fun _ => a) (Sum.elim l r)) (e.symm c)
  left_inv := by
    intro f
    funext c
    obtain ⟨(u|j|j),rfl⟩:=e.surjective c <;> simp
  right_inv := by rintro ⟨a,l,r⟩;simp
theorem quotient_row_count [Fintype C] [DecidableEq C] (e : Unit ⊕ (J ⊕ J) ≃ C) (D:Finset G) (M:J→Finset G) :
    (univ.filter fun p : G×(C→G) =>
      p.1 - (p.2 (e (.inl ())) + p.2 (e (.inl ()))) ∈ D ∧ ∀ j,
        p.1 - (p.2 (e (.inr (.inl j))) + p.2 (e (.inr (.inr j)))) ∈ M j).card =
      (Fintype.card G)^(Fintype.card J+1)*D.card*∏ j,(M j).card := by
  classical
  rw [←row_hit_count G J D M]
  apply card_equiv ((Equiv.refl G).prodCongr (splitShifts G J e))
  intro p
  simp only [mem_filter,mem_univ,true_and]
  rfl
#print axioms quotient_row_count

end Green33LayerSlides

/-! Coordinate pairs above one residue of a cyclic quotient of odd order. -/
open Finset
namespace Green33LayerSlides
def positiveHalf (m:ℕ+) := univ.filter fun z:ZMod m => z.val<(-z).val
private theorem half_nonzero {m:ℕ+} {z : ZMod m} (hz:z∈positiveHalf m) : z≠0 := by
  intro e;subst z;simp [positiveHalf] at hz
private theorem no_opposites {m:ℕ+} {x y: ZMod m} (hx:x∈positiveHalf m) (hy:y∈positiveHalf m) : x≠-y := by
  intro e;subst x
  change -y∈univ.filter _ at hx
  have a:= (mem_filter.mp hx).2
  have b:= (mem_filter.mp hy).2
  simp only [neg_neg] at a
  omega
private def offset {m:ℕ+} : Unit ⊕ (positiveHalf m ⊕ positiveHalf m) → ZMod m :=
  Sum.elim (fun _ => 0) (Sum.elim (fun z => z.val) (fun z => -z.val))
private theorem offset_inj {m:ℕ+} : Function.Injective (offset (m:=m)) := by
  rintro (a|a|a) (b|b|b) eq
  · simp
  · exact (half_nonzero b.property eq.symm).elim
  · exact (half_nonzero b.property (neg_eq_zero.mp eq.symm)).elim
  · exact (half_nonzero a.property eq).elim
  · have r : a=b := Subtype.ext eq
    rw [r]
  · exact (no_opposites a.property b.property eq).elim
  · exact (half_nonzero a.property (neg_eq_zero.mp eq)).elim
  · exact (no_opposites b.property a.property eq.symm).elim
  · have r:a=b:=Subtype.ext (neg_injective eq)
    rw [r]
private theorem offset_surj {m:ℕ+} (odd:Odd m.val) : Function.Surjective (offset (m:=m)) := by
  intro x
  by_cases zero:x=0
  · exact ⟨.inl (),zero.symm⟩
  have diff:=ZMod.ne_neg_self odd zero
  have ne:x.val≠(-x).val:=fun eq => diff (ZMod.val_injective _ eq)
  rcases lt_or_gt_of_ne ne with h|h
  · exact ⟨.inr (.inl ⟨x,mem_filter.mpr ⟨mem_univ _,h⟩⟩),rfl⟩
  · have neg : -x ∈positiveHalf m := mem_filter.mpr ⟨mem_univ _,by simpa only [neg_neg] using h⟩
    exact ⟨.inr (.inr ⟨-x,neg⟩),neg_neg x⟩
noncomputable def labelEquiv {m:ℕ+} (odd:Odd m.val) (c:ZMod m) :
    Unit ⊕ (positiveHalf m ⊕ positiveHalf m) ≃ ZMod m :=
  (Equiv.ofBijective offset ⟨offset_inj,offset_surj odd⟩).trans (Equiv.addLeft c)
theorem half_count {m:ℕ+} (odd:Odd m.val) : 1+2*(positiveHalf m).card=m.val := by
  have h:=Fintype.card_congr (labelEquiv odd 0)
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_coe,ZMod.card] at h
  omega
#print axioms labelEquiv
#print axioms half_count

/-- Unordered pairs of quotient labels above 2c consist of one diagonal
and the pairs c±x indexed by the positive half. -/
theorem row_cases {m:ℕ+} (odd:Odd m.val) (c:ZMod m) (P:ZMod m→ZMod m→Prop)
    (sym:∀ a b,P a b ↔ P b a) :
    (∃ i j:ZMod m,i+j=c+c ∧ P i j) ↔
      P c c ∨ ∃ z:positiveHalf m, P (c+z.val) (c-z.val) := by
  constructor
  · rintro ⟨i,j,ij,p⟩
    obtain ⟨(u|x|x),rfl⟩:=(labelEquiv odd c).surjective i
    · change c+0+j=c+c at ij
      change P (c+0) j at p
      simp only [add_zero] at ij p
      exact Or.inl ((add_left_cancel ij : j=c) ▸ p)
    · change c+x.val+j=c+c at ij
      change P (c+x.val) j at p
      have e:j=c-x.val:=add_left_cancel (a:=c+x.val) (ij.trans (by abel))
      exact Or.inr ⟨x,e ▸ p⟩
    · change c+-x.val+j=c+c at ij
      change P (c+-x.val) j at p
      have e:j=c+x.val:=add_left_cancel (a:=c+-x.val) (ij.trans (by abel))
      exact Or.inr ⟨x,by simpa only [sub_eq_add_neg] using (sym _ _).mp (e ▸ p)⟩
  · rintro (p|⟨x,p⟩)
    · exact ⟨c,c,rfl,p⟩
    · exact ⟨_,_,by abel,p⟩
#print axioms row_cases

end Green33LayerSlides
