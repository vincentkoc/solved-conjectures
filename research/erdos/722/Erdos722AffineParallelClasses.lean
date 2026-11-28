import Erdos722SymmetricPairPlane
import Erdos722QuartetCovers

/-!
# Parallel classes in a pair design on a square number of points

At a point outside a block, exactly one of the lines in the pencil
misses the block. This identifies parallel classes without assuming
coordinates or a translation group.
-/

namespace Erdos722.InversiveOrder
open Finset IntegralDesign
open scoped Classical
noncomputable section

def Parallel {P : Type*} (B C : Finset P) : Prop := B=C ∨ Disjoint B C

theorem parallel_symm {P : Type*} {B C : Finset P} (h : Parallel B C) : Parallel C B :=
  h.elim (fun e => Or.inl e.symm) (fun d => Or.inr d.symm)

theorem pair_line {P : Type*} [DecidableEq P] {H : Finset (Finset P)} {q : ℕ}
    (hH : H.IsBlockDesign 2 q) {x y : P} (hxy : x≠y) :
    ∃! B : Finset P, B∈H ∧ x∈B ∧ y∈B :=
  (Erdos722.Quartet.Cover.ofDesign hH).through x y hxy trivial

theorem affine_pencil_card {q : ℕ} (hq : 2≤q) {H : Finset (Finset (Fin (q^2)))}
    (hH : H.IsBlockDesign 2 q) (x : Fin (q^2)) : (H.filter (x∈·)).card=q+1 := by
  have h := flag_count hH {x} (by simp)
  simp only [card_singleton,singleton_subset_iff,Nat.reduceSub,Nat.choose_one_right] at h
  have hq' : 1≤q := by omega
  have hqq : 1≤q^2 := by nlinarith [Nat.mul_self_le_mul_self hq]
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0<q-1)
  rw [h]
  nlinarith [Nat.sub_add_cancel hq',Nat.sub_add_cancel hqq]

/-- The unique block through a point parallel to a specified block.
When the point is already on the specified block this returns that block. -/
theorem parallel_through {q : ℕ} (hq : 2≤q) {H : Finset (Finset (Fin (q^2)))}
    (hH : H.IsBlockDesign 2 q) {B : Finset (Fin (q^2))} (hB : B∈H) (x : Fin (q^2)) :
    ∃! C : Finset (Fin (q^2)), C∈H ∧ x∈C ∧ Parallel C B := by
  classical
  by_cases hx : x∈B
  · refine ⟨B,⟨hB,hx,Or.inl rfl⟩,?_⟩
    rintro C ⟨_,hxC,he|hd⟩
    · exact he
    · exact (disjoint_left.mp hd hxC hx).elim
  let U := H.filter (x∈·)
  let T := U.filter (fun C => ¬ Disjoint C B)
  have join (y : B) : ∃! C, C∈H ∧ x∈C ∧ (y:Fin (q^2))∈C :=
    pair_line hH (fun he => hx (he ▸ y.property))
  let J (y : B) := (join y).choose
  have spec (y : B) : J y∈H ∧ x∈J y ∧ (y:Fin (q^2))∈J y := (join y).choose_spec.1
  have injective : Function.Injective J := by
    intro y z he
    by_contra hn
    have hd : (y:Fin (q^2))≠z := fun e => hn (Subtype.ext e)
    have hb := (pair_line hH hd).unique
      (show J y∈H ∧ (y:Fin (q^2))∈J y ∧ (z:Fin (q^2))∈J y from
        ⟨(spec y).1,(spec y).2.2,he ▸ (spec z).2.2⟩) ⟨hB,y.property,z.property⟩
    exact hx (hb ▸ (spec y).2.1)
  have ht : T=univ.image J := by
    ext C
    constructor
    · intro hc
      obtain ⟨hxC,hd⟩ := mem_filter.mp hc
      obtain ⟨y,hyC,hyB⟩ := Finset.not_disjoint_iff.mp hd
      let y' : B := ⟨y,hyB⟩
      exact mem_image.mpr ⟨y',mem_univ _,(join y').choose_spec.2 C
        ⟨(mem_filter.mp hxC).1,(mem_filter.mp hxC).2,hyC⟩ |>.symm⟩
    · rintro hc
      obtain ⟨y,_,rfl⟩ := mem_image.mp hc
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨(spec y).1,(spec y).2.1⟩,
        Finset.not_disjoint_iff.mpr ⟨y,(spec y).2.2,y.property⟩⟩
  have hm : T.card=q := by rw [ht,card_image_of_injective _ injective,card_univ,Fintype.card_coe,hH.1 B hB]
  have hd : (U.filter (fun C => Disjoint C B)).card=1 := by
    have h := U.card_filter_add_card_filter_not (fun C => Disjoint C B)
    have hu : U.card=q+1 := affine_pencil_card hq hH x
    change _ + T.card=U.card at h
    omega
  obtain ⟨C,hC,huniq⟩ := card_eq_one_iff_existsUnique.mp hd
  obtain ⟨hxC,hCB⟩ := mem_filter.mp hC
  refine ⟨C,⟨(mem_filter.mp hxC).1,(mem_filter.mp hxC).2,Or.inr hCB⟩,?_⟩
  rintro D ⟨hD,hxD,he|hd'⟩
  · exact (hx (he ▸ hxD)).elim
  · exact huniq D (mem_filter.mpr ⟨mem_filter.mpr ⟨hD,hxD⟩,hd'⟩)

theorem parallel_trans {q : ℕ} (hq : 2≤q) {H : Finset (Finset (Fin (q^2)))}
    (hH : H.IsBlockDesign 2 q) {A B C : Finset (Fin (q^2))}
    (hA : A∈H) (hB : B∈H) (hC : C∈H) (hAB : Parallel A B) (hBC : Parallel B C) :
    Parallel A C := by
  classical
  by_cases hd : Disjoint A C
  · exact Or.inr hd
  obtain ⟨x,hxA,hxC⟩ := Finset.not_disjoint_iff.mp hd
  exact Or.inl ((parallel_through hq hH hB x).unique ⟨hA,hxA,hAB⟩ ⟨hC,hxC,parallel_symm hBC⟩)

#print axioms parallel_symm
#print axioms pair_line
#print axioms affine_pencil_card
#print axioms parallel_through
#print axioms parallel_trans
end
end Erdos722.InversiveOrder
