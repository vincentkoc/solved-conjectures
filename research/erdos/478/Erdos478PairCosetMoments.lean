import Erdos478CosetFixedCounts
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.NormNum

/-! # First and second fixed-point moments in every two-transitive subgroup coset -/

namespace Erdos478.FrobeniusCounts
open Finset MulAction Function
noncomputable section
open scoped Classical
variable {G : Type*} [Group G] (N : Subgroup G) [Fintype N]

private theorem orbit_mean {Y L : Type*} [Fintype Y] [MulAction G Y] (q : Y → L) (onto : Surjective q)
    (orb : ∀ x y, q x=q y ↔ ∃ a : N, a.val • x=y) :
    uniform N (fun a => (fixedCount Y a.val : ℝ))=(Nat.card L : ℝ) := by
  classical
  let Ω := orbitRel.Quotient N Y
  let : Fintype Ω := Fintype.ofFinite _
  let (a : N) : Fintype (fixedBy Y a) := Fintype.ofFinite _
  have eq : orbitRel N Y=Setoid.ker q := Setoid.ext fun x y => by
    rw [orbitRel_apply,mem_orbit_iff]
    exact (orb y x).symm.trans eq_comm
  have count : Nat.card Ω=Nat.card L := by
    change Nat.card (Quotient (orbitRel N Y))=_
    rw [eq]
    exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective q onto)
  rw [← count]
  change (∑ a : N, (fixedCount Y (a : G) : ℝ)) / Fintype.card N=_
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card N ≠ 0))).mpr
  rw [← Nat.cast_sum,← Nat.cast_mul]
  have burn := sum_card_fixedBy_eq_card_orbits_mul_card_group N Y
  exact_mod_cast (by simpa only [fixedCount,Nat.card_eq_fintype_card] using burn :
    (∑ a : N, fixedCount Y a)=Nat.card Ω*Fintype.card N)

private theorem fixed_square (Y : Type*) [MulAction G Y] (g : G) :
    fixedCount (Y×Y) g=fixedCount Y g*fixedCount Y g := by
  let e : fixedBy (Y×Y) g ≃ fixedBy Y g × fixedBy Y g :=
    { toFun := fun x => (⟨x.val.1,congrArg Prod.fst (mem_fixedBy.mp x.prop)⟩,
                         ⟨x.val.2,congrArg Prod.snd (mem_fixedBy.mp x.prop)⟩)
      invFun := fun z => ⟨(z.1.val,z.2.val),Prod.ext z.1.prop z.2.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_prod _ _)

/-- Transitivity on both the diagonal and its complement is sufficient, even
when the ambient permutation group is larger than the subgroup. -/
theorem pair_coset_moments {Y : Type*} [Fintype Y] [Nontrivial Y] [MulAction G Y]
    (pairs : ∀ a b c d : Y, (a=b ↔ c=d) → ∃ n : N, n.val • a=c ∧ n.val • b=d) (g : G) :
    uniform N (fun n => (fixedCount Y (n.val*g) : ℝ))=1 ∧
      uniform N (fun n => (fixedCount Y (n.val*g) : ℝ)^2)=2 := by
  classical
  have trans (x y : Y) : ∃ n : N, n.val • x=y := by
    obtain ⟨n,h,_⟩ := pairs x x y y (by simp)
    exact ⟨n,h⟩
  constructor
  · rw [twisted_fixed N Y g (fun y => trans y _)]
    simpa only [Nat.card_unique,Nat.cast_one] using
      orbit_mean N (fun _ : Y => (() : Unit)) (fun _ => ⟨Classical.choice inferInstance,rfl⟩)
        (fun x y => ⟨fun _ => trans x y,fun _ => rfl⟩)
  · let q (x : Y×Y) := decide (x.1=x.2)
    have onto : Surjective q := by
      obtain ⟨a,b,ne⟩ := exists_pair_ne Y
      intro c
      cases c
      · exact ⟨(a,b),by simpa [q]⟩
      · exact ⟨(a,a),by simp [q]⟩
    have orb (x y : Y×Y) : q x=q y ↔ ∃ n : N, n.val • x=y := by
      constructor
      · intro he
        have h : x.1=x.2 ↔ y.1=y.2 := by simpa [q] using he
        obtain ⟨a,h₁,h₂⟩ := pairs _ _ _ _ h
        exact ⟨a,Prod.ext h₁ h₂⟩
      · rintro ⟨n,rfl⟩
        simp [q]
    have within (x : Y×Y) : ∃ n : N, n.val • x=g • x := (orb x _).mp (by simp [q])
    have h := (twisted_fixed N (Y×Y) g within).trans (orbit_mean N q onto orb)
    simpa only [fixed_square,Nat.cast_mul,pow_two,Nat.card_eq_fintype_card,Fintype.card_bool,Nat.cast_ofNat] using h

#print axioms pair_coset_moments
end
end Erdos478.FrobeniusCounts
