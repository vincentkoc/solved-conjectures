import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

/-!
# Simultaneous roots of two integer polynomials

A homomorphism out of the iterated root algebra records an ordered pair of
roots. This construction does not require separability or invertibility of
any discriminant.
-/

namespace Erdos478.RootPairs
noncomputable section
open Polynomial

abbrev pairOrder (f g : ℤ[X]) := AdjoinRoot (g.map (AdjoinRoot.of f))

def firstGen (f g : ℤ[X]) : pairOrder f g := AdjoinRoot.of _ (AdjoinRoot.root f)

def secondGen (f g : ℤ[X]) : pairOrder f g := AdjoinRoot.root _

abbrev solutions (f : ℤ[X]) (R : Type*) [CommRing R] :=
  {x : R // f.eval₂ (Int.castRingHom R) x = 0}

variable {R : Type*} [CommRing R] {f g : ℤ[X]}

private theorem at_root (h : AdjoinRoot f →+* R) :
    f.eval₂ (Int.castRingHom R) (h (AdjoinRoot.root f)) = 0 := by
  have he := congrArg h (AdjoinRoot.eval₂_root f)
  rw [hom_eval₂,map_zero,RingHom.ext_int (h.comp (AdjoinRoot.of f)) (Int.castRingHom R)] at he
  exact he

/-- The pair of evaluations on the two integral generators is universal. -/
def equiv (f g : ℤ[X]) (R : Type*) [CommRing R] :
    (solutions f R × solutions g R) ≃ (pairOrder f g →+* R) where
  toFun z := AdjoinRoot.lift (AdjoinRoot.lift _ z.1.val z.1.property) z.2.val
    (by rw [eval₂_map,AdjoinRoot.lift_comp_of]; exact z.2.property)
  invFun h :=
    (⟨h (firstGen f g),at_root (h.comp (AdjoinRoot.of _))⟩,
     ⟨h (secondGen f g),by
        have he := congrArg h (AdjoinRoot.eval₂_root (g.map (AdjoinRoot.of f)))
        rw [hom_eval₂,eval₂_map] at he
        simpa [secondGen,RingHom.ext_int _ (Int.castRingHom R)] using he⟩)
  left_inv z := by
    apply Prod.ext <;> apply Subtype.ext <;> simp [firstGen,secondGen]
  right_inv h := by
    apply AdjoinRoot.ringHom_ext
    · rw [AdjoinRoot.lift_comp_of]
      apply AdjoinRoot.ringHom_ext
      · exact RingHom.ext_int _ _
      · simp [firstGen]
    · simp [secondGen]


/-- Homomorphisms from an order to a field extend across a finite-index
inclusion when the index is invertible. The statement only needs a common
denominator for the ambient ring. -/
theorem extend_order {A k : Type*} [CommRing A] [Field k] (S : Subring A) (d : ℕ)
    (hd : (d : k) ≠ 0) (hs : ∀ x : A, (d : A)*x ∈ S) (φ : S →+* k) :
    ∃ ψ : A →+* k, ψ.comp S.subtype = φ := by
  let D (x : A) : S := ⟨(d : A)*x,hs x⟩
  let F (x : A) : k := φ (D x) / d
  have clear (x : A) : F x * d = φ (D x) := div_mul_cancel₀ _ hd
  have mult (x y : A) : (d : S)*D (x*y) = D x*D y := by
    apply Subtype.ext
    change (d:A)*((d:A)*(x*y)) = ((d:A)*x)*((d:A)*y)
    ring
  let ψ : A →+* k := {
    toFun := F
    map_one' := by
      apply (mul_left_inj' hd).mp
      rw [clear,one_mul,show D 1 = (d : S) by apply Subtype.ext; simp [D],map_natCast]
    map_zero' := by
      apply (mul_left_inj' hd).mp
      rw [clear,zero_mul,show D 0 = 0 by apply Subtype.ext; simp [D],map_zero]
    map_add' := by
      intro x y
      apply (mul_left_inj' hd).mp
      rw [add_mul,clear,clear,clear,← map_add]
      congr 1
      apply Subtype.ext
      exact mul_add _ _ _
    map_mul' := by
      intro x y
      apply (mul_left_inj' hd).mp
      apply (mul_left_inj' hd).mp
      rw [clear,show F x*F y*d*d = (F x*d)*(F y*d) by ring,clear,clear]
      have he := congrArg φ (mult x y)
      simpa only [map_mul,map_natCast,mul_comm (d:k)] using he }
  refine ⟨ψ,RingHom.ext fun x => ?_⟩
  change φ (D x.val) / d = φ x
  apply (div_eq_iff hd).mpr
  rw [show D x.val = (d : S)*x by rfl,map_mul,map_natCast,mul_comm]

#print axioms extend_order
#print axioms equiv

end
end Erdos478.RootPairs
