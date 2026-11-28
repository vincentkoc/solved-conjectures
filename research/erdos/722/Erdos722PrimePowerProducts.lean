import Erdos722PointedDesignProduct
import Erdos722SingletonFaceCovers
import Erdos722QuadraticCircleLine
import Erdos722ProjectiveCircleGraphs
import Erdos722InversiveSquareTiles

/-!
# The prime-power product theorem for Steiner 3-designs

Wilson's product takes designs on a+1 and b+1 points, with common block
size q+1 for q a prime power, to a design on ab+1 points. Mohácsy and
Ray-Chaudhuri proved the theorem independently using candelabra systems.
The local covers here use the affine and projective lines over GF(q).
-/

namespace Erdos722.PointedProduct.PrimePower
open Finset OnePoint
open scoped Classical
noncomputable section

def field_tiles (F : Type*) [Field F] [DecidableEq F] [Fintype F] (p : ℕ)
    [Fact p.Prime] [CharP F p] : ∀ s t, Tile (Fintype.card F) s t
  | .point,.point => (singleton_singleton _).tile (by simp [Shape.width]) (by simp [Shape.width])
  | .point,.line => (line_singleton F).transpose.tile (by simp [Shape.width]) rfl
  | .line,.point => (line_singleton F).tile rfl (by simp [Shape.width])
  | .point,.circle => (circle_singleton (Option F) Fintype.card_option).transpose.tile
      (by simp [Shape.width]) Fintype.card_option
  | .circle,.point => (circle_singleton (Option F) Fintype.card_option).tile
      Fintype.card_option (by simp [Shape.width])
  | .circle,.line => (quadratic_circle_line F).tile Fintype.card_option rfl
  | .line,.circle => (quadratic_circle_line F).transpose.tile rfl Fintype.card_option
  | .circle,.circle => (projective_circle_circle F).tile Fintype.card_option Fintype.card_option
  | .line,.line => (inversive_line_line F p).tile rfl rfl

/-- For every prime power q and arbitrary punctured orders a,b, the genuine
canonical design predicate is closed under the pointed product. -/
theorem product {q a b : ℕ} (hq : IsPrimePow q)
    (ha : ∃ H : Finset (Finset (Fin (a+1))), H.IsBlockDesign 3 (q+1))
    (hb : ∃ H : Finset (Finset (Fin (b+1))), H.IsBlockDesign 3 (q+1)) :
    ∃ H : Finset (Finset (Fin (a*b+1))), H.IsBlockDesign 3 (q+1) := by
  obtain ⟨p,e,hp,he,rfl⟩ := (isPrimePow_nat_iff _).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p e
  let : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F=p^e := (Nat.card_eq_fintype_card (α:=F)).symm.trans (GaloisField.card p e he.ne')
  apply order_product _ ha hb
  rw [← hF]
  exact field_tiles F p

/-- The multiplicative closure includes the empty product, whose order is two. -/
theorem power_order {q a : ℕ} (hq : IsPrimePow q) (ha : ExistsDesign q (a+1)) (u : ℕ) :
    ExistsDesign q (a^u+1) := by
  induction u with
  | zero =>
    rw [pow_zero]
    refine ⟨∅,?_,?_⟩
    · intro B hB
      exact (notMem_empty _ hB).elim
    · intro T hT
      have h := T.card_le_univ
      simp [hT] at h
  | succ u ih =>
    rw [pow_succ]
    exact product hq ih ha

/-- All orders 1 + q^u a^v from one additional punctured seed a. -/
theorem mixed_orders {q a : ℕ} (hq : IsPrimePow q) (ha : ExistsDesign q (a+1)) (u v : ℕ) :
    ∃ H : Finset (Finset (Fin (q^u*a^v+1))), H.IsBlockDesign 3 (q+1) := by
  have seed : ExistsDesign q (q+1) := by
    refine ⟨{univ},?_,?_⟩
    · intro B h
      obtain rfl := mem_singleton.mp h
      simp
    · intro T _
      exact ⟨univ,⟨mem_singleton_self _,subset_univ _⟩,fun B h => mem_singleton.mp h.1⟩
  exact product hq (power_order hq seed u) (power_order hq ha v)

#print axioms field_tiles
#print axioms product
#print axioms power_order
#print axioms mixed_orders
end
end Erdos722.PointedProduct.PrimePower
