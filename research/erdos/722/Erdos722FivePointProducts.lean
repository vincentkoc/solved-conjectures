import Erdos722PointedDesignProduct
import Erdos722FivePointTiles
import Erdos722MixedOrderIntervals
import Erdos722SecondOrderTwentySix

/-!
# Wilson's rank-three product at block size five

Puncturing at the distinguished point multiplies the two punctured
orders. Iteration starting with the whole five-point block and the
cyclic system on 26 points gives orders 1 + 4ᵃ 25ᵇ.
-/

namespace Erdos722.PointedProduct.Five
open Finset

theorem product {a b : ℕ}
    (ha : ∃ H : Finset (Finset (Fin (a+1))), H.IsBlockDesign 3 5)
    (hb : ∃ H : Finset (Finset (Fin (b+1))), H.IsBlockDesign 3 5) :
    ∃ H : Finset (Finset (Fin (a*b+1))), H.IsBlockDesign 3 5 :=
  order_product tiles ha hb

private theorem one : ExistsDesign 4 (1+1) := by
  refine ⟨∅,by simp [IsUniform],?_⟩
  intro T hT
  have := T.card_le_univ
  simp [hT] at this

private theorem four : ExistsDesign 4 (4+1) := by
  refine ⟨{univ},?_,?_⟩
  · intro B h
    obtain rfl := mem_singleton.mp h
    simp
  · intro T _
    exact ⟨univ,⟨mem_singleton_self _,subset_univ _⟩,fun B h => mem_singleton.mp h.1⟩

theorem power_order {a : ℕ} (h : ExistsDesign 4 (a+1)) (u : ℕ) :
    ExistsDesign 4 (a^u+1) := by
  induction u with
  | zero => simpa using one
  | succ u ih =>
    rw [pow_succ]
    exact order_product tiles ih h

theorem mixed_orders (u v : ℕ) :
    ∃ H : Finset (Finset (Fin (4^u*25^v+1))), H.IsBlockDesign 3 5 :=
  product (power_order four u) (power_order SecondOrder.order_twenty_six v)

/-- Every sufficiently large interval of any fixed positive relative length
contains an ordinary five-point triple design of an explicit mixed order. -/
theorem designs_in_relative_intervals {ε : ℝ} (he : 0<ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ u v : ℕ,
      n≤4^u*25^v+1 ∧ ((4^u*25^v+1:ℕ):ℝ)<(1+ε)*n ∧
      ∃ H : Finset (Finset (Fin (4^u*25^v+1))), H.IsBlockDesign 3 5 := by
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.mp (Mixed.dense_mixed_orders he)
  have h := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (A+1)
  filter_upwards [h] with n hn
  obtain ⟨u,v,hlo,hhi⟩ := hA ((n:ℝ)-1) (by linarith)
  refine ⟨u,v,?_,?_,mixed_orders u v⟩
  · exact_mod_cast (show (n:ℝ)≤4^u*25^v+1 by linarith)
  · push_cast
    linarith

#print axioms designs_in_relative_intervals
#print axioms product
#print axioms power_order
#print axioms mixed_orders
end Erdos722.PointedProduct.Five
