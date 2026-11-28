import Erdos722FiveOrders

/-!
# A finite reduction for the exact five-point pair-design spectrum

For an admissible group count outside the seed list, write it as `5t+r+a`
with smaller admissible column counts `t+a` and `r+a`. The small search
only tests the nine integers up to and including the quotient by five.
-/

namespace Erdos722.Five

/-- Group counts for the elementary truncation recursion. -/
def exactSeeds : List ℕ :=
  [0,1,5,6,10,11,15,16,20,21,35,36,40,41,45,70,71,75,76,116,120,121]

private def Split (u t a : ℕ) : Prop :=
  0<t ∧ Good t ∧ a≤1 ∧ 5*t+a≤u ∧ u≤6*t+a ∧ (t+a)%5≤1 ∧ t+a<u

private instance (u t a : ℕ) : Decidable (Split u t a) := by unfold Split; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem small_splits : ∀ u : Fin 900, u.val%5≤1 → u.val ∈ exactSeeds ∨
    ∃ j : Fin 9, ∃ a : Fin 2, Split u.val (u.val/5-j.val) a.val := by decide +kernel

private theorem seed_or_split (u : ℕ) (hu : u%5≤1) :
    u ∈ exactSeeds ∨ ∃ t a : ℕ, Split u t a := by
  by_cases h : u<900
  · rcases small_splits ⟨u,h⟩ hu with h | ⟨j,a,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_,_,h⟩
  · let t := 30*((u-5)/150)+1
    have ht : Good t := Or.inl (by dsimp [t]; omega)
    exact Or.inr ⟨t,0,by unfold Split; dsimp [t] at *; exact ⟨by omega, ht, by omega,
      by omega, by omega, by omega, by omega⟩⟩

/-- The specified seeds suffice for every admissible group count, with no
lower cutoff. Each recursive use calls the same five-column filling rule. -/
theorem all_orders_from_seeds (P : ℕ → Prop) (seed : ∀ u ∈ exactSeeds, P u)
    (grow : ∀ t r a, Good t → r≤t → a≤1 → P (t+a) → P (r+a) → P (5*t+r+a))
    (u : ℕ) (hu : u%5≤1) : P u := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    rcases seed_or_split u hu with h | ⟨t,a,ht,hgood,ha,hlo,hhi,hmod,hlt⟩
    · exact seed u h
    · let r := u-5*t-a
      have he : 5*t+r+a=u := by dsimp [r]; omega
      exact he ▸ grow t r a hgood (by dsimp [r]; omega) ha (ih _ hlt hmod)
        (ih _ (by dsimp [r]; omega) (by dsimp [r]; omega))

#print axioms all_orders_from_seeds

end Erdos722.Five
