import Erdos722QuartetOrders
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic

/-!
# Ring orders supplying transversal designs

A product of two field constructions supplies orders 12 and 20. At orders
congruent to one modulo twelve the ordinary residue ring already suffices.
-/

namespace Erdos722.Quartet

structure Directions (a t : ℕ) where
  K : Type
  [ring : CommRing K]
  [finite : Fintype K]
  card : Fintype.card K = t
  c : Fin a → K
  units : ∀ i j, i ≠ j → IsUnit (c i - c j)

attribute [instance] Directions.ring Directions.finite

namespace Directions

noncomputable def primePower (a p e : ℕ) (he : e ≠ 0) (ha : a ≤ p^e)
    (hp : p.Prime := by decide) :
    Directions a (p^e) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let K := GaloisField p e
  letI : Fintype K := Fintype.ofFinite _
  have hK : Fintype.card K = p^e := by rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p e he
  let c := (Fin.castLEEmb ha).trans (Fintype.equivFinOfCardEq hK).symm.toEmbedding
  exact ⟨K,hK,c,fun i j h => isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (c.injective.ne h))⟩

def prod {a t u : ℕ} (A : Directions a t) (B : Directions a u) : Directions a (t*u) where
  K := A.K × B.K
  card := by simp [A.card,B.card]
  c i := (A.c i,B.c i)
  units i j h := Prod.isUnit_iff.mpr ⟨A.units i j h,B.units i j h⟩

noncomputable def twelve : Directions 3 12 :=
  (primePower 3 3 1 (by decide) (by decide)).prod (primePower 3 2 2 (by decide) (by decide))

private noncomputable def modular (t : ℕ) (ht : t%12=1) : Directions 4 t := by
  haveI : NeZero t := ⟨by omega⟩
  have h2 : IsUnit (2 : ZMod t) := ZMod.isUnit_prime_of_not_dvd (p := 2) (by decide) (by omega)
  have h3 : IsUnit (3 : ZMod t) := ZMod.isUnit_prime_of_not_dvd (p := 3) (by decide) (by omega)
  refine ⟨ZMod t,ZMod.card t,![0,1,2,3],?_⟩
  intro i j h
  fin_cases i <;> fin_cases j <;> try exact (h rfl).elim
  all_goals norm_num <;> assumption

/-- Four finite directions for every order used in the truncation recursion. -/
theorem four {t : ℕ} (ht : t ∈ QuartetOrders.transversalOrders ∨ t%12=1) :
    Nonempty (Directions 4 t) := by
  rcases ht with ht | ht
  · simp [QuartetOrders.transversalOrders] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨primePower 4 2 2 (by decide) (by decide)⟩
    · exact ⟨primePower 4 5 1 (by decide) (by decide)⟩
    · exact ⟨primePower 4 2 3 (by decide) (by decide)⟩
    · exact ⟨primePower 4 3 2 (by decide) (by decide)⟩
    · exact ⟨primePower 4 13 1 (by decide) (by decide)⟩
    · exact ⟨primePower 4 2 4 (by decide) (by decide)⟩
    · exact ⟨primePower 4 17 1 (by decide) (by decide)⟩
    · exact ⟨(primePower 4 2 2 (by decide) (by decide)).prod (primePower 4 5 1 (by decide) (by decide))⟩
    · exact ⟨primePower 4 5 2 (by decide) (by decide)⟩
    · exact ⟨primePower 4 29 1 (by decide) (by decide)⟩
    · exact ⟨primePower 4 2 5 (by decide) (by decide)⟩
    · exact ⟨primePower 4 37 1 (by decide) (by decide)⟩
    · exact ⟨primePower 4 41 1 (by decide) (by decide)⟩
    · exact ⟨primePower 4 7 2 (by decide) (by decide)⟩
    · exact ⟨primePower 4 53 1 (by decide) (by decide)⟩
  · exact ⟨modular t ht⟩

#print axioms four

end Directions
end Erdos722.Quartet
