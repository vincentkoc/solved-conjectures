import Erdos722CyclotomicCosets
import Mathlib.Data.Fintype.Prod

/-!
# A starter representing all difference classes

Label the increasing pairs of positions by the multiplicative cosets.
Realizing these prescribed differences gives distinct entries and a
representative of every coset among the forward differences.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

theorem rainbow_starter (k : ℕ) (H : Subgroup Fˣ) (hm : H.index = k.choose 2)
    (hpos : 0 < H.index)
    (hbig : let C := 4*H.index; k*(4*C^2*C^k)*C^k < Fintype.card F) :
    ∃ f : Fin k → F, Function.Injective f ∧
      ∀ c : Fˣ ⧸ H, ∃ i j : Fin k, i<j ∧ f j-f i ∈ colorSet H c := by
  classical
  let Edge := {e : Fin k × Fin k // e.1<e.2}
  have hEdge : Fintype.card Edge = k.choose 2 := by
    dsimp [Edge]
    rw [Fintype.card_subtype]
    simpa using Fintype.card_product_filter_lt (α := Fin k)
  have hQ : Fintype.card (Fˣ ⧸ H) = H.index := (Nat.card_eq_fintype_card).symm
  let labels : Edge ≃ Fˣ ⧸ H := Fintype.equivOfCardEq (hEdge.trans (hQ.trans hm).symm)
  let col (i j : Fin k) : Fˣ ⧸ H := if h : i<j then labels ⟨(i,j),h⟩ else 1
  obtain ⟨f,hf⟩ := prescribed_differences (by positivity : 0<4*H.index) hbig
    (fun i j => colorSet H (col i j)) (fun _ _ _ => classBounds ..)
  have distinct (i j : Fin k) (h : i<j) : f j≠f i := by
    obtain ⟨u,hu,_⟩ := mem_color.mp (hf _ _ h)
    exact sub_ne_zero.mp (hu ▸ u.ne_zero)
  refine ⟨f,?_,?_⟩
  · intro i j h
    rcases lt_trichotomy i j with e|e|e
    · exact (distinct _ _ e h.symm).elim
    · exact e
    · exact (distinct _ _ e h).elim
  · intro c
    obtain ⟨⟨⟨i,j⟩,hi⟩,hc⟩ := labels.surjective c
    refine ⟨i,j,hi,?_⟩
    simpa [col,hi,hc] using hf i j hi

#print axioms rainbow_starter

end Erdos722.Cyclotomy
