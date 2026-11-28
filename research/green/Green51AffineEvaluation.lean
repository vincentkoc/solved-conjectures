import Green51TwelveCodes

/-! # The seven-coordinate obstruction for evaluations on twenty-five points -/

open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51AffineEvaluation
local notation "F" => ZMod 2

private def extendParity {n : ℕ} : Cube n →ₗ[F] Cube (n+1) :=
  LinearMap.pi (fun i => Fin.cases (∑ j : Fin n, (LinearMap.proj j : Cube n →ₗ[F] F))
    (fun j => LinearMap.proj j) i)

private theorem parity_zero {n : ℕ} (x : Cube n) :
    extendParity x 0 = ((supp x).card : F) := by
  change (∑ j : Fin n, (LinearMap.proj j : Cube n →ₗ[F] F)) x = _
  rw [LinearMap.sum_apply]
  change (∑ j : Fin n, x j) = _
  calc
    _ = ∑ j : Fin n, if x j ≠ 0 then (1:F) else 0 := by
      apply sum_congr rfl
      intro j _
      rcases (show ∀ a : F, a = 0 ∨ a = 1 by decide) (x j) with h|h <;> simp [h]
    _ = _ := by rw [←sum_filter]; simp [supp]

private theorem weight_extend {n : ℕ} (x : Cube n) :
    (supp (extendParity x)).card = (if ((supp x).card : F) = 0 then 0 else 1) +
      (supp x).card := by
  classical
  simp only [supp, card_filter, Fin.sum_univ_succ]
  change (if extendParity x 0 ≠ 0 then 1 else 0) + (∑ i : Fin n, if x i ≠ 0 then 1 else 0) = _
  rw [parity_zero]
  split_ifs <;> simp_all [supp, card_filter]

/-- Any linear space of binary words of length 25 and minimum weight seven
has dimension at most twelve. Appending the parity bit gives length 26 and distance eight. -/
theorem rank_of_seven (C : Submodule F (Cube 25))
    (dist : ∀ x : C, x ≠ 0 → 7 ≤ (supp x.val).card) : Module.finrank F C ≤ 12 := by
  have inj : Function.Injective (extendParity (n:=25)) := by
    intro x y eq
    funext i
    exact congrFun eq i.succ
  let D := C.map extendParity
  have bound := Green51TwelveResidual.no_26_13_8 D (by
    intro z nz
    obtain ⟨x, hx, eq⟩ := z.property
    have non : (⟨x,hx⟩ : C) ≠ 0 := by
      rintro h
      have xz : x = 0 := congrArg Subtype.val h
      exact nz (Subtype.ext (by rw [←eq,xz,map_zero];rfl))
    have low := dist ⟨x,hx⟩ non
    change 8 ≤ (supp z.val).card
    rw [←eq, weight_extend]
    change 7 ≤ (supp x).card at low
    by_cases seven : (supp x).card = 7
    · rw [seven];decide
    · split <;> omega)
  exact (C.equivMapOfInjective extendParity inj).finrank_eq.trans_le bound

end Green51AffineEvaluation
#print axioms Green51AffineEvaluation.rank_of_seven
