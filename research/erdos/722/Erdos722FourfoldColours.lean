import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic

/-!
# Two edge colourings for Hanani's fourfold construction

On an even cyclic group, edges with fixed endpoint sum are matchings.
An odd sum gives a perfect matching. An even sum leaves precisely the
two points with the same residue modulo half the group order.
A second colouring supplies a one-factorization of the complete graph.
-/

namespace Erdos722.Fourfold

/-- In each row of a symmetric Latin square every edge colour occurs once.
The diagonal records a missing neighbour in the corresponding matching. -/
structure Colours (X C : Type*) where
  row : X → X ≃ C
  symm (x y : X) : row x y = row y x

namespace Colours
variable {X C : Type*} (F : Colours X C)

def mate (c : C) (x : X) : X := (F.row x).symm c

@[simp] theorem colour_mate (c : C) (x : X) : F.row x (F.mate c x) = c :=
  (F.row x).apply_symm_apply c

@[simp] theorem mate_colour (x y : X) : F.mate (F.row x y) x = y :=
  (F.row x).symm_apply_apply y

@[simp] theorem mate_twice (c : C) (x : X) : F.mate c (F.mate c x) = x := by
  apply (F.row (F.mate c x)).injective
  rw [F.colour_mate,F.symm,F.colour_mate]

def transport {Y D : Type*} (e : Y ≃ X) (f : C ≃ D) : Colours Y D where
  row x := e.trans ((F.row (e x)).trans f)
  symm x y := congrArg f (F.symm (e x) (e y))
end Colours

abbrev Bit := Fin 2
abbrev Label (k : ℕ) := Bit × Fin (k+1)

private def number (k : ℕ) : Label k ≃ Fin (2*(k+1)) := finProdFinEquiv

private def sumCode (k : ℕ) : Label k ≃ Fin (2*(k+1)) :=
  (Equiv.prodComm ..).trans (finProdFinEquiv.trans (finCongr (Nat.mul_comm ..)))

private def plusColours (G : Type*) [AddCommGroup G] : Colours G G where
  row := Equiv.addLeft
  symm := add_comm

/-- Cyclic endpoint sums give both the perfect and the two-hole matchings. -/
def crossing (k : ℕ) : Colours (Label k) (Label k) :=
  haveI : NeZero (2*(k+1)) := ⟨by omega⟩
  (plusColours (Fin (2*(k+1)))).transport (number k) (sumCode k).symm

theorem crossing_diag (k : ℕ) (x : Label k) : (crossing k).row x x = (0,x.2) := by
  have : NeZero (2*(k+1)) := ⟨by omega⟩
  apply (sumCode k).injective
  change sumCode k ((sumCode k).symm (number k x + number k x)) = _
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  obtain ⟨b,t⟩ := x
  fin_cases b
  · change (t.val+(k+1)*0+(t.val+(k+1)*0))%(2*(k+1)) = 0+2*t.val
    simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · change (t.val+(k+1)*1+(t.val+(k+1)*1))%(2*(k+1)) = 0+2*t.val
    rw [show t.val+(k+1)*1+(t.val+(k+1)*1) = t.val+t.val+2*(k+1) by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    omega

private abbrev OddGroup (k : ℕ) := ZMod (2*k+1)

private noncomputable def twice (k : ℕ) : OddGroup k ≃ OddGroup k := by
  have hu : IsUnit (2 : OddGroup k) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr (Nat.coprime_two_left.mpr ⟨k,by omega⟩)
  exact { toFun := fun x => 2*x
          invFun := fun x => (2 : OddGroup k)⁻¹*x
          left_inv := fun x => by dsimp only; rw [← mul_assoc,ZMod.inv_mul_of_unit _ hu,one_mul]
          right_inv := fun x => by dsimp only; rw [← mul_assoc,ZMod.mul_inv_of_unit _ hu,one_mul] }

private noncomputable def roundRobin (k : ℕ) : Colours (Option (OddGroup k)) (Option (OddGroup k)) where
  row
    | none => (twice k).optionCongr
    | some x => (Equiv.swap none (some x)).trans (Equiv.addLeft x).optionCongr
  symm := by
    rintro (_|x) (_|y)
    · rfl
    · simp [twice,two_mul]
    · simp [twice,two_mul]
    · by_cases h : x=y
      · subst y; rfl
      · simp [Equiv.swap_apply_def,h,Ne.symm h,add_comm]

private theorem roundRobin_diag (k : ℕ) (x : Option (OddGroup k)) :
    (roundRobin k).row x x = none := by
  cases x <;> simp [roundRobin]

private noncomputable def rrEquiv (k : ℕ) : Label k ≃ Option (OddGroup k) :=
  Fintype.equivOfCardEq (by simp [Label,OddGroup,Bit]; omega)

/-- A synchronized one-factorization covers triples using both columns
of the same half. Its diagonal colour acts as the identity. -/
noncomputable def parallel (k : ℕ) : Colours (Label k) (Option (OddGroup k)) :=
  (roundRobin k).transport (rrEquiv k) (Equiv.refl _)

theorem parallel_diag (k : ℕ) (x : Label k) : (parallel k).row x x = none :=
  roundRobin_diag k _

#print axioms crossing_diag
#print axioms parallel_diag

end Erdos722.Fourfold
