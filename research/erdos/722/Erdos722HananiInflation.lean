import Erdos722TwoStemTransversals
import Erdos722TwoStemPencil
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Two-stem inflation over an even field

For q the size of a finite field of characteristic two, a design of
order q(q+1)+2 supplies the line filling for block size q+2. The
hyperoval array and the full single fiber supply the other two fillings.
Hanani's six-point-block construction takes q=4 and the small Witt seed.
-/

namespace Erdos722.TwoStem
open Finset PointedProduct
noncomputable section

/-- Two ordinary designs give an ordinary design. The first supplies
the finite pencil and the second is the master that is inflated. -/
theorem even_field_inflation (F : Type*) [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {m v : ℕ} (hF : Fintype.card F=m) (seed : ExistsDesign (m+1) ((m+1)*m+2))
    (master : ExistsDesign (m+1) (v+1)) : ExistsDesign (m+1) (m*v+2) := by
  classical
  have hm : 0<m := hF ▸ Fintype.card_pos
  obtain ⟨H,hH⟩ := seed
  let Y := Fin ((m+1)*m)
  let e := (Fintype.equivFinOfCardEq (by simp [Y,Nat.add_assoc] :
    Fintype.card (Option (Option Y))=(m+1)*m+2)).symm
  have line := pencil_filling (d:=m+1) hm (by simp [Y] : Fintype.card Y=(m+1)*m) (relabel_design e hH)
  have circle := hyperoval_template F
  rw [hF] at circle
  rw [Nat.mul_comm]
  apply order_inflate _ master
  intro s
  cases s with
  | point => exact point_template m
  | line => exact line
  | circle => exact circle

/-- Hanani's 4v+2 construction with the 22-point seed explicit. -/
theorem hanani_of_seed (seed : ExistsDesign 5 22) {v : ℕ} (master : ExistsDesign 5 (v+1)) :
    ExistsDesign 5 (4*v+2) := by
  classical
  let F := GaloisField 2 2
  let : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F=4 :=
    (Nat.card_eq_fintype_card (α:=F)).symm.trans (GaloisField.card 2 2 (by decide))
  exact even_field_inflation F hF seed master

/-- Punctured orders under repeated two-stem inflation. -/
def orbit (a : ℕ) : ℕ → ℕ
  | 0 => a
  | d+1 => 4*orbit a d+1

theorem orbit_formula (a d : ℕ) : 3*(orbit a d+1)=4^d*(3*a+1)+2 := by
  induction d with
  | zero => simp [orbit]; omega
  | succ d ih =>
    rw [orbit,pow_succ]
    nlinarith only [ih]

theorem orbit_design (seed : ExistsDesign 5 22) {a : ℕ} (master : ExistsDesign 5 (a+1)) (d : ℕ) :
    ExistsDesign 5 (orbit a d+1) := by
  induction d with
  | zero => exact master
  | succ d ih => exact hanani_of_seed seed ih

#print axioms even_field_inflation
#print axioms hanani_of_seed
#print axioms orbit_formula
#print axioms orbit_design
end
end Erdos722.TwoStem
