import Erdos722IngredientIntervals
import Erdos722ResidueDilation

/-!
# Enlarging intervals of admissible group counts

An interval with a fixed margin can be multiplied by one more than any
usable width divisible by the block size. Round the full group height so
that its one-point completion has residue zero. The last group then has
the residue of the target.
-/

namespace Erdos722.PairDesign

def Full (k J l h : ℕ) := FullFor (· ≤ 1) k J l h

theorem dilate {k J s N l h : ℕ} (hk : 2≤k) (hs : 0<s) (hds : k ∣ s)
    (H : Adjacent k s) (hN : ∀ t ≥ N, ArrayAt (s+1) t)
    (hnj : N≤J) (hsj : (s+1)*(k+2)≤J) (F : Full k J l h) :
    Full k J ((s+1)*l) ((s+1)*h) :=
  dilate_for (by decide : 0 ≤ 1) hk hs hds H hN hnj hsj F

#print axioms dilate
end Erdos722.PairDesign
