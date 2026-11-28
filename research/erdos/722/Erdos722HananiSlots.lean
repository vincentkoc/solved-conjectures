import Erdos722ThreeColumnRule
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The cyclic sum intervals for Hanani's three-column construction

After the stem sums, each column receives an interval of length twice the
number of positive short shifts. Reflection around its midpoint realizes each
signed odd shift exactly once.
-/

namespace Erdos722.HananiSlots
open ThreeColumn

abbrev Dir (d : ℕ) := Fin d ⊕ Fin d
abbrev Labels (r : ℕ) := ZMod (2*r)

def flip {d : ℕ} : Dir d → Dir d := Sum.swap

private def offset (d : ℕ) : Dir d ≃ Fin (d+d) :=
  (Equiv.sumCongr Fin.revPerm (Equiv.refl _)).trans finSumFinEquiv

private theorem finCast {n : ℕ} [NeZero n] (x : Fin n) : ZMod.finEquiv n x = (x.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (ZMod.natCast_zmod_val (ZMod.finEquiv (n+1) x)).symm

/-- A stem, followed by one ordinary interval per column. -/
def slot {h d r : ℕ} [NeZero (2*r)] (hr : h+6*d=2*r) :
    Fin h ⊕ (Col × Dir d) ≃ Labels r :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl (Fin 3)) (offset d)).trans
    finProdFinEquiv)).trans (finSumFinEquiv.trans ((finCongr (by omega)).trans (ZMod.finEquiv _).toEquiv))

private theorem slot_low {h d r : ℕ} [NeZero (2*r)] (hr : h+6*d=2*r) (i : Col) (a : Fin d) :
    slot hr (.inr (i,.inl a)) = ((h+(d-(a.val+1)+(d+d)*i.val) : ℕ) : Labels r) := by
  apply finCast

private theorem slot_high {h d r : ℕ} [NeZero (2*r)] (hr : h+6*d=2*r) (i : Col) (a : Fin d) :
    slot hr (.inr (i,.inr a)) = ((h+(d+a.val+(d+d)*i.val) : ℕ) : Labels r) := by
  apply finCast

private def diff {d : ℕ} (r : ℕ) : Dir d → Labels r
  | .inl a => ((2*a.val+1 : ℕ) : Labels r)
  | .inr a => -((2*a.val+1 : ℕ) : Labels r)

private theorem diff_nat_neg {r a : ℕ} (ha : a ≤ 2*r) :
    - (a : Labels r) = ((2*r-a : ℕ) : Labels r) := by
  rw [Nat.cast_sub ha, ZMod.natCast_self,zero_sub]

private theorem diff_inj {d r : ℕ} (hd : 2*d ≤ r) : Function.Injective (@diff d r) := by
  rintro (a|a) (b|b) he <;> simp only [diff] at he
  · have he' := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at he'
    exact congrArg Sum.inl (Fin.ext (by omega))
  · rw [diff_nat_neg (by omega)] at he
    have he' := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at he'
    omega
  · rw [diff_nat_neg (by omega)] at he
    have he' := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at he'
    omega
  · have he' := congrArg ZMod.val (neg_inj.mp he)
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at he'
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- The signed odd displacements, embedded in the full cyclic label group. -/
def shift {d r : ℕ} (hd : 2*d ≤ r) : Dir d ↪ Labels r := ⟨diff r,diff_inj hd⟩

theorem shift_flip {d r : ℕ} (hd : 2*d ≤ r) (a : Dir d) : shift hd (flip a) = -shift hd a := by
  cases a <;> simp [flip,shift,diff]

theorem slot_flip {h d r : ℕ} [NeZero (2*r)] (hr : h+6*d=2*r) (hd : 2*d ≤ r)
    (i : Col) (a : Dir d) : slot hr (.inr (i,flip a)) = slot hr (.inr (i,a)) + shift hd a := by
  have forward (q : Fin d) : slot hr (.inr (i,.inr q)) =
      slot hr (.inr (i,.inl q)) + ((2*q.val+1 : ℕ) : Labels r) := by
    rw [slot_high,slot_low,← Nat.cast_add]
    exact congrArg _ (by omega)
  cases a with
  | inl q => exact forward q
  | inr q =>
    change slot hr (.inr (i,.inl q)) = slot hr (.inr (i,.inr q)) + -_
    rw [forward]
    abel

/-- Reduction of a label modulo two distinguishes the two layers. -/
def parity (r : ℕ) : Labels r →+* ZMod 2 := ZMod.castHom (dvd_mul_right 2 r) _

theorem parity_shift {d r : ℕ} (hd : 2*d ≤ r) (a : Dir d) : parity r (shift hd a) = 1 := by
  have ho (q : Fin d) : parity r ((2*q.val+1 : ℕ) : Labels r) = 1 := by
    rw [map_natCast]
    push_cast
    rw [show (2 : ZMod 2) = 0 by decide,zero_mul,zero_add]
  cases a with
  | inl q => exact ho q
  | inr q =>
    change parity r (-_) = 1
    rw [map_neg,ho]
    decide

/-- One unused odd shift pairs the two parity layers. -/
def reserved (d r : ℕ) : Labels r := ((2*d+1 : ℕ) : Labels r)

theorem parity_reserved (d r : ℕ) : parity r (reserved d r) = 1 := by
  unfold reserved
  rw [map_natCast]
  push_cast
  rw [show (2 : ZMod 2) = 0 by decide,zero_mul,zero_add]

theorem shift_ne_reserved {d r : ℕ} (hr : 2*d+1 ≤ r) (a : Dir d) :
    shift (by omega : 2*d ≤ r) a ≠ reserved d r := by
  rcases a with q|q <;> intro he
  · change ((2*q.val+1 : ℕ) : Labels r) = ((2*d+1 : ℕ) : Labels r) at he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at hv
    omega
  · change -((2*q.val+1 : ℕ) : Labels r) = ((2*d+1 : ℕ) : Labels r) at he
    rw [diff_nat_neg (by omega)] at he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_natCast_of_lt (by omega)] at hv
    omega

#print axioms parity_shift
#print axioms parity_reserved
#print axioms shift_ne_reserved
#print axioms slot_flip
#print axioms shift_flip

end Erdos722.HananiSlots
