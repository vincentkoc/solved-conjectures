import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! # Coordinates for an element of order equal to the prime degree -/

namespace Erdos478.PrimeDifferences
open Equiv Function
noncomputable section
variable {p : ℕ} [Fact p.Prime] {Y : Type*} [Fintype Y]

theorem prime_cycle_coordinates (hY : Fintype.card Y=p) (s : Perm Y) (hs : orderOf s=p) :
    ∃ e : ZMod p ≃ Y, ∀ t x : ZMod p, (s^t.val) (e x)=e (t+x) := by
  classical
  have pp := (Fact.out : p.Prime)
  have hn : s≠1 := by intro h; exact pp.ne_one (by simpa [h] using hs.symm)
  obtain ⟨a,ha⟩ : ∃ a, s a≠a := by
    by_contra! h
    exact hn (Equiv.ext h)
  have hpwr : s^p=1 := hs ▸ pow_orderOf_eq_one s
  have hper : IsPeriodicPt (s : Y → Y) p a := by
    change (⇑s)^[p] a=a
    rw [← Perm.coe_pow,hpwr]
    rfl
  have hmper : minimalPeriod (s : Y → Y) a=p :=
    (Nat.dvd_prime pp).mp hper.minimalPeriod_dvd |>.resolve_left (fun h => ha (minimalPeriod_eq_one_iff_isFixedPt.mp h))
  let f (x : ZMod p) := (s^x.val) a
  have fi : Injective f := by
    intro x y he
    apply ZMod.val_injective p
    apply iterate_injOn_Iio_minimalPeriod (f := (s : Y → Y)) (x:=a)
    · exact hmper ▸ x.val_lt
    · exact hmper ▸ y.val_lt
    · simpa only [f,Perm.coe_pow] using he
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨fi,(ZMod.card p).trans hY.symm⟩)
  refine ⟨e,fun t x => ?_⟩
  change (s^t.val) ((s^x.val) a)=(s^(t+x).val) a
  have hw (n : ℕ) : s^(n%p)=s^n := by simpa only [hs] using pow_mod_orderOf s n
  rw [ZMod.val_add,hw,pow_add,Perm.mul_apply]

#print axioms prime_cycle_coordinates
end
end Erdos478.PrimeDifferences
