import Erdos478WindowImageCard
import Erdos478ShortCollisionAvoidance

/-! # Roots bounding pairs of equal factorials at two positions in a moving window -/

namespace Erdos478.WindowAverage
open Finset Polynomial LocalSpacing
open scoped Classical
noncomputable section

/-- Positive starting indices whose entire closed window is in the canonical domain. -/
def starts (p H : ℕ) := Icc 1 (p-1-H)

theorem mem_starts {p H a : ℕ} : a∈starts p H ↔ 1≤a ∧ a+H<p := by
  rw [starts,mem_Icc]
  omega

theorem starts_card (p H : ℕ) : (starts p H).card=p-1-H := by simp [starts,Nat.card_Icc]

def equalStarts (p H r s : ℕ) :=
  (starts p H).filter fun a => (a+r).factorial%p=(a+s).factorial%p

/-- For a fixed pair of positions each colliding translate gives a distinct
root of the same monic polynomial of degree equal to the index gap. -/
theorem equalStarts_card_le {p H r s : ℕ} (prime : p.Prime) (rs : r<s) (sH : s≤H) :
    (equalStarts p H r s).card≤s-r := by
  let : Fact p.Prime := ⟨prime⟩
  let f := translatedGap (ZMod p) s (s-r)
  have degree := translated_degree (ZMod p) s (show 0<s-r by omega)
  have valid {a : ℕ} (ha : a∈equalStarts p H r s) := mem_starts.mp (mem_filter.mp ha).1
  calc
    _ ≤ f.roots.toFinset.card := by
      apply card_le_card_of_injOn (fun a : ℕ => (a:ZMod p))
      · intro a ha
        apply Multiset.mem_toFinset.mpr
        apply (mem_roots degree.monic.ne_zero).mpr
        have h := collision_root prime (Nat.le_add_right a r) (Nat.add_lt_add_left rs a)
          (show a+s<p by have vp := valid ha; omega) (mem_filter.mp ha).2
        simpa only [Nat.add_sub_cancel_left,Nat.add_sub_add_left] using h
      · intro a ha b hb eq
        have x := (ZMod.natCast_eq_natCast_iff' a b p).mp eq
        have va := valid ha
        have vb := valid hb
        rwa [Nat.mod_eq_of_lt (by omega : a<p),Nat.mod_eq_of_lt (by omega : b<p)] at x
    _ ≤ f.natDegree := f.roots.toFinset_card_le.trans f.card_roots'
    _ = _ := degree.natDegree_eq

theorem adjacent_starts_empty {p H r : ℕ} (prime : p.Prime) (bound : r+1≤H) :
    equalStarts p H r (r+1)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨valid,eq⟩ := mem_filter.mp ha
  obtain ⟨lo,hi⟩ := mem_starts.mp valid
  exact FirstCollision.no_gap_one prime ⟨a+r,mem_Ico.mpr ⟨by omega,by omega⟩,
    mem_Ico.mpr ⟨by omega,by omega⟩,by simpa only [Nat.add_assoc] using eq⟩

#print axioms starts
#print axioms mem_starts
#print axioms starts_card
#print axioms equalStarts
#print axioms equalStarts_card_le
#print axioms adjacent_starts_empty
end
end Erdos478.WindowAverage
