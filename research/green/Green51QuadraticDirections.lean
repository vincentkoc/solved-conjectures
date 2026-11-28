import Green51SimplexDirections
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! # Quadratic obstruction to a binary three-space of directions -/

namespace Green51SimplexDirections
local notation "F" => ZMod 2

private def bit (x i : ℕ) : F := if x.testBit i then 1 else 0
private theorem bit_xor (x y i : ℕ) : bit (x ^^^ y) i = bit x i+bit y i := by
  cases a:x.testBit i <;> cases b:y.testBit i <;> simp [bit,Nat.testBit_xor,a,b,show (1:F)+1=0 by decide]

/-- The Pfaffian of the alternating four-by-four matrix in six coordinates. -/
def quadratic (x : ℕ) : F := bit x 2*bit x 6+bit x 1*bit x 7+bit x 0*bit x 8

private theorem value_one {x : ℕ} (hx : x∈directions) : quadratic x=1 := by
  have h : directions.all (fun i => decide (quadratic i=1))=true := by decide +kernel
  simpa using List.all_eq_true.mp h x hx

private theorem third_difference (u v w : ℕ) :
    quadratic u + quadratic v + quadratic w + quadratic (u ^^^ v) +
    quadratic (u ^^^ w) + quadratic (v ^^^ w) + quadratic ((u ^^^ v) ^^^ w)=0 := by
  simp only [quadratic,bit_xor]
  ring_nf
  simp [show (2:F)=0 by decide,show (4:F)=0 by decide]

/-- A binary plane of admissible directions cannot extend to a three-space
all of whose nonzero directions remain admissible. -/
theorem no_three_space {u v w : ℕ} (hu : u∈directions) (hv : v∈directions)
    (hw : w∈directions) (uv : u ^^^ v∈directions) (uw : u ^^^ w∈directions)
    (vw : v ^^^ w∈directions) : (u ^^^ v) ^^^ w∉directions := by
  intro bad
  have h := third_difference u v w
  rw [value_one hu,value_one hv,value_one hw,value_one uv,value_one uw,value_one vw,value_one bad] at h
  exact (by decide : ¬ ((1:F)+1+1+1+1+1+1=0)) h

end Green51SimplexDirections
#print axioms Green51SimplexDirections.no_three_space
