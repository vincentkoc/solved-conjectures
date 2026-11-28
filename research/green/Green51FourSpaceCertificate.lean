import Mathlib

/-! # Finite obstructions for sixteen binary coordinates partitioned into two eights -/

namespace Green51FourSpace.Certificate
def planes : List Nat := [21845, 43690, 13107, 52428, 39321, 26214, 3855, 61680, 42405, 23130, 50115, 15420, 26985, 38550, 255, 65280, 43605, 21930, 52275, 13260, 26265, 39270, 61455, 4080, 23205, 42330, 15555, 49980, 38505, 27030]

private def nibbleWeight (x : Nat) := (155746543670344 >>> (3*(x%16))) % 8
def byteWeight (x : Nat) := nibbleWeight x + nibbleWeight (x/16)
def admissible (u v : Nat) : Bool :=
  let w := byteWeight u + byteWeight v
  let s := 256*u+v
  s == 0 || (w%2 == 0 && (decide (8≤w) || (w == 6 && planes.any (fun p => s &&& p == s))))
def allowed (u v : Nat) : Bool :=
  !v.testBit 5 && admissible u v && admissible u (v ^^^ 63)

def extendPairs (seen : List (Nat × Nat)) (u v : Nat) :=
  seen ++ seen.map (fun (x,y) => (u ^^^ x,v ^^^ y))

def templates : List (List Nat) := [[5,17], [3,5], [3,20], [5,11], [5,10], [3,13],
  [5,80], [5,18], [5,96], [5,19,99], [23,45,78], [3,12,53,81], [3,12,48,192]]

/-- Once the high byte vanishes, the canonical low offset also vanishes. -/
theorem zero_low_offset {b:Nat} (small:b<256) (good:allowed 0 b=true) : b=0 := by
  have check : ∀ v:Fin 256,allowed 0 v.val=true → v.val=0 := by decide +kernel
  exact check ⟨b,small⟩ good

end Green51FourSpace.Certificate
#print axioms Green51FourSpace.Certificate.zero_low_offset
