import Green51FourSpaceCertificate

/-! # Eight-coordinate parity checks for the projected four-space obstruction -/
namespace Green51FourSpace.Certificate
open Lean

private def spanWords (b : List Nat) : List Nat :=
  b.foldl (fun old u => old ++ old.map (· ^^^ u)) [0]
private def independentBasis (b : List Nat) : List Nat :=
  let words := (spanWords b).mergeSort
  (words.foldl (fun (p : List Nat × List Nat) u =>
    if u ∈ p.1 then p else (p.1 ++ p.1.map (· ^^^ u),p.2 ++ [u])) ([0],[])).2
private def relabel (b c t u : Nat) : Nat :=
  ((List.range 8).filter u.testBit).foldl (fun s i =>
    let j := (i%2) ^^^ (if i.testBit 1 then b else 0) ^^^ (if i.testBit 2 then c else 0) ^^^ t
    s ||| 2^j) 0
private def chooseShapes : List (List Nat) := Id.run do
  let mut out := (List.range 8).map (fun i => [2^i])
  for b in [2:8] do
    for c in [2:8] do
      if c != b && c != (b ^^^ 1) then
        for t in [:8] do
          for B in templates do
            out := independentBasis (B.map (relabel b c t)) :: out
  return out.eraseDups
/-- Candidate configurations. Both their impossibility and their coverage
are checked below, independently of the choice of these search candidates. -/
elab "chosenShapes%" : term => return toExpr chooseShapes
def shapes : List (List Nat) := chosenShapes%

def collectBits (l : List Nat) : Nat := l.foldr (fun i m => 2^i ||| m) 0
theorem collectBits_iff (l:List Nat) (i:Nat) : (collectBits l).testBit i=true ↔ i∈l := by
  induction l with
  | nil => simp [collectBits]
  | cons x xs ih =>
    change ((2^x ||| collectBits xs).testBit i=true) ↔ _
    simp only [Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr eq_comm Iff.rfl
def orthogonal (u r : Nat) : Bool := byteWeight (u &&& r) % 2 == 0
def zone (b : List Nat) : Nat :=
  collectBits ((List.range 256).filter (fun r => b.all (fun u => orthogonal u r)))
theorem zone_iff (B : List Nat) (r:Nat) : (zone B).testBit r=true ↔
    r<256 ∧ ∀ u∈B,orthogonal u r=true := by
  simp [zone,collectBits_iff,List.mem_range,List.all_eq_true]

elab "chosenZones%" : term => return toExpr (shapes.map zone)
def zones : List Nat := chosenZones%
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem zones_exact : shapes.map zone=zones := by decide +kernel

end Green51FourSpace.Certificate
#print axioms Green51FourSpace.Certificate.zones_exact
