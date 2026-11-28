import CunninghamCoefficientSlices

/-! Search of the low and high coefficient lists for the seed 2(X−1). -/

namespace CunninghamChain.BalancedTwo
open CoefficientSlices

abbrev State := List ℤ × List ℤ × ℕ

def leading (k : Bool) : ℤ := if k then -2 else 2
def nextCoeff (k : Bool) : ℤ := if k then 4 else -4
def thirdCoeff (k : Bool) : ℤ := if k then -3 else 1
def lagOne (k : Bool) : ℤ := if k then -20 else -12
def lagTwo (k : Bool) : ℤ := if k then 6 else 2
def initial (k : Bool) : State := ([1],[leading k],if k then 25 else 17)

def matched (k : Bool) (s : State) : Bool :=
  s.2.1.reverse.take 3 == [leading k,nextCoeff k,thirdCoeff k]

def terminal (k : Bool) (s : State) : Bool :=
  let (a,b,room) := s
  let mid := -(a.sum+b.sum)
  let bad (xs : List ℤ) := xs.length ≥ 6 && (k || xs.length != 6) &&
    dot xs (xs.drop 1) == lagOne k && dot xs (xs.drop 2) == lagTwo k
  (room == 0 && mid == 0 && bad (a.reverse++b)) ||
    (mid.natAbs^2 == room && bad (a.reverse++mid::b))

def edgeTarget (k : Bool) (n : ℕ) : ℤ :=
  if n=1 then nextCoeff k else if n=2 then thirdCoeff k else 0

def children (k : Bool) (s : State) : List State :=
  let (a,b,room) := s
  let t := edgeTarget k a.length-dot a b.reverse.tail
  (List.range 11).filterMap fun (i : ℕ) =>
    let x := (i:ℤ)-5
    let y := t-leading k*x
    let cost := x.natAbs^2+y.natAbs^2
    if cost≤room then some (x::a,y::b,room-cost) else none

/-- A matched high endpoint already exhausts the polynomial's full weight.
Otherwise each level either checks a complete list or advances both ends. -/
def check (k : Bool) : ℕ → State → Bool
  | 0,s => matched k s
  | j+1,s => matched k s || (!terminal k s && (children k s).all (check k j))

private def Checked (k : Bool) (j : ℕ) : List State → Prop
  | [] => True
  | x::xs => check k j x=true ∧ Checked k j xs

private theorem checked_node (k : Bool) (j : ℕ) (s : State) (cs : List State)
    (term : terminal k s=false) (eq : children k s=cs) (sub : Checked k j cs) :
    check k (j+1) s=true := by
  suffices h : cs.all (check k j)=true by simp [check,term,eq,h]
  clear eq term
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨h,rest⟩ := sub
    simp [h,ih rest]

open Lean Meta in
/-- After seven endpoint extensions each surviving branch has its own closed
kernel reduction. The parent proof combines those results. -/
private partial def certificate (k : Bool) (j : Nat) (s : State) : MetaM Expr := do
  let ke := toExpr k
  let se := toExpr s
  let call := mkApp3 (mkConst ``check) ke (toExpr j) se
  let yes := mkConst ``Bool.true
  if matched k s || s.1.length ≥ 8 || j == 0 then
    return ← mkAuxTheorem (←mkEq call yes) (←mkEqRefl yes) (kind? := `_balancedEnd)
  let next := children k s
  if terminal k s then throwError "unexpected terminal {repr s}"
  let je := toExpr (j-1)
  let cs := toExpr next
  let mut sub := mkConst ``True.intro
  for child in next.reverse do
    let childProof ← certificate k (j-1) child
    sub ← mkAppM ``And.intro #[childProof,sub]
  let proof := mkAppN (mkConst ``checked_node)
    #[ke,je,se,cs,←mkEqRefl (mkConst ``Bool.false),←mkEqRefl cs,sub]
  if s.1.length % 4 == 0 then
    mkAuxTheorem (←mkEq call yes) proof (kind? := `_balancedNode)
  else return proof

open Lean Elab Tactic in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem minus_search : check false 20 (initial false)=true := by
  run_tac liftMetaTactic fun g => do
    g.assign (←certificate false 20 (initial false))
    return []

open Lean Elab Tactic in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem plus_search : check true 30 (initial true)=true := by
  run_tac liftMetaTactic fun g => do
    g.assign (←certificate true 30 (initial true))
    return []

#print axioms minus_search
#print axioms plus_search

end CunninghamChain.BalancedTwo
