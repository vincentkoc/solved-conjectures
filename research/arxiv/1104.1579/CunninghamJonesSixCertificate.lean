import Lean

/-! A kernel-checked finite search for the normalized endpoint coefficients at Jones’s first parameter. -/

open Lean Meta Elab Tactic
namespace CunninghamChain.JonesSix
abbrev State := List Int × List Int × Nat

def dot (a b : List Int) : Int := (List.zipWith (·*·) a b).sum

def terminal (s : State) : Bool :=
  let (a,b,budget) := s
  let middle := -(a.sum+b.sum)
  let check (xs : List Int) :=
    xs.length ≥ 6 && dot xs (xs.drop 1) == -30 && dot xs (xs.drop 2) == 0 && dot xs (xs.drop 3) == 0
  (budget == 0 && middle == 0 && check (a.reverse ++ b)) ||
    (middle.natAbs^2 == budget && check (a.reverse ++ middle::b))

def children (s : State) : List State :=
  let (a,b,budget) := s
  let target : Int := (if a.length = 1 then 5 else 0) - dot a b.reverse.tail
  (List.range 15).filterMap fun (i : Nat) =>
    let x : Int := (i:Int)-7
    let y := (target+3*x)/2
    let w := x.natAbs^2 + y.natAbs^2
    if 2*y-3*x = target ∧ w ≤ budget then some (x::a,y::b,budget-w) else none

inductive Excluded : State → Prop where
  | step {s : State} (notTerminal : terminal s = false) (smaller : ∀ child ∈ children s, Excluded child) : Excluded s

private def AllExcluded : List State → Prop
  | [] => True
  | x::xs => Excluded x ∧ AllExcluded xs

private theorem certify (s : State) (next : List State)
    (ht : terminal s = false) (hn : children s = next) (hs : AllExcluded next) : Excluded s := by
  refine .step ht ?_
  rw [hn]
  clear hn ht
  induction next with
  | nil => simp
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact hs.1
    · exact ih hs.2 _ hx

/-- Evaluate the finite search to construct proof terms. Each group of five levels is
checked in a separate auxiliary theorem to bound kernel memory. -/
private partial def buildCertificate (s : State) : MetaM Expr := do
  let next := children s
  if terminal s then throwError "unexpected terminal {repr s}"
  let mut hs := mkConst ``True.intro
  for child in next.reverse do
    let h ← buildCertificate child
    hs ← mkAppM ``And.intro #[h,hs]
  let se := toExpr s
  let ne := toExpr next
  let p := mkApp5 (mkConst ``certify) se ne
    (← mkEqRefl (mkConst ``Bool.false)) (← mkEqRefl ne) hs
  if s.1.length % 5 == 0 then
    mkAuxTheorem (mkApp (mkConst ``Excluded) se) p (kind? := `_jonesBranch)
  else return p

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
/-- The normalized coefficients exhaust the square-sum budget without a viable terminal of degree at least five. -/
theorem six_certificate : Excluded ([2],[-3],49) := by
  run_tac liftMetaTactic fun g => do
    g.assign (← buildCertificate ([2],[-3],49))
    return []
#print axioms six_certificate
end CunninghamChain.JonesSix
