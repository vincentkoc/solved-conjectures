import Lean

/-! Endpoint certificate for the reflected Jones factor at parameter five.
The energy budget counts squared deviations of coefficients from one. -/

open Lean Meta Elab Tactic
namespace CunninghamChain.JonesTwentyTwo
abbrev State := List Int × List Int × Nat

def dot (a b : List Int) : Int := (List.zipWith (·*·) a b).sum

/-- A completed even-length coefficient list at a candidate degree above five. -/
def terminal (s : State) : Bool :=
  let (a, b, budget) := s
  3 < a.length && (2 * a.length) % 30 == 6 && budget == 0 &&
    a.sum+b.sum == 2*(a.length : Int)+21

/-- If all remaining energy is at most 340, the new high coefficient lies from
−17 to 19. The convolution fixes `11*x+2*y`, leaving at most eight low coefficients. -/
def children (s : State) : List State :=
  let (a, b, budget) := s
  let target : Int := 22 + (a.length : Int) - dot a b.reverse.tail
  let low := (target - 38) / 11
  (List.range 8).filterMap fun (i : Nat) =>
    let x := low + (i : Int)
    let y := (target - 11 * x) / 2
    let cost := (x-1).natAbs^2 + (y-1).natAbs^2
    if 11*x + 2*y = target ∧ cost ≤ budget then some (x::a, y::b, budget-cost) else none

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

/-- Evaluate the finite search to construct proof terms. Each group of four levels is
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
  if s.1.length % 4 == 0 then
    mkAuxTheorem (mkApp (mkConst ``Excluded) se) p (kind? := `_jonesBranch)
  else return p

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
/-- The normalized coefficients exhaust the square-sum budget without a viable terminal of degree congruent to 5 modulo 30 beyond degree five. -/
theorem twenty_two_certificate : Excluded ([2],[11],340) := by
  run_tac liftMetaTactic fun g => do
    g.assign (← buildCertificate ([2],[11],340))
    return []
#print axioms twenty_two_certificate
end CunninghamChain.JonesTwentyTwo
