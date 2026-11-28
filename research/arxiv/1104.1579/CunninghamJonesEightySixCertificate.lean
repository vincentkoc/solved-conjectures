import CunninghamJonesEndpointSearch

namespace CunninghamChain.JonesEndpointSearch

/-- The endpoint constants are 2 and 43. A putative reducible degree is
7 modulo 56, so its coefficient list has length 8 modulo 56. -/
def eightySix : Parameters := ⟨2, 43, 7, 56, 8⟩

open Lean Meta Elab Tactic

private def AllExcluded : List State → Prop
  | [] => True
  | s :: ss => Excluded eightySix s ∧ AllExcluded ss

private theorem certify (s : State) (next : List State)
    (ht : terminal eightySix s = false) (hn : children eightySix s = next)
    (hs : AllExcluded next) : Excluded eightySix s := by
  refine .step ht ?_
  rw [hn]
  clear hn ht
  induction next with
  | nil => simp
  | cons t ts ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hs.1
    · exact ih hs.2 _ hx

private def nodeCount : Nat → State → Nat
  | 0, _ => 1
  | n+1, s => 1 + ((children eightySix s).map (nodeCount n)).sum

/-- Small subtrees are checked by conversion. Each gets a separate kernel
declaration so the conversion cache is bounded by the size of one subtree. -/
private partial def buildCertificate (fuel : Nat) (s : State) : MetaM Expr := do
  let se := toExpr s
  let goal := mkApp2 (mkConst ``Excluded) (mkConst ``eightySix) se
  if nodeCount fuel s ≤ 96 then
    let proof := mkApp4 (mkConst ``excluded_of_check) (mkConst ``eightySix)
      (mkNatLit fuel) se (← mkEqRefl (mkConst ``Bool.true))
    return ← mkAuxTheorem goal proof (kind? := `_jonesSearch)
  let next := children eightySix s
  let mut hs := mkConst ``True.intro
  for child in next.reverse do
    hs ← mkAppM ``And.intro #[← buildCertificate (fuel-1) child, hs]
  let ne := toExpr next
  let proof := mkApp5 (mkConst ``certify) se ne
    (← mkEqRefl (mkConst ``Bool.false)) (← mkEqRefl ne) hs
  return ← mkAuxTheorem goal proof (kind? := `_jonesBranch)

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem eighty_six_certificate : Excluded eightySix ([2], [43], 5460) := by
  run_tac liftMetaTactic fun g => do
    g.assign (← buildCertificate 40 ([2], [43], 5460))
    return []

#print axioms eighty_six_certificate

end CunninghamChain.JonesEndpointSearch
