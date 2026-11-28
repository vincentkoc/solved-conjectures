import Lean

/-! A finite search of low and high coefficients of a reflected Jones factor.
The endpoint convolution fixes the next high coefficient once the low one is known. -/

namespace CunninghamChain.JonesEndpointSearch

abbrev State := List Int × List Int × Nat

structure Parameters where
  left : Nat
  right : Nat
  exception : Nat
  period : Nat
  residue : Nat
  deriving Repr

def terminal (p : Parameters) (s : State) : Bool :=
  let (a, b, budget) := s
  let len := 2 * a.length
  len != p.exception + 1 && len % p.period == p.residue && budget == 0 &&
    a.sum + b.sum == (len : Int) + p.left * p.right - 1

def dot (a b : List Int) : Int := (List.zipWith (· * ·) a b).sum

def children (p : Parameters) (s : State) : List State :=
  let (a, b, budget) := s
  let u : Int := p.left
  let v : Int := p.right
  let target := u*v + a.length - dot a b.reverse.tail
  let radius : Int := budget.sqrt
  let lo := (target - u*(1+radius)) / v
  let hi := (target - u*(1-radius)) / v
  (List.range (hi-lo+1).toNat).filterMap fun (i : Nat) =>
    let x := lo + (i : Int)
    let y := (target-v*x)/u
    let cost := (x-1).natAbs^2 + (y-1).natAbs^2
    if v*x+u*y = target ∧ cost ≤ budget then some (x::a, y::b, budget-cost) else none

inductive Excluded (p : Parameters) : State → Prop where
  | step {s : State} (ht : terminal p s = false)
      (hc : ∀ c ∈ children p s, Excluded p c) : Excluded p s

/-- At zero fuel an unexplored branch stays open. A successful check therefore
excludes every terminal descendant, even ones at depths greater than the fuel. -/
def check (p : Parameters) : Nat → State → Bool
  | 0, _ => false
  | fuel+1, s => !terminal p s && (children p s).all (check p fuel)

theorem excluded_of_check (p : Parameters) (fuel : Nat) (s : State)
    (h : check p fuel s = true) : Excluded p s := by
  induction fuel generalizing s with
  | zero => simp [check] at h
  | succ fuel ih =>
    simp only [check, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact .step h.1 (fun c hc => ih c (h.2 c hc))

#print axioms excluded_of_check

end CunninghamChain.JonesEndpointSearch
