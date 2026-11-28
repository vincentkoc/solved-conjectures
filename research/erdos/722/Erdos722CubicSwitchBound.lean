import Erdos722ExceptionalSwitches
import Erdos722QuadrupleBlockMotion
import Erdos722IteratedSwitchCounts

/-! # An exponentially small exceptional fraction for all separating binary-order bases -/

namespace Erdos722.QuadSwitch
open Finset Equiv

/-- Finite bound for any separating base. The exponent accounts for the motion
of every nonidentity automorphism, including ones with fixed points. -/
theorem separating_exceptional_bound {n : ℕ} [NeZero n] {H : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign 3 4) (sep : Separates H) :
    (exceptional hH).card≤2^n+n.factorial*2^n*2^(H.card-(n*(n-2)*(n-4)/96)) := by
  apply (exceptional_bound hH sep (n*(n-2)*(n-4)/96) ?_).trans_eq (by simp)
  intro σ hp ne
  have h := quadruple_block_motion hH σ hp ne
  omega

private theorem binary_size (d : ℕ) (hd : 7≤d) : 128≤2^d ∧ 8*(d+2)≤2^d := by
  induction d,hd using Nat.le_induction with
  | base => decide
  | succ d hd ih => rw [pow_succ]; omega

theorem binary_motion_budget (d : ℕ) (hd : 7≤d) {H : Finset (Finset (Fin (2^d)))} (hH : H.IsBlockDesign 3 4) :
    let n := 2^d
    let E := n^3/1024
    192*E≤n*(n-2)*(n-4) ∧ 2*E≤H.card ∧ d*n+n+1≤E := by
  let n := 2^d
  let E := n^3/1024
  have ⟨hn,large⟩ := binary_size d hd
  change 128≤n at hn
  change 8*(d+2)≤n at large
  have floorE : E*1024≤n^3 := Nat.div_mul_le_self ..
  have powerBudget : n*(d+2)≤E := by
    apply (Nat.le_div_iff_mul_le (by decide : 0<1024)).mpr
    calc
      n*(d+2)*1024 = n*(128*(8*(d+2))) := by ring
      _ ≤ n*(n*n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hn large)
      _ = n^3 := by ring
  have poly : n^3≤4*(n*(n-2)*(n-4)) := by
    calc
      n^3 = n*n*n := by ring
      _ ≤ (n*(2*(n-2)))*(2*(n-4)) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = _ := by ring
  have budget : 192*E≤n*(n-2)*(n-4) := by omega
  have enough : 2*E≤H.card := by
    have bc := base_block_count hH
    rw [Fintype.card_fin] at bc
    change H.card=blockNumber n at bc
    rw [bc,blockNumber_formula]
    apply (Nat.le_div_iff_mul_le (by decide : 0<24)).mpr
    have mono : n*(n-2)*(n-4)≤n*(n-1)*(n-2) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    omega
  exact ⟨budget,enough,by change d*n+n+1≤E; nlinarith [powerBudget]⟩

/-- At order n=2^d, d≥7, fewer than or equal to one in 2^(n³/1024) switches
can give a double with an automorphism outside its vertical check group. -/
theorem cubic_exceptional_bound (d : ℕ) (hd : 7≤d) {H : Finset (Finset (Fin (2^d)))}
    (hH : H.IsBlockDesign 3 4) (sep : Separates H) :
    (exceptional hH).card * 2^((2^d)^3/1024) ≤ 2^H.card := by
  let n := 2^d
  let E := n^3/1024
  obtain ⟨budget,enough,expCap⟩ := binary_motion_budget d hd hH
  change 192*E≤n*(n-2)*(n-4) at budget
  change 2*E≤H.card at enough
  change d*n+n+1≤E at expCap
  have ex := exceptional_bound hH sep (2*E) (fun σ hp ne => by
    have motion := quadruple_block_motion hH σ hp ne
    change n*(n-2)*(n-4)≤48*_ at motion
    omega)
  rw [Fintype.card_fin] at ex
  change (exceptional hH).card≤2^n+n.factorial*2^n*2^(H.card-2*E) at ex
  have factorial : n.factorial≤2^(d*n) :=
    n.factorial_le_pow.trans_eq (pow_mul 2 d n).symm
  have lower : n+1≤E := (Nat.le_add_left (n+1) (d*n)).trans (by simpa only [Nat.add_assoc] using expCap)
  have epos : 0<E := (Nat.succ_pos n).trans_le lower
  have pos : 0<H.card := (Nat.mul_pos (by decide : 0<2) epos).trans_le enough
  have one : 2^n*2^E≤2^(H.card-1) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have two : n.factorial*2^n*2^(H.card-2*E)*2^E≤2^(H.card-1) := by
    apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ factorial))).trans
    simp only [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  change (exceptional hH).card*2^E≤_
  apply (Nat.mul_le_mul_right _ ex).trans
  rw [add_mul]
  apply (Nat.add_le_add one two).trans_eq
  rw [← Nat.mul_two,← pow_succ,show H.card-1+1=H.card by omega]

#print axioms separating_exceptional_bound
#print axioms binary_motion_budget
#print axioms cubic_exceptional_bound
end Erdos722.QuadSwitch
