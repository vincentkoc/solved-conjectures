import Erdos722PlaneExtensionArithmetic
import Erdos722SignedSteinerObstruction

/-!
# The first two possible orders of a nontrivial Steiner design

The replication number at an (r-1)-set forces the order to take steps
of size k-r+1. At the first order allowed by Cameron's exterior-point
bound, Hughes's arithmetic leaves only five possible parameter triples.
-/

namespace Erdos722.MinimumOrder
open Finset IntegralDesign

/-- Apart from the five listed arithmetic exceptions, a nontrivial
design of rank at least three has at least `(k-r+2)^2+r-2` points. -/
theorem boundary_or_square {n r k : ℕ} (hr : 3 ≤ r) (hrk : r < k) (hkn : k < n)
    {H : Finset (Finset (Fin n))} (hH : H.IsBlockDesign r k) :
    (k-r+2)^2+(r-2) ≤ n ∨
      (r=3 ∧ k=4 ∧ n=8) ∨ (r=3 ∧ k=6 ∧ n=22) ∨ (r=4 ∧ k=7 ∧ n=23) ∨
      (r=5 ∧ k=8 ∧ n=24) ∨ (r=3 ∧ k=12 ∧ n=112) := by
  let q := k-r+1
  have hq : 2 ≤ q := by dsimp [q]; omega
  have hkq : k=q+(r-1) := by dsimp [q]; omega
  have hbase := exterior_point_bound (s:=r-2) (by omega : r-2+2≤k) hkn
    (show H.IsBlockDesign (r-2+2) k by rwa [show r-2+2=r by omega])
  rw [show k-(r-2+1)=q by dsimp [q]; omega,
    show k-(r-2)=q+1 by dsimp [q]; omega,
    show r-2+1=r-1 by omega] at hbase
  have tests := (signed_steiner_iff n r k hrk.le hkn.le).mp ⟨_,design_weights hH⟩
  by_cases he : n=q*(q+1)+(r-1)
  · right
    rw [hkq,he] at tests
    rcases (equality_divisibilities hq hr).mp tests with
      (⟨a,b⟩|⟨a,b|b|b⟩|⟨a,b⟩) <;> rw [a,b] at hkq he <;> norm_num at hkq he <;> omega
  · left
    have step := tests (r-1) (by omega)
    rw [show r-(r-1)=1 by omega,Nat.choose_one_right,Nat.choose_one_right,
      show k-(r-1)=q by dsimp [q]; omega] at step
    obtain ⟨a,ha⟩ := step
    have hlt : q*(q+1)<q*a := by omega
    have hnext : q+2 ≤ a := Nat.lt_of_mul_lt_mul_left hlt
    have hb := Nat.mul_le_mul_left q hnext
    rw [show k-r+2=q+1 from rfl,show (q+1)^2=q*(q+2)+1 by ring]
    omega

/-- For every other triple block size, the inversive-plane order is a
lower bound, without assuming that the block size minus one is a prime power. -/
theorem triple_square_lower {v k : ℕ} (hk : 3 < k) (hv : k < v)
    (h₄ : k ≠ 4) (h₆ : k ≠ 6) (h₁₂ : k ≠ 12)
    {H : Finset (Finset (Fin v))} (hH : H.IsBlockDesign 3 k) : (k-1)^2+1 ≤ v := by
  rcases boundary_or_square (by decide : 3≤3) hk hv hH with h|h
  · simpa [show k-3+2=k-1 by omega] using h
  · omega

#print axioms boundary_or_square
#print axioms triple_square_lower
end Erdos722.MinimumOrder
