import Erdos722ExceptionalMatchingWords

/-! # A relative error bound even after accounting for all rooted frames -/

namespace Erdos722.FourPoint
open Finset Filter Topology
noncomputable section

private theorem quadratic_room {d : ℕ} (hd : 8≤d) : 2*d*d+d+10≤2^d := by
  induction d,hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_self_le_mul_self hd]

private theorem enough_edges {n : ℕ} (hn : 2≤n) : n-2≤(n-1).choose 2 := by
  rw [show n-1=(n-2)+1 by omega,Nat.choose_succ_succ' (n-2) 1,Nat.choose_one_right]
  omega

/-- The exceptional mass times an upper bound on the orbit size is still
exponentially small. This permits counting isomorphism classes as well as words. -/
theorem scaled_exceptional_bound {d : ℕ} (hd : 8≤d) :
    exceptionalBound d * (6*(2^d)^d) * 2^d ≤ 6^numberEdges d := by
  let n := 2^d
  let m := numberEdges d
  have hn : 2≤n := by exact Nat.le_trans (by decide : 2≤2^8) (Nat.pow_le_pow_right (by decide) hd)
  have em : n-2≤m := enough_edges hn
  have tm : n-3≤m := by omega
  have shrink (r : ℕ) (hr : n-3≤r) (rm : r≤m) : 6^(m-r)*2^(n-3)≤6^m := by
    calc
      _ ≤ 6^(m-r)*6^r := Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by decide : 2≤6) _).trans
        (Nat.pow_le_pow_right (by decide) hr))
      _ = _ := by rw [← pow_add,Nat.sub_add_cancel rm]
  have mono : 3^m*2^(n-3)≤6^m := by
    calc
      _ ≤ 3^m*2^m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) tm)
      _ = _ := (mul_pow 3 2 m).symm
  have mass : exceptionalBound d*2^(n-3) ≤ ((n-1)+6*n^d+5)*6^m := by
    change ((n-1)*6^(m-(n-2))+n^d*(6*6^(m-(n-3)))+5*3^m)*2^(n-3)≤_
    calc
      _ = (n-1)*(6^(m-(n-2))*2^(n-3)) + (6*n^d)*(6^(m-(n-3))*2^(n-3)) + 5*(3^m*2^(n-3)) := by ring
      _ ≤ (n-1)*6^m + (6*n^d)*6^m + 5*6^m := Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left _ (shrink _ (by omega) em)) (Nat.mul_le_mul_left _ (shrink _ le_rfl tm)))
        (Nat.mul_le_mul_left _ mono)
      _ = _ := by ring
  have power : n^d=2^(d*d) := (pow_mul 2 d d).symm
  have large : n≤n^d := by simpa using (Nat.pow_le_pow_right (by omega : 0<n) (by omega : 1≤d))
  have coeff : (n-1)+6*n^d+5 ≤ 2^(d*d+4) := by
    rw [pow_add,← power]
    norm_num
    omega
  have weight : 6*n^d≤2^(d*d+3) := by rw [pow_add,← power]; omega
  have room := quadratic_room hd
  have budget : (6*n^d)*2^d*2^(d*d+4) ≤ 2^(n-3) := by
    calc
      _ ≤ 2^(d*d+3)*2^d*2^(d*d+4) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ weight)
      _ = 2^(2*d*d+d+7) := by rw [← pow_add,← pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [n]; omega)
  have combined := (Nat.mul_le_mul_left (exceptionalBound d) budget).trans (mass.trans (Nat.mul_le_mul_right _ coeff))
  apply Nat.le_of_mul_le_mul_right (c:=(2:ℕ)^(d*d+4)) _ (by positivity)
  calc
    _ = exceptionalBound d * ((6*n^d)*2^d*2^(d*d+4)) := by dsimp [n]; ring
    _ ≤ _ := combined.trans_eq (Nat.mul_comm ..)

#print axioms scaled_exceptional_bound
end
end Erdos722.FourPoint
