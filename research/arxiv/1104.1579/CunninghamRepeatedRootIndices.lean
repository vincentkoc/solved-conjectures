import CunninghamCollisionCofactor
import CunninghamLinearReciprocalRoots

/-! A reduction modulo two bounds the smaller iterate in a noncyclotomic collision. -/

namespace CunninghamChain.SharedFactors
open Polynomial LinearRoots

private lemma mod_two_degree {g i j : ℕ} (hg : 0 < g) (hj : 0 < j) :
    ((cofactor g i j).map (Int.castRingHom (ZMod 2))).natDegree+g = g*j := by
  let Q := (cofactor g i j).map (Int.castRingHom (ZMod 2))
  have e := congrArg (Polynomial.map (Int.castRingHom (ZMod 2))) (cofactor_identity g i j)
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    simpa only [map_ofNat,map_zero] using congrArg (C (R := ZMod 2)) (show (2 : ZMod 2)=0 by decide)
  have eq : (X^g-1)*Q = -(X^(g*j)+1 : (ZMod 2)[X]) := by
    simpa [Q,Polynomial.map_sub,h2] using e
  have hn : (X^(g*j)+1 : (ZMod 2)[X]).natDegree = g*j :=
    natDegree_X_pow_add_C (r := 1)
  have hpos := Nat.mul_pos hg hj
  have hne : (X^(g*j)+1 : (ZMod 2)[X]) ≠ 0 := by intro h; simp [h] at hn; omega
  have hp : (X^g-1 : (ZMod 2)[X]) ≠ 0 := by
    intro h
    have := leadingCoeff_X_pow_sub_one (R := ZMod 2) hg
    simp [h] at this
  have hq : Q ≠ 0 := by intro h; rw [h,mul_zero] at eq; exact (neg_ne_zero.mpr hne) eq.symm
  have dd := congrArg natDegree eq
  rw [natDegree_mul hp hq,show (X^g-1:(ZMod 2)[X]).natDegree = g from natDegree_X_pow_sub_C (r:=1),
    natDegree_neg,hn] at dd
  dsimp [Q] at dd
  omega

private lemma third_coeff (k : Bool) (f : ℤ[X]) (s : ℕ) :
    ((polynomialTerm k f (s+3)).map (Int.castRingHom (ZMod 2))).coeff 2 = 1 := by
  cases k <;> simp [polynomialTerm,coeff_X_mul,coeff_map,coeff_one]

lemma quotient_degree {a b : ℤ} (ha : a ≠ 0) {k : Bool} {g i j : ℕ}
    (hg : 0 < g) (hi : 0 < i) {B : ℤ[X]}
    (hB : polynomialTerm k (C a*X+C b) (g*i) = cofactor g i j*B) :
    B.natDegree+g*j=g+1 := by
  let f := polynomialTerm k (C a*X+C b) (g*i)
  have hlin : (C a*X+C b).natDegree = 1 := natDegree_linear ha
  have hf : f.natDegree = 1+g*i := by
    have := (polynomialTerm_shape k _ (show 0 < (C a*X+C b).natDegree by omega) (g*i)).1
    dsimp [f]; omega
  have hf0 : f ≠ 0 := by intro h; rw [h,natDegree_zero] at hf; omega
  change f=cofactor g i j*B at hB
  have h0 := mul_ne_zero_iff.mp (hB ▸ hf0)
  have fd := congrArg natDegree hB
  rw [natDegree_mul h0.1 h0.2,hf] at fd
  have hd := (cofactor_shape (j:=j) hg hi).1
  rw [Nat.mul_add] at hd
  omega

/-- If the noncyclotomic cofactor divides the earlier iterate, its index is at most two. -/
theorem collision_index_bounds {a b : ℤ} (ha : a ≠ 0) {k : Bool} {g i j : ℕ}
    (hg : 0 < g) (hi : 0 < i) (hj : 0 < j)
    (hdvd : cofactor g i j ∣ polynomialTerm k (C a*X+C b) (g*i)) :
    g*i ≤ 2 ∧ g*j ≤ g+1 := by
  let f := polynomialTerm k (C a*X+C b) (g*i)
  obtain ⟨B,hB : f=cofactor g i j*B⟩ := hdvd
  have fd := quotient_degree ha hg hi hB
  refine ⟨?_,by omega⟩
  by_contra! big
  let φ := Int.castRingHom (ZMod 2)
  have hlo : 2 ≤ (f.map φ).natDegree := by
    apply le_natDegree_of_ne_zero
    obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_le (show 3 ≤ g*i by omega)
    dsimp [f,φ]; rw [hs,add_comm 3,third_coeff]
    decide
  have e := congrArg (Polynomial.map φ) hB
  rw [Polynomial.map_mul] at e
  have htop : (f.map φ).natDegree ≤ ((cofactor g i j).map φ).natDegree+B.natDegree := by
    rw [e]
    exact (natDegree_mul_le ..).trans (Nat.add_le_add_left natDegree_map_le _)
  have hm := mod_two_degree (i:=i) hg hj
  change ((cofactor g i j).map φ).natDegree+g = g*j at hm
  omega

#print axioms collision_index_bounds

end CunninghamChain.SharedFactors
