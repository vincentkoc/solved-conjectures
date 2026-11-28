import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-!
# A cubic residue-field obstruction at two

For odd lengths 3 and 11 modulo 14 the gap polynomial in characteristic
two has an irreducible cubic factor. Any finite splitting field in that
characteristic has degree divisible by three.
-/

namespace Erdos478.BinaryGap
open Polynomial Function
open scoped Polynomial
noncomputable section

theorem odd_value {K : Type*} [CommRing K] [CharP K 2] (x : K) (h : ℕ) :
    (descPochhammer K (2*h+1)).eval x=x*(x*(x+1))^h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show 2*(h+1)+1=(2*h+1)+1+1 by omega,descPochhammer_succ_eval,descPochhammer_succ_eval,ih]
    push_cast
    rw [CharTwo.two_eq_zero]
    simp only [zero_mul,zero_add,CharTwo.add_self_eq_zero,CharTwo.sub_eq_add,pow_succ]
    ring

def cubic (second : Bool) : (ZMod 2)[X] := if second then X^3+X+1 else X^3+X^2+1

theorem cubic_degree (s : Bool) : (cubic s).natDegree=3 := by
  cases s <;> simp only [cubic,Bool.false_eq_true,if_false,if_true] <;> compute_degree!

theorem cubic_irreducible (s : Bool) : Irreducible (cubic s) := by
  have hd := cubic_degree s
  apply (irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr
  apply Multiset.eq_zero_of_forall_notMem
  intro x hx
  have h := (mem_roots (show cubic s≠0 by intro he; simp [he] at hd)).mp hx
  cases s <;> simp only [IsRoot,cubic,Bool.false_eq_true,if_false,if_true,eval_add,eval_pow,eval_one,eval_X] at h <;>
    fin_cases x <;> revert h <;> decide

private theorem root_value (s : Bool) (m : ℕ) :
    let K := AdjoinRoot (cubic s)
    let x : K := AdjoinRoot.root (cubic s)
    (descPochhammer K (2*(7*m+(if s then 5 else 1))+1)).eval x=1 := by
  let K := AdjoinRoot (cubic s)
  let x : K := AdjoinRoot.root (cubic s)
  let w := x*(x+1)
  let : Fact (Irreducible (cubic s)) := ⟨cubic_irreducible s⟩
  have hn := (cubic_irreducible s).ne_zero
  let B := AdjoinRoot.powerBasis hn
  let : FiniteDimensional (ZMod 2) K := B.finite
  let : Fintype K := Fintype.ofEquiv _ B.basis.equivFun.symm.toEquiv
  let : CharP K 2 := charP_of_injective_ringHom (algebraMap (ZMod 2) K).injective 2
  have hdim : Module.finrank (ZMod 2) K=3 := by
    rw [PowerBasis.finrank B,AdjoinRoot.powerBasis_dim hn,cubic_degree]
  have hcard : Fintype.card K=8 := by
    rw [@Module.card_eq_pow_finrank (K:=ZMod 2),ZMod.card,hdim]
    decide
  have hx : aeval x (cubic s)=0 := by
    rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_eq_zero]
  have rel : (if s then (x+1)*w else x*w)=1 := by
    cases s with
    | false =>
      simp [cubic] at hx
      change x*w=1
      have hh : x^3+x^2=1 := by
        simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left hx)
      dsimp [w]; linear_combination hh
    | true =>
      simp [cubic] at hx
      change (x+1)*w=1
      have hh : x^3+x=1 := by
        simpa only [CharTwo.neg_eq] using (eq_neg_of_add_eq_zero_left hx)
      calc (x+1)*w = x^3+x+2*x^2 := by dsimp [w]; ring
           _ = 1 := by rw [show (2:K)=0 from CharTwo.two_eq_zero,zero_mul,add_zero,hh]
  have hw : w≠0 := by
    intro h
    simp [h] at rel
  have pow7 : w^7=1 := by
    have h := FiniteField.pow_card_sub_one_eq_one w hw
    simpa only [hcard,show 8-1=7 by decide] using h
  change (descPochhammer K (2*(7*m+(if s then 5 else 1))+1)).eval x=1
  rw [odd_value]
  change x*w^(7*m+(if s then 5 else 1))=1
  rw [pow_add,pow_mul,pow7,one_pow,one_mul]
  cases s with
  | false => simpa using rel
  | true =>
    change (x+1)*w=1 at rel
    have he : x=w^2 := by
      calc x = x*((x+1)*w) := by rw [rel,mul_one]
           _ = w^2 := by dsimp [w]; ring
    change x*w^5=1
    rw [he,← pow_add]
    exact pow7

theorem cubic_factor (s : Bool) (m : ℕ) :
    cubic s ∣ descPochhammer (ZMod 2) (2*(7*m+(if s then 5 else 1))+1)-1 := by
  rw [← AdjoinRoot.mk_eq_zero,← AdjoinRoot.aeval_eq]
  rw [map_sub,map_one,sub_eq_zero,aeval_def,eval₂_eq_eval_map,descPochhammer_map]
  exact root_value s m

/-- Splitting the binary reduction at either length forces a cubic subdegree. -/
theorem three_dvd_reduction {K : Type*} [Field K] [Algebra (ZMod 2) K] (s : Bool) (m : ℕ)
    (h : (descPochhammer K (2*(7*m+(if s then 5 else 1))+1)-1).Splits) :
    3∣Module.finrank (ZMod 2) K := by
  rw [← cubic_degree s]
  apply (cubic_irreducible s).natDegree_dvd_finrank
  have hd := map_dvd (algebraMap (ZMod 2) K) (cubic_factor s m)
  simp only [Polynomial.map_sub,descPochhammer_map,Polynomial.map_one] at hd
  apply h.of_dvd _ hd
  intro he
  have eq := congrArg (Polynomial.eval (0:K)) (sub_eq_zero.mp he)
  simp at eq

#print axioms odd_value
#print axioms cubic_degree
#print axioms cubic_irreducible
#print axioms cubic_factor
#print axioms three_dvd_reduction
end
end Erdos478.BinaryGap
