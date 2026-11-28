import Mathlib

/-! A Frobenius inversion criterion for monic factors at Jones degrees. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

/-- Every monic divisor of X^(p^h+1)−1 over the prime field that is nonzero at
one has constant term one. In its quotient algebra, the hth Frobenius power acts on the
class of X by inversion. -/
theorem frobenius_divisor_constant {p h : ℕ} [Fact p.Prime] {a : (ZMod p)[X]}
    (ha : a.Monic) (hdiv : a ∣ X^(p^h+1)-1) (hone : a.eval 1 ≠ 0) :
    a.coeff 0 = 1 := by
  let x := AdjoinRoot.root a
  let y := x^(p^h)
  have hxy : y*x = 1 := by
    have he := AdjoinRoot.mk_eq_zero.mpr hdiv
    simpa [y,x,map_sub,map_pow,AdjoinRoot.mk_X,pow_succ,sub_eq_zero] using he
  let : Invertible y := ⟨x, mul_comm y x ▸ hxy, hxy⟩
  have fid : iterateFrobenius (ZMod p) p h = RingHom.id _ :=
    RingHom.ext (fun z => ZMod.pow_card_pow z)
  have hexp := map_iterateFrobenius_expand p a h
  rw [fid, Polynomial.map_id, expand_eq_comp_X_pow] at hexp
  have hy : a.eval₂ (AdjoinRoot.of a) y = 0 := by
    have he := congrArg (fun b : (ZMod p)[X] => b.eval₂ (AdjoinRoot.of a) x) hexp
    simpa [y,x,eval₂_comp,eval₂_pow,AdjoinRoot.eval₂_root, zero_pow (Nat.pow_pos (Fact.out : p.Prime).pos (n := h)).ne'] using he
  have hr : a ∣ a.reverse := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [← AdjoinRoot.aeval_eq, aeval_def, AdjoinRoot.algebraMap_eq]
    exact (eval₂_reverse_eq_zero_iff (AdjoinRoot.of a) y a).mpr hy
  have he := eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le ha hr a.reverse_natDegree_le
  let : Invertible (1 : ZMod p) := invertibleOne
  have hs : a.reverse.eval 1 = a.eval 1 := by
    simpa using eval₂_reverse_mul_pow (RingHom.id (ZMod p)) (1 : ZMod p) a
  have hlead : a.reverse.leadingCoeff = 1 := by
    rw [he, eval_mul, eval_C] at hs
    exact mul_left_cancel₀ hone (hs.trans (mul_one _).symm)
  have hv := congrArg (fun b : (ZMod p)[X] => b.coeff 0) he
  simpa [coeff_zero_reverse, ha.leadingCoeff, hlead] using hv.symm

#print axioms frobenius_divisor_constant

end CunninghamChain
