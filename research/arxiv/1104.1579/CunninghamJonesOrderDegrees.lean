import Mathlib

/-! Common divisors of the degrees of factors of X^j−1 over a prime
field. Evaluation at 1 removes the trivial root. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

private theorem irreducible_degree_multiple {p j k : ℕ} [Fact p.Prime] (hj : 0<j)
    (orders : ∀ q : ℕ, q.Prime → q ∣ j → k ∣ orderOf (p : ZMod q))
    {f : (ZMod p)[X]} (hir : Irreducible f) (hd : f ∣ X^j-1) (h1 : f.eval 1 ≠ 0) :
    k ∣ f.natDegree := by
  classical
  let : Fact (Irreducible f) := ⟨hir⟩
  let K := AdjoinRoot f
  let b := AdjoinRoot.powerBasis hir.ne_zero
  let : Module.Finite (ZMod p) K := Module.Finite.of_basis b.basis
  let : Finite K := Module.finite_of_finite (ZMod p)
  let : Fintype K := Fintype.ofFinite _
  let x := AdjoinRoot.root f
  have hjx : x^j=1 := by
    simpa [x,map_sub,map_pow,AdjoinRoot.mk_X,sub_eq_zero] using AdjoinRoot.mk_eq_zero.mpr hd
  have hx : x ≠ 0 := by
    intro he
    rw [he,zero_pow hj.ne'] at hjx
    exact zero_ne_one hjx
  have hn : x ≠ 1 := by
    intro he
    have hz := AdjoinRoot.eval₂_root f
    change f.eval₂ (algebraMap (ZMod p) K) x=0 at hz
    rw [he,← map_one (algebraMap (ZMod p) K),eval₂_hom] at hz
    exact h1 (by simpa using hz)
  have card : Fintype.card K = p^f.natDegree := by
    rw [Module.card_eq_pow_finrank (K:=ZMod p),ZMod.card]
    congr 1
    exact finrank_quotient_span_eq_natDegree
  let q := (orderOf x).minFac
  have hpq : q.Prime := Nat.minFac_prime (fun h => hn (orderOf_eq_one_iff.mp h))
  have hq : q ∣ orderOf x := Nat.minFac_dvd _
  have hsize : q ∣ p^f.natDegree-1 := by
    rw [←card]
    exact hq.trans (orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one x hx))
  have hp : p.Prime := Fact.out
  have he : 1 ≡ p^f.natDegree [MOD q] :=
    (Nat.modEq_iff_dvd' (Nat.pow_pos hp.pos)).mpr hsize
  have hf : (p : ZMod q)^f.natDegree = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff ..).mpr he.symm
  exact (orders q hpq (hq.trans (orderOf_dvd_of_pow_eq_one hjx))).trans (orderOf_dvd_of_pow_eq_one hf)

/-- If k divides the order of p modulo each prime dividing j, every
factor of X^j−1 which is nonzero at 1 has degree divisible by k. -/
theorem factor_degree_multiple_of_orders {p j k : ℕ} [Fact p.Prime] (hj : 0<j)
    (orders : ∀ q : ℕ, q.Prime → q ∣ j → k ∣ orderOf (p : ZMod q))
    {f : (ZMod p)[X]} (hd : f ∣ X^j-1) (h1 : f.eval 1 ≠ 0) : k ∣ f.natDegree := by
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at h1
  | unit u hu => rw [natDegree_eq_zero_of_isUnit hu]; exact dvd_zero _
  | mul a i ha hi ih =>
    rw [eval_mul,mul_ne_zero_iff] at h1
    rw [natDegree_mul hi.ne_zero ha]
    exact dvd_add (irreducible_degree_multiple hj orders hi ((dvd_mul_right ..).trans hd) h1.1)
      (ih ((dvd_mul_left ..).trans hd) h1.2)

#print axioms factor_degree_multiple_of_orders

end CunninghamChain
