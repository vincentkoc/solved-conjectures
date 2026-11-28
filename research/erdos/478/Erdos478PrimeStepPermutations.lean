import Erdos478PrimeDifferenceMoments

/-!
# Permutations preserving a small set of prime-field differences

This is the polynomial argument of Peter Müller, *Permutation groups of prime
degree, a quick proof of Burnside's theorem*, in finite-difference form.
-/

namespace Erdos478.PrimeDifferences
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem eq_on_field {f g : (ZMod p)[X]} (hf : f.natDegree<p) (hg : g.natDegree<p)
    (h : ∀ x, f.eval x=g.eval x) : f=g := by
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (univ : Finset (ZMod p))
  · simpa only [card_univ,ZMod.card,Nat.cast_withBot] using (degree_le_natDegree (p := f)).trans_lt (WithBot.coe_lt_coe.mpr hf)
  · simpa only [card_univ,ZMod.card,Nat.cast_withBot] using (degree_le_natDegree (p := g)).trans_lt (WithBot.coe_lt_coe.mpr hg)
  · exact fun x _ => h x

private theorem difference_zero {U : Finset (ZMod p)} {k : ℕ}
    (hsmall : ∀ i, 0 < i → i < k → moment U i=0) {f : (ZMod p)[X]} (hf : f.natDegree<k) :
    difference U f=0 := by
  ext j
  rw [difference_coeff U f hf,coeff_zero]
  apply sum_eq_zero
  intro i hi
  obtain ⟨hi₀,hi⟩ := mem_erase.mp hi
  rw [hsmall i (by omega) (mem_range.mp hi),mul_zero]

private theorem transport {U : Finset (ZMod p)} {g : Equiv.Perm (ZMod p)}
    (hg : ∀ x u, u∈U → g (x+u)-g x∈U) (x : ZMod p) (F : ZMod p → ZMod p) :
    ∑ u ∈ U, (F (g (x+u))-F (g x))=∑ u ∈ U, (F (g x+u)-F (g x)) := by
  let t (u : ZMod p) := g (x+u)-g x
  have ht : Function.Injective t := fun a b h => add_left_cancel (g.injective (sub_left_inj.mp h))
  have him : U.image t=U :=
    eq_of_subset_of_card_le (by simpa [Finset.image_subset_iff,t] using hg x)
      (le_of_eq (card_image_of_injective U ht).symm)
  calc
    _ = ∑ u ∈ U, (F (g x+t u)-F (g x)) := by simp [t]
    _ = ∑ u ∈ U.image t, (F (g x+u)-F (g x)) := (sum_image (f := fun u => F (g x+u)-F (g x)) ht.injOn).symm
    _ = _ := by rw [him]

/-- Preserving a nonempty set of at most half of the nonzero differences forces affinity. -/
theorem affine_of_step_preserving {U : Finset (ZMod p)} (hU : U.Nonempty) (h0 : 0∉U)
    (hhalf : 2*U.card<p) (g : Equiv.Perm (ZMod p))
    (hg : ∀ x u, u∈U → g (x+u)-g x∈U) :
    ∃ a b : ZMod p, ∀ x, g x=a*x+b := by
  classical
  have pp := (Fact.out : p.Prime).pos
  let f := Lagrange.interpolate (univ : Finset (ZMod p)) id (g : ZMod p → ZMod p)
  have hv (x : ZMod p) : f.eval x=g x :=
    Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn (mem_univ x)
  have hd : f.natDegree<p := by
    have hf := natDegree_le_of_degree_le (Lagrange.degree_interpolate_le (g : ZMod p → ZMod p)
      (s:=(univ : Finset (ZMod p))) Function.injective_id.injOn)
    simp only [card_univ,ZMod.card] at hf
    change (Lagrange.interpolate _ _ _).natDegree<p
    omega
  have hex := exists_moment hU h0 (by omega)
  let k := Nat.find hex
  obtain ⟨hk,hcard,hM⟩ := Nat.find_spec hex
  change 0<k at hk
  change k≤U.card at hcard
  change moment U k≠0 at hM
  have hsmall (i : ℕ) (hi : 0 < i) (hik : i<k) : moment U i=0 := by
    by_contra h
    have := Nat.find_min' hex (show 0 < i ∧ i≤U.card ∧ moment U i≠0 from ⟨hi,by omega,h⟩)
    change k ≤ i at this
    omega
  have hconstant : difference U f=C (moment U 1) := by
    apply eq_on_field ((difference_degree U f).trans_lt hd) (by simpa using pp)
    intro x
    rw [difference_eval,eval_C]
    simp_rw [hv]
    simpa [moment] using transport hg x id
  have hdeg : f.natDegree≤1 := by
    by_contra! hlarge
    have hdk : f.natDegree≤k := by
      by_contra! hlt
      have hne := difference_leading hk hM hsmall hlt.le hd
      rw [hconstant,coeff_C_of_ne_zero (by omega)] at hne
      exact hne rfl
    let d := f.natDegree
    let w := (k-1)/d+1
    have hd₂ : 2≤d := hlarge
    have hwl : w<k := by
      have hq : (k-1)/d<k-1 := (Nat.div_lt_iff_lt_mul (by omega)).2 (by
        have := Nat.mul_le_mul_left (k-1) hd₂
        dsimp [d] at *
        omega)
      dsimp [w]
      omega
    have hkw : k≤w*d := by
      have := Nat.lt_mul_div_succ (k-1) (show 0<d by omega)
      rw [mul_comm d] at this
      dsimp [w]
      omega
    have hwp : w*d<p := by
      have := Nat.div_mul_le_self (k-1) d
      simp only [w,add_mul,one_mul]
      change d≤k at hdk
      omega
    have hdegpower : (f^w).natDegree=w*d := natDegree_pow f w
    have hz : difference U (X^w)=0 := difference_zero hsmall (by simpa using hwl)
    have hpow : difference U (f^w)=0 := by
      apply eq_on_field ((difference_degree U _).trans_lt (hdegpower ▸ hwp)) (by simpa using pp)
      intro x
      have he := congrArg (Polynomial.eval (g x)) hz
      rw [difference_eval,eval_zero] at he
      rw [difference_eval,eval_zero]
      simp_rw [eval_pow,hv]
      simpa only [eval_pow,eval_X] using (transport hg x (fun z => z^w)).trans (by simpa using he)
    have hne := difference_leading hk hM hsmall (hdegpower ▸ hkw) (hdegpower ▸ hwp)
    simp [hpow] at hne
  refine ⟨f.coeff 1,f.coeff 0,fun x => ?_⟩
  rw [← hv,eval_eq_sum_range' (show f.natDegree<2 by omega)]
  simp [sum_range_succ,add_comm]

#print axioms affine_of_step_preserving
end
end Erdos478.PrimeDifferences
