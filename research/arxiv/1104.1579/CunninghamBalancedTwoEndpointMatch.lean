import CunninghamBalancedTwoCoefficients

/-! The four prescribed entries consume the entire squared coefficient weight. -/

namespace CunninghamChain.BalancedTwo
open Polynomial CoefficientSlices CoefficientEnergy LargeGap

lemma rigid_match (k : Bool) {N n : ℕ} (hN : 5≤N) (g : ℤ[X]) (dg : g.natDegree≤N)
    (h₀ : g.coeff 0=1) (hg : g*reflect N g=sparse k N*reflect N (sparse k N))
    (hit : (high N g.coeff n).reverse.take 3=[leading k,nextCoeff k,thirdCoeff k]) :
    g=sparse k N := by
  have len : 3≤n := by
    have hl := congrArg List.length hit
    simp [high,slice] at hl
    omega
  have coeff (i : ℕ) (hi : i<3) :
      g.coeff (N-i)=[leading k,nextCoeff k,thirdCoeff k][i]'(by simpa using hi) := by
    have l := congrArg (fun a : List ℤ => a[i]?) hit
    simpa [high,slice,List.getElem?_eq_getElem,hi,show i<n by omega,
      show i < min 3 n by omega] using l
  have top := coeff 0 (by decide)
  have near := coeff 1 (by decide)
  have third := coeff 2 (by decide)
  simp only [Nat.sub_zero,List.getElem_cons_zero,List.getElem_cons_succ] at top near third
  have wt : energy g (N+1)=energy (sparse k N) (N+1) := by
    rw [←coeff_mul_self_reflect,←coeff_mul_self_reflect,hg]
  apply fixed_energy_agreement _ _ (sparse_degree k (by omega)) dg wt
  intro i _ nz
  rw [sparse_eq k (by omega)] at nz ⊢
  simp only [coeff_add,coeff_monomial] at nz ⊢
  split_ifs at nz ⊢ <;> first | omega | (subst i; omega)

lemma witness_data (k : Bool) {N : ℕ} (hN : 5≤N) (g : ℤ[X]) (dg : g.natDegree≤N)
    (hg : g*reflect N g=sparse k N*reflect N (sparse k N)) :
    let xs := slice (N+1) g.coeff
    xs.sum=0 ∧ squaredNorm xs=(if k then 30 else 22) ∧
      dot xs (xs.drop 1)=lagOne k ∧ dot xs (xs.drop 2)=lagTwo k := by
  dsimp only
  have hv : g.eval 1=0 := by
    have ev := congrArg (fun U : ℤ[X] => U.eval 1) hg
    have same : (reflect N g).eval 1=g.eval 1 := by
      let := invertibleOne (α:=ℤ)
      simpa [eval₂_id] using eval₂_reflect_mul_pow (RingHom.id ℤ) (1:ℤ) N g dg
    simp only [eval_mul,sparse_at_one k (by omega : 2≤N),zero_mul,same,mul_eq_zero,or_self] at ev
    exact ev
  have lag (i : ℕ) (hi : i≤N) := (full_lag N i hi g).trans
    ((congrArg (fun P : ℤ[X] => P.coeff (N-i)) hg).trans
      (sparse_correlation k hN (Nat.sub_le N i)))
  refine ⟨?_,?_,?_,?_⟩
  · rw [slice_sum,←hv,Polynomial.eval_eq_sum_range' (by omega : g.natDegree<N+1)]
    simp
  · have h := lag 0 (by omega)
    simp only [Nat.sub_zero,List.drop_zero,←squaredNorm_cast] at h
    split_ifs at h ⊢ <;> omega
  · have h := lag 1 (by omega)
    split_ifs at h <;> omega
  · have h := lag 2 (by omega)
    split_ifs at h <;> omega

#print axioms rigid_match
#print axioms witness_data

end CunninghamChain.BalancedTwo
