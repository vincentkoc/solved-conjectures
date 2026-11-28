import CunninghamJonesPrimeConstruction
import research.arxiv.«1104.1579».CunninghamPolynomialInfinite

/-! Infinite first-kind polynomial chains with a squarefree leading coefficient
composed of a prescribed number of arbitrarily large primes. -/

namespace CunninghamChain.JonesSplitParity
open Polynomial Finset

private theorem linear_iterate_reflect (m i : ℕ) :
    (jonesSumPolynomial m (i+1)).reflect (i+1)=polynomialTerm true (C (m:ℤ)*X+1) i := by
  induction i with
  | zero =>
    simp [jonesSumPolynomial, polynomialTerm,add_comm]
    simpa using reflect_C (m:ℤ) 1
  | succ i ih =>
    have grow := reflect_mul (jonesSumPolynomial m (i+1)) (1 : ℤ[X])
      (le_of_eq (jonesSumPolynomial_shape ..).1) (show (1:ℤ[X]).natDegree≤1 by simp)
    simp only [mul_one,reflect_one,pow_one] at grow
    rw [jonesSumPolynomial_succ,reflect_add,reflect_monomial,revAt_le (le_refl _),Nat.sub_self,
      pow_zero,grow,ih,polynomialTerm]
    simp [mul_comm,add_comm]

private theorem chain_of_irreducible_sums {m : ℕ} (hm : 0 < m)
    (h : ∀ i : ℕ, Irreducible ((jonesSumPolynomial m (i+1)).map (Int.castRingHom ℚ))) :
    IsInfinitePolynomialChain true (C (m:ℤ)*X+1) := by
  have hm' : (m:ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨?_,?_⟩
  · change 0 < (C (m:ℤ)*X + C 1).leadingCoeff
    rw [leadingCoeff_linear hm']
    exact_mod_cast hm
  intro i
  let f := (jonesSumPolynomial m (i+1)).map (Int.castRingHom ℚ)
  have hd : f.natDegree=i+1 := by
    dsimp [f]
    rw [natDegree_map_eq_of_injective (Int.cast_injective), (jonesSumPolynomial_shape ..).1]
  have hz : f.coeff 0 ≠ 0 := by
    simp [f,jonesSumPolynomial,finsetSum_coeff,coeff_X_pow,hm.ne']
  let mir : ℚ[X] ≃* ℚ[X] := {
    toFun := mirror
    invFun := mirror
    left_inv := mirror_mirror
    right_inv := mirror_mirror
    map_mul' := fun a b => mirror_mul_of_domain a b }
  have hh := (MulEquiv.irreducible_iff (x:=f) mir).mpr (h i)
  change Irreducible f.mirror at hh
  rw [mirror,natTrailingDegree_eq_zero.mpr (Or.inr hz),pow_zero,mul_one,reverse,hd] at hh
  simpa only [f,reflect_map,linear_iterate_reflect] using hh

/-- For each positive r and cutoff B, infinitely many squarefree leading
coefficients have exactly r prime divisors, all above B, and the first-kind
chain from mX+1 consists of irreducible rational polynomials at every index. -/
theorem infinitely_many_squarefree_linear_chains (r B : ℕ) (hr : 0<r) :
    {m : ℕ | Squarefree m ∧ m.primeFactors.card=r ∧
      (∀ p ∈ m.primeFactors, B<p) ∧ IsInfinitePolynomialChain true (C (m:ℤ)*X+1)}.Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro L
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  obtain ⟨q,k,h,hs,above⟩ := exists_prime_pattern n (max B L)
  let T := range (n+1)
  let m := ∏ i ∈ T,q i
  have pr {i} (hi : i ∈ T) := h.prime i (Nat.le_of_lt_succ (mem_range.mp hi))
  have inj : Set.InjOn q T := fun _ hi _ hj he => hs.injOn (mem_range.mp hi) (mem_range.mp hj) he
  have sf : Squarefree m := squarefree_prod_of_pairwise_isCoprime
    (fun i hi j hj hij => (Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (pr hi) (pr hj)).mpr (fun he => hij (inj hi hj he)))))
    (fun i hi => (pr hi).prime.squarefree)
  have prod_eq : (∏ p ∈ T.image q,p)=m := Finset.prod_image inj
  have factors : m.primeFactors=T.image q := by
    rw [←prod_eq]
    exact Nat.primeFactors_prod fun p hp => by obtain ⟨i,hi,rfl⟩ := mem_image.mp hp; exact pr hi
  have hgt : max B L < m := (above 0 (Nat.zero_le n)).trans_le
    (Nat.le_of_dvd (prod_pos fun i hi => (pr hi).pos) (dvd_prod_of_mem q (mem_range.mpr (show 0<n+1 by omega))))
  refine ⟨m,⟨sf,?_,?_,chain_of_irreducible_sums (by omega) (fun i => irreducible_of_prime_pattern h (by omega))⟩,by omega⟩
  · rw [factors,card_image_of_injOn inj]
    exact card_range _
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (factors ▸ hp)
    exact (le_max_left ..).trans_lt (above i (Nat.le_of_lt_succ (mem_range.mp hi)))

#print axioms infinitely_many_squarefree_linear_chains

end CunninghamChain.JonesSplitParity
