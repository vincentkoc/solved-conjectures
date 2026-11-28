import CunninghamJonesPrescribedBlocks
import CunninghamSquarefreeLinearChains

/-! Infinite first-kind polynomial Cunningham chains with prescribed prime multiplicities. -/

namespace CunninghamChain.JonesSplitParity
open Polynomial Finset

private theorem chain_of_certificate {m : ℕ} (hm : 3 ≤ m) (cert : UnitarySplitCertificate m) :
    IsInfinitePolynomialChain true (C (m:ℤ)*X+1) :=
  chain_of_irreducible_sums (by omega) (fun i => irreducible_all_degrees_of_coprime_splits hm cert (by omega))

/-- Every prime-power leading coefficient gives an infinite chain. -/
theorem prime_power_linear_infinite {m : ℕ} (hm : IsPrimePow m) :
    IsInfinitePolynomialChain true (C (m:ℤ)*X+1) := by
  have hpos := hm.one_lt
  by_cases ht : m=2
  · subst m
    simpa using prime_linear_firstKind_infinite 2 Nat.prime_two
  apply chain_of_certificate (by omega)
  intro u v hu hv he hc
  have hd : m ∣ u*v := he ▸ dvd_refl _
  rcases (hc.isPrimePow_dvd_mul hm).mp hd with h|h
  · have := Nat.le_of_dvd (by omega : 0<u) h
    nlinarith
  · have := Nat.le_of_dvd (by omega : 0<v) h
    nlinarith

/-- Infinitely many coefficients m have exactly the prescribed positive
multiplicities on increasing primes above the cutoff. For each such m, all
odd powers of m give chains irreducible in every degree. -/
theorem infinitely_many_prescribed_linear_chains (e : ℕ → ℕ) (n B : ℕ)
    (he : ∀ i ≤ n, 0 < e i) :
    {m : ℕ | (∃ q : ℕ → ℕ, StrictMonoOn q (Set.Iio (n+1)) ∧
       (∀ i ≤ n, (q i).Prime ∧ B < q i ∧ m.factorization (q i) = e i) ∧
       m = ∏ i ∈ range (n+1),q i^e i) ∧
      ∀ h : ℕ, Odd h → IsInfinitePolynomialChain true (C ((m^h : ℕ):ℤ)*X+1)}.Infinite := by
  classical
  apply Set.infinite_of_forall_exists_gt
  intro L
  obtain ⟨q,k,c,pat,incr,large⟩ := exists_prescribed_blocks e n (max B L) he
  let T := range (n+1)
  let m := ∏ i ∈ T,q i^e i
  have pos (i : ℕ) (hi : i ∈ T) := (large i (Nat.lt_succ_iff.mp (mem_range.mp hi))).1.pos
  have dv : q 0 ∣ m := (dvd_pow_self (q 0) (he 0 (Nat.zero_le n)).ne').trans
    (dvd_prod_of_mem (fun i => q i^e i) (mem_range.mpr (show 0<n+1 by omega)))
  have le := Nat.le_of_dvd (prod_pos fun i hi => pow_pos (pos i hi) _) dv
  have hm : 3 ≤ m := by have := pat.large 0 (Nat.zero_le n); omega
  refine ⟨m,⟨⟨q,incr,?_,rfl⟩,?_⟩,((le_max_right ..).trans_lt (large 0 (Nat.zero_le n)).2).trans_le le⟩
  · intro i hi
    obtain ⟨hp,hl⟩ := large i hi
    refine ⟨hp,(le_max_left ..).trans_lt hl,?_⟩
    rw [show m=(∏ j ∈ T,q j^e j) by rfl,Nat.factorization_prod_apply (fun j hj => pow_ne_zero _ (pos j hj).ne')]
    have hit : i ∈ T := mem_range.mpr (Nat.lt_succ_of_le hi)
    rw [sum_eq_single_of_mem i hit]
    · exact Nat.factorization_pow_self hp
    · intro j hj hne
      have hq := (large j (Nat.lt_succ_iff.mp (mem_range.mp hj))).1
      have hdiff := incr.injOn.ne (mem_range.mp hj) (Nat.lt_succ_of_le hi) hne
      simp [hq.factorization_pow,hdiff]
  · intro h hh
    obtain ⟨t,ht⟩ := hh
    have hm' : m ≤ m^h := Nat.le_of_dvd (pow_pos (by omega : 0 < m) _) (dvd_pow_self _ (by omega))
    apply chain_of_certificate (by omega)
    exact (pat.certificate (fun i hi => (isPrimePow_pow_iff (he i hi).ne').mpr (large i hi).1.isPrimePow)).odd_pow ⟨t,ht⟩

#print axioms prime_power_linear_infinite
#print axioms infinitely_many_prescribed_linear_chains

end CunninghamChain.JonesSplitParity
