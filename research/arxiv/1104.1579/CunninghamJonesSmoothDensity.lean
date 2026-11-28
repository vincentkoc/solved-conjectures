import CunninghamJonesSmoothBounds
import CunninghamJonesPoweredDensity
import Mathlib.Data.Set.Card.Arithmetic

/-! Simultaneous density for Jones coefficients supported on at most three bounded primes. -/

namespace CunninghamChain
open Set Filter

/-- A bounded set of prime divisors supplies a finite union of progressions
once the exponent cutoff is fixed. -/
theorem exceptional_windows_of_prime_power_cover {B : ℕ} {E : Set ℕ}
    (cover : ∀ k : ℕ, ∃ D : ℕ, ∀ j ∈ E, D ≤ j → ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ p^k ∣ j)
    {ε : ℝ} (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ, (((E ∩ Ico a (a+N)).ncard : ℝ)/N) < ε := by
  classical
  let P := (Finset.range (B+1)).filter Nat.Prime
  obtain ⟨k,hk⟩ := exists_nat_gt (2*(P.card:ℝ)/ε)
  obtain ⟨D,hD⟩ := cover k
  let q := 2^k
  have hq : 2*(P.card:ℝ) < ε*q := by
    have hr : (k:ℝ) < q := by exact_mod_cast (Nat.lt_two_pow_self : k<2^k)
    linarith [(div_lt_iff₀ hε).mp (hk.trans hr)]
  obtain ⟨N₀,h₀⟩ := exists_nat_gt (2*((D:ℝ)+2*P.card)/ε)
  refine ⟨N₀+1,?_⟩
  intro N hn a
  let I := Ico a (a+N)
  let W (p : ℕ) := {j : ℕ | p^k ∣ j} ∩ I
  have hsub : E ∩ I ⊆ Iio D ∪ ⋃ p ∈ P, W p := by
    rintro j ⟨hj,hi⟩
    by_cases hl : j<D
    · exact Or.inl hl
    · obtain ⟨p,hp,hpB,hd⟩ := hD j hj (by omega)
      refine Or.inr (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨?_,hd,hi⟩⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp⟩
  have hf : (⋃ p ∈ P, W p).Finite := P.finite_toSet.biUnion (fun p _ => (finite_Ico ..).subset inter_subset_right)
  have count (p : ℕ) (hp : p ∈ P) : (W p).ncard ≤ N/q+2 := by
    have h := count_in_interval_of_divisibility (D:=0) (q:=p^k) (E:={j : ℕ | p^k ∣ j})
      (fun _ hj _ => hj) a N
    have hp₂ := (Finset.mem_filter.mp hp).2.two_le
    have hd : N/p^k ≤ N/q := Nat.div_le_div_left (Nat.pow_le_pow_left hp₂ k) (by dsimp [q]; positivity)
    exact (show (W p).ncard ≤ N/p^k+2 by simpa [W,I] using h).trans (by omega)
  have hsum := (P.set_ncard_biUnion_le W).trans (Finset.sum_le_sum count)
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc := (ncard_le_ncard hsub ((finite_Iio D).union hf)).trans (ncard_union_le ..)
  rw [Nat.ncard_Iio] at hc
  have hc' : ((E ∩ I).ncard : ℝ) ≤ D+(P.card:ℝ)*((N/q:ℕ)+2) := by
    exact_mod_cast hc.trans (Nat.add_le_add_left hsum D)
  have hfloor : ((N/q:ℕ):ℝ)*q ≤ N := by exact_mod_cast Nat.div_mul_le_self N q
  have hvar : (P.card:ℝ)*(N/q:ℕ) ≤ ε*N/2 := by
    have h₁ := mul_le_mul_of_nonneg_right hq.le (Nat.cast_nonneg (α:=ℝ) (N/q))
    have h₂ := mul_le_mul_of_nonneg_left hfloor hε.le
    nlinarith only [h₁,h₂]
  have hsize := (div_lt_iff₀ hε).mp (h₀.trans_le (show (N₀:ℝ) ≤ N by exact_mod_cast (show N₀ ≤ N by omega)))
  apply (div_lt_iff₀ (show (0:ℝ)<N by exact_mod_cast (show 0<N by omega))).mpr
  change ((E ∩ I).ncard:ℝ) < ε*N
  nlinarith only [hc',hvar,hsize]

/-- Degrees where at least one coefficient in the chosen family fails irreducibility. -/
def jonesCoefficientExceptions (M : Set ℕ) : Set ℕ :=
  {j | ∃ m ∈ M, ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ))}

/-- Coefficients at least two whose prime divisors are bounded by B. -/
def jonesSmoothCoefficients (B : ℕ) : Set ℕ :=
  {m | 2 ≤ m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ≤ B}

private theorem windows_for_family {B : ℕ} {M : Set ℕ}
    (h : ∀ k : ℕ, ∃ D : ℕ, ∀ j ≥ D, ∀ m ∈ M,
      ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) →
      ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ p^k ∣ j) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ, (((jonesCoefficientExceptions M ∩ Ico a (a+N)).ncard : ℝ)/N) < ε := by
  apply exceptional_windows_of_prime_power_cover (B:=B) _ hε
  intro k
  obtain ⟨D,hD⟩ := h k
  refine ⟨D,?_⟩
  rintro j ⟨m,hm,hred⟩ hj
  exact hD j hj m hm hred

/-- The exceptional proportion for all coefficients up to three bounded primes
tends to zero uniformly over interval starts. -/
theorem jones_three_prime_exceptional_windows (B : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ,
      (((jonesCoefficientExceptions {m ∈ jonesSmoothCoefficients B | m.primeFactors.card ≤ 3} ∩
        Ico a (a+N)).ncard : ℝ)/N) < ε := by
  apply windows_for_family (B:=B) _ hε
  intro k
  obtain ⟨D,hD⟩ := jones_three_prime_exceptional_degrees B k
  exact ⟨D,fun j hj m hm => hD j hj m hm.1.1 hm.2 hm.1.2⟩

/-- One set of density one works for the entire three-prime family, including
independently chosen and unbounded multiplicities at the three primes. -/
theorem jones_three_prime_density_one (B : ℕ) :
    {j : ℕ | ∀ m ∈ jonesSmoothCoefficients B, m.primeFactors.card ≤ 3 →
      Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ))}.HasDensity 1 := by
  have h := density_one_of_exceptional_windows _ (fun _ hε => jones_three_prime_exceptional_windows B hε)
  simpa only [jonesCoefficientExceptions,Set.compl_ofPred,Set.mem_ofPred_eq,not_exists,not_and,
    not_not,and_imp] using h

/-- Under the smooth-part estimate, the same uniform conclusion holds for
every B-smooth coefficient. -/
theorem jones_smooth_exceptional_windows {B : ℕ} (arith : JonesPadicLogBound B)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ,
      (((jonesCoefficientExceptions (jonesSmoothCoefficients B) ∩ Ico a (a+N)).ncard : ℝ)/N) < ε := by
  apply windows_for_family (B:=B) _ hε
  intro k
  obtain ⟨D,hD⟩ := jones_smooth_exceptional_degrees arith k
  exact ⟨D,fun j hj m hm => hD j hj m hm.1 hm.2⟩

/-- Conditional simultaneous irreducibility for all B-smooth coefficients,
with no limit on the number of prime divisors. -/
theorem jones_smooth_density_one {B : ℕ} (arith : JonesPadicLogBound B) :
    {j : ℕ | ∀ m ∈ jonesSmoothCoefficients B,
      Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ))}.HasDensity 1 := by
  have h := density_one_of_exceptional_windows _ (fun _ hε => jones_smooth_exceptional_windows arith hε)
  simpa only [jonesCoefficientExceptions,Set.compl_ofPred,not_exists,not_and,not_not] using h

#print axioms exceptional_windows_of_prime_power_cover
#print axioms jones_three_prime_exceptional_windows
#print axioms jones_three_prime_density_one
#print axioms jones_smooth_exceptional_windows
#print axioms jones_smooth_density_one

end CunninghamChain
