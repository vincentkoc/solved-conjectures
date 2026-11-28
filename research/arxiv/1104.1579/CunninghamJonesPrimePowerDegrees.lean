import research.arxiv.«1104.1579».CunninghamJonesLinearFactors

/-! Irreducibility of Jones's sums in prime-power degrees from their reduction
at a prime dividing the constant term or one less than the constant term. -/

namespace CunninghamChain

open Polynomial Finset

private lemma geometric_sum_mod_prime (p a : ℕ) [Fact p.Prime] :
    (∑ i ∈ range (p^a), (X : (ZMod p)[X])^i) = (X - C 1)^(p^a - 1) := by
  apply mul_right_cancel₀ (X_sub_C_ne_zero (1 : ZMod p))
  rw [C_1, geom_sum_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pow_pos (Fact.out : p.Prime).pos)]
  rw [sub_pow_char_pow]
  simp

/-- If the reduction has only a residual factor d outside X−1, a factor whose
value at 1 is prime to p cannot have degree larger than d. -/
private lemma degree_of_factor_away_from_one {p k : ℕ} [Fact p.Prime]
    {f g : ℤ[X]} (hg : g.Monic) (hgf : g ∣ f) (d : (ZMod p)[X]) (hd : d ≠ 0)
    (hmod : f.map (Int.castRingHom (ZMod p)) = d * (X - C 1)^k)
    (hval : ¬(p : ℤ) ∣ g.eval 1) : g.natDegree ≤ d.natDegree := by
  let φ := Int.castRingHom (ZMod p)
  have away : ¬ X - C (1 : ZMod p) ∣ g.map φ := by
    intro h
    have hr := (dvd_iff_isRoot.mp h)
    have he := eval_map_apply (p := g) φ (1 : ℤ)
    have hz : ((g.eval 1 : ℤ) : ZMod p) = 0 := by
      simpa [φ] using he.symm.trans (by simpa [φ, IsRoot.def] using hr)
    exact hval ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  have cop := ((irreducible_X_sub_C (1 : ZMod p)).coprime_iff_not_dvd.mpr away).symm
  have hdiv : g.map φ ∣ d * (X - C 1)^k := hmod ▸ Polynomial.map_dvd φ hgf
  rw [← hg.natDegree_map φ]
  exact natDegree_le_of_dvd (cop.pow_right.dvd_of_dvd_mul_right hdiv) hd

private lemma small_factor_degree {p k : ℕ} [Fact p.Prime] {f g h : ℤ[X]}
    (hg : g.Monic) (hh : h.Monic) (hgh : g*h = f) (d : (ZMod p)[X]) (hd : d ≠ 0)
    (hmod : f.map (Int.castRingHom (ZMod p)) = d * (X - C 1)^k)
    (hval : ¬(p : ℤ)^2 ∣ f.eval 1) : g.natDegree ≤ d.natDegree ∨ h.natDegree ≤ d.natDegree := by
  by_cases hgv : (p : ℤ) ∣ g.eval 1
  · right
    apply degree_of_factor_away_from_one hh (hgh ▸ dvd_mul_left _ _) d hd hmod
    intro hhv
    apply hval
    rw [← hgh, eval_mul, pow_two]
    exact mul_dvd_mul hgv hhv
  · exact Or.inl (degree_of_factor_away_from_one hg (hgh ▸ dvd_mul_right _ _) d hd hmod hgv)

private lemma sum_at_one (m j : ℕ) : (jonesSumPolynomial m j).eval 1 = (m + j : ℕ) := by
  simp [jonesSumPolynomial, eval_finsetSum]

private lemma sum_mod (m j p : ℕ) :
    (jonesSumPolynomial m j).map (Int.castRingHom (ZMod p)) =
      C (m : ZMod p) + ∑ i ∈ range j, X^(i+1) := by
  rw [jonesSumPolynomial, Polynomial.map_add, map_C, Polynomial.map_sum]
  simp only [Polynomial.map_pow, map_X, map_natCast]

private lemma reduction_at_zero (m p a : ℕ) [Fact p.Prime] (hm : p ∣ m) :
    (jonesSumPolynomial m (p^a)).map (Int.castRingHom (ZMod p)) =
      X * (X - C 1)^(p^a - 1) := by
  have hm' := (ZMod.natCast_eq_zero_iff m p).mpr hm
  rw [sum_mod, hm', C_0, zero_add]
  simp_rw [pow_succ X]
  rw [← sum_mul, geometric_sum_mod_prime, mul_comm]

private lemma reduction_at_one (m p a j : ℕ) [Fact p.Prime] (hm : (m : ZMod p) = 1)
    (hj : j + 1 = p^a) :
    (jonesSumPolynomial m j).map (Int.castRingHom (ZMod p)) = (X - C 1)^j := by
  have he := geometric_sum_mod_prime p a
  rw [← hj, sum_range_succ'] at he
  rw [sum_mod, hm, C_1]
  simpa [add_comm] using he

private lemma irreducible_of_small_factor {m j : ℕ} (hj : 0 < j)
    (hroot : ∀ z : ℤ, (jonesSumPolynomial m j).eval z ≠ 0)
    (hsmall : ∀ g h : ℤ[X], g.Monic → h.Monic → g*h = jonesSumPolynomial m j →
      g.natDegree ≤ 1 ∨ h.natDegree ≤ 1) :
    Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape m j
  have hm := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).mp
  apply hm.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h, natDegree_one] at hdeg; omega, ?_⟩
  intro g h hg hh he
  have zero (g : ℤ[X]) (hg : g.Monic) (hdvd : g ∣ jonesSumPolynomial m j) (hs : g.natDegree ≤ 1) :
      g.natDegree = 0 := by
    by_contra hn
    have hlin := hg.eq_X_add_C (show g.natDegree = 1 by omega)
    have hv : g.IsRoot (-(g.coeff 0)) := by
      change g.eval _ = 0
      conv_lhs => arg 2; rw [hlin]
      simp
    exact hroot _ (hv.dvd hdvd)
  exact (hsmall g h hg hh he).imp (zero g hg (he ▸ dvd_mul_right _ _))
    (zero h hh (he ▸ dvd_mul_left _ _))

/-- For j a power of a prime dividing m, simple divisibility of m+j by that prime
forces any nontrivial rational factorization to have an integer root. -/
theorem jones_prime_power_degree_irreducible {m p a : ℕ} [Fact p.Prime] (hm : p ∣ m)
    (hval : ¬p^2 ∣ m + p^a) (hroot : ∀ z : ℤ, (jonesSumPolynomial m (p^a)).eval z ≠ 0) :
    Irreducible ((jonesSumPolynomial m (p^a)).map (Int.castRingHom ℚ)) := by
  apply irreducible_of_small_factor (pow_pos (Fact.out : p.Prime).pos _) hroot
  intro g h hg hh he
  have hv : ¬(p : ℤ)^2 ∣ (jonesSumPolynomial m (p^a)).eval 1 := by
    rw [sum_at_one]
    exact_mod_cast hval
  simpa only [natDegree_X] using small_factor_degree hg hh he X X_ne_zero
    (reduction_at_zero m p a hm) hv

/-- For Jones's parameter and sufficiently large prime-power degree, the integer-root
hypothesis is discharged by the rational-root classification. -/
theorem jones_prime_power_degree_iff {t p a : ℕ} [Fact p.Prime] (ht : 3 ≤ t) (ho : Odd t)
    (hdiv : p ∣ jonesConstant t) (hval : ¬p^2 ∣ jonesConstant t + p^a)
    (hj : 2 ≤ p^a) (hrange : t ≤ p^a * (p^a + 1)) :
    Irreducible ((jonesSumPolynomial (jonesConstant t) (p^a)).map (Int.castRingHom ℚ)) ↔
      p^a ≠ t := by
  let f := jonesSumPolynomial (jonesConstant t) (p^a)
  have roots := jones_rational_root_iff t (p^a) ht ho (by omega) hrange
  constructor
  · intro hi he
    have hd := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hi
      ((roots (-2)).mpr ⟨rfl,he⟩))
    rw [natDegree_map_eq_of_injective Int.cast_injective, (jonesSumPolynomial_shape _ _).1] at hd
    change p^a = 1 at hd
    omega
  · intro hne
    apply jones_prime_power_degree_irreducible hdiv hval
    intro z hz
    have hr : (f.map (Int.castRingHom ℚ)).IsRoot (z : ℚ) := by
      change (f.map (Int.castRingHom ℚ)).eval ((Int.castRingHom ℚ) z) = 0
      rw [eval_map_apply, show f.eval z = 0 from hz, map_zero]
    exact hne ((roots z).mp hr).2

/-- For j+1 a prime power, reduction is a pure power of X−1 when m ≡ 1.
Simple divisibility of m+j suffices for irreducibility. -/
theorem jones_pred_prime_power_degree_irreducible {m p a j : ℕ} [Fact p.Prime]
    (hj : 0 < j) (hpow : j + 1 = p^a) (hm : (m : ZMod p) = 1) (hval : ¬p^2 ∣ m+j) :
    Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape m j
  have hmon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmon.isPrimitive).mp
  apply hmon.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at hdeg; omega, ?_⟩
  intro g h hg hh he
  have hv : ¬(p : ℤ)^2 ∣ (jonesSumPolynomial m j).eval 1 := by
    rw [sum_at_one]
    exact_mod_cast hval
  have hr := reduction_at_one m p a j hm hpow
  rw [← one_mul ((X - C (1 : ZMod p))^j)] at hr
  simpa using small_factor_degree hg hh he 1 one_ne_zero hr hv

private lemma even_degree_positive (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : Even j) (z : ℤ) :
    0 < (jonesSumPolynomial m j).eval z := by
  obtain ⟨k,rfl⟩ := hj
  induction k with
  | zero => simpa [jonesSumPolynomial] using hm
  | succ k ih =>
    rw [show k.succ + k.succ = (k+k)+1+1 by omega, jonesSumPolynomial_succ, eval_add, eval_pow, eval_X,
      jonesSumPolynomial_succ, eval_add, eval_pow, eval_X]
    have hz : 0 ≤ z*(z+1) := by
      rcases le_or_gt 0 z with ht|ht
      · exact mul_nonneg ht (by omega)
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    have hpair := mul_nonneg (sq_nonneg (z^k)) hz
    rw [pow_succ z (k+k+1), pow_succ z (k+k), pow_add z k k]
    nlinarith only [ih, hpair]

/-- Every positive power-of-two degree, including degree one, is irreducible for
every positive constant congruent to two modulo four. -/
theorem dyadic_degree_irreducible {m : ℕ} (hm : m % 4 = 2) (a : ℕ) :
    Irreducible ((jonesSumPolynomial m (2^a)).map (Int.castRingHom ℚ)) := by
  have ht : 0 < m := by omega
  cases a with
  | zero =>
    apply irreducible_of_degree_eq_one
    rw [← Nat.cast_one, degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1),
      natDegree_map_eq_of_injective Int.cast_injective, pow_zero]
    exact (jonesSumPolynomial_shape m 1).1
  | succ a =>
    have even : Even (2^(a+1)) := ⟨2^a, by rw [pow_succ, mul_two]⟩
    have hroot (z : ℤ) := (even_degree_positive m ht _ even z).ne'
    cases a with
    | zero =>
      apply irreducible_of_small_factor (by decide) hroot
      intro g h hg hh he
      have hd := (jonesSumPolynomial_shape m (2^(0+1))).1
      rw [← he, hg.natDegree_mul hh] at hd
      omega
    | succ a =>
      apply jones_prime_power_degree_irreducible (p := 2) (by omega) _ hroot
      have : 2^(a+1+1) = 2^a*4 := by ring
      rw [this]
      norm_num
      omega

/-- Jones's conjectured irreducibility holds at all dyadic degrees for every
admissible t, with no primality assumption on the odd part of his constant. -/
theorem jones_dyadic_degree_irreducible {t : ℕ} (ht : 3 ≤ t) (ho : Odd t) (a : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant t) (2^a)).map (Int.castRingHom ℚ)) := by
  apply dyadic_degree_irreducible
  obtain ⟨s, hs⟩ : 3 ∣ 2^t + 1 := by simpa using ho.nat_add_dvd_pow_add_pow 2 1
  have he : 2 ∣ 2^t := dvd_pow_self _ (by omega)
  unfold jonesConstant
  omega

#print axioms jones_prime_power_degree_irreducible
#print axioms jones_prime_power_degree_iff
#print axioms jones_pred_prime_power_degree_irreducible
#print axioms dyadic_degree_irreducible
#print axioms jones_dyadic_degree_irreducible

end CunninghamChain
