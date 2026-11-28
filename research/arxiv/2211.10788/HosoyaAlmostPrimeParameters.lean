import Mathlib.NumberTheory.AlmostPrime
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-! Arithmetic of integer residue classes visited by numbers with exactly
a prescribed number of prime factors, counted with multiplicity. -/

namespace Arxiv.«2211.10788».AlmostPrimeClosure
open scoped ArithmeticFunction.Omega
open ArithmeticFunction

/-- The parameter modulus detects zero and every possible nonzero
index of absolute value at most B. -/
def indexModulus (k B : ℕ) : ℕ := 2^(k+1)*B.factorial

lemma indexModulus_pos (k B : ℕ) : 0 < indexModulus k B :=
  Nat.mul_pos (by positivity) B.factorial_pos

private lemma factors_le_of_dvd {a n : ℕ} (hn : n≠0) (h : a∣n) : Ω a≤Ω n := by
  obtain ⟨b,rfl⟩ := h
  rw [cardFactors_mul (left_ne_zero_of_mul hn) (right_ne_zero_of_mul hn)]
  omega

private lemma factors_lt_of_proper_dvd {a n : ℕ} (hn : n≠0) (h : a∣n) (lt : a<n) : Ω a<Ω n := by
  obtain ⟨b,rfl⟩ := h
  have ap := left_ne_zero_of_mul hn
  have bp := right_ne_zero_of_mul hn
  have big : 1<b := by
    by_contra! small
    have eq : b=1 := by omega
    simp [eq] at lt
  rw [cardFactors_mul ap bp]
  have := cardFactors_pos_iff_one_lt.mpr big
  omega

/-- A large k-almost prime in this class forces the signed representative
to have strictly fewer than k factors. -/
theorem fewer_factors_of_class {k B n : ℕ} {w : ℤ} (size : w.natAbs≤B)
    (hn : Nat.IsAlmostPrime k n) (large : B<n) (hit : (n:ℤ) ≡ w [ZMOD indexModulus k B]) :
    w≠0 ∧ Ω w.natAbs<k := by
  have projection {a : ℕ} (dvd : a∣indexModulus k B) (zero : (a:ℤ)∣w) : a∣n := by
    have h := hit.of_dvd (show (a:ℤ)∣(indexModulus k B:ℤ) by exact_mod_cast dvd)
    have z := h.trans (Int.modEq_zero_iff_dvd.mpr zero)
    exact_mod_cast Int.modEq_zero_iff_dvd.mp z
  have nz : w≠0 := by
    rintro rfl
    have bad := projection (a:=2^(k+1)) (dvd_mul_right ..) (dvd_zero _)
    have bound := factors_le_of_dvd hn.1 bad
    rw [cardFactors_apply_prime_pow Nat.prime_two,hn.2] at bound
    omega
  have hmod : w.natAbs ∣ indexModulus k B :=
    (Nat.dvd_factorial (by omega) size).trans (dvd_mul_left ..)
  have dv := projection hmod (by simp)
  exact ⟨nz,(factors_lt_of_proper_dvd hn.1 dv (size.trans_lt large)).trans_eq hn.2⟩

/-- Every nonzero signed integer with spare factor budget is approached
modulo any given modulus by arbitrarily large k-almost primes. -/
theorem large_almost_prime_congruent {w : ℤ} {k : ℕ} (nz : w≠0) (budget : Ω w.natAbs<k)
    {M : ℕ} (mp : 0<M) (B : ℕ) :
    ∃ n : ℕ, B<n ∧ Nat.IsAlmostPrime k n ∧ (n:ℤ) ≡ w [ZMOD M] := by
  let h := k-Ω w.natAbs-1
  have gap : Ω w.natAbs+h+1=k := by dsimp [h]; omega
  let sign : ℤ := if 0≤w then 1 else -1
  have unit : IsCoprime sign (M:ℤ) := by
    dsimp [sign]
    split
    · exact ⟨1,0,by ring⟩
    · exact ⟨-1,0,by ring⟩
  obtain ⟨p,_,pp,one⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (q:=M) (a:=1) mp.ne' ⟨1,0,by ring⟩
  obtain ⟨q,big,qp,cls⟩ := Nat.forall_exists_prime_gt_and_zmodEq B mp.ne' unit
  let n := w.natAbs*p^h*q
  have wp : 0<w.natAbs := Int.natAbs_pos.mpr nz
  have scale : q≤n := Nat.le_mul_of_pos_left q (Nat.mul_pos wp (pow_pos pp.pos h))
  have npos : n≠0 := (Nat.mul_pos (Nat.mul_pos wp (pow_pos pp.pos _)) qp.pos).ne'
  refine ⟨n,big.trans_le scale,⟨npos,?_⟩,?_⟩
  · simp only [n,cardFactors_mul (Nat.mul_ne_zero wp.ne' (pow_ne_zero _ pp.ne_zero)) qp.ne_zero,
      cardFactors_mul wp.ne' (pow_ne_zero _ pp.ne_zero),cardFactors_apply_prime_pow pp,
      cardFactors_apply_prime qp,gap]
  · have congr := ((one.pow h).mul_left (w.natAbs:ℤ)).mul cls
    have val : (w.natAbs:ℤ)*sign=w := by
      dsimp [sign]; split <;> simp_all [abs_of_nonneg,abs_of_neg]
    simpa only [n,Nat.cast_mul,Nat.cast_pow,one_pow,mul_one,val] using congr

#print axioms fewer_factors_of_class
#print axioms large_almost_prime_congruent

end Arxiv.«2211.10788».AlmostPrimeClosure
