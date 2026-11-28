import CunninghamOddPowerFactorCriterion
import CunninghamSharedLinearPrefixes

/-! Common irreducible prefixes with the prime base fixed in advance. -/

namespace CunninghamChain.LinearRoots
open Polynomial

private lemma high_coefficients (k : Bool) (a : ℤ) (i : ℕ) :
    let f := polynomialTerm k (C a*X + C (-a)) (i+1)
    f.coeff (i+2) = a ∧ f.coeff (i+1) = -a ∧ f.coeff i = sign k := by
  let seed : ℤ[X] := C a*X + C (-a)
  have step (t j : ℕ) : (polynomialTerm k seed (t+1)).coeff (j+1) =
      (polynomialTerm k seed t).coeff j := by
    rw [polynomialTerm,coeff_add,coeff_X_mul,coeff_C]
    simp
  change (polynomialTerm k seed (i+1)).coeff (i+2) = _ ∧ _
  induction i with
  | zero =>
    refine ⟨(step 0 1).trans ?_,(step 0 0).trans ?_,?_⟩
    · simp only [polynomialTerm,seed,coeff_add,coeff_mul_X,coeff_C]; simp
    · simp only [polynomialTerm,seed,coeff_add,coeff_mul_X_zero,coeff_C]; simp
    · rw [polynomialTerm,coeff_add,coeff_X_mul_zero,coeff_C_zero,zero_add]; rfl
  | succ i ih =>
    exact ⟨(step _ _).trans ih.1,(step _ _).trans ih.2.1,(step _ _).trans ih.2.2⟩

/-- Reversing a factorization of a positive balanced iterate preserves its three
leading coefficients as the constant, linear, and quadratic coefficients. -/
theorem balanced_reverse_coefficients {a : ℕ} (ha : 0 < a) (k : Bool) {n : ℕ}
    (hn0 : n≠0) (A B : ℤ[X])
    (hab : polynomialTerm k (C (a:ℤ)*X+C (-(a:ℤ))) n=A*B) :
    let H := A.reverse*B.reverse
    H.coeff 0=(a:ℤ) ∧ H.coeff 1= -(a:ℤ) ∧ H.coeff 2=sign k := by
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  let seed : ℤ[X] := C (a:ℤ)*X+C (-(a:ℤ))
  let f := polynomialTerm k seed (i+1)
  have a0 : (a:ℤ)≠0 := by exact_mod_cast ha.ne'
  have ds : seed.natDegree=1 := natDegree_linear a0
  have df : f.natDegree=i+2 := by
    have h := (polynomialTerm_shape k seed (by omega) (i+1)).1
    change f.natDegree=_ at h
    omega
  have hf : f.reverse=A.reverse*B.reverse := by rw [show f=A*B from hab,reverse_mul_of_domain]
  obtain ⟨h₀,h₁,h₂⟩ := high_coefficients k (a:ℤ) i
  have rev (j : ℕ) (hj : j ≤ i+2) : f.reverse.coeff j=f.coeff (i+2-j) := by
    rw [coeff_reverse,df,revAt_le hj]
  have e₀ : (A.reverse*B.reverse).coeff 0 = (a:ℤ) := by
    rw [←hf,rev 0 (by omega),Nat.sub_zero]; exact h₀
  have e₁ : (A.reverse*B.reverse).coeff 1 = -(a:ℤ) := by
    rw [←hf,rev _ (by omega),show i+2-1=i+1 by omega]; exact h₁
  have e₂ : (A.reverse*B.reverse).coeff 2 = sign k := by
    rw [←hf,rev _ (by omega),show i+2-2=i by omega]; exact h₂
  exact ⟨e₀,e₁,e₂⟩

/-- Any integral factorization of a positive iterate at an odd prime-power coefficient
has a factor with unit leading coefficient. -/
theorem odd_prime_power_factor_leading {p : ℕ} (hp : p.Prime) (r : ℕ) (k : Bool)
    {n : ℕ} (hn0 : n≠0) (A B : ℤ[X])
    (hab : polynomialTerm k (C ((p^(2*r+1):ℕ):ℤ)*X+C (-(p^(2*r+1):ℕ):ℤ)) n=A*B) :
    IsUnit A.leadingCoeff ∨ IsUnit B.leadingCoeff := by
  obtain ⟨e₀,e₁,e₂⟩ := balanced_reverse_coefficients (pow_pos hp.pos _) k hn0 A B hab
  have hu := unit_constant_of_odd_power (r:=r) hp A.reverse B.reverse
    (by simp [e₀]) (by simp [e₀,e₁]) (by
      rw [e₂]; cases k <;> simpa [sign] using (Nat.prime_iff_prime_int.mp hp).not_dvd_one)
  simpa using hu

/-- For every fixed prime p, the same bounds as for a prime coefficient hold at all its
odd powers. Both signs start at p^(2r+1)(X−1). -/
theorem shared_odd_prime_power_prefix {p : ℕ} (hp : p.Prime) (r s : ℕ)
    (hsize : 2*16^s < p^(2*r+1)) (k : Bool) (n : ℕ) (hn : n≤4*s^2*4^s) :
    Irreducible (term k (p^(2*r+1):ℕ) (-(p^(2*r+1):ℕ):ℤ) n) := by
  apply shared_seed_prefix_of_unit_leading_factor s hsize k n hn
  exact fun hn0 A B hab => odd_prime_power_factor_leading hp r k hn0 A B hab

/-- Fix even the prime base in advance. Every sufficiently large odd exponent then gives
a common irreducible prefix of any prescribed finite length. -/
theorem fixed_prime_eventually_shared_prefix {p : ℕ} (hp : p.Prime) (L : ℕ) :
    ∃ R, ∀ r≥R, ∀ k : Bool, ∀ n≤L,
      Irreducible (term k (p^(2*r+1):ℕ) (-(p^(2*r+1):ℕ):ℤ) n) := by
  let s := L+1
  refine ⟨2*16^s,?_⟩
  intro r hr k n hn
  have hpwr : 2*r+1 < p^(2*r+1) := Nat.lt_pow_self hp.one_lt
  apply shared_odd_prime_power_prefix hp r s (by omega) k n
  have one : 1≤4^s := Nat.one_le_pow _ _ (by decide)
  have hL : L≤4*s^2 := by dsimp [s]; nlinarith [Nat.zero_le (L^2)]
  exact hn.trans (hL.trans (Nat.le_mul_of_pos_right _ (by omega)))

#print axioms balanced_reverse_coefficients
#print axioms odd_prime_power_factor_leading
#print axioms shared_odd_prime_power_prefix
#print axioms fixed_prime_eventually_shared_prefix

end CunninghamChain.LinearRoots
