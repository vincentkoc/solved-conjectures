import CunninghamLinearReciprocalRoots
import CunninghamIntegralRootTests
import CunninghamBalancedRootEstimate

/-! Simultaneous irreducible prefixes, for both signs, from the same prime-scaled seed. -/

namespace CunninghamChain.LinearRoots
open Polynomial

/-- The balanced root estimate proves irreducibility once every factorization of a positive
iterate has a factor with unit leading coefficient. -/
theorem shared_seed_prefix_of_unit_leading_factor {p : ℕ} (s : ℕ) (hsize : 2*16^s<p)
    (k : Bool) (n : ℕ) (hn : n≤4*s^2*4^s)
    (hsplit : n≠0 → ∀ A B : ℤ[X], polynomialTerm k (C (p:ℤ)*X+C (-(p:ℤ))) n = A*B →
      IsUnit A.leadingCoeff ∨ IsUnit B.leadingCoeff) : Irreducible (term k p (-p) n) := by
  let seed : ℤ[X] := C (p:ℤ)*X+C (-(p:ℤ))
  have hpz : (p:ℤ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hdeg : seed.natDegree=1 := natDegree_linear hpz
  let f := polynomialTerm k seed n
  have shape := polynomialTerm_shape k seed (by omega) n
  have deg : f.natDegree=1+n := by simpa [f,hdeg] using shape.1
  change Irreducible (f.map (Int.castRingHom ℚ))
  by_cases hn0 : n=0
  · apply Polynomial.irreducible_of_degree_eq_one
    change (f.map (Int.castRingHom ℚ)).degree = ((1:ℕ):WithBot ℕ)
    rw [degree_eq_iff_natDegree_eq_of_pos (by decide : 0<1), natDegree_map_eq_of_injective Int.cast_injective]
    omega
  have hu : IsUnit (f.coeff 0) := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    dsimp [f]
    rw [hj]
    cases k <;> simp [polynomialTerm]
  let G : ℤ[X] := X^(s*4^s)*(X-1)
  apply irreducible_of_unit_leading_factor_root_test f G (by omega) hu (hsplit hn0)
  intro z hz
  have hz0 : z≠0 := by
    rintro rfl
    have he : (Int.castRingHom ℂ) (f.coeff 0)=0 := by
      simpa only [IsRoot.def,←coeff_zero_eq_eval_zero,coeff_map] using hz
    exact hu.ne_zero (Int.cast_eq_zero.mp he)
  have hz1 : z≠1 := by
    rintro rfl
    have hi : f.eval (1:ℤ) ≠ 0 := by
      dsimp [f]
      rw [polynomialTerm_eval_one]
      cases k <;> simp [seed,hn0]
    have hv := eval₂_at_apply (R := ℤ) (p := f) (Int.castRingHom ℂ) (1:ℤ)
    have hc : (Int.castRingHom ℂ) (f.eval 1) = 0 := by
      rw [←hv,map_one]
      simpa only [IsRoot.def,eval_map] using hz
    exact hi (Int.cast_eq_zero.mp hc)
  have atRoot : aeval z (term k p (-p) n)=0 := by
    have comp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := Subsingleton.elim _ _
    simpa only [term,seed,f,aeval_def,eval_map,eval₂_map,comp,IsRoot.def] using hz
  have he := (root_equation k p (-p) n z hz1).mp atRoot
  have eq : (p:ℂ)*z^n*(z-1)^2 = (sign k:ℂ)*(1-z^n) := by
    push_cast at he
    linear_combination he
  have eunit : ‖(sign k:ℂ)‖=1 := by cases k <;> norm_num [sign]
  have hbound : (p:ℝ)*‖z‖^n*‖z-1‖^2 ≤ 1+‖z‖^n := calc
    (p:ℝ)*‖z‖^n*‖z-1‖^2 = ‖1-z^n‖ := by simpa only [norm_mul,norm_pow,Complex.norm_natCast,eunit,one_mul] using congrArg norm eq
    _ ≤ 1+‖z‖^n := by simpa using norm_sub_le (1:ℂ) (z^n)
  have hs : 2*((4:ℝ)^s)^2<p := by
    have h : 2*(16:ℝ)^s<(p:ℝ) := by exact_mod_cast hsize
    rwa [←pow_mul,Nat.mul_comm s 2,pow_mul,show (4:ℝ)^2=16 by norm_num]
  have hplus : ‖z‖≤1+‖z-1‖ := by
    have := norm_add_le (z-1) 1
    simpa [add_comm] using this
  have hminus : ‖z-1‖≤1+‖z‖ := by simpa [add_comm] using norm_sub_le z 1
  have hb := balanced_root_estimate (norm_nonneg z) (norm_nonneg (z-1)) hplus hminus hs hn hbound
  have calcG : ‖(G.map (Int.castRingHom ℂ)).eval z‖=‖z‖^(s*4^s)*‖z-1‖ := by
    simp [G,norm_pow]
  rw [calcG]
  exact ⟨mul_pos (pow_pos (norm_pos_iff.mpr hz0) _) (norm_pos_iff.mpr (sub_ne_zero.mpr hz1)),hb⟩

/-- Every prime p above the stated dyadic threshold gives a common irreducible prefix for
the two Jones recurrences starting from p(X−1). Index zero is the seed. -/
theorem shared_prime_seed_prefix {p : ℕ} (hp : p.Prime) (s : ℕ) (hsize : 2*16^s<p)
    (k : Bool) (n : ℕ) (hn : n≤4*s^2*4^s) : Irreducible (term k p (-p) n) := by
  apply shared_seed_prefix_of_unit_leading_factor s hsize k n hn
  intro _ A B he
  let seed : ℤ[X] := C (p:ℤ)*X+C (-(p:ℤ))
  have hne : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  have hdeg : seed.natDegree=1 := natDegree_linear hne
  have hl := (polynomialTerm_shape k seed (by omega) n).2.trans (leadingCoeff_linear hne)
  have eq : (p:ℤ)=A.leadingCoeff*B.leadingCoeff := by
    rw [←leadingCoeff_mul,←he]
    exact hl.symm
  exact (Nat.prime_iff_prime_int.mp hp).irreducible.isUnit_or_isUnit eq

/-- At every prescribed finite length there are arbitrarily large prime coefficients
for which all indices through that length are irreducible for both signs. -/
theorem arbitrarily_large_shared_prefixes (L B : ℕ) :
    ∃ p>B, p.Prime ∧ ∀ k : Bool, ∀ n≤L, Irreducible (term k p (-p) n) := by
  let s := L+1
  obtain ⟨p,hle,hp⟩ := Nat.exists_infinite_primes (max (B+1) (2*16^s+1))
  have hB := (le_max_left (B+1) (2*16^s+1)).trans hle
  have hT := (le_max_right (B+1) (2*16^s+1)).trans hle
  refine ⟨p,by omega,hp,fun k n hn => shared_prime_seed_prefix hp s (by omega) k n ?_⟩
  have one : 1 ≤ 4^s := Nat.one_le_pow _ _ (by decide)
  have hL : L ≤ 4*s^2 := by dsimp [s]; nlinarith [Nat.zero_le (L^2)]
  exact hn.trans (hL.trans (Nat.le_mul_of_pos_right _ (by omega)))

#print axioms shared_seed_prefix_of_unit_leading_factor
#print axioms shared_prime_seed_prefix
#print axioms arbitrarily_large_shared_prefixes

end CunninghamChain.LinearRoots
