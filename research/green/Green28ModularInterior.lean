
import Green28InteriorRatios
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! Reduction modulo the endpoint binomial for a single marginal. -/

namespace Green28ModularInterior

open Finset Polynomial Green28PolynomialReduction Green28InteriorRatios
open scoped Polynomial

/-- Inverting the interior polynomial modulo the rational endpoint
polynomial recovers the scaled cofactor there over the rational numbers. -/
theorem scaled_remainder {f g : ℝ[X]} (H A L : ℚ[X]) (am : A.Monic) (an : A ≠ 1)
    (cop : IsCoprime L A) {u : ℝ} (shape : f = A.map (algebraMap ℚ ℝ)+C u*(L.map (algebraMap ℚ ℝ)))
    (product : H.map (algebraMap ℚ ℝ) = f*g) :
    ∃ T : ℚ[X], T.natDegree < A.natDegree ∧
      ∃ K : ℝ[X], C u*g = T.map (algebraMap ℚ ℝ)+A.map (algebraMap ℚ ℝ)*K := by
  let h := algebraMap ℚ ℝ
  obtain ⟨s,t,st⟩ := cop
  let T := (s*H)%ₘ A
  let U := (s*H)/ₘ A
  have bez := congrArg (Polynomial.map h) st
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_one] at bez
  have div := congrArg (Polynomial.map h) (modByMonic_add_div (s*H) A)
  rw [Polynomial.map_add] at div
  change T.map h+(A*U).map h = (s*H).map h at div
  simp only [Polynomial.map_mul] at div
  change H.map h = f*g at product
  change f = A.map h+C u*L.map h at shape
  refine ⟨T,natDegree_modByMonic_lt _ am an,U.map h+C u*t.map h*g-s.map h*g,?_⟩
  rw [product,shape] at div
  change C u*g = T.map h+A.map h*(U.map h+C u*t.map h*g-s.map h*g)
  linear_combination -div - C u*g*bez

/-- At every power-of-two width the endpoint binomial is irreducible over
the rationals, hence coprime to every nonzero shorter interior polynomial. -/
theorem dyadic_coprime (n : ℕ) {L : ℚ[X]} (ln : L ≠ 0) (short : L.natDegree < 2^n) :
    IsCoprime L (X^(2^n)+1) := by
  have cyc : cyclotomic (2^(n+1)) ℚ = X^(2^n)+1 := by
    rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [sum_range_succ,add_comm]
  have ir := cyc ▸ cyclotomic.irreducible_rat (n:=2^(n+1)) (by positivity)
  apply IsCoprime.symm
  apply (ir.isCoprime_or_dvd L).resolve_right
  intro h
  have bound := natDegree_le_of_dvd h ln
  rw [←C_1,natDegree_X_pow_add_C] at bound
  omega

/-- A polynomial congruence modulo the endpoint binomial reads off the
constant alternating fibre using three coefficients when the width is at
most twice the binomial degree. -/
theorem recover_scale {g : ℝ[X]} {u : ℝ} {d : ℕ} (dp : 0 < d)
    (gc : g.coeff 0 = 1) (gd : g.coeff d = 0) (width : g.natDegree ≤ 2*d)
    (T : ℚ[X]) (short : T.natDegree < d) (K : ℝ[X])
    (eq : C u*g = T.map (algebraMap ℚ ℝ)+(X^d+1)*K) :
    (T.coeff 0:ℝ) = u*(1+g.coeff (2*d)) := by
  let A : ℝ[X] := X^d+1
  have ad : A.natDegree = d := by simpa only [A,map_one] using (natDegree_X_pow_add_C (n:=d) (r:=(1:ℝ)))
  have kn : K.natDegree ≤ d := by
    by_cases zero : K = 0
    · simp [zero]
    have an : A ≠ 0 := fun h => by simp [h] at ad; omega
    have diff : A*K = C u*g-T.map (algebraMap ℚ ℝ) := by dsimp [A]; linear_combination -eq
    have h := natDegree_sub_le (C u*g) (T.map (algebraMap ℚ ℝ))
    rw [←diff,natDegree_mul an zero,natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective,ad] at h
    have := natDegree_C_mul_le u g
    omega
  have co (i : ℕ) : u*g.coeff i = (T.coeff i:ℝ)+(if d ≤ i then K.coeff (i-d) else 0)+K.coeff i := by
    have e := congrArg (fun f : ℝ[X] => f.coeff i) eq
    change u*g.coeff i = ((algebraMap ℚ ℝ) (T.coeff i)+_)+_
    simpa only [add_mul,one_mul,coeff_add,coeff_X_pow_mul',coeff_map,coeff_C_mul,add_assoc] using e
  have a := co 0
  have b := co d
  have c := co (2*d)
  rw [gc,mul_one,if_neg (by omega),add_zero] at a
  rw [gd,mul_zero,coeff_eq_zero_of_natDegree_lt short,Rat.cast_zero,if_pos le_rfl,Nat.sub_self,zero_add] at b
  rw [coeff_eq_zero_of_natDegree_lt (p:=T) (by omega),Rat.cast_zero,
    if_pos (by omega),show 2*d-d = d by omega,coeff_eq_zero_of_natDegree_lt (p:=K) (n:=2*d) (by omega),
    zero_add,add_zero] at c
  linear_combination -a+b-c

/-- One occupied site in the endpoint residue class suffices regardless of
the cofactor degree. The quotient coefficients in that class alternate,
and the vanishing tail forces all of them to vanish. -/
theorem recover_isolated {g : ℝ[X]} {u : ℝ} {d : ℕ} (dp : 0 < d)
    (gc : g.coeff 0 = 1) (isolated : ∀ n : ℕ, 0 < n → g.coeff (n*d) = 0)
    (T : ℚ[X]) (short : T.natDegree < d) (K : ℝ[X])
    (eq : C u*g = T.map (algebraMap ℚ ℝ)+(X^d+1)*K) : (T.coeff 0:ℝ) = u := by
  have co (i : ℕ) : u*g.coeff i = (algebraMap ℚ ℝ) (T.coeff i)+(if d ≤ i then K.coeff (i-d) else 0)+K.coeff i := by
    have e := congrArg (fun f : ℝ[X] => f.coeff i) eq
    simpa only [add_mul,one_mul,coeff_add,coeff_X_pow_mul',coeff_map,coeff_C_mul,add_assoc] using e
  have step (m : ℕ) : K.coeff ((m+1)*d) = -K.coeff (m*d) := by
    have e := co ((m+1)*d)
    have de : d ≤ (m+1)*d := by rw [Nat.succ_mul]; omega
    rw [isolated _ (by omega),mul_zero, coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le short de),
      map_zero,if_pos de,show (m+1)*d-d = m*d by rw [Nat.succ_mul]; omega,zero_add] at e
    linarith
  have desc (m : ℕ) : K.coeff (m*d) = 0 → K.coeff 0 = 0 := by
    induction m with
    | zero => simpa only [Nat.zero_mul] using (fun h : K.coeff 0 = 0 => h)
    | succ n ih => intro h; exact ih (by rw [step] at h; simpa using h)
  have tail : K.natDegree < (K.natDegree+1)*d := by
    have := Nat.mul_le_mul_left (K.natDegree+1) dp
    simpa using lt_of_lt_of_le (Nat.lt_succ_self _) this
  have z := co 0
  rw [gc,mul_one,if_neg (by omega),add_zero,desc _ (coeff_eq_zero_of_natDegree_lt tail),add_zero] at z
  exact z.symm

open Green28 Green28UniformSums Green28PrimitiveSupport Green28AlgebraicWidth

/-- The least support point is the sole occupied member of its residue class. -/
def IsolatedEndpoint (Q : PMF ℤ) (d : ℕ) : Prop :=
  ∃ b : ℤ, IsLeast Q.support b ∧ ∀ n : ℕ, 0 < n → b+(n*d:ℕ) ∉ Q.support

/-- At power-of-two width, rational interior ratios in one marginal suffice
when the partner has at most twice its width or an isolated endpoint residue. -/
theorem uniform_of_dyadic_interior {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (pr : InteriorRatios P) {k : ℕ} (dyadic : width P = 2^k) (rangeQ : width Q ≤ 2*width P ∨ IsolatedEndpoint Q (width P)) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨S,sn,hs⟩ := flat
  obtain ⟨f,g,a,b,s,t,pf,pg,fm,gm,fw,gw,fc,gc,product⟩ := mask_factorization sn hs
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp ⟨S,sn,hs⟩
  let d := f.natDegree
  have de : d = 2^k := fw.trans dyadic
  have dp : 0 < d := de ▸ (by positivity : 0 < 2^k)
  let A : ℚ[X] := X^d+1
  let H := (outputMask S sn).map (Int.castRingHom ℚ)
  have hH : H.map (algebraMap ℚ ℝ) = f*g := by
    rw [product]; ext i; simp [H,coeff_map]
  have gd : g.coeff d = 0 := by
    rcases Green28RootLocation.reverse_coeff_eq_zero_or fm gc pf.nonneg pg.nonneg bin dp with h|h
    · rw [coeff_reverse,revAt_le (le_refl d),Nat.sub_self,fc] at h
      exact (one_ne_zero h).elim
    · exact h
  have ad : A.natDegree = d := by simpa only [A,map_one] using (natDegree_X_pow_add_C (n:=d) (r:=(1:ℚ)))
  have am : A.Monic := by simpa only [A,map_one] using (monic_X_pow_add_C (1:ℚ) dp.ne')
  have an : A ≠ 1 := fun h => by simp [h] at ad; omega
  obtain ⟨fb,gb⟩ := rational_factor fm gm pf.nonneg pg.nonneg bin (fun i => by
    rcases Nat.eq_zero_or_pos i with rfl|ip
    · exact ⟨1,by simp [fc]⟩
    rcases lt_trichotomy i d with il|rfl|gt
    · by_cases zero : f.coeff i = 0
      · exact ⟨0,by simp [zero]⟩
      obtain ⟨L,ln,_,short,shape⟩ := shape_of_interior_ratios pf fm fc pr ip il zero
      have cop : IsCoprime L A := by simpa only [A,de] using dyadic_coprime k ln (de ▸ short)
      obtain ⟨T,td,K,eq⟩ := scaled_remainder H A L am an cop
        (by simpa only [A,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_one] using shape) hH
      rcases rangeQ with rangeQ|iso
      · have size : g.natDegree ≤ 2*d := by simpa only [gw,fw,d] using rangeQ
        have g2 : g.coeff (2*d) = 0 ∨ g.coeff (2*d) = 1 := by
          rcases size.eq_or_lt with eq|lt
          · exact Or.inr (eq ▸ gm.coeff_natDegree)
          · exact Or.inl (coeff_eq_zero_of_natDegree_lt lt)
        have c := recover_scale dp gc gd size T (ad ▸ td) K (by simpa [A] using eq)
        rcases g2 with gz|go
        · exact ⟨T.coeff 0,by simpa [gz] using c⟩
        · exact ⟨T.coeff 0/2,by push_cast; rw [go] at c; linarith⟩
      · obtain ⟨x,hx,off⟩ := iso
        have least : IsLeast Q.support b := by
          constructor
          · apply (Q.mem_support_iff b).mpr
            intro zero
            have e := pg.coeff 0
            simp [zero,gc] at e
            exact pg.pos.ne' e.symm
          · intro z hz
            by_contra! lo
            exact (Q.mem_support_iff _).mp hz (pg.below _ lo)
        have off' (n : ℕ) (np : 0 < n) : g.coeff (n*d) = 0 := by
          have absent := off n np
          rw [hx.unique least,←fw] at absent
          have e := pg.coeff (n*d)
          rw [(Q.apply_eq_zero_iff _).mpr absent,ENNReal.toReal_zero] at e
          exact (mul_eq_zero.mp e.symm).resolve_left pg.pos.ne'
        exact ⟨T.coeff 0,recover_isolated dp gc off' T (ad ▸ td) K (by simpa [A] using eq)⟩
    · exact ⟨1,by simp [d,fm.coeff_natDegree]⟩
    · exact ⟨0,by simp [coeff_eq_zero_of_natDegree_lt gt]⟩)
  exact ⟨(pf.uniform_iff fm).mpr fb,(pg.uniform_iff gm).mpr gb⟩

#print axioms scaled_remainder
#print axioms dyadic_coprime
#print axioms recover_scale
#print axioms recover_isolated
#print axioms uniform_of_dyadic_interior
end Green28ModularInterior
