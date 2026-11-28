import Green28ReversalField
import Green28PrimeFactors

/-!
# Cyclotomic factors of unrestricted degree in Green 28

A real monic factor supported on the unit circle is reciprocal up to a
rational sign. Removing it from a normalized marginal leaves a divisor with
rational constant coefficient, to which the prime-degree subproduct theorem applies.
-/

namespace Green28PaddedFactors

open Polynomial Green28 Green28UniformSums Green28PrimitiveSupport Green28PolynomialReduction
open Green28RootLocation Green28ReversalField Green28PrimeFactors
open scoped Polynomial

/-- A product of rational linear and distinct prime-degree factors may be
multiplied by an arbitrary nonzero real polynomial with all roots on the unit circle. -/
theorem binary_of_padded_prime_factors {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (L : List ℚ[X]) (good : ∀ H ∈ L, PrimeOrLinear H)
    (order : L.Pairwise (fun H J => H.natDegree = 1 ∨ J.natDegree < H.natDegree))
    (U : ℝ[X]) (un : U ≠ 0) (unit : ∀ z ∈ (U.map Complex.ofRealHom).roots, ‖z‖=1)
    (dvd : f ∣ L.prod.map (algebraMap ℚ ℝ)*U) : Binary f ∧ Binary g := by
  obtain ⟨D,W,dm,wm,dd,dw,fact⟩ := split_monic_divisor fm dvd
  have wn := (wm.map Complex.ofRealHom).ne_zero
  have un' : U.map Complex.ofRealHom ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr un
  have wu (z : ℂ) (hz : z ∈ (W.map Complex.ofRealHom).roots) : ‖z‖=1 := by
    apply unit z ((mem_roots un').mpr ?_)
    exact dvd_iff_isRoot.mp <| (dvd_iff_isRoot.mpr ((mem_roots wn).mp hz)).trans
      (Polynomial.map_dvd Complex.ofRealHom dw)
  have rev := reverse_eq_scaled_of_unit_roots W wm wu
  have sq := congrArg (fun T : ℝ[X] => T.coeff 0) rev
  simp only [coeff_zero_reverse,wm.leadingCoeff,coeff_C_mul] at sq
  have signs : W.coeff 0 = 1 ∨ W.coeff 0= -1 := by
    have eq : (W.coeff 0-1)*(W.coeff 0+1) = 0 := by nlinarith
    rcases mul_eq_zero.mp eq with h|h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have prod := congrArg (fun T : ℝ[X] => T.coeff 0) fact
  rw [fc,mul_coeff_zero] at prod
  obtain ⟨c,hc,hD⟩ : ∃ c : ℚ, W.coeff 0 = (c:ℝ) ∧ D.coeff 0 = (c:ℝ) := by
    rcases signs with h|h
    · exact ⟨1,by simpa using h,by rw [h,mul_one] at prod; simpa using prod.symm⟩
    · exact ⟨-1,by simpa using h,by rw [h,mul_neg_one] at prod; push_cast; linarith⟩
  have nz : c ≠ 0 := by intro h; simp [h,hc,hD] at prod
  have cover : D.map Complex.ofRealHom ∣ L.prod.map (algebraMap ℚ ℂ) := by
    have h := Polynomial.map_dvd Complex.ofRealHom dd
    rwa [Polynomial.map_map,RingHom.ext_rat (Complex.ofRealHom.comp (algebraMap ℚ ℝ)) (algebraMap ℚ ℂ)] at h
  obtain ⟨A,_,sel⟩ := complex_subproduct L good order _ (dm.map _) cover
    ⟨c,nz,by rw [coeff_map,hD]; exact Complex.ofReal_ratCast c⟩
  apply binary_of_rational_times_reciprocal fm gm fc gc fp gp bin fact _ (c:=c) (hc ▸ rev)
  intro i
  refine ⟨A.prod.coeff i,?_⟩
  have eq := congrArg (fun T : ℂ[X] => T.coeff i) sel
  simp only [coeff_map] at eq
  apply Complex.ofReal_injective
  exact (Complex.ofReal_ratCast _).trans eq

/-- A rational divisibility certificate on the shifted mask, with unrestricted
cyclotomic degrees and multiplicities. All assertions concern the original PMFs. -/
theorem uniform_of_cyclotomic_prime_core {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (L : List ℚ[X])
    (good : ∀ H ∈ L, PrimeOrLinear H)
    (order : L.Pairwise (fun H J => H.natDegree = 1 ∨ J.natDegree < H.natDegree))
    (m e : ℕ) (mp : 0 < m) (cover : (outputMask S ne).map (Int.castRingHom ℚ) ∣ L.prod*(X^m-1)^e) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨f,g,_,_,_,_,pf,pg,fm,gm,_,_,fc,gc,eq⟩ := mask_factorization ne sum
  let U := ((X:ℝ[X])^m-1)^e
  have un : (X:ℝ[X])^m-1 ≠ 0 := by simpa using X_pow_sub_C_ne_zero mp (1:ℝ)
  have unit (z : ℂ) (hz : z ∈ (U.map Complex.ofRealHom).roots) : ‖z‖=1 := by
    apply norm_of_cyclotomic_part (e:=e) mp
    simpa only [U,Polynomial.map_pow,Polynomial.map_sub,map_X,Polynomial.map_one] using hz
  have h := Polynomial.map_dvd (algebraMap ℚ ℝ) cover
  rw [Polynomial.map_map,RingHom.ext_int ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℝ),
    ←eq] at h
  have div : f ∣ L.prod.map (algebraMap ℚ ℝ)*U := (dvd_mul_right f g).trans <| by
    simpa only [U,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub,map_X,Polynomial.map_one] using h
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
  have fair := binary_of_padded_prime_factors fm gm fc gc pf.nonneg pg.nonneg bin L good order U
    (pow_ne_zero e un) unit div
  exact ⟨(pf.uniform_iff fm).mpr fair.1,(pg.uniform_iff gm).mpr fair.2⟩

#print axioms binary_of_padded_prime_factors
#print axioms uniform_of_cyclotomic_prime_core

end Green28PaddedFactors
