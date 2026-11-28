import HosoyaLocalRootCounts

/-! # Factor degrees of the upper Hosoya index forms -/

namespace Arxiv.«2211.10788»
open Polynomial
open scoped Polynomial

/-- Multiplying the two evaluations over a factor's roots descends the power
equation from the roots to its coefficients. Multiplicities are included. -/
theorem factor_eval_power_identity {K : Type*} [Field K] {f : K[X]} (hs : f.Splits)
    (A B a b : K) (d : ℕ)
    (h : ∀ x ∈ f.roots, A*(x+a)^d = B*(x+b)^d) :
    A^f.natDegree * (f.eval (-a))^d = B^f.natDegree * (f.eval (-b))^d := by
  classical
  have prod (s : Multiset K) (hz : ∀ x ∈ s, A*(x+a)^d = B*(x+b)^d) :
      A^s.card * (s.map (fun x => -a-x)).prod^d =
        B^s.card * (s.map (fun x => -b-x)).prod^d := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      have hx := hz x (Multiset.mem_cons_self ..)
      have he : A*(-a-x)^d = B*(-b-x)^d := by
        rw [show -a-x=(-1)*(x+a) by ring, show -b-x=(-1)*(x+b) by ring, mul_pow, mul_pow]
        linear_combination (-1:K)^d * hx
      have ht := ih (fun y hy => hz y (Multiset.mem_cons_of_mem hy))
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ, mul_pow]
      linear_combination (A^s.card * (s.map (fun y => -a-y)).prod^d)*he +
        (B*(-b-x)^d)*ht
  rw [hs.natDegree_eq_card_roots,hs.eval_eq_prod_roots,hs.eval_eq_prod_roots,mul_pow,mul_pow]
  linear_combination f.leadingCoeff^d * prod f.roots h

/-- The same two base-field coordinates evaluate a polynomial at both roots of
the Fibonacci characteristic polynomial, even when the roots lie in an extension. -/
private theorem fibonacci_linear_coordinates {F K : Type*} [Field F] [Field K] [Algebra F K]
    (g : F[X]) : ∃ u v : F, ∀ a : K, a^2 = a+1 →
      g.aeval a = algebraMap F K u + algebraMap F K v * a := by
  induction g using Polynomial.recOnHorner with
  | M0 => exact ⟨0,0,by simp⟩
  | MC g c _ _ ih =>
    obtain ⟨u,v,h⟩ := ih
    refine ⟨u+c,v,fun a ha => ?_⟩
    simp only [map_add,aeval_C,h a ha]
    ring
  | MX g _ ih =>
    obtain ⟨u,v,h⟩ := ih
    refine ⟨v,u+v,fun a ha => ?_⟩
    simp only [map_mul,aeval_X,h a ha,map_add]
    linear_combination (algebraMap F K v)*ha

private theorem coprime_exponents {e d : ℕ} (hd : 1 < d) (hc : e.Coprime d) :
    ∃ c s : ℕ, e*c = 1+d*s := by
  let : NeZero d := ⟨by omega⟩
  let c := ((e:ZMod d)⁻¹).val
  have hu : IsUnit (e:ZMod d) := (ZMod.isUnit_iff_coprime ..).mpr hc
  have hmod : e*c ≡ 1 [MOD d] := (ZMod.natCast_eq_natCast_iff ..).mp (by
    simp only [Nat.cast_mul,c,ZMod.natCast_zmod_val,Nat.cast_one,ZMod.mul_inv_of_unit _ hu])
  have he : (e*c)%d=1 := Eq.trans hmod (Nat.mod_eq_of_lt hd)
  exact ⟨c,(e*c)/d,by simpa [he] using (Nat.mod_add_div (e*c) d).symm⟩

/-- Evaluating the reduced polynomial is the affine specialization of the form. -/
theorem upperIndexPolynomial_aeval {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r d : ℕ) (x : K) :
    ((upperIndexPolynomial r d).map (Int.castRingHom F)).aeval x = upperIndexForm x 1 d r := by
  let f := (Polynomial.aeval x).toRingHom.comp (Polynomial.mapRingHom (Int.castRingHom F))
  change f (upperIndexForm X 1 d r)=_
  rw [upperIndexForm_map]
  simp [f]

/-- Over the algebraic closure the Fibonacci roots are distinct and both
weights in the formula for the upper form are nonzero away from 5 and 11. -/
theorem upperIndexForm_conjugate_data (K : Type*) [Field K] [IsAlgClosed K]
    (h5 : (5:K)≠0) (h11 : (11:K)≠0) (r : ℕ) :
    ∃ a b : K, a^2=a+1 ∧ b^2=b+1 ∧ b=1-a ∧ a≠b ∧
      (3+a)*a^r≠0 ∧ (3+b)*b^r≠0 := by
  obtain ⟨a,ha₀⟩ := IsAlgClosed.exists_root (X^2-X-1 : K[X]) (by
    have h : (X^2-X-1 : K[X]).degree=2 := by compute_degree!
    rw [h]; decide)
  have ha : a^2=a+1 := by
    simp only [IsRoot,eval_sub,eval_pow,eval_X,eval_one] at ha₀
    linear_combination ha₀
  let b := 1-a
  have hb : b^2=b+1 := by dsimp [b]; linear_combination ha
  have hab : a≠b := by
    have he : (a-b)^2=(5:K) := by dsimp [b]; linear_combination 4*ha
    intro h
    exact h5 (by simpa [h] using he.symm)
  let A : K := (3+a)*a^r
  let B : K := (3+b)*b^r
  have ha'b' : a*b≠0 := by
    have h : a*b=(-1) := by dsimp [b]; linear_combination -ha
    rw [h]; simp
  have hn : (3+a)*(3+b)≠0 := by
    have h : (3+a)*(3+b)=11 := by dsimp [b]; linear_combination -ha
    rw [h]; exact h11
  have hA : A≠0 := mul_ne_zero (left_ne_zero_of_mul hn) (pow_ne_zero _ (left_ne_zero_of_mul ha'b'))
  have hB : B≠0 := mul_ne_zero (right_ne_zero_of_mul hn) (pow_ne_zero _ (right_ne_zero_of_mul ha'b'))
  exact ⟨a,b,ha,hb,rfl,hab,hA,hB⟩

/-- A divisor whose degree is coprime to the step yields a base-field zero in
homogeneous coordinates. The restrictions on 5 and 11 exclude the repeated
characteristic root and the zero conjugate of the starting coefficient. -/
theorem upperIndexForm_zero_of_coprime_factor {F : Type*} [Field F]
    (h5 : (5:F)≠0) (h11 : (11:F)≠0) {r d : ℕ} (hd : 1 < d) {g : F[X]}
    (hg : g ∣ (upperIndexPolynomial r d).map (Int.castRingHom F)) (hc : g.natDegree.Coprime d) :
    ∃ u v : F, (u≠0 ∨ v≠0) ∧ upperIndexForm u v d r=0 := by
  classical
  let K := AlgebraicClosure F
  let incl := algebraMap F K
  have hinj := (algebraMap F K).injective
  have nz (n : ℕ) (h : (n:F)≠0) : (n:K)≠0 := fun he => h (hinj (by simpa using he))
  obtain ⟨a,b,ha,hb,_,hab,hA,hB⟩ := upperIndexForm_conjugate_data K (nz 5 h5) (nz 11 h11) r
  let T : F[X] := (3+X)*X^r
  let A : K := (3+a)*a^r
  let B : K := (3+b)*b^r
  change A≠0 at hA
  change B≠0 at hB
  have zero (x : K) (hx : g.aeval x=0) : A*(x+a)^d=B*(x+b)^d := by
    obtain ⟨q,hq⟩ := hg
    have hz := (upperIndexPolynomial_aeval (F:=F) r d x).symm
    rw [hq,map_mul,hx,zero_mul] at hz
    have he := upper_form_conjugates ha hb x 1 r d
    rw [hz,mul_zero] at he
    exact sub_eq_zero.mp (by simpa [A,B] using he.symm)
  have hga : g.aeval (-a)≠0 := by
    intro h
    have ht := zero (-a) h
    have hba : -a+b≠0 := fun he => hab (by linear_combination -he)
    exact (mul_ne_zero hB (pow_ne_zero d hba)) (by simpa [zero_pow (by omega : d≠0)] using ht.symm)
  let G := g.map incl
  have key : A^g.natDegree * (g.aeval (-a))^d = B^g.natDegree * (g.aeval (-b))^d := by
    have hh := factor_eval_power_identity (f:=G) (IsAlgClosed.splits G) A B a b d (by
      intro x hx
      apply zero x
      simpa [G,incl,eval_map_algebraMap] using (mem_roots'.mp hx).2)
    simpa [G,incl,natDegree_map,eval_map_algebraMap] using hh
  obtain ⟨c,s,hes⟩ := coprime_exponents hd hc
  let P := T^s * (g.comp (-X))^c
  obtain ⟨u,v,coord⟩ := fibonacci_linear_coordinates (K:=K) P
  have cv (x : K) (hx : x^2=x+1) :
      ((3+x)*x^r)^s * (g.aeval (-x))^c = incl u + incl v*x := by
    have hthree : (3:F[X]).aeval x = (3:K) := map_ofNat _ _
    simpa [P,T,incl,aeval_comp,hthree] using coord x hx
  have eqn := congrArg (fun z : K => z^c) key
  simp only [mul_pow,←pow_mul,hes,pow_add,pow_one] at eqn
  have H : A*(incl u+incl v*a)^d = B*(incl u+incl v*b)^d := by
    rw [←cv a ha,←cv b hb]
    dsimp only [A,B] at eqn ⊢
    simpa only [mul_pow,←pow_mul,Nat.mul_comm s d,Nat.mul_comm c d,mul_assoc] using eqn
  refine ⟨u,v,?_,?_⟩
  · by_contra! hnz
    have hw := cv a ha
    rw [hnz.1,hnz.2,map_zero,zero_mul,add_zero] at hw
    exact mul_ne_zero (pow_ne_zero s hA) (pow_ne_zero c hga) hw
  · apply hinj
    rw [map_zero,upperIndexForm_map]
    apply (mul_eq_zero.mp (by
      rw [upper_form_conjugates ha hb, mul_comm a, mul_comm b]
      exact sub_eq_zero.mpr H : (a-b)*upperIndexForm (incl u) (incl v) d r=0)).resolve_left
      (sub_ne_zero.mpr hab)

private theorem reduced_degree {F : Type*} [Field F] {r : ℕ} (hU : (lucasFibonacciSum r : F)≠0)
    (d : ℕ) : ((upperIndexPolynomial r d).map (Int.castRingHom F)).natDegree=d := by
  apply Nat.le_antisymm (natDegree_map_le.trans (upperIndexPolynomial_natDegree r d).le)
  apply le_natDegree_of_ne_zero
  simpa [coeff_map,upperIndexPolynomial_top_coeff] using hU

/-- The value at infinity is the term at the offset. -/
theorem upperIndexForm_at_infinity {F : Type*} [Field F] (r d : ℕ) :
    upperIndexForm (1:F) 0 d r = (lucasFibonacciSum r:F) := by
  induction d generalizing r with
  | zero => rfl
  | succ d ih => simp [upperIndexForm,ih]

private theorem not_root_of_irreducible {F : Type*} [Field F] {r d : ℕ}
    (hU : (lucasFibonacciSum r : F)≠0) (hd : 1 < d)
    (hirr : Irreducible ((upperIndexPolynomial r d).map (Int.castRingHom F))) (x : F) :
    upperIndexForm x 1 d r ≠ 0 := by
  intro hz
  apply hirr.not_isRoot_of_natDegree_ne_one (by rw [reduced_degree hU]; omega) (x:=x)
  simpa [IsRoot,aeval_def] using (upperIndexPolynomial_aeval (F:=F) r d x).trans hz

/-- At prime step and full degree, a rootless affine reduction is irreducible
over any field in which the Fibonacci discriminant and initial norm are nonzero. -/
theorem upperIndexPolynomial_irreducible_iff_no_root {F : Type*} [Field F]
    (h5 : (5:F)≠0) (h11 : (11:F)≠0) {r d : ℕ} (hd : d.Prime)
    (hU : (lucasFibonacciSum r : F)≠0) :
    Irreducible ((upperIndexPolynomial r d).map (Int.castRingHom F)) ↔
      ∀ x : F, upperIndexForm x 1 d r≠0 := by
  refine ⟨not_root_of_irreducible hU hd.one_lt,fun hroot => ?_⟩
  let P := (upperIndexPolynomial r d).map (Int.castRingHom F)
  have hdeg : P.natDegree=d := reduced_degree hU d
  have hp0 : P≠0 := fun h => hd.ne_zero (hdeg.symm.trans (by rw [h,natDegree_zero]))
  have hnu : ¬IsUnit P := fun h => hd.ne_zero (hdeg.symm.trans (natDegree_eq_zero_of_isUnit h))
  apply (irreducible_iff_lt_natDegree_lt hp0 hnu).mpr
  intro g _ hq hg
  obtain ⟨hpos,hle⟩ := Finset.mem_Ioc.mp hq
  rw [hdeg] at hle
  have hcop := (hd.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hpos (by omega))).symm
  obtain ⟨u,v,huv,hzero⟩ := upperIndexForm_zero_of_coprime_factor h5 h11 hd.one_lt hg hcop
  by_cases hv : v=0
  · subst v
    have hu := huv.resolve_right (by simp)
    have he := upperIndexForm_scale u 1 0 r d
    simp only [mul_one,mul_zero,upperIndexForm_at_infinity,hzero] at he
    exact mul_ne_zero (pow_ne_zero d hu) hU he.symm
  · have he := upperIndexForm_scale v (u/v) 1 r d
    rw [show v*(u/v)=u by field_simp,mul_one,hzero] at he
    exact hroot (u/v) ((mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hv))

private theorem count_zero_iff {p r d : ℕ} [Fact p.Prime] (hU : ¬p ∣ lucasFibonacciSum r) :
    upperProjectiveRootCount p r d=0 ↔ ∀ x : ZMod p, upperIndexForm x 1 d r≠0 := by
  classical
  unfold upperProjectiveRootCount
  rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff]
  constructor
  · intro h x
    exact h (Finset.mem_univ (some x))
  · intro h z _
    cases z with
    | none => simpa [upperIndexChart,upperIndexForm_at_infinity,ZMod.natCast_eq_zero_iff] using hU
    | some x => exact h x

/-- At full degree the absence of projective roots exactly detects irreducible
reductions at prime step, including characteristics five and eleven. -/
theorem upperIndexPolynomial_irreducible_iff_count_zero {p r d : ℕ} [Fact p.Prime]
    (hd : d.Prime) (hU : ¬p ∣ lucasFibonacciSum r) :
    Irreducible ((upperIndexPolynomial r d).map (Int.castRingHom (ZMod p))) ↔
      upperProjectiveRootCount p r d=0 := by
  have hu := (ZMod.natCast_eq_zero_iff ..).not.mpr hU
  refine ⟨fun h => (count_zero_iff hU).mpr (not_root_of_irreducible hu hd.one_lt h),fun h => ?_⟩
  by_cases h5 : p=5
  · subst p
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne_zero
    rw [upperProjectiveRootCount_five] at h
    split_ifs at h
  by_cases h11 : p=11
  · subst p
    rw [upperProjectiveRootCount_eleven r d hd.pos] at h
    contradiction
  have nz (ℓ : ℕ) (hℓ : ℓ.Prime) (hne : p≠ℓ) : (ℓ:ZMod p)≠0 :=
    (ZMod.natCast_eq_zero_iff ..).not.mpr ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).not.mpr hne)
  exact (upperIndexPolynomial_irreducible_iff_no_root (nz 5 (by decide) h5) (nz 11 (by decide) h11)
    hd hu).mpr ((count_zero_iff hU).mp h)

#print axioms upperIndexPolynomial_irreducible_iff_no_root
#print axioms upperIndexPolynomial_irreducible_iff_count_zero

#print axioms upperIndexForm_zero_of_coprime_factor

#print axioms upperIndexForm_map
#print axioms upperIndexPolynomial_top_coeff
#print axioms upperIndexPolynomial_natDegree
#print axioms upperIndexPolynomial_next_coeff
#print axioms upperIndex_consecutive_coprime
#print axioms upperIndexForm_scale
#print axioms upper_form_conjugates
#print axioms upperIndexPolynomial_aeval
#print axioms upperIndexForm_at_infinity
#print axioms upperIndexForm_conjugate_data
#print axioms factor_eval_power_identity

end Arxiv.«2211.10788»
