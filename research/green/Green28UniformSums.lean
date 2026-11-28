import Green28PolynomialReduction
import Mathlib.FieldTheory.AlgebraicClosure
import FormalConjectures.GreensOpenProblems.«28»

/-! Finite integer laws and nonnegative polynomials, with explicit shifts and scales. -/

open Finset Polynomial
open scoped ENNReal Polynomial
open Green28 Green28PolynomialReduction

namespace Green28UniformSums

/-- The coefficients give the probabilities after a shift and a positive scaling. -/
structure Models (P : PMF ℤ) (f : ℝ[X]) (a : ℤ) (s : ℝ) : Prop where
  pos : 0 < s
  below : ∀ z < a, P z = 0
  coeff : ∀ i : ℕ, (P (a+i)).toReal = s * f.coeff i

private theorem convolution (P Q : PMF ℤ) (z : ℤ) :
    indepSum P Q z = ∑' x, P x * Q (z-x) := by
  change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z = _
  rw [PMF.bind_apply]
  congr 1
  funext x
  rw [PMF.bind_apply, tsum_eq_single (z-x)]
  · simp [PMF.pure_apply]
  · intro y hy
    have h : z ≠ x+y := by omega
    simp [PMF.pure_apply, h]

theorem Models.mul {P Q : PMF ℤ} {f g : ℝ[X]} {a b : ℤ} {s t : ℝ}
    (h : Models P f a s) (k : Models Q g b t) :
    Models (indepSum P Q) (f*g) (a+b) (s*t) := by
  classical
  refine ⟨mul_pos h.pos k.pos, ?_, ?_⟩
  · intro z hz
    rw [convolution, ENNReal.tsum_eq_zero]
    intro x
    by_cases hx : x < a
    · simp [h.below _ hx]
    · simp [k.below (z-x) (by omega)]
  · intro n
    let u : ℕ → ℤ := fun i => a+i
    let z : ℤ := a+b+n
    have outside (x : ℤ) (hx : x ∉ (range (n+1)).image u) : P x * Q (z-x) = 0 := by
      by_cases lo : x < a
      · simp [h.below x lo]
      · have hi : a+n < x := by
          by_contra! ht
          apply hx
          exact mem_image.mpr ⟨(x-a).toNat, mem_range.mpr (by omega), by dsimp [u]; omega⟩
        simp [k.below (z-x) (by dsimp [z]; omega)]
    change (indepSum P Q z).toReal = _
    rw [convolution, tsum_eq_sum outside, ENNReal.toReal_sum
      (fun x _ => ENNReal.mul_ne_top (P.apply_ne_top x) (Q.apply_ne_top _)),
      sum_image (by intro i _ j _ hij; dsimp [u] at hij; omega),
      coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
    apply sum_congr rfl
    intro i hi
    have he : z - u i = b+(↑(n-i) : ℤ) := by
      have := mem_range.mp hi
      dsimp [u,z]
      omega
    rw [ENNReal.toReal_mul, he, k.coeff, show u i = a+i from rfl, h.coeff]
    ring


private theorem real_zero (P : PMF ℤ) (z : ℤ) : (P z).toReal = 0 ↔ P z = 0 := by
  simp [ENNReal.toReal_eq_zero_iff, P.apply_ne_top]

theorem Models.nonneg {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (h : Models P f a s) (n : ℕ) : 0 ≤ f.coeff n := by
  have hn := ENNReal.toReal_nonneg (a := P (a+n))
  rw [h.coeff] at hn
  exact nonneg_of_mul_nonneg_right hn h.pos

theorem Models.finite {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (h : Models P f a s) : P.support.Finite := by
  apply (Set.finite_Icc a (a+f.natDegree)).subset
  intro z hz
  have nz := (P.mem_support_iff z).mp hz
  have low : a ≤ z := by by_contra! he; exact nz (h.below z he)
  refine ⟨low, ?_⟩
  by_contra! he
  have hn : f.natDegree < (z-a).toNat := by omega
  have e := h.coeff (z-a).toNat
  rw [show a+↑(z-a).toNat = z by omega, coeff_eq_zero_of_natDegree_lt hn, mul_zero] at e
  exact nz ((real_zero P z).mp e)

theorem Models.uniform_iff {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (h : Models P f a s) (mon : f.Monic) : IsUniformOnSupport P ↔ Binary f := by
  classical
  constructor
  · rintro ⟨v, hv, rfl⟩
    have lead := h.coeff f.natDegree
    rw [mon.coeff_natDegree, mul_one, PMF.uniformOfFinset_apply] at lead
    split at lead
    · intro n
      have e := h.coeff n
      rw [PMF.uniformOfFinset_apply] at e
      split at e
      · exact Or.inr (by rw [lead] at e; nlinarith [h.pos])
      · exact Or.inl (by simp only [ENNReal.toReal_zero] at e; exact (mul_eq_zero.mp e.symm).resolve_left h.pos.ne')
    · simp only [ENNReal.toReal_zero] at lead
      exact (h.pos.ne lead).elim
  · intro bin
    let v := h.finite.toFinset
    have hv : v.Nonempty := h.finite.toFinset_nonempty.mpr P.support_nonempty
    have on (z : ℤ) (hz : z ∈ v) : (P z).toReal = s := by
      have nz := (P.mem_support_iff z).mp (h.finite.mem_toFinset.mp hz)
      have low : a ≤ z := by by_contra! he; exact nz (h.below z he)
      have e := h.coeff (z-a).toNat
      rw [show a+↑(z-a).toNat=z by omega] at e
      rcases bin (z-a).toNat with e'|e'
      · rw [e',mul_zero] at e
        exact (nz ((real_zero P z).mp e)).elim
      · simpa [e'] using e
    have off (z : ℤ) (hz : z ∉ v) : P z = 0 :=
      (P.apply_eq_zero_iff z).mpr (fun he => hz (h.finite.mem_toFinset.mpr he))
    have total : (v.card : ℝ)*s = 1 := by
      have ee := congrArg ENNReal.toReal (P.tsum_coe)
      rw [tsum_eq_sum off, ENNReal.toReal_sum (fun z _ => P.apply_ne_top z),
        sum_eq_card_nsmul on, nsmul_eq_mul, ENNReal.toReal_one] at ee
      exact ee
    refine ⟨v,hv,PMF.ext fun z => ?_⟩
    by_cases hz : z ∈ v
    · apply (ENNReal.toReal_eq_toReal_iff' (P.apply_ne_top z) ((PMF.uniformOfFinset v hv).apply_ne_top z)).mp
      rw [on z hz, PMF.uniformOfFinset_apply_of_mem hv hz, ENNReal.toReal_inv, ENNReal.toReal_natCast]
      exact eq_inv_of_mul_eq_one_right (by linarith only [total])
    · rw [off z hz, PMF.uniformOfFinset_apply_of_notMem hv hz]


private theorem model_of_law (P : PMF ℤ) (finite : P.support.Finite) :
    ∃ (f : ℝ[X]) (a : ℤ) (s : ℝ), Models P f a s ∧ f.Monic := by
  classical
  let v := finite.toFinset
  have vne : v.Nonempty := finite.toFinset_nonempty.mpr P.support_nonempty
  let a := v.min' vne
  let b := v.max' vne
  have below (z : ℤ) (hz : z < a) : P z = 0 := by
    apply (P.apply_eq_zero_iff z).mpr
    intro h
    exact hz.not_ge (v.min'_le z (finite.mem_toFinset.mpr h))
  have above (z : ℤ) (hz : b < z) : P z = 0 := by
    apply (P.apply_eq_zero_iff z).mpr
    intro h
    exact hz.not_ge (v.le_max' z (finite.mem_toFinset.mpr h))
  let D := (b-a).toNat
  let p : ℝ[X] := ∑ i ∈ range (D+1), monomial i (P (a+i)).toReal
  have pc (n : ℕ) : p.coeff n = (P (a+n)).toReal := by
    simp only [p, finsetSum_coeff, coeff_monomial, sum_ite_eq', mem_range]
    split
    · rfl
    · rename_i hn
      have e : b < a+n := by dsimp [D] at hn; omega
      simp [above _ e]
  have pn : p ≠ 0 := by
    intro e
    have vmem := finite.mem_toFinset.mp (v.min'_mem vne)
    have nz : P a ≠ 0 := (P.mem_support_iff a).mp vmem
    apply nz
    apply (real_zero P a).mp
    simpa [e] using (pc 0).symm
  have pos : 0 < p.leadingCoeff := by
    have nonneg : 0 ≤ p.leadingCoeff := by
      rw [← coeff_natDegree, pc]
      exact ENNReal.toReal_nonneg
    exact lt_of_le_of_ne nonneg (leadingCoeff_ne_zero.mpr pn).symm
  refine ⟨p * C p.leadingCoeff⁻¹, a, p.leadingCoeff, ⟨pos, below, ?_⟩,
    monic_mul_leadingCoeff_inv pn⟩
  intro n
  rw [coeff_mul_C, pc]
  field_simp

/-- Uniformity of the sum already forces both supports to be finite. -/
theorem finite_of_uniform_sum {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q)) :
    P.support.Finite ∧ Q.support.Finite := by
  obtain ⟨v,hv,eq⟩ := uniform
  have sumfin : (indepSum P Q).support.Finite := by rw [eq, PMF.support_uniformOfFinset]; exact v.finite_toSet
  have pair {x y : ℤ} (hx : x ∈ P.support) (hy : y ∈ Q.support) :
      x+y ∈ (indepSum P Q).support := by
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨x,hx,
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨y,hy,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
  obtain ⟨x,hx⟩ := P.support_nonempty
  obtain ⟨y,hy⟩ := Q.support_nonempty
  constructor
  · apply Set.Finite.of_finite_image (f := fun z : ℤ => z+y) (sumfin.subset ?_)
    · intro a _ b _ he; dsimp at he; omega
    · rintro _ ⟨z,hz,rfl⟩; exact pair hz hy
  · apply Set.Finite.of_finite_image (f := fun z : ℤ => x+z) (sumfin.subset ?_)
    · intro a _ b _ he; dsimp at he; omega
    · rintro _ ⟨z,hz,rfl⟩; exact pair hx hz

/-- Ratios of point probabilities to positive point probabilities are rational. -/
def RationalRatios (P : PMF ℤ) : Prop :=
  ∀ x y : ℤ, y ∈ P.support → ∃ r : ℚ, (r : ℝ) = (P x).toReal / (P y).toReal

private theorem Models.rational {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (h : Models P f a s) (mon : f.Monic) (rat : RationalRatios P) (i : ℕ) :
    ∃ r : ℚ, (r : ℝ) = f.coeff i := by
  have lead := h.coeff f.natDegree
  rw [mon.coeff_natDegree,mul_one] at lead
  have mem : a+↑f.natDegree ∈ P.support := (P.mem_support_iff _).mpr (by
    intro e; rw [e, ENNReal.toReal_zero] at lead; exact h.pos.ne lead)
  obtain ⟨r,he⟩ := rat (a+i) _ mem
  refine ⟨r,?_⟩
  rw [he,h.coeff,lead]
  field_simp [h.pos.ne']

/-- A uniform independent sum with rational probability ratios on either marginal
has two uniform marginals. The other marginal may have arbitrary real probabilities. -/
theorem uniform_of_rational_ratios {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    (rat : RationalRatios P ∨ RationalRatios Q) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨pfin,qfin⟩ := finite_of_uniform_sum uniform
  obtain ⟨f,a,s,hP,fm⟩ := model_of_law P pfin
  obtain ⟨g,b,t,hQ,gm⟩ := model_of_law Q qfin
  have bin := ((hP.mul hQ).uniform_iff (fm.mul gm)).mp uniform
  have both : Binary f ∧ Binary g := by
    rcases rat with u|v
    · exact rational_factor fm gm hP.nonneg hQ.nonneg bin (hP.rational fm u)
    · exact (rational_factor gm fm hQ.nonneg hP.nonneg (mul_comm f g ▸ bin) (hQ.rational gm v)).symm
  exact ⟨(hP.uniform_iff fm).mpr both.1,(hQ.uniform_iff gm).mpr both.2⟩

/-- At either marginal's rightmost support point the mass is maximal. After division
by that mass every atom has an algebraic-integer weight in the unit interval.
Any rational weight in this normalization is zero or one. -/
def EndpointWeights (P : PMF ℤ) : Prop :=
  ∃ b ∈ P.support, (∀ z ∈ P.support, z ≤ b) ∧ ∀ z : ℤ,
    let r := (P z).toReal / (P b).toReal
    0 ≤ r ∧ r ≤ 1 ∧ IsIntegral ℤ r ∧ ((∃ q : ℚ, (q : ℝ) = r) → r = 0 ∨ r = 1)

private theorem endpointWeights_of_model {P : PMF ℤ} {f g : ℝ[X]} {a : ℤ} {s : ℝ}
    (h : Models P f a s) (fm : f.Monic) (gm : g.Monic) (gpos : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) : EndpointWeights P := by
  let b := a+(f.natDegree : ℤ)
  have lead : (P b).toReal = s := by simpa [b,fm.coeff_natDegree] using h.coeff f.natDegree
  have up (z : ℤ) (hz : b < z) : P z = 0 := by
    have hn : f.natDegree < (z-a).toNat := by dsimp [b] at hz; omega
    have e := h.coeff (z-a).toNat
    rw [show a+↑(z-a).toNat=z by dsimp [b] at hz; omega, coeff_eq_zero_of_natDegree_lt hn, mul_zero] at e
    exact (real_zero P z).mp e
  refine ⟨b,(P.mem_support_iff _).mpr (fun e => h.pos.ne (by simpa [e] using lead)),?_,?_⟩
  · intro z hz
    by_contra! he
    exact (P.mem_support_iff _).mp hz (up z he)
  · intro z
    dsimp only
    by_cases lo : z < a
    · simp [h.below _ lo, isIntegral_zero]
    · let i := (z-a).toNat
      have he := h.coeff i
      rw [show a+↑i=z by dsimp [i]; omega] at he
      have ratio : (P z).toReal / (P b).toReal = f.coeff i := by rw [he,lead]; field_simp [h.pos.ne']
      rw [ratio]
      exact ⟨h.nonneg i,coeff_le_one gm h.nonneg gpos bin i,integral_coefficient fm gm bin i,
        fun ⟨q,eq⟩ => rational_coefficient fm gm h.nonneg gpos bin i q eq⟩

theorem endpoint_weights {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q)) :
    EndpointWeights P ∧ EndpointWeights Q := by
  obtain ⟨pfin,qfin⟩ := finite_of_uniform_sum uniform
  obtain ⟨f,a,s,hP,fm⟩ := model_of_law P pfin
  obtain ⟨g,b,t,hQ,gm⟩ := model_of_law Q qfin
  have bin := ((hP.mul hQ).uniform_iff (fm.mul gm)).mp uniform
  exact ⟨endpointWeights_of_model hP fm gm hQ.nonneg bin,
    endpointWeights_of_model hQ gm fm hP.nonneg (mul_comm f g ▸ bin)⟩

private theorem Models.field_iff {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (h : Models P f a s) (fm : f.Monic) (K : Subfield ℝ) :
    (∀ z, (P z).toReal ∈ K) ↔ (∀ i, f.coeff i ∈ K) := by
  classical
  have normalize (i : ℕ) : (P (a+i)).toReal / s = f.coeff i := by
    rw [h.coeff]; field_simp [h.pos.ne']
  constructor
  · intro hall i
    have e := h.coeff f.natDegree
    rw [fm.coeff_natDegree, mul_one] at e
    exact normalize i ▸ K.div_mem (hall _) (e ▸ hall _)
  · intro hall
    have each (z : ℤ) : (P z).toReal / s ∈ K := by
      by_cases lo : z < a
      · simp [h.below _ lo]
      · have e := normalize (z-a).toNat
        rw [show a+↑(z-a).toNat=z by omega] at e
        exact e ▸ hall _
    let v := h.finite.toFinset
    have total : ∑ z ∈ v, (P z).toReal = 1 := by
      have e := congrArg ENNReal.toReal P.tsum_coe
      rw [tsum_eq_sum (s := v) (fun z hz => (P.apply_eq_zero_iff _).mpr
        (fun he => hz (h.finite.mem_toFinset.mpr he))),
        ENNReal.toReal_sum (fun z _ => P.apply_ne_top z), ENNReal.toReal_one] at e
      exact e
    have sm := K.sum_mem (t := v) (fun z _ => each z)
    rw [← Finset.sum_div, total, one_div, inv_mem_iff] at sm
    intro z
    simpa [h.pos.ne'] using K.mul_mem (each z) sm

/-- Every real subfield containing all masses of either marginal contains all
masses of the other. In particular their probability masses generate the same field. -/
theorem same_probability_field {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    (K : Subfield ℝ) : (∀ z, (P z).toReal ∈ K) ↔ (∀ z, (Q z).toReal ∈ K) := by
  obtain ⟨pfin,qfin⟩ := finite_of_uniform_sum uniform
  obtain ⟨f,a,s,hP,fm⟩ := model_of_law P pfin
  obtain ⟨g,b,t,hQ,gm⟩ := model_of_law Q qfin
  have bin := ((hP.mul hQ).uniform_iff (fm.mul gm)).mp uniform
  rw [hP.field_iff fm K,hQ.field_iff gm K]
  exact ⟨coeff_mem_of_monic_factor fm bin K.toSubring,
    coeff_mem_of_monic_factor gm (mul_comm f g ▸ bin) K.toSubring⟩

/-- Each individual point probability of a uniform independent sum's marginals
is algebraic over the rationals. -/
theorem algebraic_masses {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q)) :
    (∀ z, IsAlgebraic ℚ (P z).toReal) ∧ (∀ z, IsAlgebraic ℚ (Q z).toReal) := by
  let K := (algebraicClosure ℚ ℝ).toSubfield
  obtain ⟨pfin,qfin⟩ := finite_of_uniform_sum uniform
  obtain ⟨f,a,s,hP,fm⟩ := model_of_law P pfin
  obtain ⟨g,b,t,hQ,gm⟩ := model_of_law Q qfin
  have bin := ((hP.mul hQ).uniform_iff (fm.mul gm)).mp uniform
  have fp : ∀ z, (P z).toReal ∈ K := (hP.field_iff fm K).mpr fun i =>
    mem_algebraicClosure_iff'.mpr ((integral_coefficient fm gm bin i).tower_top (A := ℚ))
  exact ⟨fun z => mem_algebraicClosure_iff.mp (fp z),
    fun z => mem_algebraicClosure_iff.mp ((same_probability_field uniform K).mp fp z)⟩

#print axioms same_probability_field
#print axioms algebraic_masses
#print axioms endpoint_weights
#print axioms Models.mul
#print axioms Models.uniform_iff
#print axioms finite_of_uniform_sum
#print axioms uniform_of_rational_ratios

end Green28UniformSums
