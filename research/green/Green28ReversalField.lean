import Green28RootLocation

/-! Recovering the marginal coefficient field from reversal data in Green 28. -/

namespace Green28ReversalField
open Polynomial Finset Green28PolynomialReduction
open scoped Polynomial

/-- Each successive reflected coefficient differs from its opposite in the
ground field once all earlier coefficients are known there. -/
private theorem recover_coefficients {f g : ℝ[X]} (fm : f.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (K : Subfield ℝ)
    (step : ∀ n, 0 < n → (∀ i < n, f.coeff i ∈ K) → (∀ i < n, f.reverse.coeff i ∈ K) →
      f.reverse.coeff n-f.coeff n ∈ K) :
    (∀ i, f.coeff i ∈ K) ∧ (∀ i, g.coeff i ∈ K) := by
  have rc : f.reverse.coeff 0 = 1 := (coeff_zero_reverse f).trans fm.leadingCoeff
  suffices all : ∀ i, f.coeff i ∈ K ∧ g.coeff i ∈ K ∧ f.reverse.coeff i ∈ K from
    ⟨fun i => (all i).1,fun i => (all i).2.1⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl|hn
    · exact ⟨fc ▸ K.one_mem,gc ▸ K.one_mem,rc ▸ K.one_mem⟩
    have prev := Green28RootLocation.coeff_mul_middle_mem K hn (fun i hi => (ih i hi).1) (fun i hi => (ih i hi).2.1)
    have zn : (f*g).coeff n ∈ K := (bin n).elim (fun eq => eq ▸ K.zero_mem) (fun eq => eq ▸ K.one_mem)
    have plus := K.sub_mem zn prev
    simp only [fc,gc,one_mul,mul_one,sub_sub_cancel] at plus
    have sub := step n hn (fun i hi => (ih i hi).1) (fun i hi => (ih i hi).2.2)
    rcases Green28RootLocation.reverse_coeff_eq_zero_or fm gc fp gp bin hn with h|h
    · rw [h,zero_sub] at sub
      have fx : f.coeff n ∈ K := by simpa only [neg_neg] using K.neg_mem sub
      exact ⟨fx,by simpa using K.sub_mem plus fx,h ▸ K.zero_mem⟩
    · rw [h,add_zero] at plus
      exact ⟨plus,h ▸ K.zero_mem,by simpa using K.add_mem sub plus⟩

/-- A relation between a marginal polynomial and its reverse over a subfield
recovers the coefficients of both marginals. The denominator is regular at zero. -/
theorem coefficients_of_reversal_relation {f g : ℝ[X]} (fm : f.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (K : Subfield ℝ) {U V : ℝ[X]} (u : ∀ i, U.coeff i ∈ K)
    (v : ∀ i, V.coeff i ∈ K) (nz : V.coeff 0 ≠ 0) (rel : f.reverse*V = f*U) :
    (∀ i, f.coeff i ∈ K) ∧ (∀ i, g.coeff i ∈ K) := by
  have rc : f.reverse.coeff 0 = 1 := (coeff_zero_reverse f).trans fm.leadingCoeff
  have same : U.coeff 0 = V.coeff 0 := by
    have eq := congrArg (fun p : ℝ[X] => p.coeff 0) rel
    simpa only [mul_coeff_zero,rc,fc,one_mul] using eq.symm
  apply recover_coefficients fm fc gc fp gp bin K
  intro n hn hf hr
  have rv := Green28RootLocation.coeff_mul_middle_mem (f:=f.reverse) (g:=V) K hn hr (fun i _ => v i)
  have fu := Green28RootLocation.coeff_mul_middle_mem (f:=f) (g:=U) K hn hf (fun i _ => u i)
  rw [rel,rc,one_mul] at rv
  rw [fc,one_mul,same] at fu
  have diff : (f.reverse.coeff n-f.coeff n)*V.coeff 0 ∈ K := by
    convert K.add_mem (K.sub_mem fu rv) (K.sub_mem (u n) (v n)) using 1; ring
  simpa [nz] using K.div_mem diff (v 0)

theorem coefficients_of_reversal_differences {f g : ℝ[X]} (fm : f.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (K : Subfield ℝ) (diff : ∀ n, f.reverse.coeff n-f.coeff n ∈ K) :
    (∀ i, f.coeff i ∈ K) ∧ (∀ i, g.coeff i ∈ K) :=
  recover_coefficients fm fc gc fp gp bin K (fun n _ _ _ => diff n)

/-- A rational-function presentation with a denominator nonzero at zero. -/
def ReversalDefinedOver (K : Subfield ℝ) (f : ℝ[X]) : Prop :=
  ∃ U V : ℝ[X], (∀ i, U.coeff i ∈ K) ∧ (∀ i, V.coeff i ∈ K) ∧
    V.coeff 0 ≠ 0 ∧ f.reverse*V = f*U

theorem coefficients_iff_reversal {f g : ℝ[X]} (fm : f.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (K : Subfield ℝ) : (∀ i, f.coeff i ∈ K) ↔ ReversalDefinedOver K f := by
  constructor
  · intro hf
    exact ⟨f.reverse,f,fun i => coeff_reverse f i ▸ hf _,hf,fc ▸ one_ne_zero,mul_comm ..⟩
  · rintro ⟨U,V,hu,hv,nz,rel⟩
    exact (coefficients_of_reversal_relation fm fc gc fp gp bin K hu hv nz rel).1

/-- One normalized factor may consist of a rational polynomial times an
arbitrary real factor reciprocal up to rational scaling. Neither piece
needs nonnegative coefficients. -/
theorem binary_of_rational_times_reciprocal {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) {L R : ℝ[X]} (factor : f = L*R) (rat : ∀ n, L.coeff n ∈ (algebraMap ℚ ℝ).fieldRange)
    {c : ℚ} (scale : R.reverse = C (c:ℝ)*R) : Binary f ∧ Binary g := by
  let K := (algebraMap ℚ ℝ).fieldRange
  have nz : L.coeff 0 ≠ 0 := by
    intro h
    rw [factor,mul_coeff_zero,h,zero_mul] at fc
    exact zero_ne_one fc
  apply rational_factor fm gm fp gp bin
  apply (coefficients_iff_reversal fm fc gc fp gp bin K).mpr
  refine ⟨C (c:ℝ)*L.reverse,L,?_,rat,nz,?_⟩
  · intro i
    rw [coeff_C_mul,coeff_reverse]
    exact K.mul_mem ⟨c,rfl⟩ (rat _)
  · rw [factor,reverse_mul_of_domain,scale]
    ring

open Green28 Green28UniformSums Green28PrimitiveSupport

/-- One marginal's normalized differences across its midpoint determine the
field of all point probabilities of both original integer laws. -/
theorem field_of_reflected_differences {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q)) :
    ∃ a b : ℤ, IsLeast P.support a ∧ IsGreatest P.support b ∧ ∀ K : Subfield ℝ,
      ((∀ z, (P z).toReal ∈ K) ∧ (∀ z, (Q z).toReal ∈ K)) ↔
        ∀ z, ((P (a+b-z)).toReal-(P z).toReal)/(P a).toReal ∈ K := by
  obtain ⟨S,ne,sum⟩ := flat
  obtain ⟨f,g,a,_,s,_,pf,pg,fm,gm,_,_,fc,gc,_⟩ := mask_factorization ne sum
  let b := a+(f.natDegree:ℤ)
  have pa : (P a).toReal = s := by simpa [fc] using pf.coeff 0
  have pb : (P b).toReal = s := by simpa [b,fm.coeff_natDegree] using pf.coeff f.natDegree
  have occupied {z : ℤ} (e : (P z).toReal = s) : z ∈ P.support :=
    (P.mem_support_iff z).mpr (fun h => pf.pos.ne' (by simpa [h] using e.symm))
  refine ⟨a,b,⟨occupied pa,?_⟩,⟨occupied pb,?_⟩,?_⟩
  · intro z hz
    by_contra! h
    exact (P.mem_support_iff z).mp hz (pf.below _ h)
  · intro z hz
    by_contra! h
    have big : f.natDegree < (z-a).toNat := by dsimp [b] at h; omega
    have eq := pf.coeff (z-a).toNat
    rw [show a+↑(z-a).toNat = z by omega,coeff_eq_zero_of_natDegree_lt big,mul_zero] at eq
    exact (ENNReal.toReal_pos ((P.mem_support_iff z).mp hz) (P.apply_ne_top z)).ne' eq
  intro K
  constructor
  · rintro ⟨p,_⟩ z
    exact K.div_mem (K.sub_mem (p _) (p _)) (p _)
  · intro diff
    have offsets (n : ℕ) : f.reverse.coeff n-f.coeff n ∈ K := by
      by_cases hn : n ≤ f.natDegree
      · have h := diff (a+(n:ℤ))
        rw [pa,show a+b-(a+(n:ℤ)) = a+((f.natDegree-n:ℕ):ℤ) by dsimp [b]; omega,
          pf.coeff,pf.coeff,←mul_sub,mul_div_cancel_left₀ _ pf.pos.ne'] at h
        simpa only [coeff_reverse,revAt_le hn] using h
      · have big := lt_of_not_ge hn
        rw [coeff_eq_zero_of_natDegree_lt big,coeff_eq_zero_of_natDegree_lt ((reverse_natDegree_le f).trans_lt big),
          sub_self]
        exact K.zero_mem
    have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
    have both := coefficients_of_reversal_differences fm fc gc pf.nonneg pg.nonneg bin K offsets
    exact ⟨(pf.field_iff fm K).mpr both.1,(pg.field_iff gm K).mpr both.2⟩

/-- Rational normalized differences across one marginal's midpoint suffice for
Green's two original uniformity conclusions, with arbitrary opposite support. -/
theorem uniform_of_rational_reflected_differences {P Q : PMF ℤ}
    (flat : IsUniformOnSupport (indepSum P Q)) {a b : ℤ} (lo : IsLeast P.support a)
    (hi : IsGreatest P.support b)
    (rational : ∀ z, ∃ q : ℚ, (q:ℝ) = ((P (a+b-z)).toReal-(P z).toReal)/(P a).toReal) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨a',b',lo',hi',field⟩ := field_of_reflected_differences flat
  obtain rfl := lo.unique lo'
  obtain rfl := hi.unique hi'
  let K := (algebraMap ℚ ℝ).fieldRange
  have both := (field K).mpr rational
  apply uniform_of_rational_ratios flat (Or.inl ?_)
  intro z y _
  exact K.div_mem (both.1 z) (both.1 y)

#print axioms coefficients_of_reversal_relation
#print axioms coefficients_of_reversal_differences
#print axioms coefficients_iff_reversal
#print axioms binary_of_rational_times_reciprocal
#print axioms field_of_reflected_differences
#print axioms uniform_of_rational_reflected_differences

end Green28ReversalField
