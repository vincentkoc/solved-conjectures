import ThetaJacobiRows
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Parity and harmonic factors for primitive real quadratic twists. -/
namespace Arxiv.«2501.03234».ThetaLegendreFactors
open Finset Filter Topology ThetaCharacterThree ThetaCharacterSeven ThetaRowCorrelations
variable (q : ℕ) [Fact q.Prime]

/-- The Legendre symbol on natural-number inputs. -/
noncomputable def symbol (n : ℕ) : ℤ := quadraticChar (ZMod q) (n : ZMod q)

theorem symbol_mul (a b : ℕ) : symbol q (a*b)=symbol q a * symbol q b := by
  simp only [symbol, Nat.cast_mul, map_mul]

theorem symbol_mod {d : ℕ} (hd : q ∣ d) (n : ℕ) : symbol q (n%d) = symbol q n := by
  unfold symbol
  congr 1
  exact (ZMod.natCast_eq_natCast_iff ..).mpr ((Nat.mod_modEq n d).of_dvd hd)

theorem symbol_zero {n : ℕ} (h : q∣n) : symbol q n = 0 := by
  simp [symbol,(ZMod.natCast_eq_zero_iff n q).mpr h]

theorem symbol_unit {n : ℕ} (h : ¬q∣n) : symbol q n = 1 ∨ symbol q n = -1 :=
  quadraticChar_dichotomy (mt (ZMod.natCast_eq_zero_iff n q).mp h)

/-- The complex-valued quadratic Dirichlet character of prime modulus. -/
noncomputable def dirChar : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

theorem nonprincipal (hq : q≠2) : dirChar q ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α:=ℂ))).mpr
    (quadraticChar_ne_one (by simpa [ZMod.ringChar_zmod_n] using hq))

theorem range_zero (hq : q≠2) : ∑ i ∈ range q, symbol q i = 0 := by
  have hz := quadraticChar_sum_zero (F := ZMod q) (by simpa [ZMod.ringChar_zmod_n] using hq)
  rw [← Fin.sum_univ_eq_sum_range]
  cases q with
  | zero => exact (Nat.not_prime_zero Fact.out).elim
  | succ q =>
    change ∑ i : ZMod (q+1), quadraticChar (ZMod (q+1)) (i.val : ZMod (q+1)) = 0
    simpa only [ZMod.natCast_zmod_val] using hz

/-- Unnormalized parity transform at the conductor. -/
noncomputable def parityFactor : ℤ := ∑ i ∈ range q, parity i * symbol q i

private lemma paired (m : ℕ) :
    (∑ i ∈ range (2*m), parity (i+1)*symbol q (i+1)) =
      (∑ i ∈ range (2*m), symbol q (i+1)) - 2*∑ j ∈ range m, symbol q (2*(j+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1)=2*m+1+1 by ring]
    simp only [sum_range_succ]
    rw [ih]
    have h1 : parity (2*m+1)=1 := by simp [parity,pow_add,pow_mul]
    have h2 : parity (2*m+1+1)= -1 := by simp [parity,pow_add,pow_mul]
    rw [h1,h2,show 2*(m+1)=2*m+1+1 by ring]
    ring

private lemma parity_factor_even_sum (ho : Odd q) :
    parityFactor q = -2*∑ j∈range (q/2),symbol q (2*(j+1)) := by
  let k := q/2
  have hh := Nat.odd_iff.mp ho
  have hq' : q=2*k+1 := by dsimp [k]; omega
  have hz := range_zero q (by omega)
  have hsym0 := symbol_zero q (dvd_zero q)
  have he := paired q k
  change parityFactor q= -2*∑ j ∈ range k, symbol q (2*(j+1))
  unfold parityFactor
  rw [show range q=range (2*k+1) by rw [← hq'], sum_range_succ', hsym0,mul_zero,add_zero,he]
  rw [show range q=range (2*k+1) by rw [← hq'], sum_range_succ',hsym0,add_zero] at hz
  rw [hz]; ring

/-- The reduction from the conductor factor to the classical quadratic excess. -/
theorem parityFactor_eq_excess (ho : Odd q) :
    parityFactor q= -2 * symbol q 2 * ∑ j∈range (q/2),symbol q (j+1) := by
  rw [parity_factor_even_sum q ho]
  simp_rw [symbol_mul,← mul_sum]
  ring

/-- For q ≡ 3 mod 4 the parity transform is twice an odd integer. -/
theorem parityFactor_nonzero (hq : q%4=3) : parityFactor q ≠ 0 := by
  let k := q/2
  have hq' : q=2*k+1 := by dsimp [k]; omega
  have hpar := parity_factor_even_sum q (Nat.odd_iff.mpr (by omega))
  change parityFactor q= -2*∑ j ∈ range k, symbol q (2*(j+1)) at hpar
  have hs (m : ℕ) (hm : m ≤ k) : (∑ j ∈ range m, symbol q (2*(j+1))) % 2 = (m:ℤ)%2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, Nat.cast_succ]
      have hi := ih (by omega)
      have hn : ¬q∣2*(m+1) := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      rcases symbol_unit q hn with h|h <;> rw [h] <;> omega
  have hx := hs k le_rfl
  have hk : (k:ℤ)%2=1 := by exact_mod_cast (by dsimp [k]; omega : k%2=1)
  rw [hpar]; intro h
  rw [hk] at hx
  omega

/-- At q ≡ 1 mod 4 reflection makes the conductor parity transform vanish. -/
theorem parityFactor_zero (hq : q%4=1) : parityFactor q = 0 := by
  let f (j : ℕ) := parity j*symbol q j
  have hm : quadraticChar (ZMod q) (-1) = 1 := by
    rw [quadraticChar_neg_one (by rw [ZMod.ringChar_zmod_n]; omega),ZMod.card,ZMod.χ₄_nat_one_mod_four hq]
  have hs (j : ℕ) (hj : j≤q) : f (q-j) = -f j := by
    have hsym : symbol q (q-j)=symbol q j := by
      unfold symbol
      rw [Nat.cast_sub hj,ZMod.natCast_self,zero_sub,← neg_one_mul,map_mul,hm,one_mul]
    have hpar : parity (q-j) = -parity j := by
      simp only [parity,neg_one_pow_eq_ite,Nat.even_iff]
      split_ifs <;> omega
    simp only [f,hsym,hpar,neg_mul]
  have he := sum_range_reflect f (q+1)
  simp only [Nat.add_sub_cancel] at he
  have ht : (∑ j ∈ range (q+1), f (q-j)) = -(∑ j ∈ range (q+1),f j) := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun j hj => hs j (Nat.le_of_lt_succ (mem_range.mp hj))
  rw [ht,sum_range_succ,show f q=0 by simp [f,symbol_zero q (dvd_refl q)],add_zero] at he
  change ∑ j ∈ range q, f j = 0
  omega

private lemma jacobi_eq (n : ℕ) : ThetaJacobiRows.symbol q n=symbol q n := by
  simp only [ThetaJacobiRows.symbol,←jacobiSym.legendreSym.to_jacobiSym,legendreSym,symbol,Int.cast_natCast]

private lemma sieve_eq (d : ℕ) : ThetaJacobiRows.sieve q d=d.primeFactors.erase q := by
  ext p
  simp only [ThetaJacobiRows.sieve,mem_filter,mem_erase]
  constructor
  · rintro ⟨hp,hc⟩
    exact ⟨(Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) Fact.out).mp hc,hp⟩
  · rintro ⟨hne,hp⟩
    exact ⟨hp,(Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) Fact.out).mpr hne⟩

private lemma parity_eq : ThetaJacobiRows.parityFactor q=parityFactor q := by
  simp only [ThetaJacobiRows.parityFactor,parityFactor,jacobi_eq]

/-- The conductor parity transform and its finite sieve factors. -/
theorem parity_transform {d : ℕ} (ho : Odd d) (hq : q∣d) :
    (∑ j∈(range d).filter (·.Coprime d), parity j*symbol q j) =
      parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p) := by
  simpa only [jacobi_eq,parity_eq,sieve_eq] using
    ThetaJacobiRows.parity_transform q (Fact.out : q.Prime).one_lt ho hq

theorem wave_transform {d w : ℕ} [NeZero d] (hd : Odd d) (hq : q∣d) (hw : Odd w) (hc : w.Coprime d) :
    ∑ u : (ZMod d)ˣ,symbol q (u:ZMod d).val*wave (u:ZMod d).val d w =
      symbol q w*(parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p)) := by
  simpa only [jacobi_eq,parity_eq,sieve_eq] using
    ThetaJacobiRows.wave_transform q (Fact.out : q.Prime).one_lt hd hq hw hc

/-- Ordinary reciprocal Legendre term; the zero index contributes zero. -/
noncomputable def term (n : ℕ) : ℝ := (symbol q n:ℝ)/n

private theorem continued_nonneg (hq : q≠2) : 0 ≤ (DirichletCharacter.LFunction (dirChar q) 1).re := by
  have hc : Tendsto (fun s : ℝ => (DirichletCharacter.LFunction (dirChar q) (s:ℂ)).re)
      (𝓝[>] 1) (𝓝 ((DirichletCharacter.LFunction (dirChar q) 1).re)) := by
    simpa [Function.comp_def] using (Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction (nonprincipal q hq)).continuous.comp
        Complex.continuous_ofReal)).continuousAt (x:=(1:ℝ)) |>.tendsto.mono_left
          (nhdsWithin_le_nhds (s:=Set.Ioi (1:ℝ)))
  apply ge_of_tendsto hc
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 1 < (s:ℂ).re := hs
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs']
  let a (p : Nat.Primes) : ℝ := (1-(symbol q p:ℝ)*(p:ℝ)^(-s))⁻¹
  have he (p : Nat.Primes) : (a p:ℂ) = (1-(dirChar q) (p:ZMod q)*(p:ℂ)^(-(s:ℂ)))⁻¹ := by
    simp only [a,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg _),Complex.ofReal_neg,Complex.ofReal_natCast,Complex.ofReal_intCast]
    rfl
  have H := (dirChar q).LSeries_eulerProduct_hasProd hs'
  simp_rw [← he] at H
  change Tendsto (fun t : Finset Nat.Primes => ∏ p∈t,((a p:ℝ):ℂ)) atTop _ at H
  have hprod : Tendsto (fun t : Finset Nat.Primes => ((∏ p∈t,a p:ℝ):ℂ)) atTop
      (𝓝 (LSeries (fun n : ℕ => dirChar q (n:ZMod q)) (s:ℂ))) := by
    simpa only [Complex.ofReal_prod] using H
  apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hprod)
  filter_upwards with t
  change 0 ≤ ∏ p∈t,a p
  apply prod_nonneg
  intro p _
  have hχ : (symbol q p:ℝ) ≤ 1 := by
    by_cases h : q ∣ (p:ℕ)
    · simp [symbol_zero q h]
    · rcases symbol_unit q h with h|h <;> simp [h]
  have hp : (1:ℝ) ≤ p := by exact_mod_cast p.prop.one_le
  have hp0 : (0:ℝ) ≤ p := hp.trans' zero_le_one
  have hneg : -s ≤ 0 := by change 1<s at hs; linarith
  exact inv_nonneg.mpr (sub_nonneg.mpr (mul_le_one₀ hχ (Real.rpow_nonneg hp0 _)
    (by simpa using Real.rpow_le_rpow_of_exponent_le hp hneg)))

/-- The ordinary harmonic partial sums of the real symbol have a nonzero real limit. -/
theorem reciprocal_limit (hq : q ≠ 2) :
    ∃ L : ℝ, 0 < L ∧ Tendsto (siftedSum (term q) ∅) atTop (𝓝 L) := by
  let L := DirichletCharacter.LFunction (dirChar q) 1
  obtain ⟨H,Hnz⟩ := ThetaCharacterHarmonicLimit.harmonic_limit (dirChar q) (nonprincipal q hq)
  have he (K : ℕ) : ((siftedSum (term q) ∅ K:ℝ):ℂ) =
      ∑ i ∈ range (K+1), dirChar q (i:ZMod q)/(i:ℂ) := by
    simp only [siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true,
      term,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
    rfl
  have HC : Tendsto (fun K => ((siftedSum (term q) ∅ K:ℝ):ℂ)) atTop (𝓝 L) := by
    simpa only [he,Function.comp_def] using H.comp (tendsto_add_atTop_nat 1)
  have HR := Complex.continuous_re.continuousAt.tendsto.comp HC
  have HR' : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L.re) := by simpa [Function.comp_def] using HR
  refine ⟨L.re,?_,HR'⟩
  apply lt_of_le_of_ne (continued_nonneg q hq)
  intro hh
  have h0 : L.re=0 := hh.symm
  have Hc := tendsto_nhds_unique HC (Complex.continuous_ofReal.continuousAt.tendsto.comp HR')
  exact Hnz (Hc.trans (by simp [h0]))

/-- An effective tail bound for the ordinary real harmonic factor. -/
theorem reciprocal_error (hq : q≠2) {L : ℝ}
    (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) {K : ℕ} (hK : 0<K) :
    |L - ∑ n∈range K, term q n| ≤ q/(K:ℝ) := by
  let χ := dirChar q
  have he (k : ℕ) : ((∑ n∈range k,term q n:ℝ):ℂ) =
      ∑ n∈range k,χ (n:ZMod q)/(n:ℂ) := by
    simp only [term,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
    rfl
  have HC := (ThetaCharacterHarmonicLimit.harmonic_limit χ (nonprincipal q hq)).1.comp
    (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun k => ((∑ n∈range (k+1),term q n:ℝ):ℂ)) atTop (𝓝 (L:ℂ)) := by
    have H := Complex.continuous_ofReal.continuousAt.tendsto.comp hL
    simpa only [Function.comp_def,siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true] using H
  have hs : (L:ℂ)=DirichletCharacter.LFunction χ 1 := tendsto_nhds_unique hr (by
    simpa only [Function.comp_def,he] using HC)
  have HB := ThetaCharacterHarmonicLimit.harmonic_error χ (nonprincipal q hq) hK
  rw [← hs,← he,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at HB
  exact HB

private lemma term_eq : ThetaJacobiRows.term q=term q := by
  funext n; simp only [ThetaJacobiRows.term,term,jacobi_eq]

/-- Deleting a finite set of primes gives the usual Euler factors in the ordinary limit. -/
theorem sifted_limit {L : ℝ} (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L))
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (siftedSum (term q) s) atTop (𝓝 (L * ∏ p ∈ s,(1-(symbol q p:ℝ)/p))) := by
  simpa only [term_eq,jacobi_eq] using
    ThetaJacobiRows.sifted_limit q (term_eq q ▸ hL) s hs

theorem row_factorization {d : ℕ} [NeZero d] (hd : Odd d) (hq : q∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) =
      ((parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p):ℤ):ℝ)*siftedSum (term q) (insert 2 (d.primeFactors.erase q)) K := by
  simpa only [jacobi_eq,parity_eq,sieve_eq,term_eq] using
    ThetaJacobiRows.row_factorization q (Fact.out : q.Prime).one_lt hd hq K

/-- All denominator-dependent factors multiply the same signed conductor factor. -/
theorem row_limit {d : ℕ} [NeZero d] (ho : Odd d) (hd : q∣d) {L : ℝ}
    (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) :
    Tendsto (fun K => ∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) atTop
      (𝓝 (((parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p):ℤ):ℝ) *
        (L*∏ p∈insert 2 (d.primeFactors.erase q),(1-(symbol q p:ℝ)/p)))) := by
  simpa only [jacobi_eq,parity_eq,sieve_eq,term_eq] using
    ThetaJacobiRows.row_limit q (Fact.out : q.Prime).one_lt ho hd (term_eq q ▸ hL)

#print axioms nonprincipal
#print axioms symbol_mul
#print axioms symbol_mod
#print axioms symbol_zero
#print axioms symbol_unit
#print axioms range_zero
#print axioms parity_transform
#print axioms wave_transform
#print axioms row_factorization
#print axioms row_limit

#print axioms reciprocal_error
#print axioms reciprocal_limit
#print axioms sifted_limit

#print axioms parityFactor_eq_excess
#print axioms parityFactor_zero
#print axioms parityFactor_nonzero
end Arxiv.«2501.03234».ThetaLegendreFactors
