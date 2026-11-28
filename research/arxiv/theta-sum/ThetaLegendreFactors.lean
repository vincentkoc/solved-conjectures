import ThetaCharacterHarmonicLimit
import ThetaCharacterSeven
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

private theorem raw {d : ℕ} (ho : Odd d) (hd : q∣d) :
    siftedSum (fun j => parity j*symbol q j) ∅ d = parityFactor q := by
  obtain ⟨k,rfl⟩ := hd
  have hq := ho.of_dvd_nat (dvd_mul_right q k)
  have hk := ho.of_dvd_nat (dvd_mul_left k q)
  let f j := parity j*symbol q j
  have hshift (a j : ℕ) : f (q*a+j)=(-1:ℤ)^a*f j := by
    simp only [f,parity,symbol,Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,
      pow_add,pow_mul,hq.neg_one_pow]
    ring
  have H (a : ℕ) : ∑ j ∈ range (q*a), f j = if a%2=1 then parityFactor q else 0 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [Nat.mul_succ,sum_range_add,ih]
      simp_rw [hshift,← mul_sum]
      change _ + (-1:ℤ)^a * parityFactor q = _
      simp only [neg_one_pow_eq_ite,Nat.even_iff]
      split_ifs <;> omega
  simp only [siftedSum,sift,notMem_empty,IsEmpty.forall_iff,implies_true,if_true,sum_range_succ,
    symbol_zero q (dvd_mul_right q k),mul_zero,add_zero]
  simpa only [Nat.odd_iff.mp hk,if_true] using H k

private theorem parity_prefix (s : Finset ℕ) {d : ℕ} (ho : Odd d) (hq : q∣d)
    (hs : ∀ a∈s, Nat.Prime a ∧ a≠q ∧ a∣d) :
    siftedSum (fun j => parity j*symbol q j) s d = parityFactor q*∏ a∈s,(1-symbol q a) := by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty => simpa using raw q ho hq
  | @insert p s hp ih =>
    obtain ⟨hpr,hne,hpd⟩ := hs p (mem_insert_self ..)
    have hs' (a) (ha : a∈s) := hs a (mem_insert_of_mem ha)
    have H := Nat.mul_div_cancel' hpd
    have hdiv {a : ℕ} (ha : a.Coprime p) (had : a∣d) : a∣d/p := ha.dvd_mul_left.mp (H.symm ▸ had)
    have hq' := hdiv ((Nat.coprime_primes (Fact.out : Nat.Prime q) hpr).mpr hne.symm) hq
    have ho' : Odd (d/p) := ho.of_dvd_nat ⟨p,by rw [mul_comm,H]⟩
    have hf (i) : parity (p*i)*symbol q (p*i)=symbol q p*(parity i*symbol q i) := by
      rw [parity_odd_mul (ho.of_dvd_nat hpd),symbol_mul q]; ring
    rw [prefix_insert _ hpr hf hp (fun a ha => (hs' a ha).1),ih ho hq hs',
      ih ho' hq' (fun a ha => ⟨(hs' a ha).1,(hs' a ha).2.1,
        hdiv ((Nat.coprime_primes (hs' a ha).1 hpr).mpr (fun e => hp (e ▸ ha))) (hs' a ha).2.2⟩),prod_insert hp]
    ring
omit [Fact q.Prime] in
private lemma sieve_good {d j : ℕ} (hd : d≠0) (h : ¬q∣j) :
    j.Coprime d ↔ ∀ p∈d.primeFactors.erase q, ¬p∣j := by
  constructor
  · intro hc p hp
    have hpr := Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2
    exact fun hpj => hpr.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpj (Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2))
  · intro hs; by_contra hn
    obtain ⟨p,hpr,hpj,hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    exact hs p (mem_erase.mpr ⟨fun he => h (he ▸ hpj),hpr.mem_primeFactors hpd hd⟩) hpj

/-- The conductor parity transform and its finite sieve factors. -/
theorem parity_transform {d : ℕ} (ho : Odd d) (hq : q∣d) :
    (∑ j∈(range d).filter (·.Coprime d), parity j*symbol q j) =
      parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p) := by
  classical
  let s := d.primeFactors.erase q
  have H := parity_prefix q s ho hq (fun p hp => ⟨Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2,
    (mem_erase.mp hp).1,Nat.dvd_of_mem_primeFactors (mem_erase.mp hp).2⟩)
  have hz : symbol q d=0 := symbol_zero q hq
  rw [← H,siftedSum,sum_range_succ,show sift (fun j => parity j*symbol q j) s d=0 by simp [sift,hz],
    add_zero,sum_filter]
  apply sum_congr rfl
  intro j _
  by_cases h : q∣j
  · simp [sift,symbol_zero q h]
  · simp only [sift,s,sieve_good q ho.pos.ne' h]

private lemma unit_sq {d : ℕ} (hd : q∣d) (u : (ZMod d)ˣ) : symbol q (u:ZMod d).val^2=1 := by
  have hc := ((ZMod.val_coe_unit_coprime u).coprime_dvd_right hd).symm
  have hn := (Fact.out : q.Prime).coprime_iff_not_dvd.mp hc
  rcases symbol_unit q hn with h|h <;> rw [h] <;> norm_num

private lemma unit_mul {d : ℕ} (hq : q∣d) (u v : (ZMod d)ˣ) :
    symbol q ((u*v:(ZMod d)ˣ):ZMod d).val=symbol q (u:ZMod d).val*symbol q (v:ZMod d).val := by
  rw [Units.val_mul,ZMod.val_mul,symbol_mod q hq,symbol_mul q]

theorem wave_transform {d w : ℕ} [NeZero d] (hd : Odd d) (hq : q∣d) (hw : Odd w) (hc : w.Coprime d) :
    ∑ u : (ZMod d)ˣ,symbol q (u:ZMod d).val*wave (u:ZMod d).val d w =
      symbol q w*(parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p)) := by
  classical
  let v := ZMod.unitOfCoprime w hc
  have hv : symbol q (v:ZMod d).val=symbol q w := by simp [v,ZMod.val_natCast,symbol_mod q hq]
  have hW := ThetaCharacterThree.wave_unit hd hw hc
  have hC (u : (ZMod d)ˣ) : symbol q (u:ZMod d).val=symbol q w*symbol q ((v/u:(ZMod d)ˣ):ZMod d).val := by
    have H := unit_mul q hq u (v/u)
    rw [mul_div_cancel] at H
    rw [← hv,H]
    linear_combination -(symbol q (u:ZMod d).val)*(unit_sq q hq (v/u))
  simp_rw [hW]
  rw [← parity_transform q hd hq,← ThetaReciprocalFibers.unit_sum_nat,mul_sum]
  apply Fintype.sum_bijective (fun u : (ZMod d)ˣ => v/u)
    ((show Function.Involutive (fun u : (ZMod d)ˣ => v/u) from fun u => div_div_cancel v u).bijective)
  intro u
  rw [hC u]
  ring

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

/-- Deleting a finite set of primes gives the usual Euler factors in the ordinary limit. -/
theorem sifted_limit {L : ℝ} (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L))
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Tendsto (siftedSum (term q) s) atTop (𝓝 (L * ∏ p ∈ s,(1-(symbol q p:ℝ)/p))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hL
  | @insert p s hp ih =>
    have hpr := hs p (mem_insert_self ..)
    have hs' (a) (ha : a ∈ s) := hs a (mem_insert_of_mem ha)
    have hterm (j : ℕ) : term q (p*j)=((symbol q p:ℝ)/p)*term q j := by
      simp only [term,symbol_mul,Nat.cast_mul,Int.cast_mul]; ring
    have H := ih hs'
    have G := H.sub ((H.comp (Nat.tendsto_div_const_atTop hpr.ne_zero)).const_mul ((symbol q p:ℝ)/p))
    rw [prod_insert hp]
    convert G using 1
    · funext K; exact prefix_insert _ hpr hterm hp hs' K
    · congr 1; ring

private lemma sifted_eq {d : ℕ} [NeZero d] (j : ℕ) :
    sift (term q) (insert 2 (d.primeFactors.erase q)) j =
      if j%2=1 ∧ j.Coprime d then (symbol q j:ℝ)/j else 0 := by
  by_cases h : q∣j
  · simp [sift,term,symbol_zero q h]
  · simp only [sift,term,forall_mem_insert,← sieve_good q (NeZero.ne d) h]
    have he : (¬2∣j) ↔ j%2=1 := by omega
    simp only [he]

theorem row_factorization {d : ℕ} [NeZero d] (hd : Odd d) (hq : q∣d) (K : ℕ) :
    (∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) =
      ((parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p):ℤ):ℝ)*siftedSum (term q) (insert 2 (d.primeFactors.erase q)) K := by
  classical
  let s := d.primeFactors.erase q
  let A : ℤ := parityFactor q*∏ p∈s,(1-symbol q p)
  have ht (w : ℕ) :
      (∑ u : (ZMod d)ˣ,symbol q (u:ZMod d).val*wave (u:ZMod d).val d w) =
        if w%2=1 ∧ w.Coprime d then symbol q w*A else 0 := by
    split_ifs with h
    · exact wave_transform q hd hq (Nat.odd_iff.mpr h.1) h.2
    · have H (n : ℕ) : wave n d w=0 := if_neg (fun H => h H.2.2)
      simp [H]
  have he (i : ℕ) :
      (∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*(((i:ℝ)+1)⁻¹*
        (wave (u:ZMod d).val d (i+1):ℝ))) =
        (A:ℝ)*sift (term q) (insert 2 s) (i+1) := by
    have H := congrArg (Int.cast (R:=ℝ)) (ht (i+1))
    push_cast at H
    rw [show s=d.primeFactors.erase q from rfl,sifted_eq q]
    simp_rw [show ∀ (a b c:ℝ),a*(b*c)=b*(a*c) by intros; ring,← mul_sum]
    rw [H]; split_ifs <;> push_cast <;> ring
  change _=(A:ℝ)*siftedSum (term q) (insert 2 s) K
  unfold row
  simp_rw [mul_sum]; rw [sum_comm]; simp_rw [he]; rw [← mul_sum]
  congr 1
  unfold siftedSum
  rw [sum_range_succ']
  simp [sift,term]

/-- All denominator-dependent factors multiply the same signed conductor factor. -/
theorem row_limit {d : ℕ} [NeZero d] (ho : Odd d) (hd : q∣d) {L : ℝ}
    (hL : Tendsto (siftedSum (term q) ∅) atTop (𝓝 L)) :
    Tendsto (fun K => ∑ u : (ZMod d)ˣ,(symbol q (u:ZMod d).val:ℝ)*row d K (u:ZMod d).val) atTop
      (𝓝 (((parityFactor q*∏ p∈d.primeFactors.erase q,(1-symbol q p):ℤ):ℝ) *
        (L*∏ p∈insert 2 (d.primeFactors.erase q),(1-(symbol q p:ℝ)/p)))) := by
  simp_rw [row_factorization q ho hd]
  apply Tendsto.const_mul
  apply sifted_limit q hL
  intro p hp
  rcases mem_insert.mp hp with rfl|hp
  · decide
  · exact Nat.prime_of_mem_primeFactors (mem_erase.mp hp).2

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
