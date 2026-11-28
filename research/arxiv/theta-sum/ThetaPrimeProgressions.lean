import ThetaPrimeAsymptotic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.Normed.Group.Tannery

/-! Reciprocal mass and exceptional prime counts. -/

namespace Arxiv.«2501.03234».ThetaPrimeProgressions

open Finset Filter ThetaPrimeDensity

/-- Reciprocal term on primes satisfying a predicate, extended by zero. -/
noncomputable def primeRecip (P : ℕ → Prop) (n : ℕ) : ℝ := by
  classical exact if n.Prime ∧ P n then (n:ℝ)⁻¹ else 0

private lemma primeRecip_nonneg (P : ℕ → Prop) (n : ℕ) : 0≤primeRecip P n := by
  classical unfold primeRecip; split_ifs <;> positivity

private lemma primeSet_entry {P : ℕ → Prop} {X n : ℕ} : n ∈ primeSet P X ↔ n≤X ∧ n.Prime ∧ P n := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

private lemma dyadic_mass (P : ℕ → Prop) (C : ℝ)
    (hb : ∀ X : ℕ, 2≤X → ((primeSet P X).card:ℝ) ≤ C*X/(Real.log X)^2) (k : ℕ) :
    ∑ n ∈ Ico (2^k) (2^(k+1)), primeRecip P n ≤ (2*C/(Real.log 2)^2)*((k:ℝ)+1)⁻¹^2 := by
  classical
  let U := 2^(k+1)
  let L := 2^k
  let A := (Ico L U).filter (fun n => n.Prime ∧ P n)
  have hL : 0<L := by dsimp [L]; positivity
  have hU : 2≤U := by dsimp [U]; rw [pow_succ]; have := Nat.one_le_pow k 2 (by decide); omega
  have he : ∑ n ∈ Ico L U, primeRecip P n = ∑ n ∈ A, (n:ℝ)⁻¹ := by
    classical simp [A,sum_filter,primeRecip]
  rw [he]
  have hsum : ∑ n ∈ A, (n:ℝ)⁻¹ ≤ (A.card:ℝ)/(L:ℝ) := by
    rw [div_eq_mul_inv,← nsmul_eq_mul,← sum_const]
    apply sum_le_sum; intro n hn
    apply inv_anti₀ (Nat.cast_pos.mpr hL)
    exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1
  have hA : A ⊆ primeSet P U := by
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp hn
    exact primeSet_entry.mpr ⟨(mem_Ico.mp hn).2.le,hp⟩
  apply hsum.trans
  apply (div_le_div_of_nonneg_right ((show (A.card:ℝ)≤(primeSet P U).card by exact_mod_cast card_le_card hA).trans (hb U hU)) (by positivity)).trans_eq
  dsimp [U,L]; push_cast; rw [Real.log_pow]; push_cast; rw [pow_succ]
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hk : 0 < (k:ℝ)+1 := by positivity
  field_simp

/-- An X/log² X exceptional-prime count implies summability of their reciprocals. -/
theorem summable_primeRecip_of_count (P : ℕ → Prop)
    (h : ∃ C : ℝ, 0<C ∧ ∀ X : ℕ, 2≤X → ((primeSet P X).card:ℝ) ≤ C*X/(Real.log X)^2) :
    Summable (primeRecip P) := by
  obtain ⟨C,hC,hb⟩ := h
  let A := 2*C/(Real.log 2)^2
  let b (k : ℕ) := ((k:ℝ)+1)⁻¹^2
  have hs : Summable b := by
    have H := (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).comp_injective Nat.succ_injective
    simpa [b,Function.comp_def,inv_pow] using H
  have hpartial (k : ℕ) : ∑ n ∈ range (2^k), primeRecip P n ≤ A*∑ j ∈ range k, b j := by
    induction k with
    | zero => simp [primeRecip]
    | succ k ih =>
      rw [sum_range_succ b,mul_add,← sum_range_add_sum_Ico _ (show 2^k≤2^(k+1) by simp [pow_succ])]
      exact add_le_add ih (dyadic_mass P C hb k)
  apply summable_of_sum_range_le (primeRecip_nonneg P) (c:=A*∑' j, b j)
  intro n
  have hn : range n ⊆ range (2^n) := range_mono n.lt_two_pow_self.le
  exact (sum_le_sum_of_subset_of_nonneg hn (fun i _ _ => primeRecip_nonneg P i)).trans
    ((hpartial n).trans (mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (by intro i _; dsimp [b]; positivity)) (by dsimp [A]; positivity)))

open ArithmeticFunction ArithmeticFunction.vonMangoldt

/-- The reciprocal sum of primes in any invertible residue class diverges. -/
theorem residue_primeRecip_diverges {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ¬Summable (primeRecip (fun n => (n:ZMod q)=a)) := by
  classical
  intro H
  let t (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  let f (k n : ℕ) : ℝ := t k*(residueClass a n/(n:ℝ)^(1+t k))
  let b (n : ℕ) := primeRecip (fun n => (n:ZMod q)=a) n +
    (if n.Prime then 0 else residueClass a n)/(n:ℝ)
  have hbs : Summable b := H.add (summable_residueClass_non_primes_div a)
  have ht : Tendsto t atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht₀ (k : ℕ) : 0<t k := by dsimp [t]; positivity
  have ht₁ (k : ℕ) : t k≤1 := by dsimp [t]; rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hpt (n : ℕ) : Tendsto (fun k => f k n) atTop (nhds 0) := by
    by_cases hn : n=0
    · simp [hn,f]
    have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have he : Tendsto (fun k => 1+t k) atTop (nhds 1) := by simpa using (tendsto_const_nhds (x:=(1:ℝ))).add ht
    have hpow := (Real.continuous_const_rpow hn'.ne').continuousAt.tendsto.comp he
    have hdiv := (tendsto_const_nhds (x:=residueClass a n)).div hpow (Real.rpow_pos_of_pos hn' 1).ne'
    simpa [f] using ht.mul hdiv
  have hdom (k n : ℕ) : ‖f k n‖ ≤ b n := by
    have hΛ := residueClass_nonneg a n
    have hf : 0≤f k n := by dsimp [f]; positivity [ht₀ k]
    rw [Real.norm_eq_abs,abs_of_nonneg hf]
    by_cases hn : n=0
    · simp [hn,b,f,primeRecip]
    have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn₁ : 1≤(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpw := Real.rpow_pos_of_pos hn' (t k)
    by_cases hp : n.Prime
    · by_cases hc : (n:ZMod q)=a
      · have he : residueClass a n = Real.log n := by simp [residueClass,hc,vonMangoldt_apply_prime hp]
        have hh := Real.log_le_rpow_div hn'.le (ht₀ k)
        dsimp only [f,b]; simp only [hp,if_true,zero_div,add_zero,he,primeRecip,hc,and_self]
        rw [Real.rpow_add hn',Real.rpow_one,← mul_div_assoc,div_le_iff₀ (mul_pos hn' hpw)]
        calc _ ≤ (n:ℝ)^t k := by linarith only [(le_div_iff₀ (ht₀ k)).mp hh]
             _ = _ := by field_simp
      · simp [b,f,primeRecip,hp,hc,residueClass]
    · dsimp only [f,b]; simp only [primeRecip,hp,false_and,if_false,zero_add]
      apply (mul_le_mul_of_nonneg_right (ht₁ k) (div_nonneg hΛ (Real.rpow_nonneg hn'.le _))).trans
      rw [one_mul]
      apply div_le_div_of_nonneg_left hΛ hn'
      rw [Real.rpow_add hn',Real.rpow_one]
      exact le_mul_of_one_le_right hn'.le (Real.one_le_rpow hn₁ (ht₀ k).le)
  have htends : Tendsto (fun k => ∑' n, f k n) atTop (nhds 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence (g:=fun _ : ℕ => (0:ℝ))
      hbs hpt (Eventually.of_forall hdom)
  obtain ⟨C,hC⟩ := LSeries_residueClass_lower_bound ha
  have hpole (k : ℕ) : (q.totient:ℝ)⁻¹ - t k*C ≤ ∑' n, f k n := by
    have hx : 1+t k ∈ Set.Ioc 1 2 := ⟨by linarith [ht₀ k],by linarith [ht₁ k]⟩
    have hh := mul_le_mul_of_nonneg_left (hC hx) (ht₀ k).le
    dsimp only [f]; rw [tsum_mul_left]
    calc
      _ = t k*((q.totient:ℝ)⁻¹/(1+t k-1)-C) := by rw [add_sub_cancel_left]; field_simp [ne_of_gt (ht₀ k)]
      _ ≤ _ := hh
  have hl : Tendsto (fun k => (q.totient:ℝ)⁻¹ - t k*C) atTop (nhds (q.totient:ℝ)⁻¹) := by
    simpa using (tendsto_const_nhds (x:=(q.totient:ℝ)⁻¹)).sub (ht.mul_const C)
  have h := le_of_tendsto_of_tendsto' hl htends hpole
  have htpos : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  exact (inv_pos.mpr htpos).not_ge h

open ThetaPrimeAsymptotic

private noncomputable def errorRatio (p : ℕ) : ℝ := |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|

/-- The primes at which the normalized theta sum deviates by ε have finite
reciprocal mass. -/
theorem summable_deviations {ε : ℝ} (hε : 0<ε) :
    Summable (primeRecip (fun p => ε ≤ |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|)) := by
  have he (X : ℕ) : primeSet (fun p => ε ≤ |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|) X =
      deviations ε X := by ext p; rw [primeSet_entry,deviation_mem]
  apply summable_primeRecip_of_count
  simpa only [he] using prime_asymptotic_exception_bound hε

/-- In every reduced progression the good primes have divergent reciprocal mass.
The progression modulus and the tolerance are arbitrary and fixed. -/
theorem nonsummable_good_class {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {ε : ℝ} (hε : 0<ε) :
    ¬Summable (primeRecip (fun p => (p:ZMod q)=a ∧ |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|<ε)) := by
  classical
  intro hg
  apply residue_primeRecip_diverges ha
  apply Summable.of_nonneg_of_le (primeRecip_nonneg _) _ (hg.add (summable_deviations hε))
  intro n
  change primeRecip (fun p => (p:ZMod q)=a) n ≤
    primeRecip (fun p => (p:ZMod q)=a ∧ errorRatio p<ε) n + primeRecip (fun p => ε≤errorRatio p) n
  by_cases hp : n.Prime <;> by_cases hr : (n:ZMod q)=a <;> rcases lt_or_ge (errorRatio n) ε with h|h <;>
    simp [primeRecip,hp,hr,h,not_lt_of_ge,not_le_of_gt]

/-- Good primes in each fixed class are arbitrarily large. -/
theorem large_good_class {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    {ε : ℝ} (hε : 0<ε) (B : ℕ) :
    ∃ p : ℕ, B<p ∧ p.Prime ∧ (p:ZMod q)=a ∧ |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|<ε := by
  classical
  by_contra h
  apply nonsummable_good_class ha hε
  apply (hasSum_sum_of_ne_finset_zero (s:=range (B+1)) ?_).summable
  intro p hp
  have hb : B<p := by simp only [mem_range] at hp; omega
  have hn : ¬(p.Prime ∧ ((p:ZMod q)=a ∧ |(S p:ℝ)/((p:ℝ)*Real.log p)-1/2|<ε)) :=
    fun he => h ⟨p,hb,he⟩
  simp only [primeRecip,if_neg hn]

/-- The canonical theta sum exceeds each fixed multiple of p infinitely often in
every invertible residue class. -/
theorem large_linear_growth_class {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (A : ℝ) (B : ℕ) :
    ∃ p : ℕ, B<p ∧ p.Prime ∧ (p:ZMod q)=a ∧ A*p<(S p:ℝ) := by
  obtain ⟨b,hb⟩ := exists_nat_gt (Real.exp (4*A))
  obtain ⟨p,hp,hprime,hres,hgood⟩ := large_good_class ha (by norm_num : (0:ℝ)<1/4) (max B b)
  have hpos : 0<(p:ℝ) := by exact_mod_cast hprime.pos
  have hlog : 0<Real.log p := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hpr : 4*A<Real.log p := by
    have he := Real.log_lt_log (Real.exp_pos _) (hb.trans (show (b:ℝ)<p by exact_mod_cast (show b<p by omega)))
    rwa [Real.log_exp] at he
  have hgt : 1/4 < (S p:ℝ)/((p:ℝ)*Real.log p) := by linarith [(abs_lt.mp hgood).1]
  have hh := (lt_div_iff₀ (mul_pos hpos hlog)).mp hgt
  exact ⟨p,by omega,hprime,hres,by nlinarith only [hh,mul_lt_mul_of_pos_left hpr hpos]⟩

/-- In particular, the original theta sum is positive at arbitrarily large primes
congruent to one modulo eight. -/
theorem frequently_positive_one_mod_eight (B : ℕ) :
    ∃ p : ℕ, B<p ∧ p.Prime ∧ p%8=1 ∧ 0<S p := by
  obtain ⟨p,hp,hprime,hres,hS⟩ := large_linear_growth_class (q:=8) (a:=1) isUnit_one 0 B
  have h := congrArg ZMod.val hres
  rw [ZMod.val_natCast] at h
  norm_num at h hS
  exact ⟨p,hp,hprime,h,by exact_mod_cast hS⟩

end Arxiv.«2501.03234».ThetaPrimeProgressions
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.summable_primeRecip_of_count
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.residue_primeRecip_diverges
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.summable_deviations
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.nonsummable_good_class
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.large_good_class
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.large_linear_growth_class
#print axioms Arxiv.«2501.03234».ThetaPrimeProgressions.frequently_positive_one_mod_eight
