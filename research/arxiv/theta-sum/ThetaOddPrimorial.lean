import ThetaCompositePowers
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecificLimits.Normed

/-! Unbounded negativity along the squarefree odd primorials. -/
namespace Arxiv.«2501.03234».ThetaCompositePowers
open Finset Filter Topology ThetaCompositeFourier

private noncomputable abbrev oddPrime (i : ℕ) := Nat.nth Nat.Prime (i+1)

/-- Product of the first n odd primes, starting with the empty product. -/
noncomputable def oddPrimorial (n : ℕ) : ℕ := ∏ i∈range n,oddPrime i

private theorem next_coprime (n : ℕ) : (oddPrimorial n).Coprime (oddPrime n) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  rw [(Nat.prime_nth_prime _).coprime_iff_not_dvd,
    Nat.prime_dvd_prime_iff_eq (Nat.prime_nth_prime _) (Nat.prime_nth_prime _)]
  exact ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.succ_lt_succ (mem_range.mp hi))).ne

theorem oddPrimorial_properties (n : ℕ) : Odd (oddPrimorial n) ∧ Squarefree (oddPrimorial n) ∧
    2^n≤oddPrimorial n := by
  induction n with
  | zero => simp [oddPrimorial]
  | succ n ih =>
    have hp := Nat.prime_nth_prime (n+1)
    have hb := Nat.add_two_le_nth_prime (n+1)
    change _ ≤ oddPrime n at hb
    rw [oddPrimorial,prod_range_succ,←oddPrimorial]
    exact ⟨ih.1.mul (hp.odd_of_ne_two (by change oddPrime n≠2; omega)),
      (Nat.squarefree_mul (next_coprime n)).2 ⟨ih.2.1,hp.squarefree⟩,
      by rw [pow_succ]; exact Nat.mul_le_mul ih.2.2 (by omega)⟩

private theorem nth_prime_le (i : ℕ) : Nat.nth Nat.Prime i≤2^(i+1) := by
  induction i with
  | zero => simp
  | succ i ih =>
    let p := Nat.nth Nat.Prime i
    obtain ⟨q,hq,hpq,hB⟩ := Nat.exists_prime_lt_and_le_two_mul p (Nat.prime_nth_prime i).ne_zero
    have hn : Nat.nth Nat.Prime (i+1)≤q := by
      by_contra! h
      exact hpq.not_ge (Nat.le_nth_of_lt_nth_succ h hq)
    calc _ ≤ q := hn
         _ ≤ 2*p := hB
         _ ≤ 2*2^(i+1) := Nat.mul_le_mul_left _ ih
         _ = _ := by rw [pow_succ (n:=i+1)]; omega

private theorem log_oddPrimorial (n : ℕ) :
    Real.log (oddPrimorial n)≤(n:ℝ)*(n+1)*Real.log 2 := by
  have H : oddPrimorial n≤(2^(n+1))^n := by
    rw [oddPrimorial,show (2^(n+1))^n=∏ _i∈range n,2^(n+1) by simp]
    apply prod_le_prod'
    intro i hi
    apply (nth_prime_le (i+1)).trans
    exact Nat.pow_le_pow_right (by decide) (by have := mem_range.mp hi; omega)
  have hp : 0<oddPrimorial n := (pow_pos (by decide : 0<2) n).trans_le (oddPrimorial_properties n).2.2
  have h := Real.log_le_log (by exact_mod_cast hp : 0<(oddPrimorial n:ℝ))
    (by exact_mod_cast H : (oddPrimorial n:ℝ)≤(((2:ℝ)^(n+1))^n))
  simp only [Real.log_pow,Nat.cast_add,Nat.cast_one] at h
  linarith only [h]

/-- Finite Euler product for the normalized gcd mass of the odd primorial. -/
theorem oddPrimorial_mass (n : ℕ) :
    (gcdMass (oddPrimorial n):ℝ)/(oddPrimorial n:ℝ)=
      ∏ i∈range n,(2-1/(Nat.nth Nat.Prime (i+1):ℝ)) := by
  induction n with
  | zero => simp [oddPrimorial,gcdMass]
  | succ n ih =>
    have h := gcdMass_prime_power (Nat.prime_nth_prime (n+1)) 1
    simp only [pow_one,Nat.cast_one,one_mul] at h
    rw [show oddPrimorial (n+1)=oddPrimorial n*oddPrime n by simp [oddPrimorial,prod_range_succ],
      prod_range_succ,gcdMass_mul (next_coprime n),Nat.cast_mul,Nat.cast_mul,←ih,mul_div_mul_comm]
    rw [show (gcdMass (oddPrime n):ℝ)/(oddPrime n:ℝ)=2-1/(oddPrime n:ℝ) by linarith only [h]]

private theorem normalized_mass_lower (n : ℕ) :
    (3/2:ℝ)^n≤(gcdMass (oddPrimorial n):ℝ)/(oddPrimorial n:ℝ) := by
  rw [oddPrimorial_mass,show (3/2:ℝ)^n=∏ _i∈range n,(3/2:ℝ) by simp [div_pow]]
  apply prod_le_prod (fun _ _ => by norm_num)
  intro i _
  have hp : (2:ℝ)≤Nat.nth Nat.Prime (i+1) := by exact_mod_cast (Nat.prime_nth_prime _).two_le
  have hrec : 1/(Nat.nth Nat.Prime (i+1):ℝ)≤1/2 := by gcongr
  linarith

/-- The gcd term is asymptotically exact even when each prime occurs only once. -/
theorem oddPrimorial_asymptotic :
    Tendsto (fun n : ℕ => (S (oddPrimorial n):ℝ)/(gcdMass (oddPrimorial n):ℝ))
      atTop (𝓝 (-(1:ℝ)/2)) := by
  let k (n : ℕ) : ℝ := oddPrimorial n
  let M (n : ℕ) : ℝ := (gcdMass (oddPrimorial n):ℝ)/k n
  have hk (n : ℕ) : (2:ℝ)^n≤k n := by dsimp [k]; exact_mod_cast (oddPrimorial_properties n).2.2
  have hkpos (n : ℕ) : 0<k n := (pow_pos (by norm_num : (0:ℝ)<2) n).trans_le (hk n)
  have hMpos (n : ℕ) : 0<M n := (pow_pos (by norm_num : (0:ℝ)<3/2) n).trans_le (normalized_mass_lower n)
  have hK := tendsto_atTop_mono hk (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have hM : Tendsto M atTop atTop := tendsto_atTop_mono normalized_mass_lower
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3/2))
  have hKi : Tendsto (fun n => 1/k n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hK
  have hMi : Tendsto (fun n => 1/M n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hM
  have he : Tendsto (fun n => ((S (oddPrimorial n):ℝ)/k n+(1-1/k n)/2*(M n-1))/M n)
      atTop (𝓝 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1:ℝ)<3/2)).const_mul 36
    simp only [mul_zero] at h
    apply squeeze_zero_norm' _ h
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1:ℝ)≤n := by exact_mod_cast hn
    have hp : 1<oddPrimorial n := lt_of_lt_of_le (one_lt_pow₀ (by decide : 1<2) (by omega : n≠0)) (oddPrimorial_properties n).2.2
    have hlog := log_oddPrimorial n
    have hlog2 : Real.log 2≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have hlog' : 1+Real.log (k n)≤3*(n:ℝ)^2 := by
      change 1+Real.log (oddPrimorial n)≤_
      have := mul_le_mul_of_nonneg_left hlog2 (show 0≤(n:ℝ)*(n+1) by positivity)
      nlinarith [sq_nonneg ((n:ℝ)-1)]
    have H := log_error hp (oddPrimorial_properties n).1
    change |(S (oddPrimorial n):ℝ)/k n+(1-1/k n)/2*(M n-1)|≤4*(1+Real.log (k n))^2 at H
    have h1 : 0≤1+Real.log (k n) := by have := Real.log_nonneg (show 1≤k n by dsimp [k]; exact_mod_cast hp.le); linarith
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (hMpos n)]
    calc _ ≤ 4*(3*(n:ℝ)^2)^2/(3/2:ℝ)^n := by
           apply div_le_div₀ (by positivity) (H.trans ?_) (by positivity) (normalized_mass_lower n)
           gcongr
         _ = 36*((n:ℝ)^4/(3/2:ℝ)^n) := by ring
  have C := ((tendsto_const_nhds (x:=(1:ℝ))).sub hKi).div_const 2
  have H := he.sub (C.mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hMi))
  convert H.congr' _ using 2
  · norm_num
  · filter_upwards with n
    have h1 := (hkpos n).ne'
    have h2 := (hMpos n).ne'
    have h3 : (gcdMass (oddPrimorial n):ℝ)≠0 := fun h0 => h2 (by simp [M,h0])
    dsimp [M,k] at h1 h2 ⊢
    field_simp
    ring

/-- Along the odd squarefree primorials, the canonical sum divided by its denominator
tends to minus infinity. -/
theorem oddPrimorial_unbounded_below :
    Tendsto (fun n : ℕ => (S (oddPrimorial n):ℝ)/(oddPrimorial n:ℝ)) atTop atBot := by
  have hM := tendsto_atTop_mono normalized_mass_lower
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<3/2))
  have H := oddPrimorial_asymptotic.neg_mul_atTop (by norm_num) hM
  apply H.congr'
  filter_upwards with n
  have hp : 0<(gcdMass (oddPrimorial n):ℝ)/(oddPrimorial n:ℝ) :=
    (pow_pos (by norm_num : (0:ℝ)<3/2) n).trans_le (normalized_mass_lower n)
  have hz : (gcdMass (oddPrimorial n):ℝ)≠0 := fun h0 => by simp [h0] at hp
  field_simp

#print axioms oddPrimorial_mass
#print axioms oddPrimorial_properties
#print axioms oddPrimorial_asymptotic
#print axioms oddPrimorial_unbounded_below

end Arxiv.«2501.03234».ThetaCompositePowers
