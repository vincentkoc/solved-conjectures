import ThetaDivisorLogMean
import ThetaOddHarmonicTriangle
import Mathlib.Data.Nat.Choose.Factorization

/-! Coprime harmonic mass on divisors of a saturated factorial. -/
namespace Arxiv.«2501.03234».ThetaDivisorTriangle
open Finset Real ThetaOddHarmonicTriangle ThetaDivisorLogMean
noncomputable section

def oddDivisors (m : ℕ) := m.divisors.filter Odd

/-- Odd coprime divisor pairs below the diagonal carry at least one sixteenth
of the squared reciprocal divisor mass. -/
theorem triangle (m : ℕ) :
    (mass m)^2/16≤∑ d∈oddDivisors m,U d/d := by
  classical
  let S := oddDivisors m
  have hS : S⊆odds m := by
    intro n hn
    obtain ⟨hd,ho⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1⟩,ho⟩
  have H := triangle_in S hS (fun p hp => subset_multiples S hp (by
    intro n hn hd
    obtain ⟨hg,ho⟩ := mem_filter.mp hn
    obtain ⟨hm,hm₀⟩ := Nat.mem_divisors.mp hg
    have ho' : Odd (n/p*p) := by rwa [Nat.div_mul_cancel hd]
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hd).trans hm,hm₀⟩,(Nat.odd_mul.mp ho').1⟩))
  have heq : m.divisors.filter (fun n => ¬2∣n)=S := by
    apply filter_congr; intro n _; rw [←even_iff_two_dvd,Nat.not_even_iff_odd]
  have hs := sum_filter_add_sum_filter_not m.divisors (2∣·) (fun g => (g:ℝ)⁻¹)
  rw [heq] at hs
  change _+(∑ g∈S,(g:ℝ)⁻¹)=mass m at hs
  have hh : mass m/2≤∑ g∈S,(g:ℝ)⁻¹ := by linarith only [hs,multiple_mass (m:=m) (t:=2) (by decide)]
  nlinarith only [H,pow_le_pow_left₀ (div_nonneg (mass_nonneg m) (by norm_num)) hh 2]

private lemma factorial_log (T : ℕ) (hT : 0<T) (s : Finset ℕ) (hs : ∀ p∈s,p.Prime ∧ p≤T) :
    ∑ p∈s,log p/p≤2*log T := by
  have ht : (0:ℝ)<T := by exact_mod_cast hT
  have H (p) (hp : p∈s) : (T:ℝ)/p≤2*(T.factorial.factorization p:ℝ) := by
    obtain ⟨hr,hle⟩ := hs p hp
    have hdiv : T/p≤T.factorial.factorization p := by
      rw [Nat.factorization_factorial hr (Nat.lt_succ_self _)]
      have hlog : 1≤p.log T := Nat.le_log_of_pow_le hr.one_lt (by simpa using hle : p^1≤T)
      simpa only [pow_one] using (single_le_sum (s:=Ico 1 (p.log T+1)) (f:=fun i => T/p^i)
        (fun _ _ => Nat.zero_le _) (mem_Ico.mpr ⟨le_rfl,by omega⟩ : 1∈Ico 1 (p.log T+1)))
    have he : T<(T/p+1)*p := (Nat.div_lt_iff_lt_mul hr.pos).mp (Nat.lt_succ_self _)
    have hdpos : 1≤T/p := Nat.div_pos hle hr.pos
    have hh := he.le.trans (Nat.mul_le_mul_right p (show T/p+1≤2*(T/p) by omega))
    have H' : (T:ℝ)≤2*(T.factorial.factorization p:ℝ)*p := by
      exact_mod_cast hh.trans (Nat.mul_le_mul_right p (Nat.mul_le_mul_left 2 hdiv))
    exact (div_le_iff₀ (by exact_mod_cast hr.pos)).mpr H'
  have hsub : s⊆T.factorial.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hs p hp).1,Nat.dvd_factorial (hs p hp).1.pos (hs p hp).2,Nat.factorial_ne_zero _⟩
  have hsum : ∑ p∈s,(T.factorial.factorization p:ℝ)*log p ≤ log (T.factorial:ℝ) := by
    rw [Real.log_nat_eq_sum_factorization,Finsupp.sum]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (log_nonneg_nat p))
  have hf := Real.log_le_log (Nat.cast_pos.mpr (Nat.factorial_pos T))
    (show (T.factorial:ℝ)≤(T:ℝ)^T by exact_mod_cast Nat.factorial_le_pow T)
  rw [Real.log_pow] at hf
  apply le_of_mul_le_mul_left (a:=(T:ℝ)) _ ht
  calc
    _ = ∑ p∈s,((T:ℝ)/p)*log p := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ ∑ p∈s,2*((T.factorial.factorization p:ℝ)*log p) := sum_le_sum (fun p hp =>
          (mul_le_mul_of_nonneg_right (H p hp) (log_nonneg_nat _)).trans_eq (by ring))
    _ ≤ _ := by rw [←mul_sum]; linarith only [hsum,hf]

/-- The logarithmic divisor moment costs one logarithm of the largest prime factor. -/
theorem smooth_log {m T : ℕ} (hm : 0 < m) (hT : 0<T) (hs : ∀ p∈m.primeFactors,p≤T) :
    logMass m≤mass m*(1+4*log T) := by
  have hD := mass_nonneg m
  have hp (p) (h : p∈m.primeFactors) : (∑ g∈m.divisors,(g.factorization p:ℝ)/g)*log p≤
      2*mass m*(log p/p) := by
    have hr := Nat.prime_of_mem_primeFactors h
    have hh : (2:ℝ)≤p := by exact_mod_cast hr.two_le
    have hv := valuation (m:=m) hr
    have hu : mass m/(p-1:ℝ)≤2*mass m/p := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith only [mul_le_mul_of_nonneg_left hh hD]
    exact (mul_le_mul_of_nonneg_right (hv.trans hu) (log_nonneg_nat _)).trans_eq (by ring)
  have hn := factorial_log T hT m.primeFactors (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,hs p hp⟩)
  rw [logMass_eq m hm]
  have H := sum_le_sum hp
  rw [←mul_sum] at H
  nlinarith only [H,mul_le_mul_of_nonneg_left hn (show 0≤2*mass m by positivity)]

end
end Arxiv.«2501.03234».ThetaDivisorTriangle
#print axioms Arxiv.«2501.03234».ThetaDivisorTriangle.triangle
#print axioms Arxiv.«2501.03234».ThetaDivisorTriangle.smooth_log
