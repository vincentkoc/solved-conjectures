import ThetaCompatibleCapture
import ThetaRoughInverseClasses

/-! Weighted cost of all divisor rows sharing a factor with a rough inverse. -/
namespace Arxiv.«2501.03234».ThetaRoughDivisorBudget
open Real Finset ThetaDivisorLogMean ThetaCompatibleCapture
noncomputable section

/-- The reciprocal mass of prime factors beyond P is at most log a/(P log P). -/
theorem reciprocal {a P : ℕ} (ha : 0<a) (hP : 1<P) (hrough : ∀ p∈a.primeFactors,P<p) :
    ∑ p∈a.primeFactors,(p:ℝ)⁻¹ ≤ log a/(P*log P) := by
  have hp : 0<(P:ℝ) := by exact_mod_cast (by omega : 0<P)
  have hlog := log_pos (by exact_mod_cast hP : (1:ℝ)<P)
  have hprod : P^a.primeFactors.card ≤ a := calc
    _ = ∏ _p∈a.primeFactors,P := by simp
    _ ≤ ∏ p∈a.primeFactors,p := prod_le_prod' (fun p h => (hrough p h).le)
    _ ≤ a := Nat.le_of_dvd ha (Nat.prod_primeFactors_dvd _)
  have hc := log_le_log (pow_pos hp a.primeFactors.card) (by exact_mod_cast hprod :
    (P:ℝ)^a.primeFactors.card≤a)
  rw [log_pow] at hc
  calc _ ≤ ∑ _p∈a.primeFactors,(P:ℝ)⁻¹ := by
             apply sum_le_sum; intro p h
             exact inv_anti₀ hp (by exact_mod_cast (hrough p h).le)
       _ = (a.primeFactors.card:ℝ)/P := by simp [div_eq_mul_inv]
       _ ≤ _ := by rw [div_le_div_iff₀ hp (mul_pos hp hlog)]; nlinarith only [mul_le_mul_of_nonneg_left hc hp.le]

/-- A union bound over prime divisors, weighted by the logarithmic row envelope. -/
theorem common_factor {a : ℕ} (ha : 0<a) (m : ℕ) :
    (∑ d∈m.divisors.filter (fun d => ¬d.Coprime a),(1+log d)/d) ≤
      (logMass m+log a*mass m)*∑ p∈a.primeFactors,(p:ℝ)⁻¹ := by
  classical
  let w (d : ℕ) := (1+log d)/d
  have hw (d : ℕ) : 0≤w d := div_nonneg (by linarith [log_nonneg_nat d]) (Nat.cast_nonneg _)
  have pt (d : ℕ) : (if ¬d.Coprime a then w d else 0) ≤
      ∑ p∈a.primeFactors,if p∣d then w d else 0 := by
    by_cases hc : ¬d.Coprime a
    · rw [if_pos hc]
      obtain ⟨p,hp,hd,hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      have hh := single_le_sum (s:=a.primeFactors) (f:=fun p => if p∣d then w d else 0)
        (fun p _ => by split_ifs <;> simp [hw]) (Nat.mem_primeFactors.mpr ⟨hp,hpa,ha.ne'⟩)
      simpa only [if_pos hd] using hh
    · rw [if_neg hc]; exact sum_nonneg (fun p _ => by split_ifs <;> simp [hw])
  have H := sum_le_sum (s:=m.divisors) (fun d _ => pt d)
  rw [←sum_filter,sum_comm] at H
  refine H.trans ?_
  rw [mul_sum]
  apply sum_le_sum; intro p hp
  rw [←sum_filter]
  obtain ⟨hpr,hpa,_⟩ := Nat.mem_primeFactors.mp hp
  apply (log_mass_multiple (m:=m) hpr.pos).trans
  rw [←div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact add_le_add_right (mul_le_mul_of_nonneg_right
    (log_le_log (by exact_mod_cast hpr.pos) (by exact_mod_cast Nat.le_of_dvd ha hpa))
    (mass_nonneg _)) _

/-- The captured mass survives after paying logarithmically for the inverse
and proportionally to the reciprocal mass of its exceptional prime factors. -/
theorem lower {a n m : ℕ} (ha : Odd a) (hn : n.Coprime m)
    (he : ∀ d, d∣m → d.Coprime a → (n:ZMod d)⁻¹=(a:ZMod d))
    (A : ℕ → ℝ) (K : ℕ → ℕ) {Z : ℝ} (hZ : 1≤Z)
    (hA : ∀ d∈m.divisors,1≤A d ∧ A d≤Z) (hK : ∀ d∈m.divisors,1<d → 2*d≤K d) :
    (mass m)^2/16-Z*(2*log (2*(a:ℝ))+5)*mass m-
      (1+3*Z)*((logMass m+log a*mass m)*∑ p∈a.primeFactors,(p:ℝ)⁻¹)
      ≤ ∑ d∈m.divisors,value A K n d := by
  have ha' : (1:ℝ)≤a := by exact_mod_cast ha.pos
  have hL : 1≤2*log (2*(a:ℝ))+5 := by linarith [log_nonneg (show 1≤2*(a:ℝ) by linarith)]
  have H := capture_bound (n:=n) (m:=m) (fun d => ¬d.Coprime a) hL A K hZ hA
    (fun d hd h ho had => ThetaInverseResidueRows.captured_log ha h ho (hK d hd h)
      (hn.coprime_dvd_right (Nat.mem_divisors.mp hd).1) (he d (Nat.mem_divisors.mp hd).1 (by simpa using had)))
  have hh := mul_le_mul_of_nonneg_left (common_factor ha.pos m) (show 0≤1+3*Z by linarith)
  linarith only [H,hh]

#print axioms lower
#print axioms reciprocal
#print axioms common_factor
end
end Arxiv.«2501.03234».ThetaRoughDivisorBudget
