import ThetaWorstPrimeClasses

/-! Almost every modulus simultaneously preserves every prime-rich class. -/
namespace Arxiv.«2501.03234».ThetaPrimeRichClasses
open Filter Finset Real ThetaPrimeDensity ThetaWorstPrimeClasses ThetaOccupancyScales
noncomputable section

def excluded (E : Finset ℕ) (X Q : ℕ) :=
  (Icc 1 Q).filter (fun q => (X.primeCounting:ℝ)*exp (-(saving X)) ≤ Q*(worst E q:ℝ))

private theorem markov {E : Finset ℕ} {X Q : ℕ} (hM : 0<(X.primeCounting:ℝ))
    (h : total E Q ≤ X.primeCounting*exp (-(2*saving X))) :
    ((excluded E X Q).card:ℝ) ≤ Q*exp (-(saving X)) := by
  let M := (X.primeCounting:ℝ)
  let s := saving X
  let D := excluded E X Q
  have hp : 0<M*exp (-s) := mul_pos hM (exp_pos _)
  apply (mul_le_mul_iff_left₀ hp).mp
  calc _ = ∑ _q∈D,M*exp (-s) := by simp [D]
       _ ≤ ∑ q∈D,(Q:ℝ)*(worst E q) := sum_le_sum (fun q hq => (mem_filter.mp hq).2)
       _ ≤ ∑ q∈Icc 1 Q,(Q:ℝ)*(worst E q) :=
           sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => by positivity)
       _ = (Q:ℝ)*total E Q := by rw [total,mul_sum]
       _ ≤ (Q:ℝ)*(M*exp (-(2*s))) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
       _ = (Q:ℝ)*exp (-s)*(M*exp (-s)) := by rw [show -(2*s) = -s+ -s by ring,exp_add];ring

/-- For every non-excluded modulus, at most an exponentially small fraction
of primes in every class containing at least π(X)/Q ordinary primes can fail
the fixed original slope. The excluded set is independent of the class. -/
theorem slope (k : ℕ) : ∀ᶠ X : ℕ in atTop,∀ Q : ℕ,0<Q → (Q:ℝ)^2 ≤ X*exp (saving X) →
    ∃ D ⊆ Icc 1 Q,(D.card:ℝ) ≤ Q*exp (-(saving X)) ∧
    ∀ q∈Icc 1 Q,q∉D → ∀ b<q,
      (X.primeCounting:ℝ) ≤ Q*(count (Nat.primesLE X) q b:ℝ) →
      (count (primeSet (fun p => S p≤(k:ℤ)*p) X) q b:ℝ) <
        (count (Nat.primesLE X) q b:ℝ)*exp (-(saving X)) := by
  filter_upwards [ThetaWorstPrimeClasses.slope k,eventually_ge_atTop 2] with X hx hX Q hQ hfit
  let E := primeSet (fun p => S p≤(k:ℤ)*p) X
  let D := excluded E X Q
  have hM : 0<(X.primeCounting:ℝ) := by
    rw [←Nat.primesLE_card_eq_primeCounting];exact_mod_cast card_pos.mpr ⟨2,Nat.mem_primesLE.mpr ⟨hX,Nat.prime_two⟩⟩
  refine ⟨D,filter_subset _ _,markov hM (hx Q hfit),?_⟩
  intro q hq hnot b hb hrich
  have hh : (Q:ℝ)*(worst E q) < X.primeCounting*exp (-(saving X)) := by
    by_contra! hn
    exact hnot (mem_filter.mpr ⟨hq,hn⟩)
  have h₁ := Nat.cast_le (α:=ℝ).mpr (le_sup (s:=range q) (f:=count E q) (mem_range.mpr hb))
  apply (mul_lt_mul_iff_right₀ (Nat.cast_pos.mpr hQ : 0<(Q:ℝ))).mp
  calc _ ≤ (Q:ℝ)*(worst E q) := mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)
       _ < _ := hh
       _ ≤ ((Q:ℝ)*(count (Nat.primesLE X) q b:ℝ))*exp (-(saving X)) := mul_le_mul_of_nonneg_right hrich (exp_pos _).le
       _ = _ := by ring

#print axioms slope
end
end Arxiv.«2501.03234».ThetaPrimeRichClasses
