import Erdos478CubicGapSecondMoment
import Erdos478DistinctBandEndpoints
import Erdos478SieveProportions

/-! # Concentration of distinct repeated factorial endpoints -/

namespace Erdos478.BinaryGap
open Filter Topology Finset RootMoments GapVariance GapBands GapSieve GapDensity
noncomputable section

private theorem first (A : PrimeAverage) (i : Nat.Primes) :
    Tendsto (fun X => A.avg X (observation i)) atTop (𝓝 1) :=
  first_mean A _ (gap_degree i).monic (gap_irr i)

private theorem distinct_mean (A : PrimeAverage) {i j : Nat.Primes} (h : i≠j) :
    Tendsto (fun X => A.avg X (observation i*observation j)) atTop (𝓝 1) := by
  apply joint_mean A _ _ (gap_degree i).monic (gap_degree j).monic (gap_irr i) (gap_irr j)
  rw [(gap_degree i).natDegree_eq,(gap_degree j).natDegree_eq]
  exact (Nat.coprime_primes j.property i.property).mpr (fun he => h (Subtype.ext he.symm))

private def covariance (i j : Nat.Primes) : ℕ → ℝ :=
  observation i*observation j-observation i-observation j+1

def secondMomentTwo (A : PrimeAverage) (i : Nat.Primes) :=
  Tendsto (fun X => A.avg X (observation i*observation i)) atTop (𝓝 2)

private theorem covariance_mean (A : PrimeAverage) (i j : Nat.Primes) (hi : secondMomentTwo A i) :
    Tendsto (fun X => A.avg X (covariance i j)) atTop (𝓝 (if i=j then 1 else 0)) := by
  simp only [covariance,map_add,map_sub]
  by_cases he : i=j
  · subst j
    have h := ((hi.sub (first A i)).sub (first A i)).add (constant_mean A)
    norm_num at h ⊢
    exact h
  · simpa [he] using (((distinct_mean A he).sub (first A i)).sub (first A j)).add (constant_mean A)

theorem endpoint_variance_of_moments (A : PrimeAverage) (s : Finset Nat.Primes)
    (hs : ∀ i∈s, secondMomentTwo A i) :
    Tendsto (fun X => A.avg X (fun p => ((joined s p).card-(s.card:ℝ))^2)) atTop (𝓝 (s.card:ℝ)) := by
  classical
  let C : ℕ → ℝ := ∑ i ∈ s, ∑ j ∈ s, covariance i j
  have lim : Tendsto (fun X => A.avg X C) atTop (𝓝 (s.card:ℝ)) := by
    simp only [C,map_sum]
    simpa using tendsto_finsetSum s (fun i hi => tendsto_finsetSum s (fun j _ => covariance_mean A i j (hs i hi)))
  obtain ⟨B,he⟩ := eventual_endpoint_sum s
  apply CollisionLaw.mean_of_change A B _ lim
  intro p hB hp
  rw [he p hB hp]
  have sum : ∑ i ∈ s, (observation i p-1)=∑ i ∈ s, observation i p-(s.card:ℝ) := by simp [sum_sub_distrib]
  rw [← sum,pow_two,sum_mul_sum]
  simp only [C,Finset.sum_apply,covariance,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.one_apply]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem endpoint_variance (A : PrimeAverage) (s : Finset Nat.Primes)
    (hs : ∀ i∈s, selected i.val) :
    Tendsto (fun X => A.avg X (fun p => ((joined s p).card-(s.card:ℝ))^2)) atTop (𝓝 (s.card:ℝ)) :=
  endpoint_variance_of_moments A s (fun i hi => square_mean A i (hs i hi))

/-- Two-sided Chebyshev bound on the natural proportion of observation
primes for a fixed selected family. -/
theorem finite_concentration_of_moments (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    (hs : ∀ i∈s, secondMomentTwo (countingAverage pit) i) {t ε : ℝ} (ht : 0<t) (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, fraction X (fun p => t≤|((joined s p).card:ℝ)-s.card|) <
      (s.card:ℝ)/t^2+ε := by
  classical
  let A := countingAverage pit
  let P (p : ℕ) := t≤|((joined s p).card:ℝ)-s.card|
  let ind (p : ℕ) : ℝ := if P p then 1 else 0
  have eq (X : ℕ) : A.avg X ind=fraction X P := by
    change (Nat.primeCounting X:ℝ)⁻¹*(∑ p ∈ Nat.primesLE X, if P p then 1 else 0)=_
    rw [fraction,← Nat.primesLE_card_eq_primeCounting,div_eq_inv_mul]
    congr 1
    rw [card_filter]
    push_cast
    rfl
  have tt : 0<t^2 := sq_pos_of_pos ht
  have H := (endpoint_variance_of_moments A s hs).eventually_lt_const
    (show (s.card:ℝ)<s.card+ε*t^2 by linarith only [mul_pos hε tt])
  filter_upwards [H] with X hX
  have b := A.mono X (a:=t^2 • ind) (b:=fun p => ((joined s p).card-(s.card:ℝ))^2) (fun p _ => by
    simp only [Pi.smul_apply,smul_eq_mul,ind]
    split_ifs with h
    · exact (mul_one _).le.trans ((pow_le_pow_left₀ ht.le h 2).trans_eq (sq_abs _))
    · simp [sq_nonneg])
  rw [map_smul,smul_eq_mul,eq] at b
  change fraction X P<_
  have hb : fraction X P<(s.card+ε*t^2)/t^2 := (lt_div_iff₀ tt).mpr (by linarith only [b,hX])
  simpa [add_div,tt.ne'] using hb

theorem finite_concentration (pit : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    (hs : ∀ i∈s, selected i.val) {t ε : ℝ} (ht : 0<t) (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop, fraction X (fun p => t≤|((joined s p).card:ℝ)-s.card|) <
      (s.card:ℝ)/t^2+ε :=
  finite_concentration_of_moments pit s (fun i hi => square_mean _ i (hs i hi)) ht hε

#print axioms secondMomentTwo
#print axioms endpoint_variance_of_moments
#print axioms finite_concentration_of_moments
#print axioms endpoint_variance
#print axioms finite_concentration
end
end Erdos478.BinaryGap
