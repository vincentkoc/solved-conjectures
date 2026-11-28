import Erdos478SieveProportions
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# A logarithmic estimate in the gap cutoff

The finite Euler product over primes through K bounds the reciprocal harmonic
sum. Combining it with the product distribution gives an explicit bound for
the proportion of primes with few witnessed gap lengths.
-/

namespace Erdos478.GapSieve
noncomputable section
open Finset Filter Topology GapDensity GapVariance

/-- All prime gap lengths at most K. -/
def through (K : ℕ) : Finset Nat.Primes := (Nat.primesLE K).subtype Nat.Prime

theorem mem_through {i : Nat.Primes} {K : ℕ} : i ∈ through K ↔ i.val ≤ K := by
  change (⟨i.val,i.property⟩ : {n : ℕ // n.Prime}) ∈ (Nat.primesLE K).subtype Nat.Prime ↔ _
  rw [Finset.mem_subtype,Nat.mem_primesLE]
  exact ⟨And.left,fun h => ⟨h,i.property⟩⟩

theorem euler_harmonic (K : ℕ) :
    (Real.log (K+1 : ℕ)) * (∏ i ∈ through K, (1-weight i)) ≤ 1 := by
  classical
  let f := fun n : ℕ => (n:ℝ)⁻¹
  have hf {p : ℕ} (hp : p.Prime) : 0 ≤ f p ∧ f p < 1 := by
    have h : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
    exact ⟨by dsimp [f]; positivity,inv_lt_one_of_one_lt₀ h⟩
  have hpow (p n : ℕ) : f (p^n) = (f p)^n := by simp [f]
  have hgeo {p : ℕ} (hp : p.Prime) : HasSum (fun n : ℕ => f (p^n)) (1-f p)⁻¹ := by
    simpa only [hpow] using hasSum_geometric_of_lt_one (hf hp).1 (hf hp).2
  have hu := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := f) (by simp [f]) (fun {m n} _ => by simp [f,mul_comm])
    (fun {p} hp => (hgeo hp).summable.norm) (K+1)
  let U := (Icc 1 K).attach
  let embed : (Icc 1 K : Finset ℕ) ↪ (K+1).smoothNumbers :=
    ⟨fun n => ⟨n.val,Nat.mem_smoothNumbers_of_lt (mem_Icc.mp n.property).1
      (Nat.lt_succ_of_le (mem_Icc.mp n.property).2)⟩,
      fun _ _ he => Subtype.ext (congrArg (fun x : (K+1).smoothNumbers => x.val) he)⟩
  have hle := sum_le_hasSum (U.map embed) (fun (n : (K+1).smoothNumbers) _ =>
    (show (0:ℝ) ≤ f n.val by dsimp [f]; positivity)) hu.2
  have hsum : (∑ n ∈ U.map embed, f n.val) = (harmonic K : ℝ) := by
    rw [sum_map]
    change (∑ n ∈ (Icc 1 K).attach, f n.val) = _
    simpa [f,harmonic_eq_sum_Icc] using sum_attach (Icc 1 K) f
  have hprod : (∏ p ∈ (K+1).primesBelow, ∑' n : ℕ, f (p^n)) =
      (∏ i ∈ through K, (1-weight i))⁻¹ := by
    rw [← prod_inv_distrib]
    symm
    apply prod_bij (fun i _ => i.val)
    · intro i hi; exact Nat.mem_primesLE.mpr ⟨mem_through.mp hi,i.property⟩
    · intro i _ j _ he; exact Subtype.ext he
    · intro p hp
      have h := Nat.mem_primesBelow.mp hp
      exact ⟨⟨p,h.2⟩,mem_through.mpr (by dsimp; omega),rfl⟩
    · intro i _
      simpa [weight,f] using (hgeo i.property).tsum_eq.symm
  rw [hsum,hprod] at hle
  have hpos : 0 < ∏ i ∈ through K, (1-weight i) := prod_pos fun i _ => by
    have h := (hf i.property).2
    simpa [weight,f] using sub_pos.mpr h
  apply (le_div_iff₀ hpos).mp
  simpa only [one_div] using (log_add_one_le_harmonic K).trans hle

private theorem weight_range (i : Nat.Primes) : 0 ≤ weight i ∧ weight i ≤ 1/2 := by
  have hi : (2:ℝ) ≤ i.val := by exact_mod_cast i.property.two_le
  constructor
  · unfold weight; positivity
  · exact one_div_le_one_div_of_le (by norm_num) hi

private theorem tail_markov (s : Finset Nat.Primes) (D : ℕ) :
    (1/2:ℝ)^D * eventMass weight s (fun t => t.card<D) ≤ ∏ i ∈ s, (1-weight i/2) := by
  classical
  let w := fun t : Finset Nat.Primes => pattern weight t (s \ t)
  have hw (t) : 0 ≤ w t := mul_nonneg (prod_nonneg (fun i _ => (weight_range i).1))
    (prod_nonneg (fun i _ => by have := (weight_range i).2; linarith))
  let F := s.powerset.filter (fun t => t.card<D)
  have he : eventMass weight s (fun t => t.card<D) = ∑ t ∈ F, w t := by
    unfold eventMass
    apply sum_congr _ (fun _ _ => rfl)
    ext t
    simp [F]
  rw [he,mul_sum]
  calc
    _ ≤ ∑ t ∈ F, (1/2:ℝ)^t.card * w t := by
      apply sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (mem_filter.mp ht).2.le) (hw t)
    _ ≤ ∑ t ∈ s.powerset, (1/2:ℝ)^t.card * w t := sum_le_sum_of_subset_of_nonneg
      (filter_subset ..) (fun t _ _ => mul_nonneg (by positivity) (hw t))
    _ = ∏ i ∈ s, ((1/2)*weight i + (1-weight i)) := by
      rw [prod_add]
      apply sum_congr rfl
      intro t _
      simp only [w,pattern,prod_mul_distrib,prod_const]
      ring
    _ = _ := prod_congr rfl (fun _ _ => by ring)

/-- The product-law lower tail obeys a uniform estimate in the gap cutoff
K and the threshold D. The prime-average limit still takes K and D fixed. -/
theorem tail_log (K D : ℕ) :
    Real.log (K+1 : ℕ) * (eventMass weight (through K) (fun t => t.card<D))^3 ≤ (8:ℝ)^D := by
  classical
  let t := eventMass weight (through K) (fun t => t.card<D)
  let b := ∏ i ∈ through K, (1-weight i/2)
  have ht : 0 ≤ t := sum_nonneg fun u _ => mul_nonneg (prod_nonneg fun i _ => (weight_range i).1)
    (prod_nonneg fun i _ => by have := (weight_range i).2; linarith)
  have hm : (1/2:ℝ)^D*t ≤ b := tail_markov _ _
  have hb : b^3 ≤ ∏ i ∈ through K, (1-weight i) := by
    rw [show b^3 = ∏ i ∈ through K, (1-weight i/2)^3 by simp [b,Finset.prod_pow]]
    apply prod_le_prod (fun i _ => pow_nonneg (by have := (weight_range i).2; linarith) _)
    intro i _
    obtain ⟨h0,h1⟩ := weight_range i
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1),mul_nonneg h0 (sq_nonneg (weight i))]
  have hl : 0 ≤ Real.log (K+1 : ℕ) := Real.log_natCast_nonneg _
  have h := (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (mul_nonneg (by positivity) ht) hm 3).trans hb) hl).trans (euler_harmonic K)
  change _ * t^3 ≤ _
  rw [mul_pow,← pow_mul,Nat.mul_comm D 3,pow_mul,show (1/2:ℝ)^3 = 8⁻¹ by norm_num,inv_pow] at h
  have hn : 0 < (8:ℝ)^D := by positivity
  apply (div_le_one hn).mp
  rw [div_eq_mul_inv]
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

/-- A concrete gap horizon for the lower tail. For fixed K,D,η satisfying
the displayed inequality, all sufficiently large prime samples have fewer
than an η fraction with fewer than D distinct witnessed lengths through K. -/
theorem cutoff_of_pit (h : DegreeOnePrimeIdealTheorem) (K D : ℕ) {η : ℝ}
    (hη : 0 < η) (hK : (8:ℝ)^D < Real.log (K+1 : ℕ) * η^3) :
    ∀ᶠ X in atTop, fraction X (fun p => (hits (through K) p).card<D) < η := by
  let E := fun t : Finset Nat.Primes => t.card<D
  have hsmall : eventMass weight (through K) E < η := by
    by_contra! hh
    have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hh 3)
      (Real.log_natCast_nonneg (K+1))
    exact (not_lt_of_ge (hpow.trans (tail_log K D))) hK
  have hdec : Antitone E := fun _ _ hab hb => (card_le_card hab).trans_lt hb
  have hl := upper_of_pit h (through K) E hdec (sub_pos.mpr hsmall)
  simpa [E] using hl

theorem all_hits_of_pit (h : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, (∏ i ∈ s, weight i)-ε < fraction X (fun p => s ⊆ hits s p) := by
  have hE : Monotone (fun t : Finset Nat.Primes => s ⊆ t) := fun _ _ hab ha => ha.trans hab
  simpa only [all_mass] using lower_of_pit h s _ hE hε

theorem no_hits_of_pit (h : DegreeOnePrimeIdealTheorem) (s : Finset Nat.Primes)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, fraction X (fun p => hits s p = ∅) < (∏ i ∈ s, (1-weight i))+ε := by
  have hE : Antitone (fun t : Finset Nat.Primes => t = ∅) := fun _ _ hab hb =>
    Subset.antisymm (hb ▸ hab) (empty_subset _)
  simpa only [empty_mass] using upper_of_pit h s _ hE hε

theorem no_hits_log_of_pit (h : DegreeOnePrimeIdealTheorem) {K : ℕ} (hK : 0 < K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, fraction X (fun p => hits (through K) p = ∅) < (Real.log (K+1 : ℕ))⁻¹ + ε := by
  have hpos : 0 < Real.log (K+1 : ℕ) := Real.log_pos (by exact_mod_cast (show 1<K+1 by omega))
  have bound : (∏ i ∈ through K, (1-weight i)) ≤ (Real.log (K+1 : ℕ))⁻¹ := by
    rw [← one_div,le_div_iff₀ hpos,mul_comm]
    exact euler_harmonic K
  filter_upwards [no_hits_of_pit h (through K) hε] with X hx
  exact hx.trans_le (add_le_add_left bound _)

#print axioms cutoff_of_pit
#print axioms all_hits_of_pit
#print axioms no_hits_of_pit
#print axioms no_hits_log_of_pit
#print axioms tail_log
#print axioms mem_through
#print axioms euler_harmonic

end
end Erdos478.GapSieve
