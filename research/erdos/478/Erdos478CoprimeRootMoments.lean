import Erdos478CoprimeRootFields
import Erdos478PrimeOrderMaps
import Erdos478IdealPrimeWeights

/-!
# Prime-weighted moments of roots of coprime-degree polynomials

Weight a rational prime by log(p)/p. The first Mertens theorem for degree-one
prime ideals computes the joint root moment for two irreducibles of coprime
degrees. No estimate for the ordinary prime counting function is used here.
-/

namespace Erdos478.RootMoments
noncomputable section
open Polynomial Finset Filter Topology RootPairs MeanDeficit IdealMertens

def mean (X : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun a := (∑ p ∈ Nat.primesLE X, a p * Real.log p / p) / Real.log X
  map_add' a b := by simp [Pi.add_apply,add_mul,add_div,sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [mul_assoc,mul_div_assoc]
    rw [← mul_sum,mul_div_assoc]

def roots (f : ℤ[X]) (p : ℕ) : ℝ := Nat.card (solutions f (ZMod p))

theorem mean_mono (X : ℕ) {a b : ℕ → ℝ} (h : ∀ p, p.Prime → a p ≤ b p) :
    mean X a ≤ mean X b := by
  have hx : 0 ≤ Real.log X := Real.log_natCast_nonneg _
  exact div_le_div_of_nonneg_right (sum_le_sum (fun p hp =>
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (h p (Nat.mem_primesLE.mp hp).2)
      (Real.log_natCast_nonneg _)) (Nat.cast_nonneg _))) hx

/-- A change at finitely many primes costs a constant divided by log X. -/
theorem negligible {a b : ℕ → ℝ} (B : ℕ) (h : ∀ p > B, p.Prime → a p = b p) :
    Tendsto (fun X => mean X a - mean X b) atTop (𝓝 0) := by
  let t := fun p : ℕ => (a p-b p)*Real.log p/p
  have eq : ∀ᶠ X : ℕ in atTop, mean X a - mean X b = (∑ p ∈ Nat.primesLE B, t p) / Real.log X := by
    filter_upwards [eventually_ge_atTop B] with X hX
    rw [← map_sub]
    change (∑ p ∈ Nat.primesLE X, t p)/Real.log X = _
    congr 1
    symm
    apply sum_subset
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hX,(Nat.mem_primesLE.mp hp).2⟩
    · intro p hp hnot
      have hp' := Nat.mem_primesLE.mp hp
      have hB : B < p := lt_of_not_ge fun hle => hnot (Nat.mem_primesLE.mpr ⟨hle,hp'.2⟩)
      simp [t,h p hB hp'.2]
  exact (tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).congr' (eq.mono fun _ h => h.symm)

/-- A positive averaging operator for which finite changes disappear and
the degree-one prime ideals in each number field have limiting mean one. -/
structure PrimeAverage where
  avg : ℕ → (ℕ → ℝ) →ₗ[ℝ] ℝ
  mono : ∀ X {a b : ℕ → ℝ}, (∀ p, p.Prime → a p ≤ b p) → avg X a ≤ avg X b
  finite_change : ∀ {a b : ℕ → ℝ} (B : ℕ), (∀ p > B, p.Prime → a p = b p) →
    Tendsto (fun X => avg X a - avg X b) atTop (𝓝 0)
  ideal_mean : ∀ (K : Type) [Field K] [NumberField K],
    Tendsto (fun X => avg X (fun p => (linearCount K p : ℝ))) atTop (𝓝 1)

def mertensAverage : PrimeAverage where
  avg := mean
  mono := mean_mono
  finite_change := negligible
  ideal_mean K _ _ := degree_one_mertens K

/-- The joint root moment is one for irreducible polynomials of coprime degrees. -/
theorem joint_mean (A : PrimeAverage) (f g : ℤ[X]) (hf : f.Monic) (hg : g.Monic)
    (hi : Irreducible (f.map (algebraMap ℤ ℚ))) (hj : Irreducible (g.map (algebraMap ℤ ℚ)))
    (hc : g.natDegree.Coprime f.natDegree) :
    Tendsto (fun X => A.avg X (roots f * roots g)) atTop (𝓝 1) := by
  obtain ⟨K,_,_,j,hj',hr⟩ := exists_full_order f g hf hg hi hj hc
  obtain ⟨B,hB⟩ := order_maps_count K j hj' hr
  have he := A.finite_change (a := roots f * roots g) (b := fun p => (linearCount K p : ℝ)) B (by
    intro p hp hprime
    obtain h := hB p hp hprime
    change (Nat.card (solutions f (ZMod p)) : ℝ) * Nat.card (solutions g (ZMod p)) = _
    rw [← Nat.cast_mul,← Nat.card_prod,Nat.card_congr (equiv f g (ZMod p)),h])
  have hfield : Tendsto (fun X => A.avg X (fun p => (linearCount K p : ℝ))) atTop (𝓝 1) :=
    A.ideal_mean K
  simpa only [sub_add_cancel,zero_add] using he.add hfield

private theorem roots_X : roots X = (1 : ℕ → ℝ) := by
  funext p
  have eq : solutions X (ZMod p) ≃ Unit :=
    ⟨fun _ => (),fun _ => ⟨0,by simp⟩,fun ⟨x,hx⟩ => Subtype.ext (by simpa using hx.symm),
      fun _ => rfl⟩
  change (Nat.card (solutions X (ZMod p)) : ℝ) = 1
  rw [Nat.card_congr eq]
  simp

theorem first_mean (A : PrimeAverage) (f : ℤ[X]) (hf : f.Monic) (hi : Irreducible (f.map (algebraMap ℤ ℚ))) :
    Tendsto (fun X => A.avg X (roots f)) atTop (𝓝 1) := by
  simpa [roots_X] using joint_mean A f X hf monic_X hi (by simp [irreducible_X]) (by simp)

theorem constant_mean (A : PrimeAverage) : Tendsto (fun X => A.avg X (1 : ℕ → ℝ)) atTop (𝓝 1) := by
  simpa only [roots_X] using first_mean A X monic_X (by simp [irreducible_X])

#print axioms joint_mean
#print axioms first_mean

end
end Erdos478.RootMoments
