import FormalConjectures.GreensOpenProblems.«54»
import Green54SoftmaxPair

/-! A proof of the positive DeepMind statement of Talagrand's Gaussian convexity problem,
following Hua, Song and Tudose. -/

open Set MeasureTheory ProbabilityTheory
open Green54SoftmaxPair Green54GaussianTilts Green54FiniteLaws Green54ConvexTests
open scoped ENNReal Pointwise
namespace Green54Solved

/-- The Gaussian triple decomposition for finite atomic targets strictly below a
contracted standard Gaussian in convex order. -/
theorem finite_gaussian_triple (J : Finset ℕ) {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    FiniteTripleDecomposition (finiteGaussian J) ((finiteGaussian J).map (fun x => r • x)) := by
  apply finite_triple_of_softmax_pairs J hr hr'
  intro T _ w p m hp hparts i
  let : Nonempty T := ⟨i⟩
  exact coordinate_pair w p i (hp i) (m i) (hparts.2 i).2.1 (hparts.2 i).2.2.2.1 (hparts.2 i).2.2.2.2

/-- Compact targets dominated by the standard finite-dimensional Gaussian are sums
of three standard Gaussian marginals. -/
theorem compact_gaussian_triple : GaussianTripleDecomposition :=
  fun J _ => compact_of_finite_contractions _ (fun _ hr hr' => finite_gaussian_triple J hr hr')

/-- Six Minkowski summands suffice at input mass above five sixths. -/
theorem gaussian_six {K : Set (ℕ → ℝ)} (hK : IsCompact K)
    (hm : (5 / 6 : ℝ≥0∞) < Green54Projections.gaussian K) :
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (6 : ℕ) • K ∧
      (1 / 2 : ℝ≥0∞) ≤ Green54Projections.gaussian C :=
  Green54Symmetric.gaussian_six_of_triple compact_gaussian_triple hK hm

/-- For symmetric inputs the threshold drops to two thirds. -/
theorem gaussian_symmetric {K : Set (ℕ → ℝ)} (hK : IsCompact K) (hs : ∀ x ∈ K, -x ∈ K)
    (hm : (2 / 3 : ℝ≥0∞) < Green54Projections.gaussian K) :
    ∃ C : Set (ℕ → ℝ), IsCompact C ∧ Convex ℝ C ∧ C ⊆ (2 : ℝ) • (K + K + K) ∧
      (1 / 2 : ℝ≥0∞) ≤ Green54Projections.gaussian C :=
  Green54Symmetric.gaussian_symmetric_of_triple compact_gaussian_triple hK hs hm

/-- Talagrand's convexity problem in the positive form of the pinned DeepMind Green 54 declaration. -/
theorem green_54 : type_of% Green54.green_54 :=
  Green54Symmetric.green_54_of_triple compact_gaussian_triple

#print axioms finite_gaussian_triple

#print axioms compact_gaussian_triple
#print axioms gaussian_six
#print axioms gaussian_symmetric
#print axioms green_54
end Green54Solved
