import Erdos478RootlessPrimeGaps
import Erdos478ProportionalEndpointLaw

/-!
# Proportional intervals with the binary Frobenius gap classes

The admissible prime lengths now occupy two of the six reduced classes
modulo seven. The conditional analytic statement makes the progression
and degree-one prime ideal inputs explicit.
-/

namespace Erdos478.FrobeniusBands
open Filter Finset RootMoments GapVariance BinaryGap BandWeights GapDensity GapSieve GapBands Proportional
open scoped Topology Classical
noncomputable section

def family (K H : ℕ) : Finset Nat.Primes := (lengths broad K H).subtype Nat.Prime

theorem family_mem {K H : ℕ} {l : Nat.Primes} : l∈family K H ↔ K<l.val ∧ l.val≤H ∧ broad l.val := by
  apply (mem_subtype (a:=⟨l.val,l.property⟩) (p:=Nat.Prime) (s:=lengths broad K H)).trans
  simp [lengths,l.property,and_assoc]

theorem family_card (K H : ℕ) : (family K H).card=(lengths broad K H).card := by
  change ((lengths broad K H).subtype Nat.Prime).card=_
  rw [card_subtype,filter_eq_self.mpr (fun _ hi => (mem_filter.mp hi).2.2)]

theorem broad_square_mean (A : PrimeAverage) (l : Nat.Primes) (h : broad l.val) (hl : 3<l.val) :
    secondMomentTwo A l :=
  square_mean_of_pair_conjugacy A l (broad_root_pair_conjugate l.property h hl)

theorem broad_endpoint_variance (A : PrimeAverage) {K H : ℕ} (hK : 3≤K) :
    Tendsto (fun X => A.avg X (fun p => ((joined (family K H) p).card-((family K H).card:ℝ))^2))
      atTop (𝓝 ((family K H).card:ℝ)) := by
  apply endpoint_variance_of_moments
  intro l hl
  obtain ⟨hk,_,hb⟩ := family_mem.mp hl
  exact broad_square_mean A l hb (by omega)

def good (K H : ℕ) := family_good K (family K H)

/-- The broad binary family concentrates about (L−1)/3 throughout the
tail of proportional windows, in the iterated prime-count quantifiers. -/
theorem rate_of_inputs (pit : DegreeOnePrimeIdealTheorem) (mass : countingInput broad (1/3))
    {H : ℕ → ℕ} {L η A : ℝ} (hL : 1<L) (h : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hη : 0<η) (hA : (L-1)/3/η^2<A) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, 1-A*Proportional.scale K<fraction X (good K (H K) ((L-1)/3) η) := by
  apply family_rate pit (fun K => family K (H K)) _ _ hη hA
  · rw [show (L-1)/3=1/3*(L-1) by ring]
    simpa only [family_card,Proportional.scale,mul_div_assoc] using length_asymptotic mass hL h
  · filter_upwards [eventually_ge_atTop 3] with K hK
    intro l hl
    obtain ⟨hk,_,hb⟩ := family_mem.mp hl
    exact broad_square_mean _ l hb (by omega)

#print axioms family
#print axioms family_card
#print axioms family_mem
#print axioms broad_square_mean
#print axioms broad_endpoint_variance
#print axioms good
#print axioms rate_of_inputs
end
end Erdos478.FrobeniusBands
