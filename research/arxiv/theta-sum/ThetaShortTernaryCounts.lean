import ThetaTernaryPacking
import ThetaShortPrimeInterval

/-! Uniform changes to representation counts at a fixed target in a short prime interval. -/
namespace Arxiv.«2501.03234».ThetaShortTernaryCounts
open Filter Finset Real ThetaTernaryDeletion ThetaShortPrimeInterval ThetaStrongDeviation
noncomputable section

def allPrimes (X H : ℕ) := primes X H (fun _ => True)

private theorem subtract (X H : ℕ) (P : ℕ → Prop) :
    allPrimes X H \ primes X H P = primes X H (fun p => ¬P p) := by
  ext p
  constructor
  · intro hp
    obtain ⟨ha,he⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hw,hpr,_⟩ := mem_primes.mp ha
    exact mem_primes.mpr ⟨hw,hpr,fun h => he (mem_primes.mpr ⟨hw,hpr,h⟩)⟩
  · intro hp
    obtain ⟨hw,hpr,hP⟩ := mem_primes.mp hp
    exact Finset.mem_sdiff.mpr ⟨mem_primes.mpr ⟨hw,hpr,trivial⟩,fun h => hP (mem_primes.mp h).2.2⟩

theorem card_all (X H : ℕ) : (allPrimes X H).card≤H := by
  have h : allPrimes X H ⊆ Ioc X (X+H) := fun _ hh => (mem_primes.mp hh).1
  simpa using card_le_card h

theorem transfer (X H n : ℕ) (P : ℕ → Prop) {e : ℝ}
    (he : ((primes X H P).card:ℝ)≤e) :
    let A := allPrimes X H
    let G := primes X H (fun p => ¬P p)
    ((triples A A A n).card:ℝ)≤(distinctTriples G n).card+3*(e+1)*H := by
  intro A G
  have h := distinct_deletion A (primes X H P) n
  change (triples A A A n).card ≤ (distinctTriples (allPrimes X H \ primes X H P) n).card+_ at h
  rw [subtract] at h
  have h' : ((triples A A A n).card:ℝ)≤(distinctTriples G n).card+
      3*(((primes X H P).card:ℝ)+1)*A.card := by exact_mod_cast h
  have h₁ : 3*(((primes X H P).card:ℝ)+1) ≤ 3*(e+1) := by linarith only [he]
  have h₂ : (A.card:ℝ)≤H := Nat.cast_le.mpr (card_all X H)
  have h₃ : 0≤e := (Nat.cast_nonneg _).trans he
  exact h'.trans (add_le_add (le_refl _) (mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (by positivity)))

/-- The error is uniform in every target sum, even when the ordinary triple count is zero. -/
theorem original {ε : ℝ} (hε : 0<ε) : ∀ᶠ X : ℕ in atTop,∀ H : ℕ,
    (X:ℝ)^(3/4:ℝ)*exp (rate X/512)≤H → H≤X → ∀ n : ℕ,
    let A := allPrimes X H
    let G := primes X H (fun p => |(S p:ℝ)-p*log p/2|<ε*p*log p)
    ((triples A A A n).card:ℝ) ≤ (distinctTriples G n).card+
      3*((H:ℝ)/log X*exp (-rate X/2048)+1)*H := by
  filter_upwards [ThetaShortPrimeInterval.original hε] with X hx H hH hX n
  simpa only [not_le] using transfer X H n _ (hx H hH hX)

theorem slope {c : ℝ} (hc : c<1/2) : ∀ᶠ X : ℕ in atTop,∀ H : ℕ,
    (X:ℝ)^(3/4:ℝ)*exp (rate X/512)≤H → H≤X → ∀ n : ℕ,
    let A := allPrimes X H
    let G := primes X H (fun p => c*p*log p<(S p:ℝ))
    ((triples A A A n).card:ℝ) ≤ (distinctTriples G n).card+
      3*((H:ℝ)/log X*exp (-rate X/2048)+1)*H := by
  filter_upwards [ThetaShortPrimeInterval.lower hc] with X hx H hH hX n
  simpa only [not_le] using transfer X H n _ (hx H hH hX)

#print axioms transfer
#print axioms original
#print axioms slope
end
end Arxiv.«2501.03234».ThetaShortTernaryCounts
