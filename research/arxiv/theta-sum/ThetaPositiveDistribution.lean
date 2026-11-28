import ThetaWorstPrimeClasses

/-! Transfer of ordinary prime distribution errors to theta-selected primes,
uniformly over independently chosen residue classes, cutoffs and main terms. -/
namespace Arxiv.«2501.03234».ThetaPositiveDistribution
open Filter Finset Real ThetaPrimeDensity ThetaWorstPrimeClasses ThetaOccupancyScales
open scoped Classical
noncomputable section

def discrepancy (P : ℕ → Prop) (Q : ℕ) (y b : ℕ → ℕ) (main : ℕ → ℝ) :=
  ∑ q∈Icc 1 Q,|(count (primeSet P (y q)) q (b q):ℝ)-main q|

theorem class_change (P : ℕ → Prop) {X y q b : ℕ} (hy : y≤X) (hb : b<q) (M : ℝ) :
    abs (|(count (primeSet (fun p => ¬P p) y) q b:ℝ)-M|-|(count (primeSet (fun _ => True) y) q b:ℝ)-M|) ≤ worst (primeSet P X) q := by
  classical
  let A := (Nat.primesLE y).filter (fun p => p%q=b)
  let G := A.filter (fun p => ¬P p)
  let E := A.filter P
  have hg : count (primeSet (fun p => ¬P p) y) q b=G.card := by
    unfold count;congr 1;ext p;simp [primeSet,G,A,and_left_comm,and_comm]
  have ha : count (primeSet (fun _ => True) y) q b=A.card := by simp [count,primeSet,A]
  have he : E ⊆ (primeSet P X).filter (fun p => p%q=b) := by
    intro p hp
    obtain ⟨hp',hP⟩ := mem_filter.mp hp
    obtain ⟨hh,hres⟩ := mem_filter.mp hp'
    obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hh
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hle.trans hy,hprime⟩,hP⟩,hres⟩
  have hsum : E.card+G.card=A.card := card_filter_add_card_filter_not ..
  rw [hg,ha]
  have hle : E.card ≤ worst (primeSet P X) q := (card_le_card he).trans
    (le_sup (f:=count (primeSet P X) q) (mem_range.mpr hb))
  calc _ ≤ |((G.card:ℝ)-M)-((A.card:ℝ)-M)| := abs_abs_sub_abs_le_abs_sub ..
       _ = (E.card:ℝ) := by
         rw [show ((G.card:ℝ)-M)-((A.card:ℝ)-M) = -(E.card:ℝ) by rw [←hsum,Nat.cast_add];ring,
           abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
       _ ≤ _ := Nat.cast_le.mpr hle

theorem comparison (P : ℕ → Prop) (X Q : ℕ) (y b : ℕ → ℕ) (M : ℕ → ℝ)
    (hy : ∀ q∈Icc 1 Q,y q≤X) (hb : ∀ q∈Icc 1 Q,b q<q) :
    |discrepancy (fun p => ¬P p) Q y b M-discrepancy (fun _ => True) Q y b M| ≤ total (primeSet P X) Q := by
  classical
  unfold discrepancy total
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q hq => ?_))
  exact class_change P (hy q hq) (hb q hq) (M q)

/-- Changing the prime sample to the primes with S(p)>kp preserves the
ordinary maximal-progression discrepancy up to the stated additive error. -/
theorem slope (k : ℕ) : ∀ᶠ X : ℕ in atTop,∀ Q : ℕ,(Q:ℝ)^2 ≤ X*exp (saving X) →
    ∀ y b : ℕ → ℕ, (∀ q∈Icc 1 Q,y q≤X) → (∀ q∈Icc 1 Q,b q<q) → ∀ M : ℕ → ℝ,
    |discrepancy (fun p => (k:ℤ)*p<S p) Q y b M-discrepancy (fun _ => True) Q y b M| ≤
      X.primeCounting*exp (-(2*saving X)) := by
  filter_upwards [ThetaWorstPrimeClasses.slope k] with X h Q hQ y b hy hb M
  simpa only [not_le] using (comparison (fun p => S p≤(k:ℤ)*p) X Q y b M hy hb).trans (h Q hQ)

#print axioms comparison
#print axioms slope
end
end Arxiv.«2501.03234».ThetaPositiveDistribution
