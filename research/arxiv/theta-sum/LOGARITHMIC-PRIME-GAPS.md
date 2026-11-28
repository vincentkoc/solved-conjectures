# Same-tail excess at logarithmic prime gaps

Write \(R(p)=S(p)/p-\tfrac12\log p\), using the signed double floor sum in the pinned source, and let \(B\) be its all-prime residual mean. Fix a reduced residue \(r\bmod m\) and **any** threshold \(t\ge0\). Color a prime upper when \(R(p)>B+t\) and lower when \(R(p)<B-t\). Count ordered pairs \((p,p+h)\) of these primes in the class with \(p+h\le X\). Let \(N_s\) count agreement of the two colors and \(N_o\) count disagreement. There are \(A,c>0\) such that for every sufficiently large \(X\) some positive multiple \(h\) of \(m\) satisfies
\[
 h\le A\log X,\qquad N_s(X,h)-N_o(X,h)\ge c\,X/(\log X)^2 .
\]
Both endpoints are ordinary unweighted primes. The constants depend on the fixed class and threshold. For Lebesgue-almost every \(t>0\), the two colors have equal limiting frequencies among **all** primes. The lower bound then detects pair agreement even when the global one-prime color imbalance vanishes. The displacement can change with \(X\). [All thresholds in each class](ThetaProgressionTailPairs.lean) · [Symmetry and the empirical tail difference](ThetaLagSignCounts.lean) · [Residual mean](NATURAL-PRIME-MEAN.md) · [Pinned upstream sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean#L38-L95)

## A positive fraction of displacements

The ordinary prime-pair upper sieve strengthens the conclusion. There exist \(A,b,\eta>0\) such that at every large \(X\), simultaneously for **each** integer \(A\log X\le H\le X\), at least \(\eta H\) distinct displacements \(1\le h\le H\) are multiples of \(m\) and satisfy \(N_s(X,h)-N_o(X,h)\ge bX/(\log X)^2\). Thus the number of such shifts already grows proportionally to \(\log X\) in a sufficiently long logarithmic range. [Positive fraction in the original class](ThetaFrequentTailGaps.lean)

The [pinned formal Selberg sieve](PRIME-PAIR-SIEVE.md) bounds the ordinary prime-pair count at lag \(h\) by \(CXw(h)/\log^2X\), uniformly for \(1\le h\le X\), where \(w(h)=\prod_{p\mid h}(1+3/p)\). Lemma 4 of Funkhouser, Goldston, Sengupta and Sengupta gives this classical upper bound for positive even \(h\). Each odd prime factor in their singular series contributes \(1+1/(p-2)\le1+3/p\). For odd \(h\) at most one pair has both endpoints prime. Lean proves the finite mean-square bound \(\sum_{1\le k<L}w(Dk)^2\le e^{12}DL\) by expanding over squarefree divisors. Cauchy–Schwarz then converts positive total excess into the stated count. The documented OMA bridge discharges this sieve input from its formal proof. The preceding single-displacement result uses only fixed-progression PNT. [Prime Difference Champions, Lemma 4](https://arxiv.org/pdf/1612.02938#page=16) · [Local factor estimate](ThetaLagSieveWeights.lean) · [Count of displacements](ThetaPopularLagCounts.lean)

## Subtracting a periodic predictor

For each \(m\ge1\) there are a prime \(q>m\), \(q\equiv3\bmod4\), and \(c_m>0\) with the following property. For every real \(m\)-periodic predictor \(g\), put \(D(p)=R(p)-g(p)\). For every large \(X\) there is a positive multiple \(h\le A_g\log X\) of \(q\) such that
\[
 \sum_{\substack{p,p+h\ {\rm prime}\\p+h\le X}}D(p)D(p+h)
 \ \ge\ c_m X/(\log X)^2 .
\]
The choice of \(q,c_m\) is uniform in the predictor. The coefficient of the quadratic character of conductor \(q\) in \(R\) survives the subtraction because the complete character mean vanishes against every \(m\)-periodic function. A layer-cake argument also gives a fixed positive threshold for \(D\) whose signed tail mark keeps a nonzero coefficient after subtraction of any real constant. [Quadratic witness](ThetaPeriodicCorrelationWitness.lean) · [Threshold selection](ThetaAsymmetricTails.lean) · [Centered marks](ThetaLagSignThreshold.lean)

For each such predictor there is \(K_g>0\) such that whenever \(K_g\log X\le L\le X/q\), the signed sum of \(D(p)D(p+h)D(r)D(r+h)\) for \(h=qk,\ 1\le k<L\), over four **distinct** primes up to \(X\), is at least
\[
 \tfrac12 c_m^2 X^2 L/(\log X)^4 .
\]
The two starting primes are ordered. For a given \(p,h\), at most three choices of \(r\) overlap the first pair. The pointwise polylogarithmic bound makes their total negligible at this scale. [Original sum and four distinct endpoints](ThetaLogPrimeCorrelations.lean) · [Overlap bound](ThetaDistinctPrimeQuadruples.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 174 modules, including the 154 notebook sources, the pinned DeepMind source, and the external prime-number theorem, the upper sieve and the documented bridges. All 607 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## Proof and scope

On a fine progression inside the prescribed class the earlier full-support refinement puts at least three quarters of its primes inside a ball wholly contained in the upper tail. Any real score bounded by one and equal to one on that ball has a signed sum at least half the prime count in the fine progression. Multiply by its indicator and average shifts through multiples of its modulus. Cauchy–Schwarz bounds the square of this first moment by a diagonal square sum plus positive off-diagonal lag correlations. The diagonal costs \(O(X/\log X)\), so \(K\log X\) shifts suffice. Apply the estimate to the ternary signed mark, extended by zero off the original progression, and expand the product into the difference of the two unweighted counts. [Fine-progression concentration](FULL-RESIDUAL-SUPPORT.md) · [Bounded score estimate](ThetaLocalMarkedCorrelations.lean) · [Finite sliding inequality](ThetaSlidingCorrelation.lean) · [Logarithmic shift selection](ThetaLogarithmicLags.lean)

The bridge below discharges the ordinary fixed-progression prime number theorem from the pinned formalization. The separate Romanoff sieve bridge discharges the pair-count input for the positive-fraction refinement. No prescribed nonzero gap or pair asymptotic follows. The pointwise sign of \(S(p)\) for every odd prime remains open. Berndt et al. study \(S\) itself. The active DeepMind reduction and corresponding OMA finite checks concern its one-prime pointwise inequalities. [Berndt et al.](https://arxiv.org/abs/2501.03234) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite bound](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [LTS target](https://lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1) · [Joint PNT replay](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaFrequentTailGaps
import ThetaPNTCorollaries
import ThetaPairSieveComparison

/-! Unweighted same-tail pair excess on ordinary primes and the signed raw
correlation after subtracting a fixed periodic predictor. -/
namespace Arxiv.«2501.03234».ThetaLogPrimeCorrelationsPNT
open Real Filter Finset MeasureTheory ThetaCharacterPrimeMeans ThetaPeriodMeans
open ThetaAsymmetricTails ThetaLagSignCounts ThetaProgressionTailPairs ThetaPNTCorollaries
open ThetaPrimeLaw ThetaDiagonalConstant ThetaNaturalPrimeMeans
open ThetaPositiveLag ThetaPrimeLagBounds ThetaDistinctPrimeQuadruples
open scoped Topology

theorem pairs_in_class {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (t : ℝ) (ht : 0≤t) :
    ∃ c A : ℝ,0<c ∧ 0<A ∧ ∀ᶠ X : ℕ in atTop,∃ h : ℕ,0<h ∧ q∣h ∧ (h:ℝ)≤A*log X ∧
      c*X≤((classCount q r X h (sameTail t):ℝ)-classCount q r X h (oppositeTail t))*(log X)^2 :=
  all_levels progression_mangoldt hq hr hu t ht

theorem balanced_levels :
    ∀ᵐ t : ℝ,Tendsto (primeMean (fun p => mark t ((S p:ℝ)/p-log p/2-diagonalConstant))) atTop (𝓝 0) := by
  obtain ⟨F,hF⟩ := exists_haar_representative progression_mangoldt residual_approximable
  exact balanced (law_symmetric progression_mangoldt hF) (empirical_tendsto progression_mangoldt hF)

theorem raw (m : ℕ) [NeZero m] :
    ∃ q : ℕ,m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ c : ℝ,0<c ∧ ∀ g : ℕ → ℝ,OnMod m g →
      (∃ A : ℝ,0<A ∧ ∀ᶠ X : ℕ in atTop,∃ h : ℕ,0<h ∧ q∣h ∧ (h:ℝ)≤A*log X ∧
        c*X≤corr X h (fun p => (S p:ℝ)/p-log p/2-g p)*(log X)^2) ∧
      ∃ K : ℝ,0<K ∧ ∀ᶠ X : ℕ in atTop,∀ L : ℕ,K*log X≤L → q*L≤X →
        c^2/2*(X:ℝ)^2*L≤(∑ k∈offsets L,four X (q*k) (fun p => (S p:ℝ)/p-log p/2-g p))*(log X)^4 :=
  ThetaLogPrimeCorrelations.original progression_mangoldt m

theorem positive_fraction {q r : ℕ}
    (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (t : ℝ) (ht : 0≤t) :
    ∃ A b η : ℝ,0<A ∧ 0<b ∧ 0<η ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,A*log X≤H → H≤X →
      η*H≤((ThetaFrequentTailGaps.gaps q r X H t b).card:ℝ) :=
  ThetaFrequentTailGaps.original ThetaPairSieveComparison.original progression_mangoldt hq hr hu t ht

#print axioms positive_fraction
#print axioms pairs_in_class
#print axioms balanced_levels
#print axioms raw
end Arxiv.«2501.03234».ThetaLogPrimeCorrelationsPNT
```
