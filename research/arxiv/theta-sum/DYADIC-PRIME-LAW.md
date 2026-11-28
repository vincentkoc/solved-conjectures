# The theta residual in dyadic prime progressions

Let $R(p)=S(p)/p-\tfrac12\log p$, where $S$ is the integer sum formalized by DeepMind. Write $B$ for its all-prime residual mean and $C$ for the positive modulo-three bias. For **every** $t<C$, each of the following sets has positive lower density among all primes.

\[
\begin{aligned}
 p&\equiv 1\pmod{24}, & S(p)&>\tfrac12 p\log p+(B+t)p,\\
 p&\equiv17\pmod{24}, & S(p)&<\tfrac12 p\log p+(B-t)p .
\end{aligned}
\]

Both classes lie in $p\equiv1\bmod8$, where the modulo-eight congruence permits $S(p)=0$. The two residual thresholds can approach $B+C\approx0.63842$ and $B-C\approx-0.15855$. The lower density in each line is measured against $\pi(X)$ at every sufficiently large endpoint and may depend on $t$. Both comparisons concern the size of the second term. Positivity of $S(p)$ at every prime in $1\bmod8$ remains open. [Dyadic proof](ThetaDyadicLaw.lean) · [Pinned integer sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Modulo-eight congruence](DIAGONAL.md)

Direct summation of the defining signs gives $S(241)=816$ and $S(113)=224$, with residuals about $0.64349$ and $-0.38139$ in the two classes. The earlier finite-cone theorem found opposite signs in the same classes for fixed truncations. The inequalities above concern the full integer sum. [Finite-cone theorem](RESIDUE-CLASS-BIAS.md)

## What conditioning on a dyadic class preserves

Fix $q=2^k$ and a reduced residue $0\le r<q$. The empirical law of $R(p)$ among $p\le X$ in $r\bmod q$, normalized by the number of primes in **that class**, converges to the same symmetric law $\mu$ as the all-prime sample. Every Lipschitz test has the same limiting mean, including unbounded tests of linear growth. The quantifiers allow each fixed $k,r$ and give no error uniform in $k$. [All-prime law](PRIME-RESIDUAL-LAW.md)

More generally, let $m$ be odd and $w$ any real function on residue classes modulo $m$. Whenever the all-prime mean of $w(p)\phi(R(p))$ converges for a Lipschitz $\phi$, restriction to $r\bmod q$ preserves the limit. If a Lipschitz-test mean exists within a reduced odd class $a\bmod m$, restriction to the simultaneous classes $a\bmod m$ and $r\bmod q$ preserves that mean under its own normalization. For $m=3$ this gives the exact means $B+C$ on $a=1$ and $B-C$ on $a=2$ inside **every** fixed reduced dyadic class. Both signed excursions above extend to those simultaneous classes. [Exact modulo-three bias and Euler product](EXACT-MOD-THREE-BIAS.md)

## Why the dyadic class drops out

The finite reciprocal models involve only odd primitive row denominators. The product of the finitely many such denominators is an odd period for the entire model, including the diagonal constant. Multiplication by $w$ keeps the period odd. The Chinese remainder theorem factors the mean of a periodic test against a dyadic weight into two reduced-residue means. A dyadic weight with mean zero therefore has exactly zero correlation with each finite model. The prime number theorem in fixed arithmetic progressions evaluates their prime means. Lipschitz continuity and convergence in prime mean absolute error transfer the factorization to $R$. Dividing out the class density $1/\varphi(q)$ gives the conditional mean. Bounded Lipschitz tests then give weak convergence.

To pass from a mixed-class mean $L$ to excursions above $a<L$, choose a bounded periodic approximation $g$ to $R$ in prime mean absolute error. For $s=\pm1$ and a bound $M$ on $|g|$, one has
\[
 sR-a\ \le\ (M+|a|+1)\mathbf1_{\{sR>a\}}+|R-g|.
\]
The mixed class has positive prime density by the same finite factorization. Its mean excess over $a$ is eventually bounded below, while the total approximation error over all primes can be made smaller than half that lower bound after normalization. The event therefore occupies a positive lower fraction of all primes. Taking $s=1$ and $s=-1$ gives the two lines above.

Berndt et al. study the canonical signed aggregate. Lägeler studies individual Hardy sums with the numerator also varying. The DeepMind reduction concerns the remainder controlling pointwise lower bounds. The OMA finite certificate reports all odd primes below 100,000, and the LTS-listed harmonic estimate concerns one step in a lower-bound reduction. The paper, literature and live tracker checks did not turn up this dyadic conditional law or these mixed-class signed excursions. [Original paper](https://doi.org/10.1007/s00025-025-02584-2) · [Hardy-sum distributions](https://arxiv.org/abs/2207.04828) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite range](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21967) · [Harmonic estimate](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [LTS solved feed](https://lefttosolve.com/api/solved)

## Kernel replay

The notebook module takes the named progression theorem as input. The joint module below discharges it using the previously pinned external theorem on the same Lean 4.33.1 and mathlib revisions. [Pinned progression proof and bridge instructions](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaDyadicLaw
import ThetaPNTCorollaries

namespace Arxiv.«2501.03234».ThetaDyadicLawPNT
open Filter MeasureTheory ThetaPrimeLaw ThetaProfiniteUnits ThetaNaturalPrimeMeans ThetaDyadicLaw
open ThetaCharacterPrimeMeans ThetaCharacterCoefficient ThetaDiagonalConstant ThetaPNTCorollaries
open scoped Topology NNReal

theorem dyadic_laws :
    ∃ F : G →₁[haar] ℝ, Represents residual F ∧
      reflectedLaw diagonalConstant (haarLaw F) = haarLaw F ∧
      ∀ k r : ℕ, r.Coprime (2^k) → r < 2^k →
        Tendsto (progressionLaw (2^k) r residual) atTop (𝓝 (haarLaw F)) ∧
        ∀ (φ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K φ →
          Tendsto (progressionMean (2^k) r (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ x ∂(haarLaw F))) :=
  ThetaDyadicLaw.S_dyadic_laws progression_mangoldt

#print axioms dyadic_laws

theorem mixed_class_means {k r : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r<2^k) :
    Tendsto (mixedMean (2^k) r 3 1 residual) atTop (𝓝 (diagonalConstant+characterConstant)) ∧
      Tendsto (mixedMean (2^k) r 3 2 residual) atTop (𝓝 (diagonalConstant-characterConstant)) :=
  ThetaDyadicLaw.dyadic_mod_three_means progression_mangoldt hr hlt

#print axioms mixed_class_means

theorem mixed_class_excursions {k r : ℕ}
    (hr : r.Coprime (2^k)) (hlt : r<2^k) {t : ℝ} (ht : t<characterConstant) :
    PositiveLowerPrimeDensity (fun p => (p%2^k=r ∧ p%3=1) ∧
      p*Real.log p/2+(diagonalConstant+t)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => (p%2^k=r ∧ p%3=2) ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-t)*p) :=
  ThetaDyadicLaw.S_dyadic_reflected_excursions progression_mangoldt hr hlt ht

#print axioms mixed_class_excursions

theorem one_mod_eight_excursions {t : ℝ} (ht : t<characterConstant) :
    PositiveLowerPrimeDensity (fun p => p%24=1 ∧
      p*Real.log p/2+(diagonalConstant+t)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => p%24=17 ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-t)*p) :=
  ThetaDyadicLaw.S_one_mod_eight_excursions progression_mangoldt ht

#print axioms one_mod_eight_excursions

end Arxiv.«2501.03234».ThetaDyadicLawPNT
```

After building the progression bridge, extract and verify the joint module with the same paths.

```sh
awk '/^```lean$/ { lean = 1; next } lean && /^```$/ { exit } lean { print }' \
  "$NOTEBOOK/research/arxiv/theta-sum/DYADIC-PRIME-LAW.md" > "$bridge_dir/ThetaDyadicLawPNT.lean"
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  lean -o ThetaDyadicLawPNT.olean ThetaDyadicLawPNT.lean
  leanchecker -v ThetaDyadicLawPNT
' sh "$bridge_dir" "$THETA_OLEANS" "$pnt_path"
```

All four joint declarations print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and Lean formalization.
