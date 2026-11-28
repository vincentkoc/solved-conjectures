# A limiting law for the theta residual over primes

Let $p$ run uniformly through the primes up to $X$ and put $R(p)=S(p)/p-\tfrac12\log p$ for the original integer theta sum. The empirical distribution of $R(p)$ converges weakly to a probability law $\mu$ symmetric about $B$, the all-prime residual mean. There is a single integrable real function $F$ on the profinite unit group $\widehat{\mathbb Z}^{\times}$ such that $\mu$ is the pushforward of normalized Haar measure by $F$. For every Lipschitz test $\phi:\mathbb R\to\mathbb R$, including tests of linear growth, the proof gives
\[
   \lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X}\phi(R(p))
     =\int_{\widehat{\mathbb Z}^{\times}}\phi(F(u))\,du
     =\int_{\mathbb R}\phi(x)\,d\mu(x).
\]
[Lean theorem for the residual](ThetaPrimeResidualLaw.lean) · [Pinned definition of S](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

Reflection $x\mapsto2B-x$ preserves $\mu$, so $B$ is also a median. For every $t\in\mathbb R$ the law satisfies
\[
  \int |x-t|\,d\mu(x)\ \ge\
  C=\frac{3\pi}{16\sqrt3}\prod_{\ell\equiv5\ (6),\,\ell\ {\rm prime}}
            \left(1+\frac{2}{(\ell-1)^2}\right)\approx0.398484 .
\]
For **every** $t<C$, a positive lower fraction of all primes satisfy $R(p)>B+t$, and a positive lower fraction satisfy $R(p)<B-t$. Thus the two thresholds can approach $B+C$ and $B-C$, approximately $0.63842$ and $-0.15855$, from within. The fractions may depend on $t$. In particular $\mu$ differs from every point mass. Both $\mu([13/50,\infty))$ and $\mu((-\infty,-1/1000])$ are positive. These are statements about the residual. The sign of $S(p)$ at every odd prime remains open. [Formula for B](NATURAL-PRIME-MEAN.md) · [Exact character bias C](EXACT-MOD-THREE-BIAS.md) · [Positive lower densities](NATURAL-PRIME-MEAN.md)

## Construction and scope

The group in Lean is the subgroup of $\prod_n(\mathbb Z/n!\mathbb Z)^\times$ formed by compatible sequences. The factorial moduli are cofinal for divisibility. The subgroup is closed and compact, and reduction onto each coordinate is surjective. Averaging a function of one coordinate over translates gives its uniform reduced-residue mean. The prime number theorem in fixed arithmetic progressions gives the same mean over primes. [Group, Haar measure and coordinate integrals](ThetaProfiniteUnits.lean)

For each $n$ choose a periodic function $g_n$ whose eventual prime mean absolute discrepancy from $R$ is at most $1/(n+1)$. The prime mean distance between $g_i$ and $g_j$ tends to their Haar $L^1$ distance on the common factorial modulus. It follows that their lifts form a Cauchy sequence in $L^1$ of Haar measure. Its limit is $F$. A Lipschitz test changes both discrepancies by at most its Lipschitz constant, which proves the integral formula. The bounded Lipschitz criterion gives weak convergence. For the lower bound on the absolute distance to $t$, twist $R-t$ by $\chi_3$: its signed prime mean tends to $C$, whereas its absolute value is bounded by $|R-t|$. On the units of each finite period the map $u\mapsto-u$ negates every reciprocal row: it reverses the parity of the nonzero representative of $w/u$ at each odd denominator. Thus the models of the original residual are symmetric about $B$. Passing their Lipschitz test integrals to the limit proves the same symmetry for $\mu$. [Finite reflection identity](ThetaRowReflection.lean)

The closed-set inequality for weak convergence transfers the prior prime excursions to the stated half-lines. For the stronger excursions, symmetry gives equal mass to the open tails beyond $B\pm t$. If both masses vanished, then $|x-B|\le t$ almost surely, contradicting the absolute-distance bound for $t<C$. The open-set inequality converts each positive tail mass into a positive lower prime density. The argument establishes an integrable representative and its law. A density, absence of atoms and a closed-form distribution function remain undetermined. [Haar limit and test integrals](ThetaPrimeLaw.lean) · [Periodic prime approximation](ThetaPrimeTailTransfer.lean)

Berndt, Bhat, Meyer, Xie and Zaharescu study $S(k)$ and its pointwise inequalities. Lägeler studies individual Hardy sums. The sampling here takes the signed aggregate over all numerators and varies the prime denominator. The use of periodic approximation to obtain a limiting distribution has precedents in almost-periodic number theory, including work of Akbary, Ng and Shahabi on classical prime-number error terms. The DeepMind row-remainder reduction and the LTS harmonic step concern pointwise inequalities. An OMA submission reports a certificate for the finite positivity subproblem covering the 9,591 odd primes below 100,000. [Original paper](https://arxiv.org/html/2501.03234v3) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Akbary, Ng and Shahabi](https://arxiv.org/abs/1306.1657) · [DeepMind discussion](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA pointwise reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21388) · [Finite OMA certificate](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21967) · [LTS-listed step](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

## Joint Lean replay

The notebook theorem uses the proposition `ProgressionMangoldt`. The joint module below discharges it with the pinned external theorem. [Pins and bridge setup](NATURAL-PRIME-MEAN.md#joint-lean-replay) · [External progression theorem](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/Wiener.lean#L4025-L4051)

```lean
import ThetaPrimeResidualLaw
import ThetaPNTCorollaries

/-! The limiting distribution for the original theta sum, with the progression theorem discharged. -/
namespace Arxiv.«2501.03234».ThetaResidualLawPNT
open MeasureTheory Filter ThetaProfiniteUnits ThetaPrimeLaw ThetaNaturalPrimeMeans
open ThetaCharacterPrimeMeans ThetaCharacterCoefficient ThetaDiagonalConstant ThetaPNTCorollaries
open scoped Topology NNReal

theorem prime_residual_distribution :
    ∃ F : G →₁[haar] ℝ, Represents residual F ∧
      reflectedLaw diagonalConstant (haarLaw F) = haarLaw F ∧
      Tendsto (empirical residual) atTop (𝓝 (haarLaw F)) ∧
      (∀ (φ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K φ →
        Tendsto (primeMean (fun p => φ (residual p))) atTop (𝓝 (∫ x, φ x ∂(haarLaw F)))) ∧
      (∫ x, x ∂(haarLaw F)) = diagonalConstant ∧
      (∀ t : ℝ, characterConstant ≤ ∫ x, |x-t| ∂(haarLaw F)) ∧
      (∀ t : ℝ, (haarLaw F : Measure ℝ) ≠ Measure.dirac t) ∧
      0 < (haarLaw F : Measure ℝ) (Set.Ici (13/50:ℝ)) ∧
      0 < (haarLaw F : Measure ℝ) (Set.Iic (-(1/1000):ℝ)) :=
  S_prime_residual_distribution progression_mangoldt

theorem prime_reflected_excursions {t : ℝ} (ht : t < characterConstant) :
    PositiveLowerPrimeDensity (fun p => diagonalConstant+t < residual p) ∧
      PositiveLowerPrimeDensity (fun p => residual p < diagonalConstant-t) :=
  S_prime_reflected_excursions progression_mangoldt ht

#print axioms prime_residual_distribution
#print axioms prime_reflected_excursions
end Arxiv.«2501.03234».ThetaResidualLawPNT
```

After building the progression bridge with its documented pins, extract this module and use the same bridge directory and package paths.

```sh
awk '/^```lean$/ { lean = 1; next } lean && /^```$/ { exit } lean { print }' \
  "$NOTEBOOK/research/arxiv/theta-sum/PRIME-RESIDUAL-LAW.md" > "$bridge_dir/ThetaResidualLawPNT.lean"
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  lean -o ThetaResidualLawPNT.olean ThetaResidualLawPNT.lean
  leanchecker -v ThetaResidualLawPNT
' sh "$bridge_dir" "$THETA_OLEANS" "$pnt_path"
```

Both unconditional declarations report only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and Lean formalization.
