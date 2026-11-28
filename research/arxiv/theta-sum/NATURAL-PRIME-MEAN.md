# Ordinary prime mean and lower densities for the theta sum

For the original integer sum $S(p)$, put $R(p)=S(p)/p-\tfrac12\log p$. With $\pi(X)$ counting every prime up to $X$,

\[
  \lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X}R(p)
  = B = \frac{\gamma+\log(4/\pi)}2
      -\frac4{\pi^2}\sum_{u\ge1,\;u\text{ odd}}\frac{\log u}{u^2}.
\]

The sum on the left runs over primes, including 2. The identity for $B$ follows by summing the constant part using $\sum_{u\ \mathrm{odd}}u^{-2}=\pi^2/8$. The Lean statement uses the equivalent convergent series in `diagonalConstant`. Its numerical value is approximately $0.2399341$. [Original sum and hypotheses](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Diagonal series](SECOND-ORDER-DIAGONAL.md)

There are constants $\delta_+,\delta_->0$ such that **for every sufficiently large $X$**, each row contains at least the indicated number of primes.

| Primes $p\le X$ | Lower bound on their count |
|---|---|
| $p\equiv1\pmod{24}$ and $R(p)>13/50$ | $\delta_+\pi(X)$ |
| $p\equiv17\pmod{24}$ and $R(p)<-1/1000$ | $\delta_-\pi(X)$ |

The two bounds hold simultaneously for all sufficiently large endpoints. The earlier upper-density theorem gave arbitrarily large endpoints for each sign. The proportion of primes in each row may still vary with $X$. Positivity at every odd prime and the pointwise eventual lower bounds remain open. [Upper-density theorem](ThetaHalfLogExcursions.lean) · [Natural-prime proofs](ThetaNaturalPrimeMeans.lean)

## Proof

1. For a selection $A$ of integers, compare its von Mangoldt sum $\psi_A(N)$ through $N$ with $\pi_A(N)\log N$. The error $\pi_A(N)\log N-\psi_A(N)$ lies between $-(\psi(N)-\theta(N))$ and $\pi(N)\log N-\theta(N)$. Both bounds are $o(N)$ and hold uniformly even for $A=A_N$. Passing from the upstream exclusive endpoint $N$ to $N+1$ gives ordinary equidistribution of the primes among the reduced classes of each fixed modulus. Prime divisors of the modulus have vanishing relative weight. [Count transfer and periodic averages](ThetaNaturalPrimeMeans.lean) · [Chebyshev estimates](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/Chebyshev.lean)
2. Each frozen model of the scaled off-diagonal has zero mean on the units of its period. For every $\varepsilon>0$ one model approximates the scaled off-diagonal with mean absolute error at most $\varepsilon$ at all sufficiently large prime endpoints. First fix the model, then apply equidistribution. This proves the off-diagonal has ordinary prime mean zero. The diagonal has second coefficient $B$ pointwise, so its prime average has the same limit. [Zero mean of the finite model](ThetaConditionalRows.lean) · [Prime approximation](ThetaPrimeTailTransfer.lean) · [Diagonal limit](ThetaDiagonalConstant.lean)
3. Each signed excursion has a fixed periodic test with strictly positive mean over the units. Whenever its sum over primes up to $X$ is positive, the approximation gives the required count at sufficiently large $X$. Equidistribution makes this premise hold eventually for each test. [Periodic witnesses](ThetaOffDiagonalSigns.lean) · [Witnesses at the stated thresholds](ThetaHalfLogExcursions.lean)

## Scope and related work

Berndt, Bhat, Meyer, Xie and Zaharescu conjecture eventual inequalities at each prime in v3 Conjecture 3.3. Their Section 5 asymptotic concerns a divisor sum related to $T(k)$. Lägeler proves modular distribution for individual Hardy sums. The limit here averages the signed aggregate over numerators at each prime denominator. [Original paper](https://arxiv.org/pdf/2501.03234v3) · [Lägeler](https://arxiv.org/abs/2207.04828)

The open DeepMind issue reduces the pointwise conjectures to a row remainder. The active OMA reductions include finite verifications and a continued-fraction decomposition for all-prime growth. The latter retains a uniform overshoot hypothesis. The matching Left to Solve entry credits a harmonic estimate. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA continued fractions](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21388) · [OMA harmonic reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21155) · [OMA finite range](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/18042) · [LTS-listed step](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126)

## Joint Lean replay

The notebook module states the transfer with an explicit `ProgressionMangoldt` premise to keep its standard Formal Conjectures replay self-contained. The following separate module discharges that premise using the PrimeNumberTheoremAnd project’s `WeakPNT_AP`. Both projects pin Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Compile this block as `ThetaPNTCorollaries.lean` with the notebook oleans, the pinned Formal Conjectures environment and the PNT project's Lake environment on `LEAN_PATH`. Then run `leanchecker ThetaPNTCorollaries` on the resulting module. The two named conclusions below have no progression hypothesis. [PNT project source and credits](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/PrimeNumberTheoremAnd/Wiener.lean#L4025-L4051) · [PNT project lockfile](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/55270df807213fc3584523d09e0311d7dc073ff5/lake-manifest.json)

```lean
import ThetaNaturalPrimeMeans
import PrimeNumberTheoremAnd.Wiener

/-! The natural-prime theta results with the progression input discharged. -/

namespace Arxiv.«2501.03234».ThetaPNTCorollaries

open Filter ThetaNaturalPrimeMeans ThetaDiagonalConstant
open scoped Topology

theorem progression_mangoldt : ProgressionMangoldt := by
  intro q a hq ha hlt
  apply (WeakPNT_AP hq ha hlt).congr'
  apply Filter.Eventually.of_forall
  intro N
  simp only [selectedPsi, cumsum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : n % q = a <;> simp [h]

theorem second_order_prime_mean :
    Tendsto (primeMean (fun p => (S p : ℝ) / p - Real.log p / 2))
      atTop (𝓝 diagonalConstant) :=
  S_second_order_prime_mean progression_mangoldt

theorem half_log_lower_densities :
    PositiveLowerPrimeDensity (fun p => p % 24 = 1 ∧
      (p : ℝ) * Real.log p / 2 + 13 * (p : ℝ) / 50 < (S p : ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => p % 24 = 17 ∧
      (S p : ℝ) < (p : ℝ) * Real.log p / 2 - (p : ℝ) / 1000) :=
  S_half_log_lower_densities progression_mangoldt

#print axioms WeakPNT_AP
#print axioms progression_mangoldt
#print axioms second_order_prime_mean
#print axioms half_log_lower_densities

end Arxiv.«2501.03234».ThetaPNTCorollaries
```

For the joint replay, set `NOTEBOOK` to this repository, `THETA_OLEANS` to the directory containing the compiled notebook modules, and `PNT_CHECKOUT` to the pinned PNT checkout with `PrimeNumberTheoremAnd.Wiener` built. Run the following in the pinned Formal Conjectures Lake environment.

```sh
bridge_dir=$(mktemp -d)
pnt_path=$(cd "$PNT_CHECKOUT" && lake env printenv LEAN_PATH)
awk '/^```lean$/ { lean = 1; next } lean && /^```$/ { exit } lean { print }' \
  "$NOTEBOOK/research/arxiv/theta-sum/NATURAL-PRIME-MEAN.md" > "$bridge_dir/ThetaPNTCorollaries.lean"
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  lean -o ThetaPNTCorollaries.olean ThetaPNTCorollaries.lean
  leanchecker -v ThetaPNTCorollaries
' sh "$bridge_dir" "$THETA_OLEANS" "$pnt_path"
```

The axiom reports for `WeakPNT_AP`, `progression_mangoldt` and both final declarations contain only `propext`, `Classical.choice` and `Quot.sound`. This is a declaration-level audit of the imported theorem. Two auxiliary Fourier decay lemmas elsewhere in the pinned Wiener module carry placeholders and are outside its dependency chain. Codex assisted with the derivation and formalization. [Notebook replay](../../README.md)
