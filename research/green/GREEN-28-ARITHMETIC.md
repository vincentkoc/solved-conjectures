# Green 28 and the arithmetic of a uniform sum

Let $P,Q$ be probability laws on the integers. Suppose their independent sum is uniform on a finite nonempty set. If all positive probability ratios of **either** marginal are rational, then **both** marginals are uniform on their supports. The unrestricted question remains open. [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [Lean proof](Green28UniformSums.lean)

## What the theorems prove

- `finite_of_uniform_sum` derives finiteness of both supports from uniformity of the sum alone. A translate of each support lies in the sum support.
- `endpoint_weights` takes the largest support point $b$ of each marginal. Every probability divided by the mass at $b$ is an algebraic integer in $[0,1]$. Every rational value of this ratio is zero or one. Thus $b$ attains the largest point mass.
- `algebraic_masses` proves that the actual probabilities of both marginals are algebraic over the rationals. `same_probability_field` proves that every real subfield contains all the masses of one marginal exactly when it contains all the masses of the other. Hence the generated fields coincide.
- `uniform_of_rational_ratios` proves the original pair of uniformity conclusions under the rational-ratio hypothesis above. Its Lean definition permits a zero numerator and requires a positive denominator. For finite laws, rationality of every nonzero ratio is equivalent to rationality of all the masses, since the masses sum to one. [Probability statements](Green28UniformSums.lean)

## Proof

Translate each support to nonnegative exponents. Divide the generating polynomial by its positive leading coefficient. The result is monic, with coefficients equal to the probabilities divided by the rightmost mass. Expanding the two PMF binds gives the ordinary polynomial product after accounting for both shifts and scales. A monic model has a uniform law exactly when its coefficients belong to $\{0,1\}$. The proofs use the pinned `Green28.indepSum` and `Green28.IsUniformOnSupport` directly. [PMF bridge](Green28UniformSums.lean)

For monic factors $f,g$ of a binary product, each coefficient is an algebraic integer by integrality of monic factors. If both factors have nonnegative coefficients, the term contributed by the leading monomial of $g$ bounds each coefficient of $f$ by one. A rational algebraic integer in this interval is zero or one. Monic division of the binary product by $f$ recovers $g$ over any subring containing the coefficients of $f$. Summing the coefficients and dividing by the sum recovers the point probabilities, which proves the field statement. [Coefficient lemmas](Green28PolynomialReduction.lean)

## Prior work and verification

Sil's 2019 question records Emmanuel Amiot's earlier question and credits the probabilistic reformulation to Gro-Tsen and Rémy Oudompheng. Emil Jeřábek observed the coefficient bound there. The arithmetic arguments here use classical integrality and monic polynomial division. Hare studies finite-degree verification, and Hasanbegović studies separation conditions on the support. [MathOverflow discussion](https://mathoverflow.net/questions/339137/) · [Hare](https://doi.org/10.1080/10586458.2025.2527786) · [Hasanbegović](https://arxiv.org/abs/2611.14596)

DeepMind's original issue closed with the statement formalization. Its separate MathOverflow file states the polynomial/PMF equivalence. Open Math Agents already proved that equivalence and has separate degree and reflection reductions. Its records and Left to Solve were checked for related work. This notebook contributes the arithmetic restriction on the actual PMFs. The general question currently has no solution listed in Left to Solve. [Original issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Pinned equivalence](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Mathoverflow/339137.lean) · [Formal equivalence proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/504) · [Green 28 reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21793) · [Polynomial reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21457) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28)

Both local modules were rebuilt with Lean 4.33.1 and independently replayed with `leanchecker`. The twelve printed axiom audits contain only `propext`, `Classical.choice` and `Quot.sound`.
