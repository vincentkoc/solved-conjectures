# Exact prime densities for factorial collision counts

For a prime $p$, let $A_p=\{j!\bmod p:1\le j<p\}$. Let $C_k(p)$ count the upper endpoints $k+1\le j<p$ with $j!\equiv(j-k)!\pmod p$. Fix any $m\ge1$, any finite set $S$ of gap lengths at least two, and any prescribed nonnegative integers $c_k$. The following event has a rational natural density among all primes.
$$
 m\mid p-1,\qquad C_k(p)=c_k\ (k\in S),\qquad |A_p|+\sum_{k\in S}c_k\le p-1 .
$$
The theorem supplies the density by finite rational interpolation, including zero-density patterns. It allows composite and repeated-factor degrees and imposes no conditions on intersections of splitting fields. The progression is part of the event. The denominator of the frequency is the count of all primes through the cutoff. [Exact counts](Erdos478ExactEndpointCounts.lean) · [Ordinary density](Erdos478NaturalExactCounts.lean.in) · [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

For example, the distribution of $C_3(p)$ is explicit.

| Number of pairs at distance three | Natural density |
| --- | --- |
| 0 | $1/3$ |
| 1 | $1/2$ |
| 3 | $1/6$ |
| Every other count | $0$ |

The prime $23$ realizes the zero-density count of two pairs. Their upper endpoints are $4$ and $11$.

The gap polynomial $G_3(x)=x(x-1)(x-2)-1$ becomes $y^3-y-1$ on setting $y=x-1$. Serre discusses the root counts of this cubic. In the Lean proof its splitting field contains a cubic root field and a square root of the discriminant $-23$. The field degree is divisible by both three and two, and the root permutations bound it above by six. The density of complete splitting is therefore $1/6$. A cubic with two roots counted with multiplicity has a remaining linear factor, so outside the ramified primes only counts zero, one and three occur. The mean count is one. These identities give the table. [Cubic computation](Erdos478CubicCountFrequencies.lean) · [Serre, *On a theorem of Jordan*, §§4–5](https://www.college-de-france.fr/media/jean-pierre-serre/UPL1210350903026534135_on_a_theorem_of_Jordan.pdf)

## Formula for a joint pattern

Use the tests $(G_k,c_k)$ for $k\in S$, together with $(\Phi_m,\varphi(m))$. Here $G_k(x)=x(x-1)\cdots(x-k+1)-1$. For a test $(f,c)$ of degree $d$, write
$$
 P_{d,c}(z)=\prod_{\substack{0\le j\le d\\j\ne c}}\frac{z-j}{c-j}.
$$
At every integer $z$ from zero through $d$, this is the indicator of $z=c$. It also vanishes on the entire range when $c>d$. Expand the product of these polynomials, using a variable $z_f$ for each input polynomial. Replace each monomial $z_{f_1}\cdots z_{f_n}$, with repetitions retained, by the following integer. [Interpolation](Erdos478JointCountInterpolation.lean)

Form all tuples $(a_1,\dots,a_n)$ choosing a complex root from each $f_i$. Take the least nonnegative integer $M$ for which the sums $\sum_i M^{i-1}a_i$ are distinct, with indices starting at one. The integral word polynomial $W$ has these sums as roots. Use the number of irreducible rational factors of $W$ as the value of the monomial. The empty monomial uses $W=X$, so contributes one. The resulting rational number is `jointDensity (requests m S c)`. [Mixed moments](Erdos478MixedPolynomialMoments.lean) · [Integral word polynomial](Erdos478RootWordPolynomial.lean)

Outside the finitely many primes of inseparable reduction, the weight gives a bijection from tuples of prime-field roots to prime-field roots of $W$. Indeed, a sum fixed by Frobenius has a unique tuple, so every coordinate is fixed. The prime ideal theorem gives each irreducible rational factor mean root count one. Summing these means proves the moment formula. Outside another finite set, the gap roots coincide with positive factorial endpoints, and disjoint upper endpoints give the stated bound on $A_p$. [Tuple bijection](Erdos478WordRootCounts.lean) · [Mean of a separable polynomial](Erdos478SeparableRootMean.lean) · [Endpoint bijection](Erdos478FactorialEndpointCounts.lean) · [Deficit inequality](Erdos478DisjointGapFamilies.lean)

## Scope and replay

The existence of root-count densities is classical from Frobenius density theory. Klurman and Munsch use factorial-gap polynomials to bound the mean deficit. The previous notebook law prescribed saturation or failure of saturation. This proof gives each interior count as well, including simultaneous counts at several lengths. The host question about the limit of $|A_p|/p$ remains open. The live DeepMind issue and PR concern its statement. The Left to Solve entry and Open Math Agents searches showed no overlapping formal joint law. [Klurman and Munsch](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Earlier saturation law](FactorialPatternLaw.md) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=%22Erdos478%22)

The native theorem `exact_count_of_pit` displays the degree-one prime ideal theorem as a hypothesis. The supplemental `exact_count_density` and `cubic_count_density` discharge it with the pinned Tau Ceti proof. The ordinary densities use this checked analytic input. General Chebotarev provides the classical interpretation. From the pinned Formal Conjectures Lake environment, run `lake env python3 "$notebook/erdos/478/replay-natural-density" --target counts`, with `notebook` set to the notebook’s `research` directory. [Prime ideal theorem adapter](Erdos478NaturalDensity.lean.in) · [Pinned Tau Ceti port](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean) · [Supplemental replay](replay-natural-density)

The independent Lean 4.33.1 replay rebuilt and kernel-checked all 35 notebook and adapter modules and all 197 external modules in the pinned source closure. All printed dependencies passed the axiom audit. The 12 required declarations used only `propext`, `Classical.choice`, and `Quot.sound`. A separate comparison imported the pinned conjecture to verify the factorial-image expression, the positive endpoints, the density denominator, the cubic probabilities, and the exceptional count at 23.
