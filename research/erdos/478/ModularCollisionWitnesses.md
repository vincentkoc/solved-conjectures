# Modular witnesses for factorial collision profiles

Every possible first collision distance from 2 through 11 occurs on a set of primes of positive ordinary density. Five distances are composite. Their positivity follows from explicit modular witnesses together with a joint fixed-root theorem. A second result gives the same exponential lower-tail bound for long collisions after conditioning on **any** positive-density event involving shorter endpoint counts. [First-distance theorem and ordinary window bounds](Erdos478NaturalModularWitnesses.lean.in)

## Five composite first distances

For prime $p$, a collision at distance $k$ means $j!\equiv(j+k)!\pmod p$ for some $1\le j<j+k<p$. Let $a_\ell$ be the limiting fraction of primes with least such distance $\ell$. For each row below,
$$
a_\ell\ \ge\ \left(\prod_{k=2}^{\ell}k!\right)^{-1}.
$$

| First distance $\ell$ | Witness prime $p$ | Upper endpoint $x$ |
|---:|---:|---:|
| 4 | 47 | 15 |
| 6 | 193 | 88 |
| 8 | 5,477 | 2,268 |
| 9 | 1,013 | 316 |
| 10 | 25,117 | 10,336 |

At the listed endpoint, $x(x-1)\cdots(x-\ell+1)\equiv1\pmod p$. The kernel checks the congruence, every residue for every shorter length $2\le k<\ell$, and primality. Length one is impossible on the positive factorial interval. Integer Bézout identities for $f_k=X(X-1)\cdots(X-k+1)-1$ and $f'_k$ certify separable reduction for all the tested lengths. The preceding least-distance law supplies the prime lengths. The support at larger composite lengths remains to be determined. [Residue certificates](Erdos478CompositeFirstAtoms.lean) · [Bézout identities](Erdos478LowGapBezout.lean) · [Least-distance law](LeastFactorialCollision.md)

## When a finite profile has positive density

For a finite set $S$ of lengths at least two, let $c_k(p)$ count upper endpoints of collisions of length $k$ and let $E$ be any predicate on $(c_k(p))_{k\in S}$. Define
$$
\Delta_S=\prod_{k\in S}\left|\operatorname{Res}(f_k,f'_k)\right|(k!-1).
$$
This integer is positive, including the empty product $1$. The ordinary prime density of $E$ is zero exactly when every prime realizing $E$ divides $\Delta_S$. A single occurrence at a prime outside that divisor gives density at least $(\prod_{k\in S}k!)^{-1}$. The divisor can include primes that cause no problem for a particular event. [Support criterion](Erdos478WitnessDensityDichotomy.lean) · [Exceptional divisor](Erdos478RegularGapPrimes.lean)

The local argument fixes one lift of the residue-field Frobenius in a common finite Galois splitting field. For every split monic integer polynomial with separable reduction and separable characteristic-zero roots, that same lift fixes as many roots as the polynomial has distinct roots over $\mathbf F_p$. The splitting-field degree bound gives the mass of a single witnessing automorphism. The conversion to factorials is exact at every prime. The number of roots of $f_k$ exceeds $c_k(p)$ by one precisely when $k<p$ and $k!\equiv1\pmod p$, since that endpoint pairs with $0!$. [Simultaneous lift](Erdos478SimultaneousModularWitness.lean) · [Positive endpoint correction](Erdos478ExactEndpointCorrection.lean)

## Growing image loss in all short profiles

Let $A_p=\{j!\bmod p:1\le j<p\}$. For $A<\log(32/27)/9$, all sufficiently large $K$ admit a prime cutoff $X_0(K,A)$ with the following property. For every $X\ge X_0(K,A)$ and **every** positive-density event on the counts $(c_2(p),\ldots,c_K(p))$, a fraction greater than $1-\exp(-AK/\log K)$ of the event primes $p\le X$ have at least $K/(9\log K)$ distinct collision lengths among primes $K<\ell\le2K$ with $\ell\bmod7\in\{3,4\}$. If $h$ is the number of these lengths, the counted primes satisfy $|A_p|+h\le p-1$. The cutoff works simultaneously for all short profiles and their unions. The one-sided bound is informative for $A>0$. [Uniformity over events](Erdos478UniformProfileWindows.lean) · [Conditional fraction](Erdos478ProfileWindowLimit.lean)

The proof bounds the conditional generating function before dividing by the mass of the event. At every prime $c_k(p)\le k$, so for fixed $K$ only finitely many different events can occur on prime moduli. This gives the common cutoff, even for a predicate selected after $X$. The general window theorem permits $H(K)/K\to L>1$, threshold $bK/\log K$ and rate $A<b\log z-(L-1)\log((1+z)/2)/3$ for $0<z\le1$. No explicit growth rate for $X_0(K,A)$ is supplied. The DeepMind question asks for $|A_p|/p\to1-e^{-1}$ along the prime filter and remains open. [Pinned canonical statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Sources and replay

Klurman and Munsch use factorial-gap polynomials and degree-one prime ideals to bound the mean number of missing factorial residues. The local fixed-root argument here uses the classical relation between residue Frobenius and factorization. The checked analytic inputs come from the pinned prime ideal theorem and prime progression counts used by the notebook's preceding density laws. These results establish partial progress on the canonical question. The five finite certificates and the common-cutoff theorem extend the notebook's prime-length atoms and its short-free conditional bound. [Klurman–Munsch](https://doi.org/10.5802/jtnb.974) · [Preceding notebook result](https://github.com/vincentkoc/solved-conjectures/pull/358) · [Pinned analytic sources](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti)

The DeepMind issue, its statement PR, the Left to Solve entry, and Open Math Agents were checked for overlapping declarations. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=Erdos478)

Run the supplemental proof from the pinned Formal Conjectures checkout. An optional local archive can be supplied with `--archive`. [Replay runner](replay-natural-density)

```sh
lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target modular-witnesses
```

Clean compilation and independent kernel replay covered 303 distinct modules, including 197 pinned external modules. The axiom audit checked all 46 public declarations added here and four analytic inputs. Twenty Lean examples compared statements against the pinned host and checked the interval, denominator, concrete witnesses and dyadic quantifiers. The audit found only standard Lean axioms.
