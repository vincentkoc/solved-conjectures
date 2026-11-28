# A relative symmetric-group test for factorial collisions

For a rational prime $p$, let $C_k(p)$ count the pairs $(j-k,j)$ with $1\le j-k<j<p$ and $(j-k)!\equiv j!\pmod p$. **The smallest collision gap is five on a set of primes of ordinary density $19/288$.** Avoiding all gaps through five has density $11/288$. At $p=13$ the pair $(4,9)$ realizes this minimum. Every density below uses $\pi(X)$ as the denominator. [Fifth-gap coefficient](Erdos478FifthCollisionAtom.lean) · [ordinary limits](Erdos478NaturalQuinticLaw.lean.in)

### The joint distribution

The limiting laws of $C_2,C_3,C_4,C_5$ are independent. The table gives integer weights for every count, with the denominator in the last column. Weights at larger counts vanish. Arbitrary selections of counts in the four rows have joint density equal to the product of their row probabilities. [Joint permutation law](Erdos478QuinticJointLaw.lean) · [quintic weights](Erdos478QuinticFixedCounts.lean)

| Gap | 0 | 1 | 2 | 3 | 4 | 5 | Denominator |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 1 | 0 | 1 | 0 | 0 | 0 | 2 |
| 3 | 2 | 3 | 0 | 1 | 0 | 0 | 6 |
| 4 | 5 | 0 | 2 | 0 | 1 | 0 | 8 |
| 5 | 44 | 45 | 20 | 10 | 0 | 1 | 120 |

The earlier gaps are absent with probability $5/48$. Among those primes the conditional probability of a fifth-gap hit is $76/120=19/30$, which gives $19/288$ overall. The remaining $44/120$ gives $11/288$. The same four-coordinate law and both first-gap frequencies hold after restricting to the previously constructed family on which the number of missing residues is at least a finite-search threshold tending to infinity. [Previous three-gap result and threshold](QuarticCollisionLaw.md) · [four-gap specialization](Erdos478NaturalQuinticLaw.lean.in)

### One prime certifies an entire relative action

Let $f_k(X)=X(X-1)\cdots(X-k+1)-1$. For a prime degree $\ell$ and a finite set $S\subseteq\{2,\ldots,\ell-1\}$, suppose one prime $q$ satisfies all three conditions.

1. Every $f_k$ for $k\in S\cup\{\ell\}$ has separable reduction modulo $q$.
2. Every $f_k$ for $k\in S$ has $k$ roots modulo $q$.
3. The polynomial $f_\ell$ has exactly $\ell-2$ roots modulo $q$.

In a common Galois splitting field a single Frobenius lift then fixes every smaller root and swaps two new roots. The subgroup fixing the smaller roots is already transitive on the $\ell$ roots. Its prime-degree action is primitive, and a primitive permutation group containing a transposition is the full symmetric group. Consequently, each permutation of the new roots can occur with any realized tuple of smaller permutations. `ordinary_modular_independence` turns this into an ordinary prime-density product for *every* event in the smaller collision counts and every selection of new counts. The test requires a witness satisfying the three hypotheses for each degree to which it is applied. [Simultaneous profile](Erdos478CommonModularProfile.lean) · [permutation criterion](Erdos478RelativePermutationCriterion.lean) · [relative action](Erdos478RelativeGapIndependence.lean) · [density theorem](Erdos478ModularGapIndependence.lean)

For $\ell=5$ and $S=\{2,3,4\}$, the witness is $q=9209$. The following are all the roots. [Factorization certificates](Erdos478QuinticFactorCertificate.lean) · [root counts and lift](Erdos478QuinticFrobenius.lean)

| $k$ | Roots in $\mathbb F_{9209}$ |
| ---: | --- |
| 2 | 750, 8460 |
| 3 | 4868, 6407, 7146 |
| 4 | 488, 771, 8441, 8724 |
| 5 | 987, 5706, 6091 |

After the three linear factors are removed, the remaining quintic factor is $X^2+3565X+4920$. Its discriminant is $8752$ modulo $9209$, and $8752^{4604}\equiv-1\pmod{9209}$. Thus the relative action is $S_5$. The quintic splitting field has degree $120$ over $\mathbb Q$, and the compositum for the four gaps has degree $96\cdot120=11520$. At a prime such as 17, the quintic has one root, but its value $j=5$ corresponds to the excluded lower index zero. The actual host count there is $C_5(17)=0$. [Field degrees and product action](Erdos478QuinticSplittingDegrees.lean) · [exact endpoint correction](Erdos478ExactEndpointCorrection.lean)

### Scope, sources and replay

The pinned Erdős 478 question asks for the limit of the normalized number of distinct factorial residues over *all* primes, with proposed value $1-1/e$. The fixed-gap distributions proved here leave that limit open. Klurman and Munsch use falling-factorial polynomials and prime ideal counts to study the mean deficit. Remark 2.4 relates individual polynomial root events to Galois fixed points. The present calculation identifies the **relative** permutation action and the joint law through gap five. Historical priority for these restricted formulas is unestablished. [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Klurman and Munsch](https://doi.org/10.5802/jtnb.974) · [previous three-gap calculation](https://github.com/vincentkoc/solved-conjectures/pull/384)

The notebook modules separate the finite group calculation from the analytic input. The unconditional adapter supplies the degree-one prime ideal theorem from the pinned Tau Ceti source. The live DeepMind issue and PRs concern the host statement. Left to Solve lists it as research open. The Open Math Agents search returned no matching formalization of the relative criterion or the four-gap law. [Tau Ceti pin](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean/vendor/TauCeti) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [additional statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents/issues?q=Erdos478)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target quintic-law`. Pass `--archive` to reuse the source archive. [Reproduction script](replay-natural-density)

Independent Lean 4.33.1 kernel replay checked 302 freshly compiled modules, including 197 from the pinned external source. All 37 new public declarations and both analytic inputs use only standard Lean axioms. The 28 direct checks include the host interval, the denominator, both splitting-field degrees, the quintic weights and the two stated densities.
