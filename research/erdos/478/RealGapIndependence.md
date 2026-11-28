# The three-step collision among prescribed factorial gaps

For a prime $p$, let $A_p=\{j!\bmod p:1\le j<p\}$ and let $C_k(p)$ count upper endpoints $k+1\le j<p$ with $(j-k)!\equiv j!\pmod p$. Fix finite sets $S,T\subseteq\{2,5,6,7,\ldots\}$. Prescribe $C_k(p)=k$ for $k\in S$ and $C_k(p)<k$ for $k\in T$.

**Requiring $C_3(p)=3$ multiplies the pattern's natural density by exactly $1/6$.** If the original pattern has positive density, the fraction of its primes through $X$ meeting this extra requirement tends to $1/6$. The notebook's event includes $|A_p|+\sum_{k\in S}k\le p-1$ in the denominator pattern, and adds three to the required deficit in the numerator. These inequalities follow from the endpoint conditions outside a finite set. The theorem uses the unrestricted rational primes as its underlying population. [Conditional frequency](Erdos478NaturalCubicPattern.lean.in) · [Definition of the event](Erdos478FactorialPatternLaw.lean) · [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

| Required full gaps | Natural density among all primes | Bound at every such prime |
| --- | ---: | --- |
| 2 and 3 | $1/12$ | $\lvert A_p\rvert+5\le p-1$ |
| 3 and 6 | $1/144$ | $\lvert A_p\rvert+9\le p-1$ |

The earlier general pattern law expressed the density in terms of unspecified compositum degrees. For gaps two and three it gave the lower bound $1/12$. For gap six alone, full saturation has density $1/24$. The exact joint values above use independence from the cubic splitting field. The conjectured limit of $|A_p|/p$ remains open. [Pattern law](FactorialPatternLaw.md) · [Six-gap frequencies](SixGapFrequencies.md) · [Joint degrees](Erdos478CubicPatternFactor.lean)

## Where the factor six comes from

Set $P_n(x)=x(x-1)\cdots(x-n+1)$ and $G_n=P_n-1$. For $n\ge5$, the proof locates a root of $G_n$ in each open interval $(j-\frac12,j+\frac12)$ for $0\le j<n$. At every half-integer $x$, one has $|P_5(x)|>1$. For the induction use $P_{n+1}(x)=(x-n)P_n(x)=xP_n(x-1)$. At least one of $|x-n|,|x|$ is at least one. On the half-integer endpoints of each interval the values of $P_n$ have opposite signs, so continuity supplies the root. The $n$ disjoint intervals already account for the full degree. The quadratic gap also splits over the reals, with roots $(1\pm\sqrt{5})/2$. [Real root locations](Erdos478RealPochhammerRoots.lean) · [Real splitting fields](Erdos478CubicGapIndependence.lean)

Consequently the joint splitting field $E$ of any collection of these gaps embeds in $\mathbb R$ and is normal over $\mathbb Q$. The cubic $G_3$ becomes $y^3-y-1$ after translation. It is irreducible with discriminant $-23$. A root in $E$ would force all its conjugates into $E$, where its negative discriminant cannot become a square. It stays irreducible over $E$, and its splitting field over $E$ has degree divisible by both three and two. Its degree is therefore six. The formal field lemma applies to every monic irreducible rational cubic of negative discriminant and every polynomial that splits over $\mathbb R$. [General cubic degree theorem](Erdos478RealCubicDegree.lean) · [Serre on the cubic](https://www.college-de-france.fr/media/jean-pierre-serre/UPL1210350903026534135_on_a_theorem_of_Jordan.pdf)

For each fully split set the ordinary prime density is the reciprocal of its splitting degree. Inclusion–exclusion over the unsaturated tests preserves the factor $1/6$, even when the real gap fields intersect each other. The analytic input is the pinned Tau Ceti degree-one prime ideal theorem. Klurman and Munsch studied the factorial-gap polynomials and the Galois interpretation of their prime root counts. [Density factor](Erdos478CubicPatternFactor.lean) · [Klurman and Munsch](https://www.numdam.org/articles/10.5802/jtnb.974/) · [Pinned prime ideal theorem](https://github.com/KitaKen1/simultaneous-primitive-roots/tree/bb3b4fff6bb0210a0f94fc535bf9adbf46ecc55a/lean)

## The exceptional shared endpoint

Two consecutive gaps never have a common positive upper endpoint at a prime. The two window products would both be one, forcing their extra factor $j-k$ to equal one modulo $p$, while $2\le j-k<p$. For gaps three and six, there is exactly one common positive upper endpoint over all primes. It is $328$ at $p=347$. At that prime the actual sets are $\{44,325,328\}$ and $\{24,53,146,206,299,328\}$, respectively.

Indeed, a common upper endpoint $x$ makes the consecutive triples starting at $x$ and $x-3$ have falling product one. Since $p>6$, subtracting their cubic equations gives $3x^2-15x+20=0$. A further elimination gives $16x=43$, hence $347=0$ in the prime field. Direct evaluation at $347$ resolves the overlap. At every prime the canonical image size plus $C_3(p)+C_6(p)$ is at most $p-1$, including the exceptional prime, where the image has size $210$. The corresponding inequality also holds for every pair of consecutive positive gaps. [All-prime overlap and deficit](Erdos478CubicSexticOverlap.lean)

## Replay

Lean 4.33.1 rebuilt and independently kernel-replayed the 237 modules in the proof closure, including 197 pinned external modules. All 25 public theorems in the six new sources use only the standard axioms. A separate check compared the endpoint and factorial-image definitions with the pinned host, verified the two splitting degrees, and evaluated both endpoint sets and the image size at 347.

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/research/erdos/478/replay-natural-density" --target real-gaps`. An existing pinned source archive may be supplied with `--archive FILE`. The notebook runner can replay the algebra and the all-prime bounds independently with `Erdos478CubicPatternFactor Erdos478CubicSexticOverlap`. [Supplemental replay](replay-natural-density) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478)
