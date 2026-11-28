# Six-point blocks at every sufficiently large admissible order

A family of six-element subsets of `Fin n` covering every pair exactly once exists, for every sufficiently large $n$, precisely when $n$ is congruent to $1,6,16$ or $21$ modulo $30$. The theorem `Erdos722.Six.eventually_six` has the exact type of the pinned Erdős 722 declaration at $r=2$, $k=6$. It includes composite orders with any number of prime factors. [Lean endpoint](Erdos722SixSpectrum.lean) · [Pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean)

Write $n=5u+1$ and call $u$ usable for inflation when a design exists at that order. The binomial tests require $5\mid n-1$ and $15\mid\binom n2$. For positive $n$ these give $u\equiv0,1\pmod3$. Thus $u\bmod6$ can be $0,1,3,4$, giving the four order classes above. The construction begins with the following checked designs. [Arithmetic](Erdos722SixSpectrum.lean)

| Group count $u$ | Order $5u+1$ | Order modulo 30 | Construction |
|---:|---:|---:|---|
| 30 | 151 | 1 | Five cyclic starters. Their 150 oriented differences cover each nonzero residue once. |
| 31 | 156 | 6 | Lines of the projective space $\mathrm{PG}(3,5)$. |
| 39 | 196 | 16 | Four cyclic layers of size 49, with 26 translation orbits of six-point blocks. |
| 40 | 201 | 21 | Three cyclic layers of size 67, with 20 translation orbits. |

The last two designs are Abel, Bluskov, Greig and de Heer's Theorem 3.2. The Lean certificates check the ordered layer labels and the cyclic difference for every pair. For orders 196 and 201, respectively, there are 780 and 600 admissible classes. The order-151 starters are the multiples by $1,8,19,59,64$ of $\{0,1,12,33,83,90\}$. [First two seeds](Erdos722SixConsecutiveSeeds.lean) · [Layer construction](Erdos722SixLayerDesign.lean) · [Published starters in Lean](Erdos722SixMixedSeeds.lean) · [Abel et al.](https://doi.org/10.1002/jcd.20157)

## How one prime supplies two consecutive heights

Truncating a transversal design with $s$ full columns of height $t$ and a last column of size $r\le t$ gives the group count $st+r+a$, with $a=0$ or $1$ shared point. The four required local counts are $s,s+1,t+a,r+a$. For the first height take $F=39!$ and a sufficiently large prime $q\equiv1\pmod{5F^{39}}$. Put $m=(q-1)/5$. The notebook's cyclotomic construction gives a six-point design on $q$ points because $30\mid q-1$. This single prime supplies the local count $m$. [Truncation and adjacent heights](Erdos722SixHeights.lean) · [Cyclotomic prime-order construction](CyclotomicPairSpectrum.md)

At $s=30$, $t=m-1$, $a=1$, choose $r=29$ and $r=30$. The local counts $r+1$ are 30 and 31. The resulting group counts are $T=30m$ and $T+1$. Both also support 39 directions with invertible pairwise differences. For $T+1$, consecutive residues suffice because it is coprime to $F$. For $T$, form a product of finite fields over its exact prime-power factors. Every prime $p\le39$ dividing $T$ has $p^{39}\mid T$. Each larger prime already exceeds 39. The initial height $m-1$ is also coprime to $F$. Taking $q$ arbitrarily large gives the two heights above any prescribed bound. [Directions and field products](Erdos722SixDirections.lean) · [Adjacent-height theorem](Erdos722SixHeights.lean)

## From a finite interval to every large order

With $a=0$, the two heights shift any previously constructed group count $x\le T$ to both $sT+x$ and $sT+s+x$. Repeating with $s=30,39$ gives counts $C+30i+39j+z$ for bounded $i,j$ and $z=0,1$, with $3\mid C$. To cover a long interval, write $m=10i+13j$ by choosing $j=7m\bmod10$. When $117\le m\le10N$, this gives $0\le i\le N$ and $0\le j\le9$. Both admissible values of $z$ occur. [Long intervals](Erdos722SixIntervals.lean)

Pad each end of an interval by $100F$. For a requested group count $u$, round the full-column height $t$ so $t+1$ is a multiple of $F$ just above $u/(s+1)$. The other local count is $r+1=u-st$, congruent to $u$ modulo three for **both** $s=30$ and $s=39$. The padding pays for this rounding. Both endpoints of the inner interval can therefore be multiplied by 31 or by 40. [Rounding bounds](Erdos722SixDilation.lean)

For any positive inner endpoints $l<h$, normalize each $40^j$ by the largest power of 31 below or equal to it. Two normalized values fall in the same bin of width $1/l$. Clearing the denominators gives distinct scales $A<B$ with $lB\le hA$. Distinctness follows by counting factors of five. At depth $d$ the overlapping intervals cover $[lA^d,hB^d]$. For $d=30A$ the ratio of the extreme endpoints is at least 31. Multiplication by successive powers of 31 then covers every larger integer. This argument covers the full intervals before applying the residue test. [Nearby scales](Erdos722SixScales.lean) · [Tail coverage](Erdos722SixTail.lean)

## Scope and verification

This formalizes a classical existence result. Wilson proved asymptotic existence of pairwise balanced designs, and Keevash proved the general fixed-rank theorem. In print, Abel et al.'s Theorem 3.1 already gives existence at all admissible orders above 801. The Lean endpoint supplies an existential threshold. Small admissible orders really can fail. For instance, at order 16 each point would lie in three blocks. A point outside a six-point block would need six different blocks through it to meet the six points inside. The cutoff of 801 and the small-order exceptions belong to the published result. [Wilson's account](https://ir.cwi.nl/pub/13078/13078D.pdf) · [Abel et al.](https://doi.org/10.1002/jcd.20157) · [Keevash](https://arxiv.org/abs/1401.3665)

On 2026-11-28 the live DeepMind statement and its pinned copy shared a Git blob. Left to Solve lists the general theorem. The OMA entries concern a general reduction with absorption hypotheses and its rank-one case. The earlier cyclotomic result at block size six covered sufficiently large prime-power orders coprime to six. The new proof also covers, for example, all sufficiently large multiples of six congruent to six modulo 30. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17505) · [OMA rank one](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/17952) · [Earlier notebook theorem](CyclotomicPairSpectrum.md)

Lean 4.33.1 rebuilt the 33-module proof closure from an empty notebook cache. Each module passed a separate `leanchecker` run. The audit matched 17 named declarations and checked all 81 printed axiom reports against `propext`, `Classical.choice` and `Quot.sound`. A separate import of the pinned statement checked definitional equality of the two theorem types and accepted `eventually_six` as a proof of the specialization. [Replay instructions](../../README.md#replay)
