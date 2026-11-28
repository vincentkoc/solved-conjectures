# Rank-three Steiner systems through 50 points

For $3<k<n\le50$, `Erdos722.SmallOrders.spectrum` reduces existence of an ordinary $S(3,k,n)$ to the three predicates $S(3,5,41)$, $S(3,6,46)$ and $S(3,5,50)$. Away from those three pairs, existence is equivalent to membership in the table below. The three predicates remain explicit in the theorem. [Spectrum](Erdos722SmallSteinerOrders.lean.in) · [Kiermaier, Krčadinac and Wassermann, Table 1 and §3](https://doi.org/10.1007/s10623-026-01888-w)

| Block size $k$ | Orders $n$ realized here |
| --- | --- |
| 4 | $n\equiv2,4\pmod6$ |
| 5 | 17, 26 |
| 6 | 22, 26, 42 |
| 8 | 50 |

The pinned binomial tests admit 26 nontrivial pairs in this range. Fifteen have $k=4$. The other eleven are enumerated in `higher_admissible_iff`. They include $(7,22)$, which already violates the Fisher bound for the derived design, and $(7,37)$, which would give a plane of order six. The paper counts 25 admissible pairs after its design bound. The formal proof uses the existing lower bound $n\ge77$ for ordinary seven-point blocks. It gives the complete spectrum through $n=40$ and exactly $22,26,42$ for six-point blocks through $n=45$. In host notation, `divisibility_spectrum` says that away from the three pairs, existence is equivalent to $k\ne7$ together with all three pinned binomial divisibilities. The classification concerns finite orders at rank three in the canonical `Finset.IsBlockDesign` predicate. [Binomial enumeration](Erdos722SmallParameterTable.lean) · [Finite reduction](Erdos722SmallOrderSpectrum.lean) · [Bruck–Ryser transfer](Erdos722InversiveBruckRyser.lean.in) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean)

## The 42-point witness

Michael Kiermaier, Vedran Krčadinac and Alfred Wassermann constructed the 42-point design. The 42 integers in `Witness42.rows` transpose their published block list. Bit $j$ in row $i$ is set exactly when point $i+1$ is in the $(j+1)$-st block. The source file `3-42-6-1.des.gz` has SHA-256 `7cb360b06d2020600c985b67804c7feaf98e0acae5100e8bfaf2d7e9cb838b48`. The authors distribute it under CC BY 4.0. [Original dataset](https://doi.org/10.5281/zenodo.17153238) · [License](https://creativecommons.org/licenses/by/4.0/) · [Transposed witness](Erdos722SmallWitness42.lean)

Lean checks that each of the 574 columns has six points. For each of the $\binom{42}{3}=11{,}480$ triples, it computes the bitwise intersection $m$ of its three rows. The finite test requires $m<2^{574}$ and $2^{574}\bmod m=0$. These conditions force $m=2^j$ for a unique column $j<574$. The certificate lemma transfers this calculation to existence and uniqueness for each three-element finset, including after the columns are collected into a finset of blocks. [Incidence certificate](Erdos722SmallIncidenceCertificates.lean)

The other positive entries use Hanani’s quadruple spectrum, Witt’s finite-field sublines, the previously checked cyclic 26-point system studied by Grannell, Griggs and Phelan, and the twice-derived Witt design. The latter uses danielpuri1901’s finite certificate. The negative order-six plane input uses Dugongue’s formalization of Bruck–Ryser. [Quadruple spectrum](Erdos722QuadrupleSpectrum.lean) · [Sublines](../Erdos722ProjectiveSublines.lean) · [Cyclic witness](Erdos722SecondOrderTwentySix.lean) · [Witt source](https://github.com/danielpuri1901/erdos-lean-formalization/blob/6bd7a2cd9d9a50ba92c3d3b3ae1a2d64e241f4bd/Solution/Witt/Main.lean) · [Plane obstruction](https://github.com/lefttosolve2/open-math-agents/blob/819608fccbdb8a58c5b7f503607e93c05619731d/proofs/Erdos723.erdos_723.variants.bruck_ryser.lean)

## Punctured orders

Put $R_d=(4^d-1)/3$. For each $a\ge0$, each finite set $D$ of nonnegative indices and arbitrary nonnegative exponents $e_d$, `repunit_products` constructs an ordinary six-point-block design on

$$1+41^a\prod_{d\in D}R_d^{e_d}$$

points. Hanani’s inflation takes a punctured order $v$ to $4v+1$. Starting at the vacuous one-point design gives $R_0=0$ and every $R_d$. Wilson’s pointed product combines these with the published punctured order 41. For example, $a=1$ and a single factor $R_2=5$ give a design on 206 points. Empty products, zero exponents and $d=0$ have their usual natural-number meanings. The old generators $5,21,85,341$ are $R_2,R_3,R_4,R_5$. All $1+41^{d+1}$ lie outside the old four-generator family. [Hanani and Wilson constructions](https://www.math.iitb.ac.in/~niranj/papers/newcandelabras.pdf) · [Previous family](HananiTwoStemOrders.md) · [Product and separation proofs](Erdos722RepunitProducts.lean)

The identity $\gcd(R_a,R_b)=R_{\gcd(a,b)}$ makes the prime-index generators $R_p>1$ pairwise coprime. Moreover $41\mid R_{10}$, and the exceptional indices $2,5$ give $5,341$, both coprime to 41. Thus the extra generator is coprime to every prime-index generator. The least prime factor of $R_p$ is injective on the primes. For each prime in this infinite image, arbitrarily large constructed designs have punctured order divisible by that prime. The proof uses powers of $R_p$, so it also holds with any lower bound on the number of points. These are constructive consequences of the cited existence theorems. [Arithmetic and constructions](Erdos722RepunitProducts.lean) · [Unconditional specialization](Erdos722SmallSteinerOrders.lean.in)

The separation holds even if one interleaves the two old rules arbitrarily. Let $C$ be the least set containing zero and closed under $v\mapsto4v+1$ and multiplication. It contains the punctured Witt seed 21 and every finite product of powers of repunits. Every positive member of $C$ is odd. Inflating a positive member gives 5 modulo 8, while every power of a prime $q\equiv1\pmod8$ is 1 modulo 8. If a product is a power of $q$, both factors are powers of $q$. Induction on construction therefore excludes every positive power of $q$ from $C$. In particular all the nontrivial designs at orders $1+41^{d+1}$ lie outside this entire earlier construction. [Closure and separation](Erdos722PuncturedOrderClosure.lean)

## Replay and upstream status

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/research/erdos/722/replay-witt-minimum" --with-small-orders`. The runner checks the hashes of the host statements, Witt sources and Bruck–Ryser proof, compiles the combined dependency closure and independently replays its objects. To reuse both pinned downloads, supply `--archive PATH --bruck-ryser PATH`. [Replay runner](replay-witt-minimum)

The DeepMind statement and asymptotic packing PRs, the Left to Solve entry and the two Open Math Agents rank-one reduction PRs have different scopes. The authors’ 42-point design and their small-order table are published results. This contribution verifies the table to the stated exceptions and the constructive product family in Lean. [DeepMind statement](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing and covering](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [Open Math Agents reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505) · [Rank-one branch](https://github.com/lefttosolve2/open-math-agents/pull/17952)

The combined clean Lean 4.33.1 replays checked 88 distinct modules, comprising 81 notebook and adapter modules plus the six Witt modules and Bruck–Ryser. All 36 explicitly declared public definitions and theorems reported only subsets of `propext`, `Classical.choice` and `Quot.sound`. Nine direct examples compare the host statements and test finite orders, the product at 206 points and the vacuous one-point case.
