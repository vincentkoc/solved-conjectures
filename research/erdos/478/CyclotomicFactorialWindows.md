# Powers of factorials in short moving intervals

Let $p$ be prime, $k\ge0$, and $I=[a,b]\subseteq[0,p-1]$. Write $N=|I|$, $R=\max(N-2,0)$ and $h=\gcd(k,p-1)$. If $s$ is the number of distinct values of $(i!)^k\bmod p$ for $i\in I$, then
$$
R^2\le s^3\bigl(R+(h-1)(h-2)\bigr).
$$
For a target set of $s$ integer residues, let $M$ count the indices whose power residue belongs to that set. The same right-hand side bounds $\max(3M-2N-2,0)^2$. The target can be chosen after seeing the interval. The estimates include zero exponents and empty intervals. For $h=1$ the product $(h-1)(h-2)$ is zero. [Integer power residues and occupation](Erdos478PoweredFactorialProfiles.lean) · [three consecutive visits](Erdos478CosetUnionMass.lean)

## An infinite family

Take $t\ge2$ and $h=2t^{18}$. For every prime $p\equiv1\bmod h$, every interval of $N=h^2+2$ positive indices below $p$ has **more than $t^{12}$ distinct $h$th powers of factorials**. Every set of at most $t^{10}$ residues captures at most $(2N+2+3t^{33})/3$ positions. Thus at least a fraction $1/3-(2+3t^{33})/(3N)$ of the window lies outside even the best such target. For every cutoff $L$ there is a prime in the progression above both $L$ and $N$, so these windows exist and their length can be fixed independently of the prime cutoff. [Prime-family theorem](Erdos478CyclotomicWindowThresholds.lean)

Using just one adjacent quotient per starting index gives $N-1\le h s^2$, since each quotient coset contains $h$ field elements. For the displayed family that estimate gives a lower bound of order $t^9$. At $p=401$, $k=16$ and $I=[1,258]$, it gives $s\ge5$. The two-quotient estimate gives $65536\le466s^3$, hence $s\ge6$. Direct enumeration finds 25 power residues in this particular interval.

## Two successive quotients

Let $H\le\mathbb F_p^\times$ have order $h$. The relative cosets of three consecutive factorials are the cosets of $x=i+1$ and $x+1=i+2$. Write $P(x)=(xH,(x+1)H)$ for $x\ne0,-1$. Wilson's bijection counts ordered coincidences $P(x)=P(y)$ with $x\ne y$. The two multipliers $u=x/y$ and $v=(x+1)/(y+1)$ are distinct elements of $H$ different from $1$, and $y=(v-1)/(u-v)$ recovers the arguments. The full regular field therefore has exactly $(h-1)(h-2)$ off-diagonal coincidences. Betsumiya, Hirasaka, Komatsu and Munemasa give the bijection and second moment in Lemmas 2.1–2.2 and the variance in Theorem 2.3. [Paper](https://arxiv.org/pdf/1109.6539) · [formal bijection](Erdos478WilsonCyclotomicBijection.lean) · [finite-field moment](Erdos478CyclotomicProfileEnergy.lean)

Restrict to any $T$ successful starts whose three factorials all lie in a set $S$ of cosets. There are $T$ diagonal coincidences and at most the full off-diagonal count. Cauchy–Schwarz bounds $T^2$ by $T+(h-1)(h-2)$ times the number of pairs $(b/a,c/b)$ with $a,b,c\in S$. This factor is at most $|S|^3$. If $M$ individual factorials hit $S$, at least $3M-2N-2$ triples hit throughout. Finally the kernel of the $k$th-power map has order $\gcd(k,p-1)$, and its cosets correspond injectively to integer power residues. [Arbitrary selected triples](Erdos478FactorialCosetProfiles.lean) · [occupied cosets](Erdos478OccupiedFactorialCosets.lean) · [power map](Erdos478PoweredFactorialProfiles.lean)

There is a complementary full-interval consequence. If $d=[\mathbb F_p^\times:H]$ and $h\ge d^3+3$, every prescribed ordered pair of quotient cosets occurs at some triple $i!,(i+1)!,(i+2)!$ with $1\le i$ and $i+2<p$. The allowed $x$ run from $2$ to $p-2$, so there are $dh-2$ starts. With $E=dh-2+(h-1)(h-2)$, the difference $(dh-2)^2-(d^2-1)E$ equals $h(h-d^3-3)+3d(d-1)h+4>0$. At $p=23$ the subgroup of order 11 meets the threshold exactly for $d=2$. [Positive-index coverage](Erdos478CompleteFactorialProfiles.lean)

## Relation to Erdős 478

The host asks whether the image of the unpowered factorials on $[1,p-1]$ has cardinality asymptotic to $(1-e^{-1})p$. Taking $k=1$ on this interval recovers exactly the image in the host numerator. The bounds above concern occupation of quotient groups and power residues in moving windows. The limiting constant in the host remains open. Klurman and Munsch study distinct unpowered factorials in short intervals, and Garaev, Luca and Shparlinski give character-sum estimates with explicit dependence on $p$. The earlier notebook bound controls visits to one multiplicative coset through the successive gaps between selected indices. [Pinned host](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Klurman–Munsch](https://arxiv.org/abs/1505.01198) · [Garaev–Luca–Shparlinski](https://arxiv.org/abs/math/0403422) · [earlier coset result](https://github.com/vincentkoc/solved-conjectures/pull/455)

Live searches of DeepMind issues and PRs, Left to Solve, Open Math Agents and the notebook found the formal problem and its earlier companion bounds. They did not identify a matching formal declaration for these moving power windows. Historical priority for the factorial applications is unestablished. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [host PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents)

## Verification

From the pinned Formal Conjectures checkout run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos478CyclotomicWindowThresholds`. Lean 4.33.1 independently replayed all eleven modules in the import closure. All eleven objects matched the development build byte for byte. The audit checked all 45 public declarations against `propext`, `Classical.choice` and `Quot.sound`. Eleven comparisons covered the host limit, the exponent-one identification, arbitrary integer targets, boundary cases and concrete prime examples.

Independent enumeration checked the cyclotomic second moment at 192 prime/subgroup pairs and the occupation inequality on 423,482 windows. The unrounded two-quotient lower bound exceeded the single-quotient lower bound on 162,466 of those windows. A separate enumeration checked 2,076,152 target/window/exponent cases at primes through 13 and all 185 qualifying prime/subgroup pairs for the positive-domain coverage criterion at odd primes below 400.
