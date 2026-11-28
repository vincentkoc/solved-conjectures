# Many primes with a coefficient-two factorial deficit below every large cutoff

Let $A_p=\{j!\bmod p:1\le j<p\}$ and $F_p=p-1-|A_p|$. Write $T=\log\log X$. For every fixed $0<\beta<1/2$ and every sufficiently large natural cutoff $X$, at least
$$
  \exp\!\left(\exp\!\left(\beta\frac{T\log\log T}{\log T}\right)\right)
$$
primes $p\le X$ satisfy $F_p\log T\ge2T$. Both the number of witnesses and the required deficit depend on $X$. All the counted primes can be chosen to split the **same** growing list of even factorial-gap polynomials completely, with distinct roots across the entire list. [Lean endpoints](Erdos478CompleteDeficitTradeoff.lean) · [Pinned factorial image](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

More generally, take $c>0$, $\alpha,\beta\ge0$, $c/2+2\alpha\le1$ and $\beta<c/4$. For all sufficiently large $X$,
$$
\#\{p\le X:p\text{ prime},\ F_p\log T\ge cT\}
\;\ge\; \exp\!\left(\exp\!\left(\alpha T+\beta\frac{T\log\log T}{\log T}\right)\right).
$$
For example, at least $\exp((\log X)^{1/8})$ primes through $X$ satisfy $F_p\log T\ge3T/2$. This takes $c=3/2$, $\alpha=1/8$, $\beta=0$, exactly on the boundary. [General tradeoff](Erdos478CompleteDeficitTradeoff.lean)

## Counting complete splitting

For $n\ge1$ and $L\ge0$, set
$$
 W=2^{(2n+4)^{n(n+1)+38}(L+1)^2}.
$$
More than $2^L$ primes through $W$ split each polynomial $X(X-1)\cdots(X-2i+1)-1$, for $1\le i\le n$. The product is separable at each prime. Its $n(n+1)$ roots give distinct upper endpoints of repeated factorial residues, so $F_p\ge n(n+1)$. [Finite multiplicity](Erdos478ManyCompleteWitnesses.lean) · [Collision endpoints](Erdos478DisjointGapFamilies.lean)

If there were at most $2^L$ witnesses, their product $C$ would be at most $W^{2^L}$. Apply the complete-splitting construction to the same gap polynomials while excluding every prime divisor of $C$. The Schur sieve charges the extra product through its double logarithm. With $A=(2n+4)^2$, the resulting bit parameter is at most $A^7(L+1)$. The chosen prime is still at most $W$, contradicting the definition of $C$. [Exclusion estimate](Erdos478ExclusionBits.lean) · [Complete-splitting construction](Erdos478EffectiveEvenComplete.lean) · [Counting argument](Erdos478AvoidanceCount.lean)

## Why the boundary is included

Choose $n=\lceil\sqrt{cT/\log T}\rceil$. Then $n(n+1)\log T\ge cT$. The factor $1/\sqrt{\log T}$ in this choice saves a term in the logarithm of the prime ceiling. For every $\gamma<c/2$ and all sufficiently large $T$,
$$
 (n(n+1)+38)\log(2n+4)
 \le \frac{cT}{2}-\gamma\frac{T\log\log T}{\log T}.
$$
To control rounding, put $y=\sqrt{cT/\log T}$. Eventually $43\log T\le y$ since $(\log T)^3=o(T)$. The estimates $n(n+1)+38\le y^2+43y$ and $2n+4\le3y$ then give the displayed bound. [Gap cutoff proof](Erdos478CompleteGapRounding.lean)

Set $a=\alpha T+\beta T\log\log T/\log T$ and $L=\lceil2e^a\rceil$. Then $2^L\ge\exp(\exp a)$, and the cost $2\log(L+1)$ is at most $2a+2\log4$. Choose $2\beta<\gamma<c/2$. The remaining saving absorbs the constant even when $c/2+2\alpha=1$, giving $W\le X$. [Count and ceiling estimates](Erdos478CompleteCountRounding.lean)

## Comparison and scope

The earlier notebook result gave coefficient two at individual primes. Its growing-cutoff counting theorem gave coefficient one with a smaller witness count. Here the coefficient-two threshold holds at every sufficiently large cutoff with the multiplicity displayed above. Banks, Luca, Shparlinski and Stichtenoth obtained a coefficient-one subsequence in the literature. Klurman and Munsch proved an unconditional lower bound for the mean deficit with an implicit constant. The proof here counts specified primes by an elementary sieve. The limiting proportion $|A_p|/p\to1-1/e$ in Erdős 478 remains open. [Earlier subsequence](DoubledFactorialDeficit.md) · [Earlier counting theorem](AbundantFactorialDeficit.md) · [Banks et al., Theorem 3](https://journals.tubitak.gov.tr/math/vol29/iss2/6/) · [Klurman and Munsch, Theorem 2.1](https://www.numdam.org/item/10.5802/jtnb.974.pdf)

The live DeepMind statement matched the pinned source on 2026-11-28. Left to Solve lists the limit as research open. A search of the current Open Math Agents repository for the declaration returned no matching entry. [DeepMind tracking issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA search](https://github.com/lefttosolve2/open-math-agents/issues?q=Erdos478)

Lean 4.33.1 rebuilt the 34-module closure from an empty notebook cache and replayed each module with an independent kernel process. All 79 printed axiom reports, including the ten named checks, used only `propext`, `Classical.choice` and `Quot.sound`. A separate import of the pinned conjecture checked its precise factorial image and prime-filter limit, then checked the coefficient-two counting statement at that same image. [Replay instructions](../../README.md#replay)
