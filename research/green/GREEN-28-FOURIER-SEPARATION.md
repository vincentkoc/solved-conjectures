# Green 28 · Fourier separation for uniform progressions

Let $P,Q$ be arbitrary integer probability laws. Write $D(P)$ for the law of $X-X'$ for two independent draws from $P$. If $U$ is uniform on a finite arithmetic progression of at least two points, then
\[
d_{\rm TV}(P*Q,U)+d_{\rm TV}(D(P),D(Q))>\frac1{52}.
\]
The bound is independent of the length, spacing and translation. Both inputs can have infinite support and can charge points outside the target lattice. In particular every convolution square lies more than $1/52$ from $U$. The same holds for any two factors with identical difference laws, including translates or reflections of a common law. [`progression_difference_gap`, `equal_differences_gap`, `iid_progression_gap`](Green28FourierSeparation.lean)

## The two frequencies

Write $\delta=d_{\rm TV}(P*Q,U)$, $\eta=d_{\rm TV}(D(P),D(Q))$. For $k$ terms and positive spacing $d$, choose $t=\pi/(kd)$. Summing the geometric series of phases on the progression gives $|\widehat U(t)|\ge2/\pi$ and $\widehat U(2t)=0$. Translation changes only the phase. For $A=|\widehat P(t)|$ and $B=|\widehat Q(t)|$ the Lean bounds give
\[
4/\pi-1-4\delta-\sqrt{2\delta}\ \le\ |A^2-B^2|\ \le\ 2\eta .
\]
In particular an **exact** uniform progression forces $\eta\ge2/\pi-1/2$. The rational $1/52$ follows by substituting $\delta+\eta\le1/52$ in the displayed bounds. Sharpness of this rational constant remains open here. [`progression_power_gap` and `difference_power_close`](Green28FourierSeparation.lean)

For a random phase $|Z|=1$, the variance identity gives $|\mathbb E Z^2-(\mathbb E Z)^2|\le1-|\mathbb E Z|^2$. Thus $2|\mathbb E Z|^2\le1+|\mathbb E Z^2|$. Apply this to both factors. At twice the frequency the product of their moduli is at most $2\delta$, so at least one is at most $\sqrt{2\delta}$. At the first frequency their product is at least $2/\pi-2\delta$. The difference law has Fourier coefficient $|\widehat P(t)|^2$, and changing a probability law by $\eta$ changes any unit-phase expectation by at most $2\eta$. The general Lean lemma accepts an arbitrary target and a character of any finite additive quotient. The doubling inequality belongs to the classical characteristic-function literature. [General bound](Green28FourierSeparation.lean) · [Heathcote and Pitman, *An inequality for characteristic functions*](https://doi.org/10.1017/S0004972700044191)

## Relation to the conjecture

Pinned Green 28 asks whether finite independent inputs are each uniform on their support whenever their sum is exactly uniform on its support. This result uses the pinned independent-sum operation and gives a quantitative obstruction for progression targets. It leaves general finite target sets open. For exact interval targets, Zhigljavsky, Golyandina and Gryaznov characterized the decompositions. For approximate interval targets, the notebook constructs unequal factors with vanishing output error and both marginals far from every finite uniform law. The estimate above forces their difference laws to stay separated. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [Exact interval deconvolution](https://doi.org/10.1016/j.spl.2016.06.006) · [Approximate interval construction](GREEN-28-LACUNARY-MIXTURES.md)

The source check covered the DeepMind issue and formalization, the Left to Solve entry, the linked OMA polynomial reductions and small cases, and the personal notebook. I found no matching total-variation estimate in those sources. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [Second reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [Two-site case](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Degree-five case](https://github.com/lefttosolve2/open-math-agents/pull/29600)

Replay `Green28FourierSeparation` in the pinned Lake environment. The dependency closure contains eleven notebook modules and 91 printed axiom reports, including ten in this file. [Notebook runner](../../scripts/replay-research)
