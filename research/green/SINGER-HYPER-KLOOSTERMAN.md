# Singer sumsets and hyper-Kloosterman sums

Let $F\subset K$ be finite fields, $q=|F|$, and $L:K\to F$ a surjective linear functional. In the scalar quotient $G=K^\times/F^\times$ of order $v$, let $D$ consist of the projective points of $\ker L$, and set $k=|D|$. Write $P_m(c)$ for the number of ordered products of $m$ elements of $D$ giving $c\in G$, with repeats allowed. For every $m\ge1$, every lift $w\in K^\times$ of $c$, and every nontrivial additive character $\psi$ of $F$, the exact identity is
\[
 q^m\!\left(P_m(c)-\frac{k^m}{v}\right)
 = \sum_{a\in F^\times}\operatorname{Kl}_m(aw;\psi\circ L)
   -\frac{(-1)^m}{v}.
\]
Here the unnormalized $\operatorname{Kl}_m(z;\chi)$ sums $\chi(x_1+\cdots+x_m)$ over ordered tuples of units with product $z$. Lean proves both this tuple convention and the scalar-quotient identity in arbitrary characteristic and extension degree. [Exact identity, tuple formula and finite error](Green33SingerKloosterman.lean)

## Cubic extensions and Green 33

When $|K|=q^3$, the quotient is cyclic of order $v=q^2+q+1$ and $k=q+1$. Take the actual cyclic labels of $D$, write $S=D+D$, and let $I(c)=|S\cap(c-S)|$. For the two layers $B_t=\{2a:a\in D\}\cup\{1+2t-2a:a\in D\}$ in $\mathbb Z/(2v)\mathbb Z$, the finite conclusions are
\[
\begin{aligned}
  |P_4(c)-k^4/v| &\le 4q\sqrt q+1,\\
  |4I(c)-v| &\le q(4\sqrt q+10),\\
  \bigl|4\,\#(B_t+B_t)-7v\bigr| &\le q(4\sqrt q+20).
\end{aligned}
\]
These estimates hold at every center and axis. As $q\to\infty$ they give $I(c)/v\to1/4$ and $|B_t+B_t|/(2v)\to7/8$. Any full cyclic basis retaining $B_t$ has limiting lower size coefficient at least $(3+\sqrt3)/(2\sqrt2)$. The field, functional and center may vary along the sequence. [Finite inequalities, limits and repair floor](Green33SingerAllCharacteristics.lean)

**Analytic hypothesis in Lean.** These cubic bounds assume $|\operatorname{Kl}_4(z;\psi\circ L)|\le 4|K|\sqrt{|K|}$ for each $z\ne0$. This is the classical Deligne estimate in the above normalization. The formal proof supplies the reduction and all combinatorial steps. The analytic estimate itself is a named hypothesis. The earlier binary proof gives the two limits without that hypothesis. Green 33 asks about unrestricted cyclic bases of size coefficient $\sqrt2$ and remains open. [Katz, Chapter 4, §§4.0–4.1](https://web.math.princeton.edu/~nmk/Katz-GKM.pdf) · [Unconditional binary proof](SINGER-REFLECTED-COVERAGE.md) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Proof and checks

Sum the additive phase over each scalar orbit. Character orthogonality gives $q\,1_D-1$. Summing a function over fibers of a group homomorphism commutes with convolution. Replacing a function by a constant translate changes each convolution power by a constant, which its total sum determines. The total phase over $K^\times$ is $-1$. These facts give the identity, including its constant term. In degree three, simultaneous vanishing of $L(x)$ and $L(wx)$ at a nonscalar $w$ imposes two independent linear conditions. Counting the nonzero scalar orbits proves the perfect-difference property for these same cyclic labels. The diagonal correction then bounds $4I(c)-P_4(c)$ between $0$ and $4k$. [Cubic parameters](Green33SingerKloosterman.lean) · [Diagonal correction](Green33ReflectedLayers.lean) · [Singer’s projective difference sets](https://doi.org/10.1090/S0002-9947-1938-1501951-4)

The independent Lean 4.33.1 replay rebuilt and kernel-checked 12 notebook modules. The 93 axiom reports across the closure use only standard Lean axioms. Separate comparisons checked the literal pinned Green 33 basis and size predicates, and proved equality with the published Tau Ceti definition at every positive rank. Integer histograms independently verified the rank-four identity and doubled sumset counts at all 241 centers over $q=2,3,5,7,11$. The prime-power Singer formalization of Hulak, Ramos and de Queiroz establishes the classical Sidon construction. Searches of the DeepMind, Open Math Agents and personal trackers returned no matching Kloosterman reduction. Left to Solve listed Green 33 as open. [Tau Ceti’s pinned definition](https://github.com/TauCetiProject/TauCeti/blob/a314c9d0c4aa4a3f4617a246b3bf92621cb0afe3/TauCeti/NumberTheory/HyperKloosterman/Basic.lean) · [Singer formalization](https://arxiv.org/abs/2605.03274) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
