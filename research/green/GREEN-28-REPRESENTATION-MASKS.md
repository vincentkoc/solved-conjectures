# Green 28 and representation counts modulo a prime

Let $A,B$ be the supports of the two integer laws after translating each minimum to zero. For each total $n$ write $r_n=|\{(i,j)\in A\times B:i+j=n\}|$. Define $K=\{j\in B:r_j=1\}$ and write $M_E(X)=\sum_{i\in E} X^i$ for a support mask. Both $K$ and the polynomials in the following test are determined by the supports.

**Coprimality criterion.** Suppose a prime $p$ divides each $r_n$ other than one. If $M_A$ and $M_K$ are relatively prime in $\mathbb F_p[X]$, a uniform independent sum forces both marginals to be uniform. The sizes and widths of the supports and all positive atom masses are unrestricted. The result is symmetric after exchanging the two inputs and recomputing $K$. `uniform_of_coprime_column_mask` uses the original integer PMFs and the upstream definitions of uniformity and independent sum. [Lean statements and proofs](Green28RepresentationMasks.lean) · [Pinned Green 28](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean)

## The singleton rectangle

Let $H\subseteq A$ and $J\subseteq B$ consist of the sites with the same mass as the respective left endpoint. For a uniform sum, a pair $(i,j)$ gives a uniquely represented total exactly when $i\in H$ and $j\in J$. In particular $J=K$, since $0\in H$. Every singleton fibre therefore contributes one to both $M_A M_B$ and $M_H M_K$. Every other fibre contributes a multiple of $p$ to the former and zero to the latter. Hence
\[
 M_A M_B=M_H M_K \quad\text{in }\mathbb F_p[X].
\]
If $M_A$ and $M_K$ are coprime, $M_A$ divides $M_H$. These polynomials are monic of the same degree because the rightmost atom has the left endpoint mass. Thus $M_H=M_A$, and comparison of coefficients gives $H=A$. The first law is uniform, so the rational-ratio criterion gives uniformity of the second law too. [Singleton rectangle and endpoint masses](Green28UnpairedSites.lean) · [Rational-ratio theorem](Green28UniformSums.lean)

## Two consequences

- If $A$ is wider than $B$ and $M_A$ is irreducible modulo $p$, the degree of the nonzero $M_K$ gives coprimality automatically. In characteristic two, a counterexample with such a wider mask must therefore have a total with an **odd** number of representations, at least three. This permits arbitrary counts at all other totals.
- If $|A|$ is odd, all nonsingle counts are even and $K=\{0,2^k\}$, then both laws are uniform. In characteristic two, $M_K=1+X^{2^k}=(1+X)^{2^k}$ while $M_A(1)=1$. This criterion uses only cardinality, two observed singleton columns and the parity of the counts. [Checked corollaries](Green28RepresentationMasks.lean)

## Scope and replay

The unrestricted conjecture remains open. Related work studies coefficient patterns in low degrees, symmetric supports and separated blocks, and the case of a trinomial factor. The live duplicate search included the DeepMind issue and statement PR, the Left to Solve entry, both OMA reductions, and the open reduction's pinned Lean source. [Hare](https://arxiv.org/abs/2307.07363) · [Hasanbegović](https://arxiv.org/html/2611.14596v1) · [Trinomial manuscript](https://hexagonmath.org/pdf/2611.00674v2) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA polynomial reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793)

Lean 4.33.1 rebuilt the pinned upstream declaration and all five notebook modules. Each notebook module passed independent kernel replay. All 32 axiom reports listed exactly `propext`, `Classical.choice` and `Quot.sound`. For focused replay in the pinned Lake environment, give `Green28RepresentationMasks` to the [notebook runner](../../scripts/replay-research).
