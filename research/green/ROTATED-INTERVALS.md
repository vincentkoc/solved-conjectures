# Green 33 through rotated integer sumsets

For $B\subseteq[1,N]$ and $0\le t<N$, write $B_t=\{1+((b-1+N-t)\bmod N): b\in B\}$. Form $B_t+B_t$ with **ordinary integer addition**. Green 33 holds if and only if there are lengths $N\to\infty$ and sets $B\subseteq[1,N]$ of size $k$ such that
\[
 \frac{k}{\sqrt N}\to\sqrt2,\qquad
 \frac{\sum_{t=0}^{N-1}|B_t+B_t|}{N\binom{k}{2}}\to1 .
\]
The quantified lengths may be a subsequence. The formula uses the distinct-pair denominator from Erdős 840. Each integer sumset includes diagonal sums. The finite count of all unordered pairs is $\binom{k+1}{2}$, whose difference from the denominator is $k=o(N)$ at this scale. [Integer equivalence and exact count](Green33RotatedIntervals.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

## Undoing a cut

Let $E$ be the unordered pair count minus the size of the cyclic sumset. Write $e_t=\binom{k+1}{2}-|B_t+B_t|$. Cutting can separate pairs of the same cyclic sum into two integer sums, so $e_t\le E$. Conversely, for **any prescribed family** with $k=O(\sqrt N)$ and $N\to\infty$,
\[
 E/N\to0 \quad\Longleftrightarrow\quad N^{-2}\sum_t e_t\to0.
\]
This equivalence allows the cut to affect many individual representations. The earlier cyclic approximate-cover theorem converts its critical-size case into the statement of Green 33. [Mean-excess theorem](Green33RotatedIntervals.lean) · [Cyclic excess equivalence](APPROXIMATE-COVERS.md)

For an explicit bound, fix $1\le 2d\le N$, and let $W_t$ count the labels in the first $2d$ places after cut $t$. Fix a cyclic target $z$. For at least $d$ cuts, its residue after translating both summands lies in $[0,2d)$. At each such cut write the residue as $r$. The only possible integer sums in zero-based coordinates are $r$ and $r+N$. The excess at $r+N$ contributes to $e_t$. A pair summing to $r$ has both elements in the short window. Summing gives
\[
 dE\le \sum_t e_t+\sum_t\binom{W_t+1}{2}.
\]
The count of cuts holds at odd and even moduli. [Averaged finite inequality](Green33RotatedIntervals.lean)

For any reference cut $v$, pairs from the window have at most $8d$ distinct integer sums after cutting at $v$. Their modular sums fit in an arc of at most $4d$ residues, with at most two integer lifts per residue. Thus $\binom{W_t+1}{2}\le8d+e_v$, and $\sum_t W_t=2dk$. The resulting bound is
\[
 dE\le\sum_t e_t+dk\bigl(1+\lfloor\sqrt{16d+2e_v}\rfloor\bigr).
\]
If $\sum_t e_t=o(N^2)$, choose $d=1+\lfloor\sqrt{\sum_t e_t}\rfloor$ and a cut of minimum excess. Eventually $2d\le N$, $e_v\le d$ and $d=o(N)$. Dividing the bound by $dN$ proves $E/N\to0$. [Window estimate and reverse bound](Green33RotatedIntervals.lean)

## Relation to Erdős 840

Erdős and Freud introduced quasi-Sidon sets using the number of distinct ordinary integer sums. Pikhurko studies their possible size. The pinned Erdős predicate asks for one set at **every** interval length. The new Green equivalence requires rotation-averaged behavior along **unbounded** lengths. Whether the single-set Erdős predicate at $\sqrt2$ suffices for Green 33 remains open. The notebook's forward implication from Green 33 to the all-length Erdős predicate also remains available. [Erdős–Freud](https://doi.org/10.1016/0022-314X(91)90083-N) · [Pikhurko](https://pikhurko.github.io/E/Pikhurko06dm.pdf) · [Pinned Erdős 840](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/840.lean) · [All-length implication](QUASI-SIDON-INTERVALS.md)

The closed Green issue and its merged PR formalized the statement. Left to Solve listed no solution for Green 33 or Erdős 840. Targeted DeepMind, Open Math Agents and personal tracker searches found no matching rotation-averaged equivalence. The OMA proofs concern the unconditional Erdős–Freud lower bound. [Green issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Erdős 840 proof links](https://github.com/google-deepmind/formal-conjectures/pull/8281) · [OMA lower bound](https://github.com/lefttosolve2/open-math-agents/pull/1478) · [OMA shorter proof](https://github.com/lefttosolve2/open-math-agents/pull/11577)

Replay **Green33RotatedIntervals** with the [notebook runner](../../scripts/replay-research). Six notebook modules received fresh Lean 4.33.1 compilation and independent kernel checks. All 54 axiom reports used only standard axioms. Exhaustive small checks covered 29,920 choices of seed and window width at orders 2 through 12.
