# Hanani’s twelvefold construction for Steiner quadruple systems

If a Steiner quadruple system exists on $v\ge3$ points, one exists on $12v-10$ points. Taking $v=2^{d+2}$ gives the orders $38,86,182,374,\ldots$. The declaration `Erdos722.HananiTwelve.exists_twelvefold` takes a finite family on `Fin v` satisfying `H.IsBlockDesign 3 4` and returns a family on `Fin (12*v-10)` satisfying the same predicate. This is Hanani’s classical construction. The earlier notebook families did not cover these orders. [Lean recurrence and binary family](Erdos722HananiTwelve.lean) · [Hanani, *On quadruple systems* (1960)](https://doi.org/10.4153/CJM-1960-013-3)

## Two shared points

Distinguish a point $\infty$ in the base system. Replace each of the $v-1$ ordinary points with twelve points labelled by $\mathbb Z/12\mathbb Z$, and replace $\infty$ with two points shared by every local system. A base block avoiding $\infty$ supplies all transversals whose four labels sum to zero. Three labels determine the fourth. A base block containing $\infty$ supplies a copy of a 38-point system on three columns and the two shared points. The restriction to any one column and the shared points is the same labelled 14-point system. [Two-stem gluing proof](Erdos722StemInflation.lean)

For a triple meeting three ordinary columns, the base system determines a unique base block. A triple meeting exactly two ordinary columns uses the unique base block containing those columns and $\infty$. The remaining triples lie in one column together with the two shared points. The 14-point restriction gives them the same fourth point in every local 38-point system containing that column. This proves unique completion for each triple. The gluing lemma allows any finite abelian group of labels and any pair of templates with the stated compatibility. [Gluing and its hypotheses](Erdos722StemInflation.lean)

## Finite certificates

The small template has 91 blocks. Label its two layers by $0,\ldots,6$ and $7,\ldots,13$. Translate these thirteen starters by $\mathbb Z/7\mathbb Z$ within each layer to recover all blocks.

```text
0 1 2 4    0 1 5 12   0 1 8 9    0 2 8 10   0 3 8 11
0 3 10 12  0 3 9 13   0 2 9 12   0 1 10 11  0 2 11 13
0 1 7 13   0 7 11 12  7 8 9 12
```

The large template uses the mixed blocks of Hanani’s construction at $v=4$. It has 2,109 blocks covering the 8,436 triples. The three maps $e_i$ take $x<12$ to $12i+x$ and take $12,13$ to the shared points $36,37$. Each certificate stores a fourth point for every sorted triple $a<b<c$, as a six-bit field at position $\binom b2+a$ in row $c$. Lean checks the completion identities and verifies $e_i(F(a,b,c))=G(e_i(a),e_i(b),e_i(c))$ for all three maps. The completion lemma converts these identities directly to the canonical block-design predicate. [Finite certificates](Erdos722HananiTemplates.lean) · [Completion lemma](Erdos722QuadCompletion.lean) · [Hanani construction formulas in Sage](https://github.com/sagemath/sage/blob/c7cb3ca95a456a64ddc1364f1f4a89212354f522/src/sage/combinat/designs/steiner_quadruple_systems.py)

## Orders and the upstream problem

The theorem `new_order` excludes $12v-10$ for every $v\ge2$ from the closure of $2^d$ and $3^d+1$ under products and $n\mapsto3n-2$. Apart from order one, the old orders are even. A product of two nontrivial orders is divisible by four, and tripling gives order one modulo three. The nontrivial seed orders above two are also divisible by four or one modulo three. The new orders are two modulo twelve. [Order invariant](Erdos722HananiTwelve.lean)

There is a separate conditional spectrum theorem. Starting with $2,4,14,38$, the verified doubling, tripling and twelvefold steps would give every $n\equiv2,4\pmod6$ if the following remaining constructions are supplied for inputs $m\ge4$.

| Output order | Input condition on an SQS of order $m$ |
| --- | --- |
| $3m-8$ | $m\equiv2\pmod{12}$ |
| $3m-4$ | $m\equiv10\pmod{12}$ |
| $4m-6$ | $m\equiv2,4\pmod6$ |

The finite recursion is proved by strong induction and a residue check modulo 72. For $n\ge4$, `residues_of_divisibility` proves that the exact binomial hypotheses of `Erdos722.erdos_722` at $r=3,k=4$ imply one of the two required residues. The general upstream declaration quantifies over all $1\le r<k$ and all sufficiently large admissible orders. The unconditional twelvefold result supplies a family at $r=3,k=4$. The three rows above remain explicit hypotheses of the full spectrum reduction. [Reduction](Erdos722HananiTwelve.lean) · [Pinned upstream declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Canonical block-design predicate](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjecturesForMathlib/Combinatorics/Hypergraph/Finite.lean)

The 2026-11-28 overlap check found the upstream statement, a separate packing problem and an OMA Hanani entry for Erdős 1026. Left to Solve lists the general Erdős 722 statement as a known result awaiting formalization. The notebook contribution concerns this specific recurrence and its formal scope. [DeepMind statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing problem](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [Left to Solve](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA Hanani entry](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/684)

## Replay

The notebook replay discovers the four sources and their dependencies. The scoped independent check builds the four new modules and four earlier dependencies with Lean 4.33.1 in an empty output directory, treats warnings as errors, and runs `leanchecker` on all eight. The five printed declarations in the recurrence module report only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
