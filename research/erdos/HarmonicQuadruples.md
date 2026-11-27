# Erdős 722 — harmonic quadruples

For every positive integer $d$, the projective line over $\mathbb F_{3^d}$ supports a Steiner quadruple system on $3^d+1$ points. Every triple belongs to exactly one four-point block. At $d=1$ there is a single block. For all $d\ge2$ the orders lie outside the notebook’s binary family: $3^d+1$ is greater than eight and is congruent to two or four modulo eight. The Lean proof also gives such an order above any prescribed cutoff. [Proof](Erdos722HarmonicQuadruples.lean) · [Binary family](NOTES.md)

This finite family is classical. Huber describes it using the images of the four-point projective line under fractional linear transformations. Here a symmetric coefficient equation gives a direct construction. The kernel checks the incidence property used by the pinned Erdős declaration. The general theorem covers all sufficiently large admissible orders for each pair $1\le r<k$. This proof covers $(r,k)=(3,4)$ at the indicated orders. [Huber, Theorem 1(2)](https://arxiv.org/html/math/0401117v1) · [Pinned Erdős 722](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean) · [Keevash, Theorem 1.4](https://arxiv.org/abs/1401.3665)

## Completing a triple

Assign the factor $X+a$ to a finite point $a$ and the factor $1$ to infinity. Four distinct points form a block when the coefficient of $X^2$ in the product of their factors vanishes. For three distinct finite points $a,b,c$, the fourth point is

$$
\begin{cases}
-\dfrac{ab+bc+ca}{a+b+c}, & a+b+c\ne0,\\[4pt]
\infty, & a+b+c=0.
\end{cases}
$$

A triple $a,b,\infty$ completes to $-a-b$. For example, $0,1,-1$ completes to infinity over every field of characteristic three.

To see why neither degeneracy nor repetition can spoil the construction, write $[u:v]$ for a point and $[x,y]=u_xv_y-v_xu_y$ for the determinant of two representatives. If $x,y,z$ are distinct, the middle coefficient for the multiset $x,x,y,z$ is $[x,y][x,z]\ne0$ in characteristic three. For any triple with factor product $P$, the middle coefficient after adjoining $[u:v]$ is $u[X^2]P+v[X]P$. The determinant identity supplies a point where this linear form is nonzero. It therefore has a unique projective zero, and that zero lies outside the triple. This argument works over infinite fields of characteristic three as well.

## Lean declarations and replay

All names below are in `Erdos722.Harmonic`.

| Declaration | Coverage |
| --- | --- |
| `existsUnique_completion` | Unique completion on the projective line over any field of characteristic three. |
| `blocks_isBlockDesign` | The four-sets defined by the coefficient equation satisfy the upstream `Finset.IsBlockDesign 3 4` on a finite labelled ground set. |
| `exists_ternary_quadruple_design` | The design on `Fin (3 ^ d + 1)` for every positive `d`. |
| `order_ne_power_of_two` | Every order in the family with `d ≥ 2` differs from every power of two. |
| `arbitrarily_large_nonbinary_orders` | For every cutoff there is a larger nonbinary order carrying a Steiner quadruple system. |

The DeepMind statement PR added the question, and the packing PR treats a different incidence condition. Searches of open and closed DeepMind and OMA records, the LTS solved ledger, the OMA proof and reduction trees, and this notebook found no matching harmonic-quadruple formalization on 2026-11-28. LTS listed Erdős 722 as unsolved and unclaimed. [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Packing PR](https://github.com/google-deepmind/formal-conjectures/pull/4248) · [LTS target](https://lefttosolve.com/p/Erdos722.erdos_722) · [OMA search](https://github.com/GuillaumeBAUD-coder/open-math-agents/pulls?q=is%3Apr+%22Steiner+quadruple%22)

Use Lean 4.33.1 with `FC` set to the checkout pinned above. Run from the notebook root. The five axiom reports list only `propext`, `Classical.choice` and `Quot.sound`.

```bash
set -e
proof="$PWD/research/erdos/Erdos722HarmonicQuadruples.lean"
out="$(mktemp -d)"
cd "${FC:?set FC to the pinned checkout}"
lake build FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
lake env lean -DwarningAsError=true -R "$(dirname "$proof")" -o "$out/Erdos722HarmonicQuadruples.olean" "$proof"
lake env bash -c 'LEAN_PATH="$1:$LEAN_PATH" leanchecker -v Erdos722HarmonicQuadruples' _ "$out"
unlink "$out/Erdos722HarmonicQuadruples.olean"
rmdir "$out"
```
