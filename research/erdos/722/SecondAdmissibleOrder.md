# The next Steiner order after an inversive plane

At block size five, the first two nontrivial orders of an ordinary Steiner 3-design are **17 and 26**. Witt's sublines give order 17. Ten cyclic starters on 26 points attain the next admissible order. The order-26 system is classical and was studied by Grannell, Griggs and Phelan. The notebook checks the triple coverage directly. [Two ordinary minima and the starters](Erdos722SecondOrderTwentySix.lean) · [Witt construction](../Erdos722ProjectiveSublines.lean) · [Grannell, Griggs and Phelan](https://doi.org/10.1016/S0304-0208(08)72887-1)

## Exact arithmetic for every prime power

Let $q\ge2$ be a prime power and take block size $q+1$. Put $F(z)=2z(z+1)(2z+1)$ and define $Z(q)$ to be the least positive $z$ such that $q+1\mid F(z)$. The first order **above** $q^2+1$ satisfying all three binomial conditions of Erdős 722 is
$$
N(q)=q(q-1)\max(2,Z(q))+2.
$$
It is also the first such order admitting an integer-weighted design of index one. At $q=2$ the block size equals the rank, outside the strict inequality in the host. The distinction at $Z=1$ matters exactly when $q+1$ divides 12. In those cases $F(2)=60$ also passes the test. [Least signed order](Erdos722SecondSignedOrder.lean) · [Signed index and divisibility](Erdos722SteinerWeights.lean) · [Pinned host statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/722.lean)

More precisely, an order $v>q^2+1$ satisfies the three tests if and only if it has one of the following forms for a positive $z$ with $q+1\mid F(z)$.
$$
v=q(q-1)z+2 \qquad\text{or}\qquad v=q(q-1)z+q^2+1.
$$
To see this, let $m=(v-2)/(q-1)$ be the replication through a pair. Point replication requires $q\mid(v-1)m$. Substituting $v=(q-1)m+2$ gives $q\mid m(m-1)$. Since $q$ is a prime power, it divides either $m$ or $m-1$. In the first case write $m=qz$. In the second write $m=q(z+1)+1$, using $v>q^2+1$. In both cases, the remaining block-count divisibility reduces modulo $q+1$ to $q+1\mid F(z)$. The proof verifies the converse for each form. [Two forms and both converses](Erdos722PrimePowerOrderForms.lean)

If $q\ge4$ and $q+1$ is also a prime power, then $Z(q)=\lfloor q/2\rfloor$. For odd $q+1$, its prime power has to divide one of the pairwise coprime numbers $z,z+1,2z+1$. For even $q+1$, write $q+1=2^a$. The condition reduces to $2^{a-1}\mid z(z+1)$ by removing the odd factor $2z+1$. In either case the first possible $z$ is attained. These formulas apply to each qualifying pair and require no infinitude assumption on consecutive prime powers. [Evaluation of the index](Erdos722AdjacentPrimePowers.lean)

## Ordinary orders and higher ranks

For prime powers $q>11$, the least nontrivial ordinary order in rank three is $q^2+1$. A second ordinary order exists and lies between $N(q)$ and $q^3+1$, inclusive. Witt's projective sublines over the cubic extension give the upper endpoint as an actual design. The lower endpoint is attained by a signed design in general and by the ordinary cyclic example at $q=4$. [Ordinary bounds](Erdos722OrdinaryOrderSeparation.lean) · [First ordinary order](MinimumSteinerOrders.md)

Every order $v>q^2+1$ passing the three binomial tests satisfies
$$
[q(q-1)]^3(q+1)\le 12(v-2)^3.
$$
Indeed $q+1\le F(z)\le12z^3$ and $q(q-1)z\le v-2$. More explicitly, for every natural $C$, every prime power $q\ge96C^3$ and every such order, Lean proves $v>Cq^2$. Thus the ratio of the next ordinary order to $q^2$ grows without bound along all prime powers. [Cubic separation](Erdos722SecondSignedOrder.lean)

For prime powers $q>58$ the same threshold already bounds the **first** ordinary order in rank four. Every nontrivial $S(4+s,q+2+s,v+1+s)$ has $v\ge N(q)$ for all $s\ge0$. Derive at $s$ points and then at one more. A rank-four design at the square order would require $q+2\mid q(q^2+1)(q^2+2)$ by its block count, hence $q+2\mid60$. This is the arithmetic step in Penttila's one-point extension lemma. His stronger geometric restrictions involve additional incidence information. For $q=256$, a nontrivial $S(4,258,n)$ therefore needs $n\ge8\,355\,843$. [Rank-four and higher-rank bounds](Erdos722OrdinaryOrderSeparation.lean) · [Penttila, *One-point extensions of finite inversive planes*](https://ajc.maths.uq.edu.au/pdf/8/ocr-ajc-v8-p53.pdf)

| $q$ | First positive $Z(q)$ | First signed order above $q^2+1$ |
| ---: | ---: | ---: |
| 4 | 2 | 26 |
| 5 | 1 | 42 |
| 13 | 3 | 470 |
| 16 | 8 | 1,922 |
| 31 | 15 | 13,952 |
| 64 | 12 | 48,386 |
| 256 | 128 | 8,355,842 |

## Comparison and replay

The canonical conjecture asks for *eventual* ordinary existence for every fixed rank and block size. The equivalence here classifies each binomial-admissible order above the square boundary for rank three at the specified prime-power block sizes. The geometric conclusions give small-order obstructions, an upper witness, and an attained second order at block size five. Keevash proved the general existence theorem. The host proof is a placeholder at the pin. [Keevash](https://arxiv.org/abs/1401.3665) · [Host statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5495) · [Left to Solve](https://www.lefttosolve.com/p/Erdos722.erdos_722) · [Open Math Agents reduction](https://github.com/lefttosolve2/open-math-agents/pull/17505)

An independent Lean 4.33.1 replay checked all 20 notebook modules in the closure. The 21 public theorems in the five new proof files passed the standard-axiom audit. A separate comparison checked the exact host quantifiers and both order forms, the signed and ordinary predicates, ten numeric thresholds including the small moduli, and the nontrivial rank-four bound at block size 258.

From the pinned Formal Conjectures checkout use `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos722SecondOrderTwentySix`. The runner includes the full local dependency closure.
