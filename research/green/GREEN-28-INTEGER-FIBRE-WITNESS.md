# Green 28 and simultaneous congruences across sum outcomes

Let the independent integer laws $P,Q$ have a sum uniform on the finite set $S$. Group the pairs of occupied sites $(i,j)$ by equal product mass $P(i)Q(j)$. For each distinct mass class $w$, let $C_{z,w}$ count its pairs with $i+j=z$. There are **signed integers $v_w$, one per class, satisfying every equation at once**:
\[
               \sum_w C_{z,w} v_w=\mathbf 1_S(z)\qquad(z\in\mathbb Z).
\]
The two inputs may have arbitrary finite support sizes and arbitrary positive real masses. The integers describe the linear equations. They can lose positivity and the factorization into a row mass and a column mass. [Formal statements](Green28IntegerFibreWitness.lean)

## A test using several outcomes

Choose finitely many outputs and attach integer coefficients $k_z$ to them. If $d$ divides $\sum_z k_z C_{z,w}$ for every mass class, then $d$ divides $\sum_{z\in S}k_z$. This follows by multiplying the witness equations by $k_z$ and summing. It tests a proposed pattern of equal product masses without knowing their numerical values.

For example, two distinct occupied outcomes cannot have count vectors $(2,1,0)$ and $(1,2,3)$ on three classes, with zero counts in all others. Each equation separately has integer solutions. They share the positive real solution $(14/33,5/33,1/11)$. But the combined counts $(3,3,3)$ would force $3\mid 2$. Similarly, if every class occurs evenly often across a selection of occupied outputs, their number must be even. These are necessary incidence tests. The test uses the product-mass partition as well as the sites. [Modular consequence](Green28IntegerFibreWitness.lean)

## Why an integer witness exists

Normalize each marginal by its mass at its rightmost site. The normalized products are real algebraic integers, their equality classes stay the same, and each occupied fibre sums to one. Their integer span together with one is a finitely generated torsion-free abelian group. The element one is primitive there. Indeed, $1=nx$ with $n\in\mathbb Z$ makes $x=1/n$ a rational algebraic integer, so $n=\pm1$. A primitive element of a finite free abelian group admits an integer linear functional sending it to one. Apply this functional to all the fibre equations. The lemma also applies to any system of integral linear equations with finitely many unknowns and a solution in real algebraic integers. The splitting is classical. [Normalized atom weights](GREEN-28-ARITHMETIC.md) · [Hochster, notes on modules over a PID](https://sites.lsa.umich.edu/hochster/wp-content/uploads/sites/1337/2024/10/fndtc.pdf)

## Scope and verification

The formal statements use the pinned definitions of independent sum and uniformity. A nonempty uniform sum supplies the finite marginal supports and their right endpoints. The conclusion is an obstruction to proposed mass-class patterns. The general marginal-fairness conjecture remains open. Live checks covered the original DeepMind issue and statement PR, Left to Solve, the two OMA reductions and the two-site submission. Hare studies low-degree polynomial factors. These checks found no matching simultaneous fibre-witness theorem. [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/28.lean) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1563) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/2380) · [Left to Solve](https://lefttosolve.com/api/problems/Green28.green_28) · [OMA first reduction](https://github.com/lefttosolve2/open-math-agents/pull/9606) · [OMA second reduction](https://github.com/lefttosolve2/open-math-agents/pull/21793) · [OMA two-site case](https://github.com/lefttosolve2/open-math-agents/pull/27234) · [Hare](https://arxiv.org/abs/2307.07363)

Lean 4.33.1 rebuilt and independently replayed the eight notebook modules in the import closure. Each of the 51 axiom reports listed only `propext`, `Classical.choice` and `Quot.sound`. Run `Green28IntegerFibreWitness` with the [notebook replay runner](../../scripts/replay-research) in the pinned Lake environment.
