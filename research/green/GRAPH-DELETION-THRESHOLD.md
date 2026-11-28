# Deletions that preserve the sumsets of a binary graph

For a function $f:U\to V$ on finite binary vector spaces, let $\Gamma$ be its graph. To erase an attainable two-point sum $(a,b)$ with $a\ne0$, one must and can delete exactly half the inputs satisfying $f(x)+f(x+a)=b$. Indeed, $x\mapsto x+a$ partitions these inputs into disjoint pairs. Deleting one endpoint of each pair destroys the sum. The only attainable pair sum in direction zero is the origin, which survives as long as one graph point remains. [Exact deletion cost](Green50GraphDeletions.lean)

If $f$ is quadratic, let $B_a$ be the linear part of its derivative in direction $a$. Every nonempty derivative fibre is a translate of $\ker B_a$. It follows that **every** deletion of at most $m$ inputs preserves **every** sumset of order at least two exactly when
$$
m<|U| \quad\text{and}\quad 2m<|\ker B_a|\quad\text{for every }a\ne0.
$$
This includes a zero-dimensional input space. Once $T\subseteq\Gamma$ satisfies $2T=2\Gamma$, the inclusion $T+\Gamma\subseteq2T$ gives $3T=3\Gamma$, and induction gives the equality at all higher orders. [Uniform criterion](Green50GraphDeletions.lean)

The simpler bound $2m|V|<|U|$ suffices without measuring any ranks. The strict inequality is necessary for a uniform guarantee in this range of dimensions. For $U=\mathbb F_2\times V\times Z$, take $f(t,v,z)=tv$. Delete precisely the $|Z|$ inputs $(0,0,z)$. The sum with horizontal coordinate $(1,0,0)$ and vertical coordinate $0$ disappears at equality. [Sharp example](Green50GraphDeletions.lean)

## An approximate graph in a twofold sumset

Suppose $U,V$ are complementary subspaces of the ambient cube, the output dimension is at most $\log_2(1/\operatorname{dens} A)$, and fewer than $|U|/(2|V|)$ graph points lie outside $A+A$. The retained points have the same fivefold sumset as $\Gamma$. The five-sum theorem supplies a flat of dimension at least $\dim U$ there, hence also in $10A$. The Lean declaration `approximate_model_green50` gives Green's tenfold conclusion with coefficient one under these assumptions. Arbitrary sets are still open. [Five-sum proof](QUADRATIC-BOGOLYUBOV.md) · [Pinned Green 50](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean) · [Replay instructions](../README.md#replay)
