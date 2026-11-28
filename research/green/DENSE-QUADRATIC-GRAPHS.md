# Tenfold sums after deletions from a binary quadratic graph

Let $f:U\to V$ be quadratic on finite binary vector spaces, with $\dim U=n$ and $\dim V=d$. Retain any set $D$ of more than three quarters of the inputs and write $T=\{(x,f(x)):x\in D\}$. Then $10T$ contains a linear subspace of dimension at least $n$. Already $6T$ contains a linear subspace of codimension at most $2d$ in $U\times V$. The zero map attains the tenfold dimension bound. [Lean declarations](Green50DenseQuadraticGraphs.lean)

An ambient set $A$ may also contain points outside the graph. If it contains more than three quarters of the graph and its size is at most $2^n$, the tenfold subspace has codimension at most $\log_2(1/\operatorname{dens} A)$. The theorem `dense_quadratic_green50` states this in Green's original ambient cube, with coefficient one. The strict density assumption concerns the intersection with this particular graph. Green's statement for arbitrary sets remains open. [Pinned DeepMind statement](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/50.lean) · [Green, Problem 50](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#page=25)

## Proof

Write $B$ for the polarization of $f$. For any directions $a,b$, translate the four inputs $0,a,b,a+b$ together. Each excluded input rules out at most four translations. Since $4|U\setminus D|<|U|$, some translate lies entirely in $D$. The four graph points then sum to $(0,B(a,b))$.

Apply the rank estimate for the full quadratic graph with $k$ sampled directions. It gives subspaces $H\le U$ and $W\le V$ such that $B(H,H)\subseteq W$, every $w\in W$ is a sum of $k$ polar values, and $k\operatorname{codim}H\le2\dim W$. Hence every $(0,w)$ lies in $4kT$. [Rank estimate](QUADRATIC-BOGOLYUBOV.md)

Averaging over translates gives a coset $o+H$ on which $D$ occupies more than half the points. Each $h\in H$ is the difference of two retained inputs in this coset. Their graph sum has horizontal coordinate $h$. Modulo $W$, its vertical coordinate is a linear function of $h$, since $B(H,H)\subseteq W$. Adding the available vertical space lifts that linear graph to a subspace $S\subseteq(4k+2)T$ with $\dim S=\dim H+\dim W$. Taking $k=2$ gives the tenfold bound and $k=1$ gives the sixfold bound. [Proof and axiom reports](Green50DenseQuadraticGraphs.lean) · [Replay instructions](../README.md#replay)
