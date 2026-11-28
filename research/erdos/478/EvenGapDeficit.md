# Simultaneous even factorial gaps

Write $A_p=\{j!\bmod p:1\le j<p\}$ and $\delta_p=p-|A_p|$. For every $n\ge1$ there is a prime
$$
2n<p\le 2^{(2n+4)^{3n+9}}
$$
at which every even length $2,4,\dots,2n$ has at least two distinct factorial collision endpoints. The endpoint sets for different lengths are disjoint. Hence $|A_p|+2n\le p-1$. For example, at $p=241$ the endpoint pairs for lengths $2,4,6,8$ are $(52,190)$, $(28,216)$, $(93,153)$ and $(25,223)$. Direct enumeration gives $|A_{241}|=146$. [Explicit simultaneous witness](Erdos478EvenGapDeficit.lean) · [Disjoint endpoint count](Erdos478EvenGapFamily.lean)

For every $\varepsilon>0$, arbitrarily large primes satisfy $\log\log\log p\ge1$ and
$$
\log\log p\le (3/2+\varepsilon)\,\delta_p\log\log\log p.
$$
In particular, the limsup of $\delta_p\log\log\log p/\log\log p$ along primes is at least $2/3$. The notebook's earlier elementary bound gave $1/3$ by splitting a single gap polynomial. Banks, Luca, Shparlinski and Stichtenoth proved the stronger constant $1$ by effective Chebotarev. Their convention also counts the zero factorial residue for indices at least $p$. Klurman and Munsch established average results. The present proof controls a prime at which all the specified even lengths have two distinct endpoints. The relative factorial-image limit asked for in Erdős 478 remains open. [Checked rate](Erdos478EvenGapDeficit.lean) · [Earlier elementary bound](EffectiveGapDeficit.md) · [Banks et al., Theorem 3](https://mospace.umsystem.edu/server/api/core/bitstreams/5b756a2f-14b6-4cd7-b23e-f57366effec4/content) · [Klurman and Munsch](https://www.numdam.org/item/10.5802/jtnb.974.pdf) · [Upstream factorial image](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## One root from each polynomial

For monic polynomials $f$ and $g$, with roots $a_i$ and $b_j$, the resultant in $Y$ of $g(Y)$ and $f(X-MY)$ has roots $a_i+Mb_j$. Iterating this operation gives an integer polynomial with one factor for each tuple choosing one root from each input. The product formula holds after mapping coefficients into any field. If the inputs have degrees $d_1,\ldots,d_n$ and $D=\prod_i d_i$, some integer $M\le nD^2$ separates the complex tuples. At a prime retaining separability, a prime-field root fixes one tuple under Frobenius. Each coordinate therefore lies in the prime field. Applying the bounded Schur-prime theorem to the tuple polynomial gives a common root prime outside any prescribed set of prime divisors of a nonzero integer, provided those exclusions protect the input polynomials' separability. [Resultant and its factorization](Erdos478RootWordPolynomial.lean) · [Bounded common-root prime](Erdos478JointRootBound.lean) · [Separating parameter](Erdos478ResolventSeparator.lean)

## The second endpoint

The falling-factorial gap polynomial $f_{2i}(X)=X(X-1)\cdots(X-2i+1)-1$ is invariant under $X\mapsto2i-1-X$. At a fixed point the derivative is its own negative. In odd characteristic a root fixed by the reflection would therefore be multiple. A simple root has a distinct partner. Choosing a prime away from twice the resultant of $\prod_i f_{2i}$ with its derivative ensures that all these paired roots count separately. [Reflection and simplicity](Erdos478EvenGapReflection.lean) · [Family separability and collision count](Erdos478EvenGapFamily.lean)

For the even lengths through $2n$, the tuple polynomial has degree $D=2\cdot4\cdots 2n\le(2n+4)^n$. The root-radius and resultant estimates make the exponent of the Schur bound at most $(2n+4)^9((2n+4)^n)^3$. Taking logarithms twice and using $\delta_p\ge 2n+1$ gives the stated rate. [Size estimate](Erdos478EvenGapScale.lean) · [Asymptotic comparison](Erdos478EvenGapDeficit.lean)

The 2026-11-28 overlap check found the statement in DeepMind and an open Left to Solve target. The OMA factorial-residue search returned a problem about a factorial sum and a divisor-count problem. The personal notebook already had simultaneous complete splitting at unquantified primes and an explicit single-length rate. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/4078) · [Left to Solve](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450) · [Earlier simultaneous gaps](DisjointGapFamilies.md)

The scoped Lean 4.33.1 replay rebuilds the 15 modules required by the new endpoint and the earlier single-gap endpoint, 16 modules in total. It treats warnings as errors, checks each module separately with the kernel checker and audits 13 named declarations for the standard axioms `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)
