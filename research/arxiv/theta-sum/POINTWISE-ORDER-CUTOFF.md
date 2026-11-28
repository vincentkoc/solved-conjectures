# A pointwise character-order cutoff for the prime theta sum

For every fixed $0<\varepsilon<1/2$ and every sufficiently large odd prime $p$, one can discard all multiplicative characters of order at most $p^{1/2-\varepsilon}$ from the character expansion of the original integer $S(p)$ with error $O_\varepsilon(p^{1-\varepsilon/2})$. Character orders here refer to characters **modulo the prime being evaluated**. The bound holds at each prime. It needs no averaging or prime number theorem. [Original integer sum and lower conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Paper, §3](https://arxiv.org/pdf/2501.03234v3#page=4)

## The remaining sign question

Put $A_\chi=\sum_{1\le a<p,\ a\ {\rm odd}}\chi(a)$ and $C_\chi=A_\chi^2 A_{\chi^{-1}}$. Define $H_p(B)$ as $4/(p-1)$ times the sum of $\operatorname{Re}C_\chi$ over nonprincipal characters of order greater than $B$. For $B=p^{1/2-\varepsilon}$, the full family of pinned eventual lower bounds $S(p)>np$ is equivalent to the same family for $H_p(B)$, with $n$ ranging over the natural numbers. The equivalence reads the upstream theorem at the level of its type. It uses the bound with $n+1$ to absorb the error. [Exact equivalence and error](ThetaHighOrderGrowth.lean)

Every nonzero term in $H_p(B)$ has character order divisible by the full power of two in $p-1$. In particular, only multiples of eight can contribute for $p\equiv1\bmod8$. For each fixed $b>0$, every sufficiently large nonpositive candidate in this class must have $H_p(B)\le bp$. A uniform positive linear lower bound for the retained sum would give eventual positivity there. Establishing its sign and handling finite exceptions remain open. [Parity and order support](ThetaPointwiseParity.lean) · [Direct nonpositive obstruction](ThetaHighOrderGrowth.lean)

## Finite estimate

Multiplicative character orthogonality counts pairs of odd representatives with odd product representative. The principal term cancels the constant in the triple-count formula exactly, giving
\[
 (p-1)S(p)=4\sum_{\chi\ne1}C_\chi .
\]
If $\chi$ is even and nonprincipal, pairing each nonzero residue with its negative gives $2A_\chi=\sum_a\chi(a)=0$. If the character order divides $(p-1)/2$, the character is even by evaluation on a generator. [Cubic identity](ThetaPointwiseCubic.lean) · [Parity proof](ThetaPointwiseParity.lean)

For each nonprincipal character, additive completion and the norm of the primitive Gauss sum give $|A_\chi|\le\sqrt p\,\sum_{j\le(p-1)/2}1/j$. For each order $d\mid p-1$, the cyclic group has at most $d$ characters killed by $d$. Summing these bounds over $d\le B$ gives, for all real $B\ge0$,
\[
 |S(p)-H_p(B)|\le 8B\,\tau(p-1)\sqrt p\,(1+\log p)^3.
\]
Using the elementary divisor bound and absorbing the logarithm yields the power saving above. This is an application of character orthogonality and classical interval completion to the pinned sum. It gives no sign estimate for the retained cubic terms. [Completion](ThetaPointwiseCompletion.lean) · [Character count and divisor bound](ThetaPointwiseOrders.lean) · [Finite cutoff](ThetaPointwiseCutoff.lean)

## A maximal order with negative sign

At $p=241$, the contribution to $S(241)$ from all characters of order $240$ is exactly $-448/15$, while $S(241)=816$. Thus even the combined maximal-order term can have the opposite sign from the original sum in the class $1\bmod8$. The example rules out proving positivity by proving nonnegativity of each surviving order separately. [Exact kernel calculation](ThetaOrderExample.lean)

For a generator $g$, $d q=p-1$, and $N(t)$ the number of pairs of odd representatives whose product times $t$ has odd representative, the projection formula is
\[
 q\sum_{\operatorname{ord}\chi\mid d} C_\chi
   =(p-1)\sum_{i<q}N(g^{di}).
\]
For $g=7\bmod241$ the sums on the right before multiplication by $240$ are $7404,22128,36364,108560$ for $q=1,3,5,15$. Inclusion–exclusion over $3$ and $5$, together with the vanishing for nonprincipal orders dividing $120$, gives $\sum_{\operatorname{ord}\chi=240} C_\chi=-1792$. Lean verifies the row counts used in the finite computation. [Projection identity](ThetaOrderProjection.lean) · [Finite calculation](ThetaOrderExample.lean)

The reduction in DeepMind's issue gives a half-square formula. The indexed OMA harmonic estimate concerns the additive cotangent representation. The notebook's power-residue means concern fixed-order tests across primes. [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic estimate](https://github.com/lefttosolve2/open-math-agents/pull/22818) · [Left to Solve](https://lefttosolve.com/api/solved) · [Power-residue means](POWER-RESIDUE-MEANS.md)
