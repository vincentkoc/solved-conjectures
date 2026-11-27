# A uniform lower bound from inverse parity

For every odd prime $p$, let $A_p$ be the residues of $1!,\ldots,(p-1)!$ modulo $p$ and let $a=|A_p|$. The proof gives
$$
4p\le 3a(a+1)+2,\qquad a\ge \frac{2}{\sqrt3}\sqrt p-1.
$$
It also gives $6|A_p A_p|+2\ge4p$ for the products of two factorial residues. All three inequalities hold for each odd prime, with no cutoff or unspecified constant. The pinned problem asks for a positive limiting density of $A_p$, equal to $1-1/e$. The square-root lower bound leaves that limit open. [Pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean) · [Lean proof](Erdos478InverseParity.lean)

## Why a third of the inverse pairs preserve parity

Use the least nonnegative representative to define the parity of a field element. Away from $0,-1$, the map $T(x)=-1-x^{-1}$ satisfies $T^2(x)=-(x+1)^{-1}$ and $T^3(x)=x$. Fix $0,-1$ separately to obtain a permutation of the whole field. For regular $x$, the representative of $T(x)$ is $p-1-\operatorname{val}(x^{-1})$, which has the same parity as $x^{-1}$. This parity identity also holds at the two fixed exceptions, taking $0^{-1}=0$ in Lean.

Mark $x$ when its parity agrees with that of its inverse. On the circuit $x,T(x),T^2(x),x$, at least one edge joins points of equal parity. At $0$ and $-1$ all three edges do. Summing over starting points counts each mark three times, giving $3M\ge p+4$ for the total number $M$ of marks. Negation exchanges odd-odd marks with nonzero even-even marks. If $O$ counts the odd-odd marks, then $M=1+2O$, hence $6O\ge p+1$.

## From inverse pairs to factorial values

Wilson reflection gives $i!(p-1-i)!\equiv(-1)^{i+1}\pmod p$. Each nonzero even representative $i$ is the product $i!(p-i)!$. For odd $j$, the product $(j-1)!(p-1-j)!$ represents $j^{-1}$. An index zero can be replaced by one since $0!=1!$. The product set therefore contains both the $(p-1)/2$ nonzero even representatives and all $O$ odd-odd marks. These sets are disjoint. Finally every product comes from an unordered pair of elements of $A_p$, with repetition allowed, so $|A_pA_p|\le a(a+1)/2$.

Chen and Dai use the same Wilson inclusion with Zhang’s asymptotic inverse-parity estimate and obtain a stronger product-set bound. García obtains a larger asymptotic constant, and Grebennikov, Sagdeev, Semchankau and Vasilevskii prove a lower bound with leading constant $\sqrt2$ for $|A_p|/\sqrt p$. The notebook formalizes the finite three-cycle estimate and its consequences. [Chen–Dai, §2](https://math.colgate.edu/~integers/g21/g21.pdf) · [García, Theorem 1.1](https://www.smm.org.mx/boletin_anterior/v13/n1.pdf) · [Grebennikov et al., Theorem 1.1 and Corollary 1.2](https://ems.press/content/serial-article-files/47109?nt=1)

## Verification

In the namespace `Erdos478.InverseParity`, `six_mul_card_odd_inverse` gives the parity count, `product_bound` bounds the product set, and `factorial_value_bound` and `factorial_value_sqrt_bound` concern the exact upstream image `(Ico 1 p).image (fun i ↦ i.factorial % p)`. A fresh warnings-as-errors build and independent `leanchecker` replay passed. All four public declarations report only `propext`, `Classical.choice` and `Quot.sound`. [Notebook replay](../../README.md#replay)

The 2026-11-28 overlap check found the DeepMind statement work. The LTS target was unsolved and unclaimed, and the OMA factorial-residue hits concerned a factorial sum and divisor counts. The notebook’s earlier results give upper bounds for the size of the factorial image. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/5229) · [LTS target](https://lefttosolve.com/p/Erdos478.erdos_478) · [OMA factorial sum](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4056) · [OMA divisor count](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7450) · [Earlier deficit result](UnboundedDeficit.md)
