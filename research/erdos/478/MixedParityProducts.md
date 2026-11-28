# Mixed products of even and odd factorial residues

Fix an odd prime $p$. Let $E$ contain the residues $i!$ for even $0\le i<p$, and $O$ the residues $i!$ for odd $1\le i<p$. Write $e=|E|$, $o=|O|$, $a=|E\cup O|$, $t=|E\cap O|$ and $P=|EO|$. Since $0!=1!$, $a$ is exactly the size of the positive-index image in the pinned problem. For the count of residues attained at **both positive parities**, the extended intersection adds at most the residue one. [Host comparison and reflection](Erdos478ReflectedParityValues.lean) · [exact positive-index correction](Erdos478PositiveParityOverlap.lean)

For every odd prime,
$$
16P+(a-2t)^2+2(e-o)^2\le 7a^2+4(a+t).
$$
In particular $16P\le7a^2+8a$. The two square terms retain the overlap and the imbalance between the parity sets. Combined with Wilson reflection and the inverse-parity count, the inequality gives the unconditional pointwise bound
$$
32p\le 21a^2+24a+16.
$$
It also gives $a\ge c\sqrt p$ for every $0\le c<\sqrt{12/7}$ and all sufficiently large primes $p$. The previously checked elementary estimate was $4p\le3a(a+1)+2$. The new bounds concern the square-root scale. The host asks for the limit of $a/p$ to equal $1-1/e$. [Parity tradeoff](Erdos478MixedParityTradeoff.lean) · [pointwise and eventual bounds](Erdos478ParityProductValueBounds.lean) · [earlier estimate](InverseParity.md) · [pinned Erdős 478](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/ErdosProblems/478.lean)

## Two counts of repeated products

If two distinct residues belong to $E\cap O$, both orderings of the pair lie in $E\times O$ and give the same product. Removing one ordering of every such pair gives $P+\binom{t}{2}\le eo$. This observation holds for every symmetric function on two overlapping argument sets. [Commutative image bound](Erdos478MixedProductOverlap.lean)

The other count uses the identity $i!(p-1-i)!\equiv(-1)^{i+1}\pmod p$. Thus $E$ is closed under $x\mapsto-x^{-1}$ and $O$ under $x\mapsto x^{-1}$. Every common residue gives a different element $x^{-1}$ in $K=(E\cup O)\cap-(E\cup O)$. Write $|K|=2h$ and choose one representative of each opposite pair. All products of two elements of $K$ are signed products of two representatives. This saves at least $\binom{2h+1}{2}-2\binom{h+1}{2}=h^2$ unordered pairs. Consequently $4P+t^2\le 2a(a+1)$. Adding the two counts and using $a+t=e+o$ gives the displayed inequality. [Antipodal pair count](Erdos478AntipodalProducts.lean) · [Wilson reflection](Erdos478ReflectedParityValues.lean)

## How many mixed products occur?

The set $EO$ contains every nonzero even representative $i$ via $i!(p-i)!$. It contains $j^{-1}$ for every odd $j$ via $(j-1)!(p-1-j)!$. Let $M$ count odd representatives with odd inverse. The two inclusions give $P\ge(p-1)/2+M$. The notebook's three-cycle proof gives $6M\ge p+1$ for every odd prime. Its Fourier proof gives
$$
|2M-(p-1)/2|\le D_p,\qquad
D_p=4p^{3/4}\bigl(1+H_{\lfloor p/2\rfloor}\bigr)^2,
$$
where $H_n$ is the harmonic sum. Hence $12(p-1)\le7a^2+8a+8D_p$. The proof checks $D_p=o(p)$ and takes the limit on the same prime filter as the host. [Mixed product coverage](Erdos478MixedProductCoverage.lean) · [inverse parity count](Erdos478InverseParity.lean) · [odd-inverse discrepancy](../../arxiv/theta-sum/ThetaOddInverseCount.lean) · [elementary Kloosterman estimate](../../arxiv/theta-sum/ThetaReciprocalCutoff.lean)

## Sources and scope

Chen and Dai use the Wilson inclusions and Zhang's inverse-parity estimate to study two-factorial products. García obtains a larger asymptotic coverage for the unrestricted product set. Grebennikov, Sagdeev, Semchankau and Vasilevskii prove almost-full product coverage and a total-image bound with leading constant $\sqrt2$. Their proof in §5 also uses products of opposite-parity factorials. Xiyu Hu's 2026 preprint proves $a\gg p^{8/15}$ using incidences. The accompanying Lean repository makes its Stevens–de Zeeuw incidence estimate an explicit hypothesis. This notebook contribution gives the finite parity-resolved inequality and its independently checked consequences. Historical priority for the inequality is unestablished. [Chen and Dai](https://math.colgate.edu/~integers/g21/g21.pdf) · [García](https://www.smm.org.mx/boletin_anterior/v13/n1.pdf) · [Grebennikov et al.](https://ems.press/content/serial-article-files/47109?nt=1) · [Hu](https://arxiv.org/abs/2608.01781) · [Hu's formalization status](https://github.com/hxypqr/factorial-residues-mod-prime/blob/main/docs/FORMALIZATION_STATUS.md)

The live DeepMind, Left to Solve and Open Math Agents searches found the host statement and unrelated factorial results. The personal notebook contains the earlier pointwise estimate and the reciprocal-discrepancy proof used here. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/750) · [Left to Solve](https://www.lefttosolve.com/p/Erdos478.erdos_478) · [Open Math Agents search](https://github.com/lefttosolve2/open-math-agents/issues?q=Erdos478) · [previous factorial bound](https://github.com/vincentkoc/solved-conjectures/pull/24) · [reciprocal estimate](https://github.com/vincentkoc/solved-conjectures/pull/50)

From the pinned Formal Conjectures checkout, run `lake env python3 "$NOTEBOOK/scripts/replay-research" Erdos478ParityProductValueBounds Erdos478PositiveParityOverlap`.

Independent Lean 4.33.1 replay rebuilt and kernel-checked 14 modules. All 34 new public declarations and three imported results reported only the standard axioms. Eighteen direct checks covered the host filter and value set, parity conventions, constants and small primes. A separate enumeration verified the finite inequalities for all 167 odd primes through 997 and all 18,632 reflection-stable pairs of subsets at the five smallest odd primes.
