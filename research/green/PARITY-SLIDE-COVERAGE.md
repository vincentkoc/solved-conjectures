# Sliding one parity class of a thin cyclic basis

Let \(T\subseteq\mathbb Z/(2v)\) cover every residue by two summands, with diagonal pairs allowed. Leave the even elements fixed and add \(2h\) to each odd element to form \(T_h\). Along any sequence with \(v\to\infty\) and \(|T|/\sqrt{2v}\to\sqrt2\), for every \(\varepsilon>0\),
\[
 \frac1v\#\left\{h\in\mathbb Z/v:
 \left|\frac{|T_h+T_h|}{2v}-\frac78\right|\ge\varepsilon\right\}\longrightarrow 0.
\]
Thus a typical slide loses one eighth of the original group. The quantifier over slides matters since \(h=0\) always preserves full coverage. The conclusion allows every positive quotient order and arbitrary choices of the two layers. [Main theorem and exceptional fraction](Green33ParitySlides.lean)

## Where the fraction comes from

Write \(T=2A\cup(1+2B)\) and set \(U=A+A,\ W=1+(B+B)\) in \(\mathbb Z/v\). Full coverage gives \(A+B=\mathbb Z/v\) and \(U\cup W=\mathbb Z/v\). In particular \(|A||B|\ge v\). Critical size then forces \(|A|,|B|\sim\sqrt v\). Counting unordered pairs in each layer gives \(|U|,|W|\sim v/2\) and \(|U\cap W|=o(v)\).

All odd sums survive every slide. The new even sums have coordinates \(U\cup(2h+W)\). Write \(d_U(t)=|U\cap(t+U)|\). The finite count, valid at every shift of every full basis of even order, is
\[
 0\le |T_h+T_h|+|U|-2v-d_U(2h)\le |U\cap W|.
\]
The two-point bound on the fibres of \(h\mapsto 2h\) includes even \(v\). [Parity decomposition, slide count and doubling fibres](Green33ParitySlideCoordinates.lean)

It remains to show that \(d_U(t)/v\) concentrates at \(1/4\). In the real group algebra write \(P,Q\) for the indicators of \(A,B\), \(J\) for the constant one function and \(D\) for unit mass at \(1\). Products denote counting convolution. Since \(A+B\) is full, \(\|PQ-J\|_1=|A||B|-v=o(v)\). At every covered self-sum, either two distinct ordered pairs contribute or there is a diagonal pair. Summing this diagonal allowance gives both \(\|P^2+DQ^2-2J\|_1=o(v)\) and \(\|P^2-2\,1_U\|_1=o(v)\).

The identity
\[
 P^4-(2|A|^2-v)J=(P^2+DQ^2-2J)P^2-D(PQ-J)(PQ+J)
\]
and the convolution product bound in the sum norm give \(\sum_x|4r_U(x)-v|=o(v^2)\), where \(r_U\) counts ordered self-sums. The centered sum and difference counts have equal squared norms. Since \(0\le r_U(x)\le v\), it follows that \(\sum_t(d_U(t)-v/4)^2=o(v^3)\). Chebyshev's inequality and the finite slide count yield the stated limit. The proof also supplies an explicit error bound using only \(v,|A|,|B|,|U|\). [Convolution identity](Green33ParityConvolution.lean) · [Finite error bound](Green33ParityDeviation.lean) · [Centered energy identity](Green33TailEnergy.lean)

## Scope and verification

Green's problem allows arbitrary positive moduli. This result describes a sequence of even-modulus witnesses if such a sequence exists. Its normalization and ordinary sumset are those of the pinned declaration. The notebook’s prescribed-divisor theorem gives arbitrarily large even-order strict witnesses for each positive tolerance if Green 33 holds. Choosing successive orders with tolerances tending to zero supplies a sequence to which the slide theorem applies. Previously the notebook obtained seven-eighths coverage for reflected Sidon or Singer constructions, including uniform conclusions for particular Singer families. Here full initial coverage replaces the construction hypotheses, and the conclusion concerns the distribution over translations of one parity class. [Green, Problem 33](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean) · [Prescribed-divisor equivalence](DIVISIBLE-ORDERS.md) · [Reflected Sidon layers](REFLECTED-SIDON-LAYERS.md) · [Singer overlap over odd finite fields](https://github.com/vincentkoc/solved-conjectures/pull/407)

The DeepMind issue and its statement PR are closed. Left to Solve lists the declaration as research open with no solution or steps. Searches of the DeepMind and Open Math Agents issue and PR records found no matching parity-slide theorem. An exhaustive finite check tested the compressed sumset formula for all 5,460 subsets of groups of even order through 12, and the two slide inequalities on all 15,987 slides of their 2,797 full bases. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33) · [Open Math Agents](https://github.com/lefttosolve2/open-math-agents)
