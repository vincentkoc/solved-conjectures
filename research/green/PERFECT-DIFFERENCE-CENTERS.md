# Reflection centers of cyclic perfect difference sets

Let $D\subseteq\mathbb Z/v\mathbb Z$ contain exactly one ordered representation of every nonzero difference. Assume $v$ is odd and doubling permutes $D$. Embed $D$ as even residues modulo $2v$, and add its reflection across an odd residue $j=1+2t$. Write $c=1+2t\bmod v$ for the overlap center. As $v\to\infty$, **every choice with $c\ne0$ misses a fraction of the doubled group with limit inferior at least**
\[
  \frac{1-1/\sqrt2}{8}=0.03661165\ldots.
\]
The bound is uniform. For each smaller constant $b$, all sufficiently large members of any such family miss more than $2vb$ residues at every nonzero center. These seeds have size $2|D|\sim\sqrt{2}\sqrt{2v}$. Thus full or asymptotically full coverage in this construction requires the normalized center to be zero eventually. The center-zero case remains open in this argument. [Cyclic loss and exact finite count](Green33PerfectDifferenceCenters.lean) · [Pinned Green 33](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/GreensOpenProblems/33.lean)

The characteristic-two trace-zero Singer sets give an example of the hypotheses. In the classical construction $D$ consists of the projective points of the trace-zero line in $\mathbb F_{q^3}^*/\mathbb F_q^*$, with $v=q^2+q+1$ and $|D|=q+1$. In characteristic two, squaring preserves trace zero, so doubling preserves the normalized exponent set. The Lean theorem takes the perfect difference counts and doubling invariance as hypotheses. Singer's construction is classical, and Hulak, Ramos and de Queiroz have formalized the prime-field construction in Lean. [Singer](https://doi.org/10.1090/S0002-9947-1938-1501951-4) · [Trace construction, §1](https://arxiv.org/abs/math/9807029) · [Prime-field Lean development](https://arxiv.org/abs/2605.03274)

## Which centers can have small overlap?

For any finite abelian group of order $v$, put $S=D+D$ and $I(c)=|S\cap(c-S)|$. In an index-two reflected construction, the first layer of sums is $S\cup(c-S)$ in even coordinates and the other is a translate of $D-D$. For a nonempty perfect seed of size $k$, the doubled cyclic sumset has exactly $2v+2k-1-I(c)$ elements. In particular, asymptotically full coverage is equivalent to $I(c)/v\to0$. [Layer equivalence](Green33PerfectDifferenceCenters.lean) · [Reflected-layer count](REFLECTED-SIDON-LAYERS.md)

- For each $a<(1-1/\sqrt2)/4$, at most one center has $I(c)\le av$ for sufficiently large $v$. Every center moved by an affine symmetry of the seed has $I(c)>av$.
- If $I(c)/v\to0$ for a chosen center, $I(t)/v\to1/4$ uniformly over **all** $t\ne c$. Every affine symmetry $x\mapsto e(x)+s$ of the seed must eventually fix the chosen center under its induced action $c\mapsto e(c)+4s$.
- If the number of centers sharing the chosen center's ordered four-sum count tends to infinity, its overlap tends to $v/4$ in relative terms. A growing multiplier orbit suffices. Every full cyclic basis containing those reflected layers then has size coefficient with limit inferior at least $(3+\sqrt3)/(2\sqrt2)$, by the earlier Sidon repair inequality. [Center bounds and repair specialization](Green33PerfectDifferenceCenters.lean) · [Repair inequality](Green33SidonLayerRepairs.lean)

## The finite calculation

Write $P_r(x)$ for the number of ordered $r$-tuples of elements of $D$ with sum $x$, including repeated summands. With $R_r(x)=P_r(x)-k^r/v$, the perfect-difference identity gives
\[
  \sum_x R_r(x)R_r(x+t)=(k-1)^r\left(\mathbf 1_{t=0}-1/v\right).
\]
To see this, expand the product of the two translate sums. Each nonzero difference occurs once, and zero occurs $k$ times. On centered functions a convolution step therefore multiplies the inner product by $k-1$. Starting with a centered point mass gives the formula for every path length and displacement. This is the standard group-ring identity for a difference set applied to its convolution powers. [Exact covariance](Green33PerfectDifferenceCenters.lean) · [Difference sets and their character identity, §1](https://arxiv.org/abs/math/9807029)

For $r=4$, the variance divided by $v^2$ tends to one because $k^2=v+k-1$. At each center $0\le4I(c)-P_4(c)\le4k$, allowing for the diagonal sums. A center of sublinear overlap consumes the entire limiting variance, leaving a vanishing normalized deviation at every other center. Two distinct centers each falling short of the mean by more than $v/\sqrt2$ would exceed the same variance. In a doubling-invariant seed, doubling moves every nonzero center, giving the stated loss bound. [Four-step diagonal correction](Green33ReflectedLayers.lean) · [Variance bounds](Green33PerfectDifferenceCenters.lean)

## Checks and scope

The independent Lean 4.33.1 replay rebuilt six notebook modules and checked 53 axiom prints, including all 18 declarations audited in the new module. The pinned statement was compared by definitional equality and its exact cyclic basis predicate was tested directly on the doubled seeds. Exhaustive checks on the 111 perfect seeds of sizes at least two through order 21 verified 8,325 covariance identities for path lengths zero through four and 1,665 doubled sumset counts. The earlier notebook treated Ruzsa seeds and almost every center of general dense Sidon sets. The present result isolates exceptional centers for perfect difference sets. The DeepMind tracker also contains an integer reflected-Sidon construction for Erdős 864. Targeted DeepMind, Open Math Agents and personal tracker searches found no matching center obstruction. Left to Solve listed Green 33 as open. [Earlier notebook PR](https://github.com/vincentkoc/solved-conjectures/pull/86) · [Erdős 864](https://github.com/google-deepmind/formal-conjectures/pull/6947) · [Original issue](https://github.com/google-deepmind/formal-conjectures/issues/1589) · [Statement PR](https://github.com/google-deepmind/formal-conjectures/pull/3613) · [Left to Solve](https://lefttosolve.com/api/problems/Green33.green_33)
