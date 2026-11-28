# A second quadratic-character bias in the theta sum

Let $R(p)=S(p)/p-\tfrac12\log p$ for the canonical integer theta sum. Let $\chi_3,\chi_7$ be the nonprincipal real quadratic characters modulo 3 and 7. Write $B$ for the all-prime mean of $R$ and $C$ for the exact bias $\mathbb E[\chi_3(p)R(p)]$. A second bias exists, with a guaranteed sign and size.
\[
 D=\lim_{X\to\infty}\frac1{\pi(X)}\sum_{p\le X}(-\chi_7(p))R(p)
   \ \ge\ \frac{13}{324}>\frac1{25}.
\]
The expectation in this note always means a limit of ordinary averages over primes. The exact value of $D$ is undetermined here. [Prime correlation](ThetaSevenPrimeBias.lean) · [Exact value of C](EXACT-MOD-THREE-BIAS.md) · [Pinned definition and pointwise conjectures](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

For every $u<C+13/324$ the following two events each have positive lower density among **all** primes.
\[
\begin{aligned}
 p&\equiv 1\pmod{24},\quad p\bmod7\in\{3,5,6\},
 & S(p)&>\tfrac12p\log p+(B+u)p,\\
 p&\equiv17\pmod{24},\quad p\bmod7\in\{1,2,4\},
 & S(p)&<\tfrac12p\log p+(B-u)p .
\end{aligned}
\]
Both events lie in $1\bmod8$. The thresholds can approach $0.67854$ and $-0.19867$, improving the earlier $0.63842$ and $-0.15855$. The result also holds for every $u<C+D$. Direct summation gives $S(313)=1120$ and $S(113)=224$, with residuals about $0.70517$ and $-0.38139$ in the indicated classes. Pointwise positivity of $S(p)$ at every odd prime remains open. [Joint excursion theorems](ThetaJointCharacterBias.lean) · [Earlier dyadic bounds](DYADIC-PRIME-LAW.md)

## Four joint means and a variance bound

Fix $q=2^k$ and any reduced residue $r\bmod q$. Among the primes in $r\bmod q$, each sign pair
$(\chi_3(p),-\chi_7(p))=(s,t)\in\{\pm1\}^2$ has relative density $1/4$, hence density $1/(4\varphi(q))$ among all primes. In that cell the average of $R$ tends to
\[
 B+sC+tD .
\]
The denominator in this average counts only primes in the cell. The same $D$ works for every fixed $k,r,s,t$. The upper and lower excursions at $B\pm u$ have positive lower density in the two cells $(+,+)$ and $(-,-)$ for every $u<C+D$. The positive lower fractions are allowed to depend on the parameters.

The limiting empirical variance of $R$ satisfies
\[
 V\ \ge\ C^2+D^2\ \ge\ C^2+(13/324)^2 .
\]
Thus an exact fit by the two modulo-three means still leaves a strictly positive limiting mean-square error. This follows from orthogonality of the two normalized signs and the nonnegative square of $R-B-C\chi_3-D(-\chi_7)$. [Mean and variance proof](ThetaJointCharacterBias.lean)

There is also an obstruction to approximation by congruence classes. For every fixed positive modulus $m$ with $7\nmid m$, every real function $g$ of $p\bmod m$, and every $a<13/324$, one eventually has
\[
 \frac{1}{\pi(X)}\sum_{p\le X}|R(p)-g(p)|>a .
\]
The character $-\chi_7$ has zero correlation with $g$ by the Chinese remainder theorem, and absolute value at most one. The positive correlation with $R$ gives the uniform lower bound. The starting endpoint may depend on $g,m,a$. [Periodic approximation gap](ThetaSevenPrimeBias.lean)

## Sign of the seven-transform

For odd $d$ divisible by 7 the sum of representative parities twisted by $\chi_7$ is
\[
 \sum_{\substack{0\le j<d\\(j,d)=1}}(-1)^{j+1}\chi_7(j)
 =-2\prod_{\ell\mid d,\ \ell\ne7,\ \ell\ {\rm prime}}(1-\chi_7(\ell)).
\]
The value $-2$ comes from a single period at conductor seven. Inclusion and exclusion of each other prime introduces its displayed factor. Permuting the units by $v\mapsto w/v$ transfers this transform to the original primitive reciprocal wave at odd numerator $w$. [Finite transform](ThetaCharacterSeven.lean)

For the odd numerator sum $\sum_{j\le K,\,j\ {\rm odd}}\chi_7(j)/j$, the complete initial block has value $3808/6435$. Every complete block of length 14 is nonnegative. Its signs at exponents $0,2,4,8,10,12$, after shifting the first index to zero, have generating polynomial $(1-x^2)(1-x^4)(1-x^6)$. Integrating against $x^{14m}$ gives the block at $14m+1$. The Lean proof also checks the resulting rational inequality directly. Any incomplete block after $14m$ loses at most $3/(14m)$ for $m>0$. This gives a nonnegative prefix at every cutoff and a lower bound $7/12$ from cutoff 448 onward.

If the parity transform is nonzero, every other prime factor of $d$ has $\chi_7(\ell)=-1$. Removing multiples of such an $\ell$ adds $1/\ell$ times a shorter numerator prefix. Every row therefore has nonpositive $\chi_7$ transform, including partial numerator windows. At $d=7$ the transform for $-\chi_7$ is at least $7/6$. At $d=21$ it is at least $28/9$ once $K\ge1344$. Dividing by $d\varphi(d)$ gives $1/36+1/81=13/324$. The common-factor weights tend to $\pi^2/8$, which cancels the residual scaling $8/\pi^2$. Rows coprime to 7 have zero twisted mean by the Chinese remainder theorem. The prime mean absolute-error bound transfers the two contributions to the full residual.

Finally, $\chi_3(-v)(-\chi_7(-v))=\chi_3(v)(-\chi_7(v))$, whereas every centered finite residual model changes sign under $v\mapsto-v$. Their product therefore has zero mean in each sufficiently large factorial period. Expanding the joint indicator $(1+s\chi_3)(1-t\chi_7)/4$ yields the four class means. Bounded periodic approximation converts their mean excess into positive lower prime density. [Reflection](ThetaRowReflection.lean) · [Dyadic independence](DYADIC-PRIME-LAW.md)

## Source comparison and replay

Berndt et al. study the integer sum above. Lägeler treats the distribution of individual Hardy sums as the numerator and denominator vary. Guo and Zhang expand a single Hardy sum using characters of its fixed denominator in Lemma 4. The conductor seven here stays fixed as the denominator prime varies. The DeepMind issue reduces the pointwise conjectures to a remainder. OMA's finite certificate covers odd primes below 100,000, and the associated LTS solved entry concerns a harmonic estimate. The primary literature and live tracker searches yielded no matching conductor-seven prime correlation, four joint means or excursion thresholds for the signed aggregate. [Original paper](https://doi.org/10.1007/s00025-025-02584-2) · [Hardy sums](https://arxiv.org/abs/2207.04828) · [Guo and Zhang](https://dml.cz/dmlcz/141636) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite certificate](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21967) · [Harmonic estimate](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/7126) · [LTS solved feed](https://lefttosolve.com/api/solved)

The joint module below discharges the progression hypothesis with the pinned external prime number theorem in arithmetic progressions. [Bridge build and pins](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaJointCharacterBias
import ThetaPNTCorollaries

/-! Joint prime means, signed excursions and variance with the progression theorem discharged. -/
namespace Arxiv.«2501.03234».ThetaJointBiasPNT
open Filter ThetaPeriodMeans ThetaPrimeDensity ThetaSevenPrimeBias ThetaJointCharacterBias ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans
open ThetaDyadicLaw ThetaCharacterCoefficient ThetaDiagonalConstant ThetaPNTCorollaries
open scoped Topology

theorem joint_sign_means :
    ∃ D : ℝ, 13/324 ≤ D ∧ Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D) ∧
      ∀ k r : ℕ, r.Coprime (2^k) → r<2^k → ∀ s t : ℝ, (s=1 ∨ s= -1) → (t=1 ∨ t= -1) →
        Tendsto (predicateMean (jointClass (2^k) r s t) residual) atTop (𝓝 (diagonalConstant+s*characterConstant+t*D)) ∧
        Tendsto (fun X => ((primeSet (jointClass (2^k) r s t) X).card:ℝ)/X.primeCounting) atTop
          (𝓝 ((1/4:ℝ)*(1/((2^k).totient:ℝ)))) :=
  ThetaJointCharacterBias.joint_prime_means progression_mangoldt

#print axioms joint_sign_means

theorem joint_sign_excursions {k r : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) {u : ℝ} (hu : u < characterConstant+13/324) :
    PositiveLowerPrimeDensity (fun p => jointClass (2^k) r 1 1 p ∧
      p*Real.log p/2+(diagonalConstant+u)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => jointClass (2^k) r (-1) (-1) p ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-u)*p) :=
  ThetaJointCharacterBias.S_joint_excursions progression_mangoldt hr hlt hu

#print axioms joint_sign_excursions

theorem one_mod_eight_joint_excursions {u : ℝ}
    (hu : u < characterConstant+13/324) :
    PositiveLowerPrimeDensity (fun p => (p%24=1 ∧ (p%7=3 ∨ p%7=5 ∨ p%7=6)) ∧
      p*Real.log p/2+(diagonalConstant+u)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => (p%24=17 ∧ (p%7=1 ∨ p%7=2 ∨ p%7=4)) ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-u)*p) :=
  ThetaJointCharacterBias.S_one_mod_eight_joint_excursions progression_mangoldt hu

#print axioms one_mod_eight_joint_excursions

theorem variance_lower_bound :
    ∃ V : ℝ, characterConstant^2+(13/324:ℝ)^2 ≤ V ∧ Tendsto (sampleVariance residual) atTop (𝓝 V) :=
  ThetaJointCharacterBias.variance_two_characters progression_mangoldt

#print axioms variance_lower_bound

theorem periodic_approximation_gap {m : ℕ} [NeZero m] (hm : ¬7∣m)
    {g : ℕ → ℝ} (hg : OnMod m g) {a : ℝ} (ha : a < 13/324) :
    ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |residual p-g p|) X :=
  ThetaSevenPrimeBias.seven_periodic_gap progression_mangoldt hm hg ha

#print axioms periodic_approximation_gap

end Arxiv.«2501.03234».ThetaJointBiasPNT
```

After building the progression bridge, extract and verify the joint module with the same paths.

```sh
awk '/^```lean$/ { lean = 1; next } lean && /^```$/ { exit } lean { print }' \
  "$NOTEBOOK/research/arxiv/theta-sum/TWO-CHARACTER-BIAS.md" > "$bridge_dir/ThetaJointBiasPNT.lean"
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  lean -o ThetaJointBiasPNT.olean ThetaJointBiasPNT.lean
  leanchecker -v ThetaJointBiasPNT
' sh "$bridge_dir" "$THETA_OLEANS" "$pnt_path"
```

All five joint declarations print only `propext`, `Classical.choice` and `Quot.sound`. Codex assisted with the derivation and Lean formalization.
