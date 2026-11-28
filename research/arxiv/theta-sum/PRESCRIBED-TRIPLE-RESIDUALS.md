# Disjoint prime triples with prescribed theta residuals

For a prime \(p\), let \(F(p)=S(p)/p-\frac12\log p\), using the canonical integer double sum. Write \(R=n^\theta\), \(L=1+\log n\). The two conclusions below concern ordered representations \(n=p_1+p_2+p_3\) with \(|p_i-n/3|\le R\). Every prime in the entire selected family occurs only once. [Original sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Ordinary counts and the elementary relative-error result](CENTRAL-PRIME-TRIPLES.md)

**Every sufficiently large odd target.** For some fixed finite \(B>0\), there are \(\gg R/L\) disjoint representations with all three \(|F(p_i)|<B\). In particular \(|S(p_i)-p_i\log p_i/2|<B p_i\), with the same \(B\) for all targets. Lean uses the explicit three- and five-form estimates of the preceding note and ordinary short-interval prime counts in progressions. The elementary theta estimate applies for fixed \(3/4<\theta<1\). With the classical complete Weil bound, the cited ordinary inputs supply the result for \(7/12<\theta<1\). [Original-sum theorem](ThetaBoundedResidualTriples.lean) · [Window second moment](ThetaCentralResidualBudget.lean) · [Short-interval prime input and its normalization](SHORT-RESIDUAL-LAW.md)

**Any prescribed open residual interval.** Fix \(y\in\mathbb R,d>0\) and any reduced starting class \(r\bmod q\). There is a single fixed reduced refinement \(a\bmod M\), with \(q\mid M\), \(a\equiv r\bmod q\), such that **every sufficiently large odd** \(n\equiv3a\bmod M\) has \(\gg R/(\varphi(M)L)\) disjoint representations with every \(p_i\equiv a\bmod M\) and every \(|F(p_i)-y|<d\). The modulus may be chosen at arbitrarily large refinement depth. Thus all three summands can have residuals in a fixed, arbitrarily distant interval on either side of zero. The target progression is selected along with the summand class. Its eligible odd integers form an infinite progression. The target residue \(3a\) can share a prime divisor with \(M\). The published ordinary prime-pattern theorem supplies the class estimates for \(\theta>5/8\); the newer preprint supplies them for \(\theta>3/5\). With the elementary theta input the joint range is \(\theta>3/4\); with Weil it reaches the quoted ordinary thresholds. The upper endpoint throughout is \(\theta<1\). [Prescribed-residual theorem](ThetaPrescribedTripleResiduals.lean) · [Uniform concentration in a fixed refined class](ThetaCentralResidualCells.lean) · [Earlier single-prime concentration](SHORT-RESIDUAL-LAW.md)

**Prime targets with four simultaneous marks.** Every sufficiently large prime \(p\equiv a\bmod M\) is the arithmetic mean of \(\gg p^\theta/(\varphi(M)\log p)\) disjoint triples of **other** primes in the same class, each with residual in \((y-d,y+d)\) and within \((3p)^\theta\) of \(p\). Apply the previous result at \(n=3p\) and discard the at most one triple containing \(p\). Moreover, the number of such prime targets with their **own** residual in the same interval is \(\ge\delta H/\log X\) in every sufficiently late admissible window \((X,X+H]\), for a fixed \(\delta>0\). Here \(X^\beta\le H\le X\), with \(\beta<\theta\) above the theta and ordinary short-interval thresholds used in the proof. This gives four distinct primes with jointly prescribed residuals and the exact relation \(3p=p_1+p_2+p_3\). [Every prime target in the selected class and four-mark count](ThetaPrimeBarycentres.lean)

## Kernel replay

Independent Lean 4.33.1 replay checked 208 modules, including the 190 notebook sources, the pinned DeepMind source, and the 15 external prime-number theorem modules and two documented bridges. All 674 distinct axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

## What allows a fixed residual bound

Let \(A\) be the prime window, \(E\) the primes to remove, \(d_A(p)=\#\{q\in A:n-p-q\in A,\ p+q\le n\}\), and \(J\) the triples meeting \(E\). Then
\[
 |J|^2\le 9|E|\sum_{p\in A}d_A(p)^2.
\]
Every lost triple meets an outlier, each vertex may occupy any of three coordinates, and Cauchy–Schwarz controls the sum of degrees over \(E\). Suppose the ordinary ordered count is at least \(bR^2/L^3\), and \(\sum d_A(p)^2\le C R^3/L^5\). A deletion of up to \(b^2 R/(144 C L)\) vertices loses at most one quarter of that lower count. Removing all repeated-coordinate triples costs at most \(3|A|\). For large targets at least half the ordinary lower count survives. A maximal matching then has size at least \(b^2 R/(108 C L)\). The second-moment calculation allows deletion of a fixed small fraction of the prime supply. [Finite incidence inequality](ThetaTernaryVertexDeletion.lean) · [Explicit deletion and matching constants](ThetaResilientCentralTriples.lean)

The short-interval second-moment comparison and its dyadic bound give \(\sum_{p\in A}|F(p)|^2\le K R/L\) with \(K\) independent of \(n\). Markov's inequality supplies a single \(B\) making the deletion budget hold for all large \(n\). For a prescribed residual interval we instead use the existing short-window concentration theorem with a tolerance fixed **before** selecting the refined modulus. The prime count in each fixed reduced class is \(O(R/(\varphi(M)L))\) with an absolute leading constant. Containing the central window in a translated interval preserves the outlier estimate at this scale. [Finite tail estimate and packing](ThetaBoundedResidualTriples.lean) · [Class outlier count](ThetaCentralResidualCells.lean)

## Normalization in the selected class

For every fixed \(M,a\) with \(a\) a unit, the second theorem uses ordinary three- and five-form estimates with normalized constants
\[
 b_M=bM/\varphi(M)^3,\qquad C_M=C M^2/\varphi(M)^5.
\]
The constants \(b,C>0\) must be independent of \(M,a\). Thresholds may depend on them. The identity \(b_M^2/C_M=b^2/(C\varphi(M))\) makes the outlier tolerance independent of the eventual refinement. This quantifier is necessary to choose the class using concentration.

Here is the paper specialization. Parametrize the independent prime coordinates as \(a+Mx_i\). Since \(n\equiv3a\bmod M\), all three or five affine forms in the earlier count are identically \(a\bmod M\). At \(\ell\mid M\) their local factor is \((1-1/\ell)^{-t}\) for \(t=3,5\). At all other primes the change of variables is bijective modulo \(\ell\), giving the unrestricted factors of the preceding note. Their remaining products are bounded below uniformly for the three-form system on odd targets, and above uniformly for the five-form system. Scaling the coordinate box gives areas \(\asymp (R/M)^2\) and volumes \(O((R/M)^3)\). Together these give the two displayed factors. Each application has fixed coefficients \(O(M)\), translated endpoint \(\asymp n/M\), length \(\asymp R/M\), and a fixed positive exponent margin. The paper's error may depend on \(M\), and is absorbed at a later threshold. Prime powers in the lower count cost \(o_M((R/M)^2)\) in von Mangoldt weight since \(\theta>1/2\). The supplementary fixed-modulus PNT used for the earlier concentration is available through the documented PNT bridge. The analytic estimates themselves, including the complete Weil bound in the wider range, remain explicit inputs to Lean. [Matomäki–Shao–Tao–Teräväinen, Theorem 1.7](https://www.cambridge.org/core/journals/forum-of-mathematics-pi/article/higher-uniformity-of-arithmetic-functions-in-short-intervals-i-all-intervals/6DF08E2A3EFABB2DD0DA6CDA38649B18) · [Matomäki–Pandey–Pliego–Teräväinen–Wang, Theorem 1.8](https://arxiv.org/html/2610.09567v1#S1.Thmtheorem8) · [Thorner–Zaman](https://arxiv.org/pdf/2108.10878#page=3) · [Fixed-modulus PNT bridge](NATURAL-PRIME-MEAN.md)

The upstream conjectures are pointwise inequalities for all eligible primes. The active remainder reduction and finite-range checks concern that universal quantifier. The results here describe the additive structure of primes where the signed sum obeys the specified inequalities. [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA finite reduction](https://github.com/lefttosolve2/open-math-agents/pull/34398) · [Left to Solve](https://www.lefttosolve.com/p/Arxiv.2501.03234.conjecture_4_2.R1.H1)

## Fixed-progression PNT bridge

The following module discharges the global fixed-progression PNT in the prescribed-class, prime-barycentre and four-mark theorems. The short-interval and prime-pattern estimates remain explicit. Compile the documented PNT bridge first in the same pinned environment. [External source and replay instructions](NATURAL-PRIME-MEAN.md)

```lean
import ThetaPrimeBarycentres
import ThetaPNTCorollaries

/-! Three prescribed-residual theorems with the global progression PNT discharged. -/
namespace Arxiv.«2501.03234».ThetaPrescribedTriplePNT
open Real Filter Finset ThetaTernaryPacking ThetaTernaryIncidence ThetaCalibratedCone
open ThetaPrescribedTripleResiduals ThetaClassConcentration ThetaNaturalPrimeMeans
open ThetaPrimeBarycentres
noncomputable section

theorem prescribed {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β)
    (hb : 0<b) (hC : 0<C) (hc : OrdinaryClasses θ b C)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) (N : ℕ) :
    ∃ T≥N, q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧
      ∀ᶠ n : ℕ in atTop,Odd n → n%(m T)=(3*a)%(m T) →
      ∃ D : Finset Triple,
        b^2*(n:ℝ)^θ/(108*C*(m T).totient*(1+log n))≤D.card ∧ separated D ∧
        ∀ t∈D,t.1+t.2.1+t.2.2=n ∧ t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2 ∧
          ∀ p∈vertices t,p.Prime ∧ |(p:ℝ)-(n:ℝ)/3|≤(n:ℝ)^θ ∧ p%(m T)=a ∧
            |(S p:ℝ)/p-log p/2-y|<d :=
  ThetaPrescribedTripleResiduals.original he ht hk hβ hθ htop ord ThetaPNTCorollaries.progression_mangoldt
    hb hC hc hq hr hu y hd N

theorem barycentres {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β)
    (hb : 0<b) (hC : 0<C) (hc : OrdinaryClasses θ b C)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) (N : ℕ) :
    ∃ T≥N,q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧
      ∀ᶠ p : ℕ in atTop,p.Prime → p%(m T)=a → Rich θ b C (m T) a y d p :=
  ThetaPrimeBarycentres.original he ht hk hβ hθ htop ord ThetaPNTCorollaries.progression_mangoldt
    hb hC hc hq hr hu y hd N

theorem four_marks {e : ℕ} (he : 32≤e) (ht : e≤48) (hk : Kernel e)
    {β θ b C : ℝ} (hβ : (e:ℝ)/64<β) (hθ : β<θ) (htop : θ<1)
    (ord : ThetaLocalPrimeCounts.Ordinary β)
    (hb : 0<b) (hC : 0<C) (hc : OrdinaryClasses θ b C)
    {q r : ℕ} (hq : 0<q) (hr : r<q) (hu : r.Coprime q)
    (y : ℝ) {d : ℝ} (hd : 0<d) (N : ℕ) :
    ∃ T≥N,q∣m T ∧ ∃ a < m T,a.Coprime (m T) ∧ a%q=r ∧ ∃ δ : ℝ,0<δ ∧
      ∀ᶠ X : ℕ in atTop,∀ H : ℕ,H≤X → (X:ℝ)^β≤H →
        δ*H/log X≤((marked θ b C (m T) a y d X H).card:ℝ) :=
  ThetaPrimeBarycentres.four_marks he ht hk hβ hθ htop ord ThetaPNTCorollaries.progression_mangoldt
    hb hC hc hq hr hu y hd N

#print axioms prescribed
#print axioms barycentres
#print axioms four_marks
end
end Arxiv.«2501.03234».ThetaPrescribedTriplePNT
```
