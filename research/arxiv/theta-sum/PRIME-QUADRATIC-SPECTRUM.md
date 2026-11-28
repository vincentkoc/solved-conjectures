# Quadratic correlations of the prime theta residual

Let $R(p)=S(p)/p-\tfrac12\log p$ for the original integer theta sum. For every odd prime conductor $q$, the ordinary limit
\[
 C_q=\lim_{X\to\infty}\frac{1}{\pi(X)}
     \sum_{p\le X,\ p\ {\rm prime}}\left(\frac pq\right)R(p)
\]
exists. **It vanishes exactly when $q\equiv1\pmod4$.** For $q\equiv3\pmod4$ its sign is the sign of the finite integer $P_q=\sum_{0\le j<q}(-1)^{j+1}(\frac jq)$. At $q=11$ the proof gives $C_{11}>1/31$. The index $q$ labels a fixed test character, while the average runs over all primes $p$. [Kernel declarations](ThetaPrimeSpectrum.lean) · [Earlier conductors three and seven](TWO-CHARACTER-BIAS.md) · [Pinned upstream sum](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean)

**Every fixed congruence model leaves positive error.** For each $m\ge1$ there is a $\delta_m>0$ such that, for every real function $g$ on $\mathbb Z/m\mathbb Z$,
\[
  \liminf_{X\to\infty}\frac1{\pi(X)}
      \sum_{p\le X,\ p\ {\rm prime}}|R(p)-g(p\bmod m)|\ \ge\ \delta_m.
\]
Choose a prime $q>m$ with $q\equiv3\pmod4$. The Chinese remainder theorem and the prime number theorem in progressions give zero limiting correlation between $(\frac{\cdot}{q})$ and $g$. One can take $\delta_m=|C_q|$. The eventual cutoff for each strict lower threshold may depend on $g$. This permits models with growing periods to approximate $R$, as in the construction of its limiting distribution. [Finite quotient proof](ThetaPrimeSpectrum.lean) · [Prime residual law](PRIME-RESIDUAL-LAW.md)

## Magnitude and a finite certificate

Write $\chi(n)=(\frac nq)$ and $L_q=L(1,\chi)>0$. For every $q\equiv3\pmod4$,
\[
 |C_q|\ \ge\ |P_q|L_q\,\frac{1-\chi(2)/2}{q(q-1)}.
\]
For every integer $K\ge1$, the lower bound remains valid with $L_q$ replaced by $\sum_{1\le n<K}\chi(n)/n-q/K$. It becomes positive for all sufficiently large $K$. For $q=11$, $P_q=6$ and $\chi(2)=-1$. Taking $K=22$ gives a lower bound $8513783/258658400>1/31$. The joint declaration below checks the strict bound directly by rational arithmetic.

The uniform truncation estimate follows by summation by parts. A nonprincipal character has zero sum on every complete period, so every interval sum has norm at most $q$. For real $s\ge1$, decreasing weights $n^{-s}$ bound every tail starting at $K$ by $q/K$. First send the upper endpoint to infinity at $s>1$, then send $s$ down to 1 by continuity of the continued Dirichlet $L$-function. This identifies the ordinary, consecutively ordered harmonic sums at 1. For a real quadratic character, the Euler products to the right of 1 are nonnegative. Nonvanishing at 1 gives strict positivity. [Harmonic error and limit](ThetaCharacterHarmonicLimit.lean) · [Pinned mathlib nonvanishing theorem](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Nonvanishing.lean)

## Passage from rows to the prime mean

Define $A_q(d)=0$ unless $d$ is odd and $q\mid d$. Otherwise put
\[
 A_q(d)=\frac{\displaystyle
   \prod_{\ell\mid d,\,\ell\ne q}(1-\chi(\ell))\
   \prod_{\ell\mid 2d,\,\ell\ne q}(1-\chi(\ell)/\ell)}
 {d\varphi(d)},
\]
where the products run over distinct primes. Every $A_q(d)$ is nonnegative and $A_q(q)>0$. The proof gives the ordinary limit
\[
 C_q=\lim_{T\to\infty} P_qL_q \sum_{2\le d\le T}A_q(d).
\]
For each fixed denominator cutoff $T$, the numerator cutoff goes to infinity first. Inclusion and exclusion gives the two displayed products, and rows with $q\nmid d$ have zero twisted mean by the Chinese remainder theorem. The prime mean absolute approximation then permits $T\to\infty$. The sign enters after the numerator limit. For $q\equiv1\pmod4$ reflection kills $P_q$. For $q\equiv3\pmod4$, $P_q$ is minus twice a sum of $(q-1)/2$ terms in $\{\pm1\}$, an odd number of terms. [Row factorization](ThetaLegendreFactors.lean) · [Iterated transfer](ThetaPrimeSpectrum.lean)

## Relation to the classical quadratic excess

Put $H_q=\sum_{j=1}^{(q-1)/2}\chi(j)$. Lean proves $P_q=-2\chi(2)H_q$. Dirichlet's classical formula $H_q=(2-\chi(2))\sqrt q\,L_q/\pi$ for $q\equiv3\pmod4$ then yields
\[
  \operatorname{sign} C_q=-\chi(2),\qquad
  |C_q|\ge\frac{\pi H_q^2}{\sqrt q\,q(q-1)}.
\]
Thus these prime correlations are positive at conductors $3\bmod8$ and negative at conductors $7\bmod8$. Both classes contain infinitely many primes. The declaration `of_quadratic_excess_formula` checks the implication with the classical identity as an explicit premise. The unconditional kernel declarations above establish the sign through $P_q$, nonvanishing, and the finite-prefix bounds independently. [Quadratic excess formula in Göral, introduction after (1.3)](https://imar.ro/journals/Mathematical_Reports/Pdfs/2022/4/7.pdf) · [Lean implication](ThetaPrimeSpectrum.lean)

## Source comparison and replay

Berndt, Bhat, Meyer, Xie and Zaharescu define the same double sum. Their v3 Conjecture 1.1 asks for positivity at every odd prime above 5. The pinned DeepMind predicate asks for every odd prime and separately records $S(3)=2$ and $S(5)=4$. The correlation and approximation results concern ordinary prime averages. The pointwise conjecture remains open. Lägeler studies individual Hardy sums. Guo and Zhang's Lemma 4 expands a single Hardy sum $S_1(h,p)$ using characters of the denominator $p$. Here the quadratic conductor $q$ stays fixed as the denominator prime $p$ varies. The DeepMind, OMA and LTS searches found a remainder reduction, finite certificates and a harmonic estimate, with no matching all-conductor prime correlation statement. [Source paper](https://arxiv.org/pdf/2501.03234v3) · [Lägeler](https://arxiv.org/abs/2207.04828) · [Guo and Zhang, Lemma 4](https://dml.cz/dmlcz/141636) · [DeepMind issue](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA certificate](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/21967) · [LTS solved feed](https://lefttosolve.com/api/solved)

The following joint module uses the pinned prime number theorem in progressions. Save the block as `ThetaPrimeSpectrumPNT.lean` and use the same source-build procedure as for the natural prime mean. Each of the five declarations has only `propext`, `Classical.choice` and `Quot.sound` in its axiom audit. [Pinned joint replay instructions](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```lean
import ThetaPrimeSpectrum
import ThetaPNTCorollaries

/-! Ordinary quadratic correlations of the original prime theta sum. -/
namespace Arxiv.«2501.03234».ThetaPrimeSpectrumPNT
open Finset Filter Topology ThetaNaturalPrimeMeans ThetaLegendreFactors ThetaPNTCorollaries

/-- The correlation exists for every odd prime conductor. Its vanishing and sign are classified. -/
theorem quadratic_spectrum (q : ℕ) [Fact q.Prime] (ho : Odd q) :
    ∃ C : ℝ, Tendsto (primeMean (fun p => (legendreSym q (p:ℤ):ℝ)*
      ((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 C) ∧ (C=0 ↔ q%4=1) ∧
      (q%4=3 → 0<(parityFactor q:ℝ)*C) := by
  have he (p : ℕ) : legendreSym q (p:ℤ)=symbol q p := by
    simp only [legendreSym,symbol,Int.cast_natCast]
  simp_rw [he]
  by_cases h : q%4=1
  · refine ⟨0,ThetaPrimeSpectrum.even_character_mean q progression_mangoldt h,by simp [h],?_⟩
    omega
  · have h3 : q%4=3 := by have := Nat.odd_iff.mp ho; omega
    obtain ⟨_,C,_,_,hC,hn,hpos,_⟩ := ThetaPrimeSpectrum.prime_correlation q progression_mangoldt h3
    exact ⟨C,hC,by simp [h,hn],fun _ => hpos⟩

/-- The conductor alone gives a lower bound, and the full correlation is an ordinary
limit of finite denominator sums. -/
theorem conductor_bound (q : ℕ) [Fact q.Prime] (hq : q%4=3) :
    ∃ L C : ℝ, 0<L ∧ Tendsto (fun K => ∑ n∈range (K+1),(legendreSym q (n:ℤ):ℝ)/n) atTop (𝓝 L) ∧
      Tendsto (primeMean (fun p => (legendreSym q (p:ℤ):ℝ)*((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 C) ∧
      |(parityFactor q:ℝ)*L| * ((1-(legendreSym q 2:ℝ)/2)/((q:ℝ)*q.totient)) ≤ |C| ∧
      Tendsto (fun T => (parityFactor q:ℝ)*L*∑ d∈Icc 2 T,ThetaPrimeSpectrum.amplitude q d)
        atTop (𝓝 C) := by
  obtain ⟨L,C,hl,hL,hC,_,_,hbound,hlim⟩ := ThetaPrimeSpectrum.prime_correlation q progression_mangoldt hq
  have he (p : ℕ) : legendreSym q (p:ℤ)=symbol q p := by
    simp only [legendreSym,symbol,Int.cast_natCast]
  rw [ThetaPrimeSpectrum.conductor_amplitude q (Nat.odd_iff.mpr (by omega))] at hbound
  refine ⟨L,C,hl,?_,?_,?_,hlim⟩
  · change Tendsto (fun K => ThetaCharacterSeven.siftedSum (term q) ∅ K) atTop (𝓝 L) at hL
    simpa only [he,ThetaCharacterSeven.siftedSum,ThetaCharacterSeven.sift,notMem_empty,
      IsEmpty.forall_iff,implies_true,if_true,term] using hL
  · simpa only [he,ThetaCharacterPrimeMeans.residual] using hC
  · simpa only [show legendreSym q 2=symbol q 2 from he 2] using hbound

/-- Every finite Legendre prefix gives a certified lower bound for the magnitude of the
original prime correlation. For a sufficiently long prefix the bound is positive. -/
theorem finite_prefix_bound (q : ℕ) [Fact q.Prime] (hq : q%4=3) :
    ∃ C : ℝ, Tendsto (primeMean (fun p => (legendreSym q (p:ℤ):ℝ)*
      ((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 C) ∧ ∀ K : ℕ, 0<K →
      |(parityFactor q:ℝ)| * ((∑ n∈range K,(legendreSym q (n:ℤ):ℝ)/n)-q/(K:ℝ)) *
        ((1-(legendreSym q 2:ℝ)/2)/((q:ℝ)*q.totient)) ≤ |C| := by
  obtain ⟨L,C,hpos,hL,hC,_,_,hbound,_⟩ := ThetaPrimeSpectrum.prime_correlation q progression_mangoldt hq
  have he (n : ℕ) : legendreSym q (n:ℤ)=symbol q n := by simp only [legendreSym,symbol,Int.cast_natCast]
  refine ⟨C,by simpa only [he,ThetaCharacterPrimeMeans.residual] using hC,?_⟩
  intro K hK
  have h := (abs_le.mp (reciprocal_error q (by omega) hL hK)).1
  have he2 : legendreSym q 2=symbol q 2 := he 2
  simp only [he,he2,← ThetaPrimeSpectrum.conductor_amplitude q (Nat.odd_iff.mpr (by omega))]
  rw [abs_mul,abs_of_pos hpos] at hbound
  apply le_trans _ hbound
  apply mul_le_mul_of_nonneg_right _ (ThetaPrimeSpectrum.amplitude_nonneg q q)
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  unfold term at h
  linarith

local instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- An explicit third signed coefficient, using just the first 21 reciprocal terms. -/
theorem eleven_positive :
    ∃ C : ℝ, 1/31 < C ∧ Tendsto (primeMean (fun p => (legendreSym 11 (p:ℤ):ℝ)*
      ((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 C) := by
  obtain ⟨C,hC,hb⟩ := finite_prefix_bound 11 (by decide)
  obtain ⟨D,hD,_,hs⟩ := quadratic_spectrum 11 (by decide)
  have he := tendsto_nhds_unique hC hD
  have hpar : parityFactor 11 = 6 := by
    have h (j : ℕ) : symbol 11 j=legendreSym 11 (j:ℤ) := by
      simp only [legendreSym,symbol,Int.cast_natCast]
    norm_num [parityFactor,ThetaCharacterThree.parity,Finset.sum_range_succ,h]
  have hp := hs (by decide : 11%4=3)
  rw [← he,hpar] at hp
  have hp' : 0<C := by norm_num at hp; linarith
  have H := hb 22 (by decide)
  rw [abs_of_pos hp',hpar] at H
  norm_num [Finset.sum_range_succ,show Nat.totient 11=10 by decide] at H
  exact ⟨C,by linarith,hC⟩

/-- A positive obstruction to every real model on a fixed finite congruence quotient. -/
theorem finite_quotient_gap (m : ℕ) [NeZero m] :
    ∃ δ : ℝ, 0<δ ∧ ∀ g : ZMod m → ℝ, ∀ a<δ, ∀ᶠ X : ℕ in atTop,
      a < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g (p:ZMod m)|) X := by
  obtain ⟨δ,hδ,H⟩ := ThetaPrimeSpectrum.fixed_period_gap progression_mangoldt m
  refine ⟨δ,hδ,fun g => H (fun n => g (n:ZMod m)) ?_⟩
  intro n; simp

#print axioms quadratic_spectrum
#print axioms conductor_bound
#print axioms finite_prefix_bound
#print axioms eleven_positive
#print axioms finite_quotient_gap
end Arxiv.«2501.03234».ThetaPrimeSpectrumPNT
```
