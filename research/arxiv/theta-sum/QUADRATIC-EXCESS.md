# Signs of quadratic prime correlations and the error of congruence models

Write $R(p)=S(p)/p-\tfrac12\log p$, where $S$ is the original integer sum. Let $C_q$ be the ordinary prime mean of $(\frac pq)R(p)$ at a fixed odd prime conductor $q$. The previous result gave existence and a finite formula for its sign. The sign now follows directly from its residue class.
$$
 C_q>0\quad(q\equiv3\bmod8),\qquad
 C_q<0\quad(q\equiv7\bmod8),\qquad
 C_q=0\quad(q\equiv1\bmod4).
$$
The first two cases each give an infinite family. The average runs over every prime $p\le X$ with denominator $\pi(X)$. The character vanishes at $p=q$. [Previous spectrum and zero class](PRIME-QUADRATIC-SPECTRUM.md) · [Quadratic excess](ThetaQuadraticExcess.lean)

For $g:\mathbb Z/m\mathbb Z\to\mathbb R$, put
$$
 D_m(g)=\liminf_{X\to\infty}\frac1{\pi(X)}
       \sum_{p\le X,\ p\ {\rm prime}}|R(p)-g(p\bmod m)|.
$$
For every $m\ge1$, $D_m(g)\ge \pi/(4m)^{5/2}$. More sharply, for every real $b>2$, **all sufficiently large $m$** satisfy
$$
                  D_m(g)\ \ge\ \frac{\pi}{(b\log m)^{5/2}}
$$
for every such $g$. Lean states both bounds as eventual strict inequalities for each threshold below the right-hand side. The period cutoff depends on $b$. The prime endpoint cutoff may also depend on the fixed period, model and threshold. [Approximation bounds](ThetaQuotientGap.lean)

## From the half-period to the sign

For $q\equiv3\bmod4$, write $\chi=(\frac{\cdot}{q})$, $H_q=\sum_{1\le j\le(q-1)/2}\chi(j)$, $W_q=\sum_{a=0}^{q-1}a\chi(a)$ and $L_q=\sum_{n\ge1}\chi(n)/n>0$ in natural order. Abel summation of the finite Fourier transform gives $\operatorname{Im}(\tau_q)L_q=-\pi W_q/q$. Indeed the boundary value of the imaginary part of $-\log(1-r e^{2\pi i a/q})$ as $r\uparrow1$ is $\pi/2-\pi a/q$ at every $0<a<q$. The zero class has character value zero. Permuting residues by doubling gives $(\chi(2)-2)W_q=qH_q$. The classical Gauss evaluation $\tau_q=i\sqrt q$ therefore yields Dirichlet's quadratic-excess formula
$$
             H_q=(2-\chi(2))\sqrt q\, L_q/\pi.
$$
In particular $H_q>0$. The conductor parity factor is $-2\chi(2)H_q$, which gives the two signed classes by the supplementary law at 2. The classical formula is already recorded in the literature. The [all-conductor Euler products](QUADRATIC-EULER-PRODUCT.md) subsequently evaluate the full signed coefficient and isolate the uniformly convergent quadratic component. [Göral, introduction after equation (1.3)](https://imar.ro/journals/Mathematical_Reports/Pdfs/2022/4/7.pdf) · [Fourier argument and doubling](ThetaQuadraticExcess.lean) · [Ordered character harmonic limit](ThetaCharacterHarmonicLimit.lean)

For the error bound, the squared Gauss identity already gives $|\operatorname{Im}\tau_q|=\sqrt q$. The positive conductor row in the prime correlation then yields
$$
                |C_q|\ \ge\ \frac{\pi H_q^2}{\sqrt q\,q(q-1)}.
$$
The integer $H_q$ is odd because it is a sum of an odd number of signs. If $q\nmid m$, progression equidistribution gives prime mean zero for $\chi(p)g(p\bmod m)$. Since $|\chi|\le1$, this makes $D_m(g)\ge |C_q|$. Choose a prime $q\equiv3\bmod4$ dividing $4m-1$ for the bound valid at every period. For the logarithmic estimate, put $N=\lfloor b\log m\rfloor$. The sum of $\log q$ over $q\le N$, $q\equiv3\bmod4$, exceeds $cN$ eventually for each $c<1/2$, by the prime number theorem in the single progression $3\bmod4$ and a prime-power error of order $\sqrt N$. Choose $1/b<c<1/2$. If all the selected primes divided $m$, their product would divide $m$, contradicting $cN>\log m$ for large $m$. This supplies a missing conductor $q\le b\log m$. The coefficient 2 is sharp for this selection argument. For each $0<b<2$, there are arbitrarily large periods divisible by every prime $q\equiv3\bmod4$ up to $b\log m$. Take $m$ to be the product of the selected primes through $N$, so $\log m\sim N/2$. This sharpness statement concerns the missing prime, and the optimal approximation error remains open. [Quantitative proof](ThetaQuotientGap.lean) · [Period orthogonality](ThetaPrimeSpectrum.lean) · [Progression input](NATURAL-PRIME-MEAN.md#joint-lean-replay)

## Comparison with the original conjecture and related work

Berndt, Bhat, Meyer, Xie and Zaharescu ask for $S(p)>0$ at all odd primes above 5. DeepMind's pinned declaration asks for all odd primes. The sign evaluated here belongs to a correlation of the centered sum along primes. Positivity at each prime is open. Theorem 2 of the 2014 Hardy and Kloosterman sums paper also has a modulo-eight split and a class-number square. It sums squared Kloosterman weights and a Hardy sum over two numerator residues at one fixed denominator. Here the denominator varies over primes and the quadratic test character has fixed conductor. Searches of the DeepMind issue and PR tracker, OMA and Left to Solve found the existing remainder reduction, finite certificates and harmonic bounds. [Source paper](https://arxiv.org/pdf/2501.03234v3) · [Pinned declaration](https://github.com/google-deepmind/formal-conjectures/blob/f606af160664c5a10952e9a957b100a1cd45bbeb/FormalConjectures/Arxiv/2501.03234/ArithmeticSumS.lean) · [Hardy and Kloosterman sums, Theorem 2](https://doi.org/10.1186/1029-242X-2014-52) · [DeepMind reduction](https://github.com/google-deepmind/formal-conjectures/issues/7589) · [OMA harmonic bound](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/22818) · [Left to Solve](https://lefttosolve.com/api/solved)

## Joint kernel replay

The notebook modules above use the frozen Formal Conjectures environment on Lean 4.33.1. The joint module below also imports the progression theorem and the evaluated prime Gauss sum. The latter comes from the Apache-2.0 licensed `real-dirichlet-dbn-lean` project. Its native pin uses Lean 4.34.1. The following extraction keeps both prerequisite lemma bodies intact, the whole quadratic Gauss proof, and the prime-conductor file through `gaussSum_eq_gaussG`. Source hashes and output hashes fix the exact extraction. [Source and license](https://github.com/DrMurphyIsIn/real-dirichlet-dbn-lean/tree/41672de34fc7c4aab157ec5f0b5962c18e29227e) · [Gauss evaluation](https://github.com/DrMurphyIsIn/real-dirichlet-dbn-lean/blob/41672de34fc7c4aab157ec5f0b5962c18e29227e/lean/gauss/GaussQuad.lean) · [Prime-character identification](https://github.com/DrMurphyIsIn/real-dirichlet-dbn-lean/blob/41672de34fc7c4aab157ec5f0b5962c18e29227e/lean/gauss/GaussPrime.lean)

Use the same `THETA_OLEANS`, `pnt_path` and `bridge_dir` as in the natural-prime replay, including its compiled `ThetaPNTCorollaries`. Export `BRIDGE_DIR="$bridge_dir"` and run the Python block, then save the Lean block there as `ThetaExcessSignsPNT.lean`. [Natural-prime setup](NATURAL-PRIME-MEAN.md#joint-lean-replay)

```python
from hashlib import sha256
from pathlib import Path
from urllib.request import urlopen
import os

out = Path(os.environ["BRIDGE_DIR"])
base = "https://raw.githubusercontent.com/DrMurphyIsIn/real-dirichlet-dbn-lean/41672de34fc7c4aab157ec5f0b5962c18e29227e/lean/"
sources = {
    "gen/GenThetaFE": ("2aefc5e5c362c9bdc13053cd8226b4b3453e1b9f50cb23f1968c30f2e647e024",
                       "1538517d49d11ef65081e02dc99da1d0ee62c643565fa9c1e1a160bc5cc72e6b"),
    "gauss/GaussQuad": ("9a55f4bb21fc9c01dcebd3af204ba40504f36fd36bc9e9d52a8a4c37bfdee02a",
                        "9a55f4bb21fc9c01dcebd3af204ba40504f36fd36bc9e9d52a8a4c37bfdee02a"),
    "gauss/GaussPrime": ("b271b06e568be79ae93332d565c42f6239fb53f8769febbcbfc6a645bd17f96a",
                         "965ef3d9b066a10d31818d5cc0bc24f3507d5efb1325c844a779c69e79716078"),
}
for path, (source_hash, extracted_hash) in sources.items():
    with urlopen(base + path + ".lean") as response:
        data = response.read()
    assert sha256(data).hexdigest() == source_hash
    source = data.decode()
    name = path.split("/")[-1]
    if name == "GenThetaFE":
        start = source.index("theorem hasSum_residue ")
        end = source.index("/-- **Gauss sum.", start)
        header = ("import Mathlib\n\nopen Real MeasureTheory Set Filter Topology Complex HurwitzZeta ZMod\n\n"
                  "namespace DBN.Gen\nvariable {N : ℕ} [NeZero N]\n\n")
        source = header + source[start:end] + "end DBN.Gen\n"
    elif name == "GaussPrime":
        end = source.rfind("/--", 0, source.index("theorem isPrimitive_of_prime"))
        source = source[:end] + "end DBN.Gen\n"
    result = source.encode()
    assert sha256(result).hexdigest() == extracted_hash
    (out / (name + ".lean")).write_bytes(result)
```

```lean
import ThetaQuotientGap
import GaussPrime
import ThetaPNTCorollaries
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! Signed consequences of the prime quadratic Gauss sum evaluation. -/
namespace Arxiv.«2501.03234».ThetaExcessSignsPNT
open Finset Filter Topology Complex ThetaPrimeSpectrum ThetaLegendreFactors ThetaQuadraticExcess
open ThetaPNTCorollaries ThetaNaturalPrimeMeans

private theorem gauss_im (q : ℕ) [Fact q.Prime] (hq : q%4=3) : (tau q).im=Real.sqrt q := by
  have he := DBN.Gen.gaussSum_eq_gaussG (p:=q) (by omega) (dirChar q) (nonprincipal q (by omega))
    (fun n => by change ((quadraticChar (ZMod q) (n:ZMod q):ℤ):ℂ).im=0; simp)
  rw [DBN.Gen.gaussG_eq] at he
  have hp : (-I)^q=I := by
    rw [← Nat.div_add_mod q 4,hq,pow_add,pow_mul]
    norm_num [I_sq,show (-I)^4=(1:ℂ) by norm_num [neg_pow,I_pow_four],pow_succ]
  rw [hp] at he
  change (gaussSum (dirChar q) ZMod.stdAddChar).im = _
  rw [he]
  simp

/-- Dirichlet's half-period formula for the ordinary, ordered Legendre harmonic limit. -/
theorem dirichlet_excess (q : ℕ) [Fact q.Prime] (hq : q%4=3) {L : ℝ}
    (hL : Tendsto (ThetaCharacterSeven.siftedSum (term q) ∅) atTop (𝓝 L)) :
    (excess q:ℝ) = (2-(symbol q 2:ℝ))*Real.sqrt q*L/Real.pi := by
  rw [← gauss_im q hq]
  exact excess_eq_gauss q hq hL

/-- Sign and size of the correlation in the original theta residual, with the
quadratic excess evaluated by the classical Gauss sum. -/
theorem signed_correlation (q : ℕ) [Fact q.Prime] (hq : q%4=3) :
    ∃ C : ℝ, Tendsto (primeMean (fun p => (legendreSym q (p:ℤ):ℝ)*((S p:ℝ)/p-Real.log p/2))) atTop (𝓝 C) ∧
      (q%8=3 → 0<C) ∧ (q%8=7 → C<0) ∧
      Real.pi*(excess q:ℝ)^2/(Real.sqrt q*((q:ℝ)*q.totient)) ≤ |C| := by
  obtain ⟨C,hC,hs,hb⟩ := of_quadratic_excess_formula q progression_mangoldt hq (excess q) rfl
    (fun L hL => dirichlet_excess q hq hL)
  have he (p : ℕ) : legendreSym q (p:ℤ)=symbol q p := by simp only [legendreSym,symbol,Int.cast_natCast]
  have h2 : symbol q 2=ZMod.χ₈ q := (he 2).symm.trans (legendreSym.at_two (p:=q) (by omega))
  refine ⟨C,by simpa only [he,ThetaCharacterPrimeMeans.residual] using hC,?_,?_,hb⟩
  · intro h
    have H : symbol q 2= -1 := by rw [h2,ZMod.χ₈_nat_mod_eight,h]; decide
    simpa [H] using hs
  · intro h
    have H : symbol q 2=1 := by rw [h2,ZMod.χ₈_nat_mod_eight,h]; decide
    simpa [H] using hs

/-- Every function on a fixed finite residue ring incurs the explicit lower error. -/
theorem all_periods (m : ℕ) [NeZero m] (g : ZMod m → ℝ) {a : ℝ}
    (ha : a < Real.pi/(Real.sqrt (4*(m:ℝ))*(4*m)^2)) :
    ∀ᶠ X : ℕ in atTop, a < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g (p:ZMod m)|) X :=
  ThetaQuotientGap.effective_period_gap progression_mangoldt m g ha

/-- For every b > 2, all sufficiently large fixed periods have a logarithmic error floor. -/
theorem large_periods {b : ℝ} (hb : 2<b) :
    ∀ᶠ m : ℕ in atTop, ∀ g : ZMod m → ℝ, ∀ a < Real.pi/
      (Real.sqrt (b*Real.log m)*(b*Real.log m)^2), ∀ᶠ X : ℕ in atTop,
      a < primeMean (fun p => |(S p:ℝ)/p-Real.log p/2-g (p:ZMod m)|) X :=
  ThetaQuotientGap.logarithmic_period_gap progression_mangoldt hb

/-- Every smaller coefficient in the missing-conductor cutoff fails for unbounded periods. -/
theorem sharp_threshold {b : ℝ} (hb : 0<b) (hb2 : b<2) :
    ∃ᶠ m : ℕ in atTop, ∀ q : ℕ, q.Prime → q%4=3 → (q:ℝ)≤b*Real.log m → q∣m :=
  ThetaQuotientGap.sharp_conductor_threshold progression_mangoldt hb hb2

#print axioms sharp_threshold
#print axioms DBN.Gen.gaussG_eq
#print axioms DBN.Gen.gaussSum_eq_gaussG
#print axioms all_periods
#print axioms large_periods
#print axioms gauss_im
#print axioms dirichlet_excess
#print axioms signed_correlation
end Arxiv.«2501.03234».ThetaExcessSignsPNT
```

```sh
lake env sh -ec '
  export LEAN_PATH="$1:$2:$3:$LEAN_PATH"
  cd "$1"
  for module in GenThetaFE GaussQuad GaussPrime ThetaExcessSignsPNT; do
    lean -o "$module.olean" "$module.lean"
    leanchecker -v "$module"
  done
' sh "$BRIDGE_DIR" "$THETA_OLEANS" "$pnt_path"
```

The final sign and both lower bounds have only `propext`, `Classical.choice` and `Quot.sound` in their declaration-level axiom reports. Codex assisted with the proof and verification.
