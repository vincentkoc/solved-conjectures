import ThetaLocalWeightedLimits
import ThetaResidualMoments

/-! A global prime-mean periodic approximation for continuous functions with
polynomial growth, obtained by clipping on a compact residual interval. -/
namespace Arxiv.«2501.03234».ThetaPrimeTestApproximation
open Real Finset Filter MeasureTheory ThetaPrimeLaw ThetaNaturalPrimeMeans ThetaProfiniteUnits
open ThetaCharacterPrimeMeans ThetaPeriodMeans
open scoped Topology
noncomputable section

def clip (L x : ℝ) := max (min x L) (-L)

private theorem clip_mem {L : ℝ} (hL : 0≤L) (x : ℝ) : clip L x∈Set.Icc (-L) L :=
  ⟨le_max_right ..,max_le (min_le_right ..) (by linarith)⟩

private theorem pointwise {φ : ℝ → ℝ} (hφ : Continuous φ) {K : ℝ} (hK : 0≤K) (k : ℕ)
    (hg : ∀ x, |φ x|≤K*(1+|x|^k)) {L t : ℝ} (hL : 1≤L) (ht : 0<t) :
    ∃ B : ℝ, 0≤B ∧ ∀ x z : ℝ, |φ x-φ (clip L z)|≤t+B*|x-z|+(4*K/L)*|x|^(k+1) := by
  let M := K*(1+L^k)
  have hL' : 0<L := by linarith
  have hM : 0≤M := by dsimp [M];positivity
  obtain ⟨d,hd,hnear⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous (s:=Set.Icc (-L) L) hφ.continuousOn) t ht
  let B := 2*M/d
  have hB : 0≤B := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  intro x z
  have hz := clip_mem hL'.le z
  have hclip := abs_le.mpr hz
  have hφz := (hg (clip L z)).trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl 1) (pow_le_pow_left₀ (abs_nonneg _) hclip k)) hK)
  have hnorm := abs_sub (φ x) (φ (clip L z))
  have htail : 0≤(4*K/L)*|x|^(k+1) := by positivity
  have hweight := mul_nonneg hB (abs_nonneg (x-z))
  by_cases hx : |x|≤L
  · have hx' := abs_le.mp hx
    have hφx := (hg x).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (pow_le_pow_left₀ (abs_nonneg _) hx k)) hK)
    have hfix : clip L x=x := by simp [clip,min_eq_left hx'.2,max_eq_left hx'.1]
    have hlip : LipschitzWith 1 (clip L) := (LipschitzWith.id.min_const L).max_const (-L)
    have hdist := hlip.dist_le_mul x z
    rw [hfix] at hdist
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hdist
    by_cases h : |x-z|<d
    · have he := hnear x hx' (clip L z) hz (hdist.trans_lt h)
      exact (show |φ x-φ (clip L z)|≤t from he.le).trans (by linarith only [htail,hweight])
    · have hcost := mul_le_mul_of_nonneg_left (le_of_not_gt h) hB
      have heq : B*d=2*M := by dsimp [B];field_simp
      change |φ x|≤M at hφx
      change |φ (clip L z)|≤M at hφz
      linarith only [hnorm,hφx,hφz,heq,hcost,ht,htail]
  · have hx' := le_of_not_ge hx
    have hpp := one_le_pow₀ (hL.trans hx') (n:=k)
    have hpow := pow_le_pow_left₀ hL'.le hx' k
    have hsum : |φ x-φ (clip L z)|≤4*K*|x|^k := by
      have h1 := mul_le_mul_of_nonneg_left hpp hK
      have h2 := mul_le_mul_of_nonneg_left hpow hK
      nlinarith only [hnorm,hg x,hφz,h1,h2]
    have step := mul_le_mul_of_nonneg_left hx' (mul_nonneg (show 0≤4*K by positivity) (pow_nonneg (abs_nonneg x) k))
    have hbudget : 4*K*|x|^k≤(4*K/L)*|x|^(k+1) := by
      rw [div_mul_eq_mul_div,le_div_iff₀ hL',pow_succ]
      nlinarith only [step]
    exact hsum.trans (hbudget.trans (by linarith only [ht,hweight]))

theorem original (hAP : ProgressionMangoldt) {F : G →₁[haar] ℝ} (hF : Represents residual F)
    {φ : ℝ → ℝ} (hφ : Continuous φ) {K : ℝ} (hK : 0≤K) (k : ℕ)
    (hg : ∀ x, |φ x|≤K*(1+|x|^k)) : Approximable (fun p => φ (residual p)) := by
  have hp := (ThetaResidualMoments.prime_polynomial_growth hAP hF
    (φ:=fun x : ℝ => |x|^(k+1)) (by fun_prop) (K:=1) (k:=k+1)
    (fun x => by rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)];linarith)).2
  let v := ∫ x : ℝ, |x|^(k+1) ∂(haarLaw F : Measure ℝ)
  let D := |v|+1
  have hD : 0<D := by dsimp only [D];positivity
  have hm := hp.eventually_le_const (show v<D by dsimp only [D];linarith only [le_abs_self v])
  intro ε hε
  let t := ε/3
  have ht : 0<t := by dsimp [t];positivity
  let L := 1+4*K*D/t
  have hL : 1≤L := le_add_of_nonneg_right (by positivity)
  have hL' : 0<L := by linarith
  obtain ⟨B,hB,hp⟩ := pointwise hφ hK k hg hL ht
  let δ := t/(B+1)
  have hδ : 0<δ := by dsimp only [δ];positivity
  obtain ⟨T,g,hper,he⟩ := ThetaPrimeLaw.residual_approximable δ hδ
  refine ⟨T,fun p => φ (clip L (g p)),fun p => congrArg (fun x => φ (clip L x)) (hper p),?_⟩
  filter_upwards [he,hm,eventually_ge_atTop (2:ℕ)] with X he' hm' hX
  have hpr : 0<(X.primeCounting:ℝ) := by
    have hp : 0<Nat.primeCounting 2 := by decide
    exact_mod_cast hp.trans_le (Nat.monotone_primeCounting hX)
  have scale (a : ℝ) (u : ℕ → ℝ) : primeMean (fun p => a*u p) X=a*primeMean u X := by
    rw [primeMean,primeMean,←mul_sum,mul_div_assoc]
  have eqc : primeMean (fun _ => t) X=t := by
    simp [primeMean,Nat.primesLE_card_eq_primeCounting,hpr.ne']
  have HH := mean_mono (fun p => hp (residual p) (g p)) X
  rw [mean_add,mean_add,eqc,scale,scale] at HH
  have hsmall : B*δ≤t := by
    have eqn : (B+1)*δ=t := by dsimp [δ];field_simp [show B+1≠0 by linarith]
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)) hδ.le).trans_eq eqn
  have htail : (4*K/L)*D≤t := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hL']
    have hLt : L*t=t+4*K*D := by dsimp [L];field_simp
    linarith only [hLt,ht,mul_comm L t]
  have hb := (mul_le_mul_of_nonneg_left he' hB).trans hsmall
  have hl := (mul_le_mul_of_nonneg_left hm' (div_nonneg (by positivity : 0≤4*K) hL'.le)).trans htail
  dsimp only [t] at hb hl HH
  linarith only [HH,hb,hl]

#print axioms original
end
end Arxiv.«2501.03234».ThetaPrimeTestApproximation
