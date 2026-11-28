import ThetaDirichletRows
import ThetaPrimeSpectrum

/-! Transfer of complex conductor transforms to scalar projections of the original prime sum. -/
namespace Arxiv.«2501.03234».ThetaDirichletMeans
open Finset Filter Topology DirichletCharacter ThetaDirichletRows ThetaPeriodMeans ThetaConditionalRows
open ThetaNaturalPrimeMeans ThetaRowCorrelations
open ThetaJacobiRows (sieve)

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

private lemma nat_period : OnMod q (symbol χ) := by
  intro n
  simp [symbol,ZMod.natCast_mod]

omit [NeZero q] in
private lemma projected_sum {P : ℕ} [NeZero P] (L : ℂ →L[ℝ] ℝ) (f : ℕ → ℝ) :
    unitMean P (fun n => L (symbol χ n)*f n)=
      L ((∑ u : (ZMod P)ˣ,symbol χ (u:ZMod P).val*(f (u:ZMod P).val:ℂ))/(P.totient:ℂ)) := by
  have he (z : ℂ) (x : ℝ) : L (z*(x:ℂ))=L z*x := by rw [mul_comm,←Complex.real_smul,map_smul]; ring
  rw [div_eq_mul_inv,←Complex.ofReal_natCast,←Complex.ofReal_inv,he,map_sum]
  simp only [he,unitMean,div_eq_mul_inv]

/-- Character orthogonality holds for every real periodic test missing its conductor,
after any real-linear projection. -/
theorem projected_missing {P d : ℕ} [NeZero P] [NeZero d] (hq : q∣P) (hd : d∣P)
    (hm : ¬χ.conductor∣d) (L : ℂ →L[ℝ] ℝ) {f : ℕ → ℝ} (hf : OnMod d f) :
    unitMean P (fun n => L (symbol χ n)*f n)=0 := by
  have H := ThetaPrimitiveTwist.missing_conductor χ hq hd hm (fun u => (f (u:ZMod d).val:ℂ))
  have hc (u : (ZMod P)ˣ) : (changeLevel hq χ) u=symbol χ (u:ZMod P).val := by
    rw [changeLevel_eq_cast_of_dvd,← ZMod.natCast_zmod_val (u:ZMod P),ZMod.cast_natCast hq,ZMod.natCast_zmod_val]
  have hv (u : (ZMod P)ˣ) : f ((ZMod.unitsMap hd u:(ZMod d)ˣ):ZMod d).val=f (u:ZMod P).val := by
    rw [ZMod.unitsMap_val,← ZMod.natCast_zmod_val (u:ZMod P),ZMod.cast_natCast hd,
      ZMod.val_natCast,ZMod.natCast_zmod_val,hf]
  simp only [hc,hv] at H
  rw [projected_sum,H,zero_div,map_zero]

/-- Limiting contribution of an individual denominator to a primitive twist. -/
noncomputable def rowCoeff (A : ℂ) (d : ℕ) : ℂ :=
  if Odd d ∧ q∣d then
    A*(∏ p∈sieve q d,(1-symbol χ⁻¹ p))*(∏ p∈insert 2 (sieve q d),(1-symbol χ p/p))/
      ((d:ℂ)*d.totient)
  else 0

theorem row_projection (hχ : χ.IsPrimitive) (hq1 : 1<q)
    {P d : ℕ} [NeZero P] [NeZero d] (hq : q∣P) (hd : d∣P)
    (L : ℂ →L[ℝ] ℝ) {D : ℂ} (hD : Tendsto (ThetaCharacterSeven.siftedSum (term χ) ∅) atTop (𝓝 D)) :
    Tendsto (fun K => unitMean P (fun n => L (symbol χ n)*row d K n)/(d:ℝ)) atTop
      (𝓝 (L (rowCoeff χ (parityFactor χ⁻¹*D) d))) := by
  by_cases H : Odd d ∧ q∣d
  · have he (K : ℕ) : unitMean P (fun n => L (symbol χ n)*row d K n)=
        unitMean d (fun n => L (symbol χ n)*row d K n) :=
      unitMean_lift hd (fun n => congrArg₂ (·*·) (congrArg L (onMod_lift H.2 (nat_period χ) n)) (row_onMod d K n))
    simp_rw [he,projected_sum]
    have h := (((row_limit χ hq1 H.1 H.2 hD).div_const (d.totient:ℂ)).div_const (d:ℂ))
    have HL := L.continuous.continuousAt.tendsto.comp h
    convert HL using 1
    · funext K
      dsimp only [Function.comp_apply]
      rw [div_eq_mul_inv,div_eq_mul_inv _ (d:ℂ),←Complex.ofReal_natCast d,←Complex.ofReal_inv,mul_comm _ ((↑(d:ℝ)⁻¹):ℂ),
        ←Complex.real_smul,map_smul]
      ring
    · congr 2
      rw [rowCoeff,if_pos H]; ring
  · rw [rowCoeff,if_neg H,map_zero]
    have h0 (K : ℕ) : unitMean P (fun n => L (symbol χ n)*row d K n)=0 := by
      by_cases ho : Odd d
      · exact projected_missing χ hq hd (fun hh => H ⟨ho,(show χ.conductor=q from hχ) ▸ hh⟩) L (row_onMod d K)
      · simp [even_row ho,unitMean]
    simpa only [h0,zero_div] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=atTop (α:=ℕ)))

#print axioms projected_missing
#print axioms row_projection
end Arxiv.«2501.03234».ThetaDirichletMeans
