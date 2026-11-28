import ThetaJacobiRows

/-! Evaluations needed for the composite character of conductor fifteen. -/
namespace Arxiv.«2501.03234».ThetaJacobiFifteen
open Finset Filter Topology ThetaJacobiRows ThetaCharacterSeven

/-- The Jacobi symbol as a complex Dirichlet character on its residue ring. -/
noncomputable def dirChar (q : ℕ) [NeZero q] : DirichletCharacter ℂ q where
  toFun a := (symbol q a.val:ℂ)
  map_one' := by
    rw [show (1:ZMod q)=((1:ℕ):ZMod q) by simp,ZMod.val_natCast,symbol_mod q (dvd_refl q)]
    simp [symbol,jacobiSym.one_left]
  map_mul' a b := by simp only [ZMod.val_mul,symbol_mod q (dvd_refl q),symbol_mul,Int.cast_mul]
  map_nonunit' a ha := by
    have hn : ¬a.val.Coprime q := fun h => ha (by
      simpa only [ZMod.natCast_zmod_val] using (ZMod.isUnit_iff_coprime a.val q).2 h)
    rw [symbol_zero q hn,Int.cast_zero]

lemma dirChar_nat (q n : ℕ) [NeZero q] : dirChar q (n:ZMod q)=(symbol q n:ℂ) := by
  change (symbol q (n:ZMod q).val:ℂ)=_
  rw [ZMod.val_natCast,symbol_mod q (dvd_refl q)]

private lemma nonprincipal : dirChar 15≠1 := by
  intro h
  have H := dirChar_nat 15 7
  rw [h,MulChar.one_apply ((ZMod.isUnit_iff_coprime 7 15).2 (by decide))] at H
  norm_num [symbol] at H

theorem fifteen_parity : parityFactor 15= -4 := by
  norm_num [parityFactor,symbol,ThetaCharacterThree.parity,sum_range_succ]

private theorem harmonic_prefix :
    ∑ n∈range 30,term 15 n=767097285/492929008 := by
  norm_num [term,symbol,sum_range_succ]

theorem harmonic_fifteen : ∃ L : ℝ, 1<L ∧ Tendsto (siftedSum (term 15) ∅) atTop (𝓝 L) := by
  let D := DirichletCharacter.LFunction (dirChar 15) 1
  have he (K : ℕ) : ((∑ n∈range K,term 15 n:ℝ):ℂ)=
      ∑ n∈range K, dirChar 15 (n:ZMod 15)/(n:ℂ) := by
    simp only [dirChar_nat,term,Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_natCast]
  obtain ⟨H,_⟩ := ThetaCharacterHarmonicLimit.harmonic_limit (dirChar 15) nonprincipal
  have HC : Tendsto (fun K => ((∑ n∈range K,term 15 n:ℝ):ℂ)) atTop (𝓝 D) := by
    simpa only [he] using H
  have HR : Tendsto (fun K => ∑ n∈range K,term 15 n) atTop (𝓝 D.re) := by
    simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp HC
  have heq : D=(D.re:ℂ) := tendsto_nhds_unique HC (Complex.continuous_ofReal.continuousAt.tendsto.comp HR)
  have herr := ThetaCharacterHarmonicLimit.harmonic_error (dirChar 15) nonprincipal (K:=30) (by decide)
  change ‖D-_‖≤_ at herr
  rw [heq,←he,harmonic_prefix,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at herr
  refine ⟨D.re,?_,?_⟩
  · have h := (abs_le.mp herr).1
    norm_num at h
    linarith
  · apply (HR.comp (tendsto_add_atTop_nat 1)).congr'
    filter_upwards with K
    simp [siftedSum,sift]

#print axioms fifteen_parity
#print axioms harmonic_fifteen
end Arxiv.«2501.03234».ThetaJacobiFifteen
