import ThetaFiniteProjection
import ThetaPrimeResidualLaw

/-! Exhausting the full variance by finite character projections. -/
namespace Arxiv.«2501.03234».ThetaVarianceExhaustion
open Finset Filter Topology Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaNaturalPrimeMeans
open ThetaLevelCoefficients ThetaFiniteProjection ThetaPeriodMeans ThetaCharacterPrimeMeans
open ThetaPrimeTailTransfer ThetaConditionalRows ThetaDiagonalConstant
open scoped ComplexConjugate
noncomputable section

/-- Fourier transform on the finite unit group, normalized by its cardinality. -/
def transform (m : ℕ) [NeZero m] (g : ℕ → ℝ) (χ : DirichletCharacter ℂ m) : ℂ :=
  (∑ u : (ZMod m)ˣ,(g (u:ZMod m).val:ℂ)*χ (u:ZMod m))/(m.totient:ℂ)

theorem kernel {m : ℕ} [NeZero m] (v u : (ZMod m)ˣ) :
    ∑ χ : DirichletCharacter ℂ m,χ (u:ZMod m)*conj (χ (v:ZMod m)) =
      if u=v then (m.totient:ℂ) else 0 := by
  classical
  have H := sum_characters_eq ℂ ((v⁻¹*u:(ZMod m)ˣ):ZMod m)
  have he : ((v⁻¹*u:(ZMod m)ˣ):ZMod m)=1 ↔ u=v := by
    change (↑(v⁻¹*u):(ZMod m))=↑(1:(ZMod m)ˣ) ↔ _
    rw [Units.val_inj,inv_mul_eq_one]
    exact eq_comm
  simp only [he] at H
  rw [←H]
  apply sum_congr rfl
  intro χ _
  rw [Units.val_mul,map_mul,mul_comm]
  change star (χ (v:ZMod m))*χ (u:ZMod m)=_
  rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit]

theorem inversion {m : ℕ} [NeZero m] {g : ℕ → ℝ} (hg : OnMod m g) {p : ℕ} (hp : p.Coprime m) :
    ThetaFiniteProjection.model (transform m g) p=(g p:ℂ) := by
  classical
  let v := ZMod.unitOfCoprime p hp
  have hv : (v:ZMod m)=(p:ZMod m) := rfl
  have he (χ : DirichletCharacter ℂ m) :
      transform m g χ*conj (ThetaDirichletRows.symbol χ p) =
      (∑ u : (ZMod m)ˣ,(g (u:ZMod m).val:ℂ)*(χ (u:ZMod m)*conj (χ (v:ZMod m))))/m.totient := by
    simp only [transform,ThetaDirichletRows.symbol,hv,←mul_assoc,←sum_mul]; ring
  have ht : (m.totient:ℂ)≠0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  rw [ThetaFiniteProjection.model]
  simp_rw [he]
  rw [←sum_div,sum_comm]
  simp_rw [←mul_sum,kernel]
  simp only [mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true,mul_div_cancel_right₀ _ ht,hv,ZMod.val_natCast,hg p]

/-- Approximation of the mean-centered original residual by a periodic real function in
ordinary prime mean square. -/
theorem centered_models {ε : ℝ} (he : 0<ε) :
    ∃ d : ℕ, 0<d ∧ ∃ g : ℕ → ℝ, OnMod d g ∧
      ∀ᶠ X in atTop,primeMean (fun p => (centered p-g p)^2) X≤ε := by
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨T,V,_,_,H⟩ := prime_model_approximation (show 0<ε/(4*c^2) by positivity)
  let g (p : ℕ) := c*ThetaPrimeTailTransfer.model T V p
  have hg : OnMod T.factorial (ThetaPrimeTailTransfer.model T V) := low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  refine ⟨_,Nat.factorial_pos T,g,fun p => congrArg (c*·) (hg p),?_⟩
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [H,diagonal_square_error.eventually_le_const (show 0<ε/4 by positivity),
    hπ.eventually_gt_atTop 0] with X hX hD hpos
  change 0<(X.primeCounting:ℝ) at hpos
  have hA : primeMean (fun p => (scaledOff p-ThetaPrimeTailTransfer.model T V p)^2) X≤ε/(4*c^2) :=
    (div_le_iff₀ hpos).mpr hX
  have hD' : primeMean (fun p => (centered p-c*scaledOff p)^2) X≤ε/4 := hD
  let D (p : ℕ) := centered p-c*scaledOff p
  let A (p : ℕ) := scaledOff p-ThetaPrimeTailTransfer.model T V p
  have hpoint (p : ℕ) : (centered p-g p)^2 ≤ 2*(D p)^2 + 2*c^2*(A p)^2 := by
    have hh : centered p-g p=D p+c*A p := by dsimp [g,D,A]; ring
    rw [hh]; nlinarith only [sq_nonneg (D p-c*A p)]
  have hM := ThetaPrimeLaw.mean_mono hpoint X
  simp only [primeMean,sum_add_distrib,←mul_sum,add_div,mul_div_assoc] at hM
  change primeMean (fun p => (centered p-g p)^2) X≤2*primeMean (fun p => (D p)^2) X+
    2*c^2*primeMean (fun p => (A p)^2) X at hM
  apply hM.trans
  change primeMean (fun p => (A p)^2) X≤_ at hA
  change primeMean (fun p => (D p)^2) X≤_ at hD'
  rw [le_div_iff₀ (by positivity : 0<4*c^2)] at hA
  linarith

/-- A real periodic approximation bounds precisely the variance left outside that period. -/
theorem energy_gap_le {m : ℕ} [NeZero m] {g : ℕ → ℝ} (hg : OnMod m g) {ε V : ℝ}
    (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) (hε : ∀ᶠ X in atTop,primeMean (fun p => (centered p-g p)^2) X≤ε) :
    V-energy m≤ε := by
  let b := transform m g
  have hlim := squared_error b hV hAP
  have hreal : Tendsto (primeMean (fun p => (centered p-g p)^2)) atTop
      (𝓝 (V-energy m+∑ χ,‖value χ-b χ‖^2)) := by
    apply primeMean_of_close _ hlim
    intro e he
    filter_upwards [eventually_gt_atTop m] with p hp hprim
    have hc := hprim.coprime_iff_not_dvd.mpr (fun hh => hp.not_ge (Nat.le_of_dvd (NeZero.pos m) hh))
    simp only [b,inversion hg hc,←ofReal_sub,norm_real,Real.norm_eq_abs,sq_abs,sub_self,abs_zero]
    exact he
  have hub := le_of_tendsto hreal hε
  have hs : 0≤∑ χ,‖value χ-b χ‖^2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

local instance (n : ℕ) : NeZero n.factorial := ⟨(Nat.factorial_pos _).ne'⟩

/-- Along factorial levels the finite spectral energies converge to the full prime variance. -/
theorem factorial_energy {V : ℝ}
    (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V)) (hAP : ProgressionMangoldt) :
    Tendsto (fun n : ℕ => energy n.factorial) atTop (𝓝 V) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨d,hd,g,hg,H⟩ := centered_models (half_pos he)
  filter_upwards [eventually_ge_atTop d] with n hn
  have hh := energy_gap_le (onMod_lift (Nat.dvd_factorial hd hn) hg) hV hAP H
  have hl : energy n.factorial ≤ V := energy_le hV hAP
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

#print axioms energy_gap_le
#print axioms factorial_energy

#print axioms centered_models
#print axioms inversion
end
end Arxiv.«2501.03234».ThetaVarianceExhaustion
