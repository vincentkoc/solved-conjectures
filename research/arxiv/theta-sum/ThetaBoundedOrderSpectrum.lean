import ThetaBoundedOrderLayers
import ThetaSpectralVariance

/-! Absolute summability of every bounded-order part of the primitive spectrum,
even with a conductor weight below the square-root threshold. -/
namespace Arxiv.«2501.03234».ThetaBoundedOrderSpectrum
open Finset Filter Real DirichletCharacter ThetaSpectralVariance ThetaLevelCoefficients
open ThetaNaturalPrimeMeans ThetaBoundedOrderLayers
noncomputable section

def weight (k : ℕ) (δ : ℝ) (u : Mode) : ℝ := by
  classical exact if u.character^k=1 then (u.modulus:ℝ)^δ*‖value u.character‖ else 0

theorem nonneg (k : ℕ) (δ : ℝ) (u : Mode) : 0≤ weight k δ u := by
  unfold weight; split_ifs <;> positivity

theorem summable_weight (hAP : ProgressionMangoldt) {k : ℕ} (hk : 0< k) {δ : ℝ} (hd : δ<1/2) :
    Summable (weight k δ) := by
  classical
  apply summable_of_sum_le (fun _ => nonneg ..) (c:=∑' q : ℕ,major k δ q)
  intro s
  let t := s.filter (fun u => u.character^k=1)
  let c := t.image Mode.modulus
  calc ∑ u∈s,weight k δ u = ∑ u∈t,(u.modulus:ℝ)^δ*‖value u.character‖ := by simp [weight,t,sum_filter]
       _ = ∑ q∈c,∑ u∈t with u.modulus=q,(u.modulus:ℝ)^δ*‖value u.character‖ :=
         (sum_fiberwise_of_maps_to (fun u hu => mem_image_of_mem Mode.modulus hu) _).symm
       _ ≤ ∑ q∈c,major k δ q := by
         apply sum_le_sum; intro q hq
         obtain ⟨v,hv,rfl⟩ := mem_image.mp hq
         apply layer v.positive hk _ _ _ hAP
         intro u hu; exact ⟨(mem_filter.mp hu).2,(mem_filter.mp (mem_filter.mp hu).1).2⟩
       _ ≤ _ := (summable_major hk hd).sum_le_tsum _ (fun _ _ => major_nonneg ..)

private lemma descend_pow {m k : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (h : χ^k=1) :
    (descend χ).character^k=1 := by
  change χ.primitiveCharacter^k=1
  apply changeLevel_injective (R:=ℂ) χ.conductor_dvd_level
  rw [map_pow,changeLevel_primitiveCharacter,map_one,h]

/-- The same absolute bound holds at every possibly imprimitive level.
The power δ gives uniform control of the omitted conductors. -/
theorem finite_weight (hAP : ProgressionMangoldt) {k : ℕ} (hk : 0< k) {δ : ℝ} (hd : δ<1/2)
    {m : ℕ} [NeZero m] (s : Finset (DirichletCharacter ℂ m)) (hs : ∀ χ∈s,χ^k=1) :
    ∑ χ∈s,(χ.conductor:ℝ)^δ*‖value χ‖≤ ∑' u : Mode,weight k δ u := by
  classical
  have H := (summable_weight hAP hk hd).sum_le_tsum (s.image descend) (fun u _ => nonneg k δ u)
  rw [sum_image (Function.Injective.injOn descend_injective)] at H
  apply le_trans _ H
  apply sum_le_sum; intro χ hχ
  rw [weight,if_pos (descend_pow χ (hs χ hχ)),value_descend χ hAP]
  rfl

/-- Uniform conductor cutoff for any finite set of bounded-order coefficients,
independent of the ambient modulus. -/
theorem finite_tail (hAP : ProgressionMangoldt) {m k Y : ℕ} [NeZero m] (hk : 0 < k) (hY : 0 < Y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hd : δ < 1/2) (s : Finset (DirichletCharacter ℂ m))
    (hs : ∀ χ∈s,χ^k=1 ∧ Y≤χ.conductor) :
    ∑ χ∈s,‖value χ‖ ≤ (∑' u : Mode,weight k δ u)/(Y:ℝ)^δ := by
  rw [le_div_iff₀ (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hY) δ),sum_mul]
  apply le_trans _ (finite_weight hAP hk hd s (fun χ h => (hs χ h).1))
  apply sum_le_sum; intro χ hχ
  rw [mul_comm]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (hs χ hχ).2) hδ

#print axioms finite_tail
#print axioms summable_weight
#print axioms finite_weight
end
end Arxiv.«2501.03234».ThetaBoundedOrderSpectrum
