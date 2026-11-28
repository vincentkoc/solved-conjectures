import ThetaPrimitiveMomentLower

/-! A lower bound on the full primitive conductor layer. -/
namespace Arxiv.«2501.03234».ThetaConductorLayerLower
open Finset Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaPrimitiveMomentLower
open ThetaSpectralVariance ThetaConductorDecay ThetaPrimitiveCount ThetaDirichletEuler
noncomputable section

private def embed (q : ℕ) [NeZero q] (χ : {χ // χ∈good q}) : Mode :=
  ⟨q,NeZero.pos _,χ.val,((mem_good χ.val).mp χ.prop).2⟩

/-- All contributing primitive odd modes at this level. -/
def layer (q : ℕ) [NeZero q] : Finset Mode := by classical exact (good q).attach.image (embed q)

theorem mem_layer {q : ℕ} [NeZero q] {u : Mode} (h : u∈layer q) : u.modulus=q := by
  classical
  obtain ⟨χ,_,rfl⟩ := mem_image.mp h
  rfl

private theorem squared (q : ℕ) [NeZero q] (ho : _root_.Odd q) (hq : 5≤q) (χ : {χ // χ∈good q}) :
    ‖LFunction χ.val 1‖^4/(16*(q:ℝ)*q.totient^2) ≤ (embed q χ).mass := by
  obtain ⟨hod,hpr⟩ := (mem_good _).mp χ.prop
  have hv := primitive_value χ.val hpr (ThetaOddCharacterMean.ne_one hod) ho
  change _≤‖ThetaLevelCoefficients.value χ.val‖^2
  rw [hv]
  have hq' : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have ht : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have ha : 1≤5-4*(χ.val 2).re := by linarith [(re_le_norm _).trans (χ.val.norm_le_one (2:ZMod q))]
  have hw := weight_sum_norm χ.val
  have hl : ‖LFunction χ.val 1‖^2/(4*Real.sqrt q*q.totient) ≤ ‖coefficient χ.val‖ := by
    rw [odd_magnitude χ.val hpr ho (by omega) hod]
    apply div_le_div₀ (by positivity) _ (by positivity) _
    · calc _ = 1*‖LFunction χ.val 1‖^2*1 := by ring
           _ ≤ _ := by gcongr
    · gcongr; exact Real.pi_le_four
  apply le_trans _ (pow_le_pow_left₀ (by positivity) hl 2)
  rw [div_pow,mul_pow (4*_),mul_pow (4:ℝ),Real.sq_sqrt hq'.le]
  apply le_of_eq
  ring

theorem mass (q : ℕ) [NeZero q] (ho : _root_.Odd q) (hq : 5≤q) (hd : defect q≤1/1024) :
    1/(1048576*(q:ℝ)^2) ≤ ∑ u∈layer q,u.mass := by
  classical
  have he : Set.InjOn (embed q) (↑(good q).attach) := by
    intro χ _ ψ _ he
    apply Subtype.ext
    simpa [embed,Mode.mk.injEq] using he
  rw [layer,sum_image he]
  have hq' : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs : ∑ χ∈(good q).attach, ‖LFunction χ.val 1‖^4=∑ χ∈good q,‖LFunction χ 1‖^4 :=
    sum_attach (good q) (fun χ : DirichletCharacter ℂ q => ‖LFunction χ 1‖^4)
  calc _ ≤ 1/(1048576*(q:ℝ)*q.totient) := by
             apply one_div_le_one_div_of_le (by positivity)
             rw [sq,mul_assoc]
             gcongr; exact_mod_cast Nat.totient_le q
       _ = ((q.totient:ℝ)/65536)/(16*q*q.totient^2) := by field_simp; ring
       _ ≤ (∑ χ∈good q,‖LFunction χ 1‖^4)/(16*q*q.totient^2) :=
             div_le_div_of_nonneg_right (fourth_lower hq hd) (by positivity)
       _ = ∑ χ∈(good q).attach, ‖LFunction χ.val 1‖^4/(16*q*q.totient^2) := by rw [←sum_div,hs]
       _ ≤ _ := sum_le_sum (fun χ _ => squared q ho hq χ)

#print axioms mass
end
end Arxiv.«2501.03234».ThetaConductorLayerLower
