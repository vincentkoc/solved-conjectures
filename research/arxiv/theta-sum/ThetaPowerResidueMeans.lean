import ThetaBoundedOrderSpectrum
import ThetaOppositeMeans

/-! All means obtained by imposing any family of kth-power residue tests have
a bounded centered bias independent of the modulus and the size of the family. -/
namespace Arxiv.«2501.03234».ThetaPowerResidueMeans
open Finset Filter Real Complex DirichletCharacter ThetaNaturalPrimeMeans ThetaLevelCoefficients
open ThetaDirichletRows ThetaProgressionProjection ThetaBoundedOrderSpectrum ThetaSpectralVariance
open scoped ComplexConjugate
noncomputable section

def Stable {m : ℕ} (k : ℕ) (A : Finset (ZMod m)ˣ) := ∀ u v : (ZMod m)ˣ, u∈A ↔ (v^k)*u∈A

/-- Any Boolean selection determined by characters killed by k is invariant
under multiplication by kth powers. -/
theorem stable_of_tests {m k : ℕ} {A : Finset (ZMod m)ˣ}
    (h : ∀ u v : (ZMod m)ˣ, (∀ χ : DirichletCharacter ℂ m, χ^k=1 → χ (u:ZMod m)=χ (v:ZMod m)) → (u∈A ↔ v∈A)) :
    Stable k A := by
  intro u v; apply h; intro χ hχ
  have he := congrArg (fun ψ : DirichletCharacter ℂ m => ψ (v:ZMod m)) hχ
  simp only [MulChar.pow_apply_coe,MulChar.one_apply_coe] at he
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow,he,one_mul]

private theorem cancel {m k : ℕ} [NeZero m] {A : Finset (ZMod m)ˣ} (hA : Stable k A)
    (χ : DirichletCharacter ℂ m) (hχ : χ^k≠1) : ∑ u∈A,χ (u:ZMod m)=0 := by
  classical
  obtain ⟨v,hv⟩ : ∃ v : (ZMod m)ˣ,χ (v:ZMod m)^k≠1 := by
    by_contra! h
    apply hχ; apply MulChar.ext; intro v
    rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,h v]
  let e := Equiv.mulLeft (v^k)
  have hi : A.image e=A := by
    ext x
    constructor
    · intro h; obtain ⟨u,hu,rfl⟩ := mem_image.mp h
      exact (hA u v).mp hu
    · intro h; exact mem_image.mpr ⟨e.symm x,(hA (e.symm x) v).mpr (by simpa only [←show ∀ y,e y=v^k*y from fun _ => rfl,e.apply_symm_apply] using h),e.apply_symm_apply _⟩
  have H := sum_image (f:=fun u : (ZMod m)ˣ => χ (u:ZMod m)) (s:=A) (g:=e) e.injective.injOn
  rw [hi] at H
  change _ = ∑ u∈A,χ ((v^k*u : (ZMod m)ˣ):ZMod m) at H
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow,←mul_sum] at H
  exact (mul_eq_zero.mp (show (χ (v:ZMod m)^k-1)*(∑ u∈A,χ (u:ZMod m))=0 by linear_combination -H)).resolve_left (sub_ne_zero.mpr hv)

def bias (m : ℕ) [NeZero m] (A : Finset (ZMod m)ˣ) : ℝ :=
  (∑ u∈A,predictor m (u:ZMod m).val)/A.card

theorem bounded {m k : ℕ} [NeZero m] (hk : 0< k) {A : Finset (ZMod m)ˣ} (hA : Stable k A)
    (hAP : ProgressionMangoldt) : |bias m A|≤ ∑' u : Mode,weight k 0 u := by
  classical
  have h0 : 0≤ ∑' u : Mode,weight k 0 u := tsum_nonneg fun u => ThetaBoundedOrderSpectrum.nonneg k 0 u
  by_cases he : A.Nonempty
  · have hc : 0<(A.card:ℝ) := Nat.cast_pos.mpr he.card_pos
    let t := (univ : Finset (DirichletCharacter ℂ m)).filter (·^k=1)
    let W (χ : DirichletCharacter ℂ m) := ∑ u∈A,χ (u:ZMod m)
    have H : (∑ u∈A,(predictor m (u:ZMod m).val:ℂ))=∑ χ∈t,value χ*conj (W χ) := by
      simp only [predictor_real _ _ hAP,ThetaFiniteProjection.model,symbol,ZMod.natCast_zmod_val]
      rw [sum_comm]
      simp only [W,map_sum,mul_sum]
      apply (sum_subset_zero_on_sdiff (filter_subset ..) ?_ (fun _ _ => rfl)).symm
      intro χ h
      have hχ : χ^k≠1 := fun H => (mem_sdiff.mp h).2 (mem_filter.mpr ⟨mem_univ _,H⟩)
      rw [←mul_sum,←map_sum,cancel hA χ hχ,map_zero,mul_zero]
    have hW (χ : DirichletCharacter ℂ m) : ‖W χ‖≤ A.card := by
      apply (norm_sum_le _ _).trans
      simp
    have hnorm : ‖∑ χ∈t,value χ*conj (W χ)‖≤ (∑ χ∈t,‖value χ‖)*A.card := by
      apply (norm_sum_le _ _).trans; rw [sum_mul]; apply sum_le_sum; intro χ _
      rw [norm_mul,norm_conj]; exact mul_le_mul_of_nonneg_left (hW χ) (norm_nonneg _)
    have hsum := finite_weight hAP hk (δ:=0) (by norm_num) t (fun _ h => (mem_filter.mp h).2)
    simp only [Real.rpow_zero,one_mul] at hsum
    rw [←H,←ofReal_sum,norm_real,Real.norm_eq_abs] at hnorm
    rw [bias,abs_div,abs_of_pos hc,div_le_iff₀ hc]
    exact hnorm.trans (mul_le_mul_of_nonneg_right hsum hc.le)
  · simp [bias,not_nonempty_iff_eq_empty.mp he,h0]

/-- Odd powers include the sign involution, so every stable selection has
exactly zero centered bias. -/
theorem odd_bias {m k : ℕ} [NeZero m] (hk : _root_.Odd k) {A : Finset (ZMod m)ˣ}
    (hA : Stable k A) (hAP : ProgressionMangoldt) : bias m A=0 := by
  classical
  have hneg (u : (ZMod m)ˣ) : u∈A ↔ -u∈A := by
    simpa only [hk.neg_one_pow,neg_one_mul] using hA u (-1)
  let e := Equiv.neg (ZMod m)ˣ
  have hi : A.image e=A := by
    ext u; constructor
    · intro h; obtain ⟨v,hv,rfl⟩ := mem_image.mp h; exact (hneg v).mp hv
    · intro h; exact mem_image.mpr ⟨-u,(hneg u).mp h,neg_neg u⟩
  let f (u : (ZMod m)ˣ) := predictor m (u:ZMod m).val
  have hf (u : (ZMod m)ˣ) : f (e u)= -f u := by
    apply ThetaOppositeMeans.reflection _ hAP
    simp [e]
  have H := sum_image (f:=f) (s:=A) (g:=e) e.injective.injOn
  rw [hi] at H
  simp only [hf,sum_neg_distrib] at H
  have hz : ∑ u∈A,f u=0 := by linarith
  exact div_eq_zero_iff.mpr (Or.inl hz)

#print axioms odd_bias
#print axioms bounded
end
end Arxiv.«2501.03234».ThetaPowerResidueMeans
