import ThetaTorsionMajorant
import ThetaCharacterTorsion
import ThetaConductorMoment

/-! Absolute spectral mass by conductor for characters killed by a fixed exponent. -/
namespace Arxiv.«2501.03234».ThetaBoundedOrderLayers
open Finset Filter Real DirichletCharacter ThetaNaturalPrimeMeans ThetaLevelCoefficients
open ThetaConductorMoment ThetaSpectralVariance ThetaCharacterTorsion ThetaConductorDecay
open scoped Topology
noncomputable section

def major (k : ℕ) (δ : ℝ) (q : ℕ) : ℝ :=
  12*((k:ℝ)^q.primeFactors.card*((q:ℝ)/q.totient))*(2+log q)^2*(q:ℝ)^δ/(q:ℝ)^(3/2:ℝ)

theorem major_nonneg (k : ℕ) (δ : ℝ) (q : ℕ) : 0≤ major k δ q := by
  dsimp only [major]; positivity

theorem summable_major {k : ℕ} (hk : 0< k) {δ : ℝ} (hd : δ<1/2) : Summable (major k δ) := by
  let ε := (1/2-δ)/4
  have he : 0< ε := by dsimp [ε]; linarith
  obtain ⟨C,hC,H⟩ := ThetaTorsionMajorant.normalized_choices k hk he
  have hs : Summable (fun q : ℕ => (q:ℝ)^(δ+3*ε-3/2)) := Real.summable_nat_rpow.mpr (by dsimp [ε]; linarith)
  apply Summable.of_norm_bounded_eventually_nat (hs.mul_left (108*C))
  have hlog := (isLittleO_log_rpow_atTop he).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [eventually_ge_atTop 1,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hlog] with q hq hl
  have hx : 0<(q:ℝ) := by exact_mod_cast hq
  have hx1 : 1≤ (q:ℝ) := by exact_mod_cast hq
  have hr := Real.one_le_rpow hx1 he.le
  have hlg := Real.log_nonneg hx1
  have hp := Real.rpow_pos_of_pos hx ε
  simp only [Real.norm_eq_abs,abs_of_nonneg hlg,abs_of_pos hp,one_mul] at hl
  have hsq : (2+log q)^2≤ (3*(q:ℝ)^ε)^2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [Real.norm_eq_abs,abs_of_nonneg (major_nonneg ..)]
  change _≤ 108*C*((q:ℝ)^(δ+3*ε-3/2))
  calc major k δ q ≤ 12*(C*(q:ℝ)^ε)*(3*(q:ℝ)^ε)^2*(q:ℝ)^δ/(q:ℝ)^(3/2:ℝ) := by
         unfold major
         apply div_le_div_of_nonneg_right _ (by positivity)
         apply mul_le_mul_of_nonneg_right _ (by positivity)
         exact mul_le_mul (mul_le_mul_of_nonneg_left (H q hq) (by norm_num)) hsq (sq_nonneg _) (by positivity)
       _ = _ := by
         rw [Real.rpow_sub hx,show δ+3*ε=δ+ε+ε+ε by ring]
         simp only [Real.rpow_add hx]
         ring

theorem layer {q k : ℕ} (hq : 0< q) (hk : 0< k) (δ : ℝ) (t : Finset Mode)
    (ht : ∀ u∈t,u.modulus=q ∧ u.character^k=1) (hAP : ProgressionMangoldt) :
    ∑ u∈t,(u.modulus:ℝ)^δ*‖value u.character‖≤ major k δ q := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  have props (u : Mode) (h : u∈t) : (liftAt q u).IsPrimitive ∧ (liftAt q u)^k=1 ∧
      ‖value u.character‖=‖value (liftAt q u)‖ := by
    obtain ⟨he,hk⟩ := ht u h
    rcases u with ⟨v,hv,χ,hχ⟩
    change v=q at he; subst q; simp only [liftAt]
    exact ⟨hχ,hk,rfl⟩
  by_cases ho : _root_.Odd q
  · let F := t.image (liftAt q)
    let R : Finset (DirichletCharacter ℂ q) := univ.filter (fun χ => χ^k=1)
    have hR : R.card=roots (DirichletCharacter ℂ q) k := by simp [roots,R,Nat.card_eq_fintype_card,Fintype.card_subtype]
    have hcard : t.card≤ k^q.primeFactors.card := by
      have hI : Set.InjOn (liftAt q) ↑t := fun u hu v hv he => inj_level q u v (ht u hu).1 (ht v hv).1 he
      have hsub : F⊆R := by
        intro χ hχ; obtain ⟨u,hu,rfl⟩ := mem_image.mp hχ
        exact mem_filter.mpr ⟨mem_univ _,(props u hu).2.1⟩
      rw [←card_image_of_injOn hI]
      exact (card_le_card hsub).trans (hR.trans_le (ThetaCharacterTorsion.count hk ho))
    let D := (q:ℝ)^δ*(12*(2+log q)^2/(sqrt q*q.totient))
    have hval (u : Mode) (hu : u∈t) : (u.modulus:ℝ)^δ*‖value u.character‖≤ D := by
      rw [(props u hu).2.2,(ht u hu).1]
      exact mul_le_mul_of_nonneg_left (primitive_bound _ (props u hu).1 hAP) (by positivity)
    have hD : 0≤ D := by dsimp [D]; positivity
    have hh := (sum_le_sum hval).trans_eq (by simp : ∑ _∈t,D=(t.card:ℝ)*D)
    apply hh.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast hcard : (t.card:ℝ)≤ (k:ℝ)^q.primeFactors.card) hD).trans_eq ?_)
    have hx : 0<(q:ℝ) := Nat.cast_pos.mpr hq
    have ht' : 0<(q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hq)
    have hpow : (q:ℝ)^(3/2:ℝ)=(q:ℝ)*sqrt q := by
      rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hx,Real.rpow_one,Real.sqrt_eq_rpow]
    simp only [D,major,hpow]; field_simp
  · apply le_trans _ (major_nonneg ..)
    apply le_of_eq; apply sum_eq_zero; intro u hu
    have hodd : ¬ _root_.Odd u.character.conductor := by
      rwa [show u.character.conductor=u.modulus from u.primitive,(ht u hu).1]
    simp [value,hodd]

#print axioms layer
#print axioms summable_major
end
end Arxiv.«2501.03234».ThetaBoundedOrderLayers
