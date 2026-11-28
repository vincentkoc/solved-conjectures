import ThetaConductorLayerLower
import ThetaRoughConductors
import ThetaInverseConductorTail

/-! The full primitive-conductor variance tail has exact order one over the cutoff. -/
namespace Arxiv.«2501.03234».ThetaSharpConductorTail
open Finset Filter Topology ThetaNaturalPrimeMeans ThetaSpectralVariance ThetaFullVarianceTail
open ThetaLevelCoefficients ThetaRoughConductors ThetaConductorLayerLower
noncomputable section

/-- A positive proportion of a fixed progression of conductors forces a matching lower tail. -/
private theorem sharp_at (T : ℕ) (hT : 16384≤T) {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ Y : ℕ in atTop,
      c ≤ Y*(V-∑ u∈through Y,u.mass) ∧ Y*(V-∑ u∈through Y,u.mass)≤449280 := by
  classical
  let M := T.factorial
  let D : ℝ := 2*M+1
  let q (k : ℕ) := M*k+1
  let (k : ℕ) : NeZero (q k) := ⟨Nat.succ_ne_zero _⟩
  let b (k : ℕ) := layer (q k)
  have hM : 0<M := Nat.factorial_pos _
  have hD : 0<D := by dsimp only [D]; positivity
  have hodd (k : ℕ) : Odd (q k) :=
    (even_iff_two_dvd.mpr (Nat.dvd_factorial (by decide) (show 2≤T by omega))).mul_right k |>.add_one
  refine ⟨1/(2097152*D^2),by positivity,?_⟩
  filter_upwards [many T hT,eventually_ge_atTop 5] with Y hcount hY
  let c := candidates T Y
  have hy : 0<(Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
  have hk (k) (h : k∈c) : Y≤k ∧ k<2*Y ∧ ThetaPrimitiveCount.defect (q k)≤1/1024 :=
    ⟨(mem_Ico.mp (mem_filter.mp h).1).1,(mem_Ico.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
  have hgt (k) (h : k∈c) : Y<q k := by
    have hh := Nat.mul_le_mul_right k (show 1≤M by omega)
    dsimp only [q]; simp only [one_mul] at hh; have := (hk k h).1; omega
  have hud (k) (h : k∈c) : (q k:ℝ)≤D*Y := by
    have hh := Nat.mul_le_mul_left M (hk k h).2.1.le
    dsimp only [q,D]; push_cast
    have hy1 : (1:ℝ)≤Y := by exact_mod_cast (show 1≤Y by omega)
    have hh' : (M:ℝ)*k≤M*(2*Y:ℝ) := by exact_mod_cast hh
    nlinarith only [hh',hy1]
  have hlow (k) (h : k∈c) : 1/(1048576*(D*Y)^2) ≤ ∑ u∈b k,u.mass := by
    apply le_trans _ (mass (q k) (hodd k) (by have := hgt k h; omega) (hk k h).2.2)
    apply one_div_le_one_div_of_le (by have := NeZero.pos (q k); positivity)
    gcongr
    exact hud k h
  have he : ∑ u∈c.biUnion b,u.mass=∑ k∈c,∑ u∈b k,u.mass := by
    apply sum_biUnion
    intro k _ j _ hne
    apply disjoint_left.mpr
    intro u hu hv
    have H := (mem_layer hu).symm.trans (mem_layer hv)
    change M*k+1=M*j+1 at H
    exact hne (Nat.eq_of_mul_eq_mul_left hM (Nat.add_right_cancel H))
  have hd : Disjoint (through Y) (c.biUnion b) := by
    apply disjoint_left.mpr
    intro u hu hv
    obtain ⟨k,hk,huk⟩ := mem_biUnion.mp hv
    have h := (mem_through u Y).mp hu
    rw [mem_layer huk] at h
    exact (hgt k hk).not_ge h
  have H := parseval hV hAP
  have hmass := H.summable.sum_le_tsum ((through Y) ∪ c.biUnion b) (fun u _ => sq_nonneg _)
  change ∑ u∈(through Y) ∪ c.biUnion b,u.mass ≤ ∑' u:Mode,u.mass at hmass
  rw [H.tsum_eq,sum_union hd,he] at hmass
  have hband : (Y:ℝ)/2*(1/(1048576*(D*Y)^2)) ≤ V-∑ u∈through Y,u.mass := by
    calc _ ≤ (c.card:ℝ)*(1/(1048576*(D*Y)^2)) := mul_le_mul_of_nonneg_right hcount (by positivity)
         _ = ∑ _k∈c,1/(1048576*(D*Y)^2) := by rw [sum_const,nsmul_eq_mul]
         _ ≤ _ := sum_le_sum hlow
         _ ≤ _ := by linarith
  refine ⟨?_,?_⟩
  · apply le_trans _ (mul_le_mul_of_nonneg_left hband hy.le)
    apply le_of_eq; field_simp; ring
  · have hh := (ThetaInverseConductorTail.truncation hV hAP Y (by omega)).2
    have hl : V-∑ u∈through Y,u.mass ≤ 449280/Y := by linarith
    exact (mul_le_mul_of_nonneg_left hl hy.le).trans_eq (by field_simp)

theorem sharp {V : ℝ} (hV : Tendsto (primeMean (fun p => (centered p)^2)) atTop (𝓝 V))
    (hAP : ProgressionMangoldt) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ Y : ℕ in atTop,
      c ≤ Y*(V-∑ u∈through Y,u.mass) ∧ Y*(V-∑ u∈through Y,u.mass)≤449280 := sharp_at 16384 (by decide) hV hAP

#print axioms sharp
end
end Arxiv.«2501.03234».ThetaSharpConductorTail
