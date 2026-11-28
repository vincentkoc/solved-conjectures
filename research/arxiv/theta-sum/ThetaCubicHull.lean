import ThetaDirectionalProportions
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Topology

/-! A fixed disk in the convex hull of the high-order theta coefficients after deletions. -/
namespace Arxiv.«2501.03234».ThetaCubicHull
open Finset Filter Real Complex DirichletCharacter ThetaPointwiseCubic ThetaPointwiseCutoff
open ThetaSignedCubicMass ThetaDirectionalMass ThetaDirectionalProportions
noncomputable section

private theorem disk_of_support {F : Set ℂ} (hf : F.Finite) {r : ℝ}
    (hs : ∀ z : ℂ, ‖z‖=1 → ∃ v∈F,r≤(z*v).re) :
    Metric.closedBall (0:ℂ) r ⊆ convexHull ℝ F := by
  classical
  intro x hx
  have hnorm : ‖x‖≤r := by simpa using hx
  by_contra hout
  obtain ⟨f,u,hF,hu⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜:=ℂ)
    (convex_convexHull ℝ F) (hf.isClosed_convexHull ℝ) hout
  let a := f 1
  have hrep (t : ℂ) : f t=a*t := by
    calc f t=f (t • (1:ℂ)) := by simp
         _ = t • f 1 := f.map_smul t 1
         _ = a*t := mul_comm _ _
  have hsep (v : ℂ) (hv : v∈F) : (a*v).re<(a*x).re := by
    simpa only [←hrep,RCLike.re_eq_complex_re] using (hF v (subset_convexHull ℝ F hv)).trans hu
  by_cases ha : a=0
  · obtain ⟨v,hv,_⟩ := hs 1 norm_one
    simpa [ha] using hsep v hv
  have hpos : 0<‖a‖ := norm_pos_iff.mpr ha
  let z : ℂ := a/(‖a‖:ℂ)
  have hz : ‖z‖=1 := by simp [z,Complex.norm_real,hpos.ne']
  obtain ⟨v,hv,hr⟩ := hs z hz
  have h : (‖a‖:ℂ)*z=a := by
    have hc : (‖a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    dsimp [z]
    field_simp [hc]
  have hm (w : ℂ) : (a*w).re=‖a‖*(z*w).re := by
    conv_lhs => rw [←h,mul_assoc,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hx' : (z*x).re≤r := (re_le_norm _).trans (by rw [norm_mul,hz,one_mul]; exact hnorm)
  have hh := hsep v hv
  rw [hm,hm] at hh
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (hx'.trans hr) hpos.le)) hh

def coefficient {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) : ℂ :=
  cubic χ/(((p:ℝ)*Real.sqrt p:ℝ):ℂ)

def remaining (p : ℕ) [Fact p.Prime] (ε : ℝ) (B : Finset (DirichletCharacter ℂ p)) : Set ℂ :=
  coefficient '' (↑(large p ε \ B) : Set (DirichletCharacter ℂ p))

theorem disk : ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0<ε →
    ∀ᶠ p : ℕ in atTop,∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ B : Finset (DirichletCharacter ℂ p), (B.card:ℝ)<δ*p →
        Metric.closedBall (0:ℂ) (1/8192:ℝ) ⊆ convexHull ℝ (remaining p ε B) := by
  classical
  obtain ⟨δ,hδ,H⟩ := ThetaDirectionalProportions.proportions
  refine ⟨δ,hδ,?_⟩
  intro ε he
  filter_upwards [H ε he] with p h
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro B hB
  apply disk_of_support ((large p ε \ B).finite_toSet.image coefficient)
  intro z hz
  have hc : (B.card:ℝ)<((high p ε z).card:ℝ) := hB.trans_le (h hp ho z hz)
  have hns : ¬high p ε z⊆B := fun hsub => hc.not_ge (by exact_mod_cast card_le_card hsub)
  obtain ⟨χ,hχ,hout⟩ := Set.not_subset.mp hns
  obtain ⟨hgood,hord⟩ := mem_filter.mp hχ
  obtain ⟨hn,hval⟩ := mem_filter.mp hgood
  have hl : χ∈large p ε := mem_filter.mpr ⟨hn,not_le.mpr hord⟩
  refine ⟨coefficient χ,⟨χ,mem_sdiff.mpr ⟨hl,hout⟩,rfl⟩,?_⟩
  simpa only [coefficient,mul_div_assoc',Complex.div_ofReal_re,ordinate,projection] using hval

#print axioms disk
end
end Arxiv.«2501.03234».ThetaCubicHull
