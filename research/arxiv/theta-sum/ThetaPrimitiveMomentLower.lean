import ThetaOddCharacterMean
import ThetaPrimitiveCount

/-! Primitive odd fourth moment at levels where few characters descend. -/
namespace Arxiv.«2501.03234».ThetaPrimitiveMomentLower
open Finset Complex DirichletCharacter ThetaOddCharacterMean ThetaPrimitiveCount
noncomputable section

def good (q : ℕ) : Finset (DirichletCharacter ℂ q) := by classical exact (oddChars q).filter (·.IsPrimitive)

theorem mem_good {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ∈good q ↔ χ.Odd ∧ χ.IsPrimitive := by classical simp only [good,mem_filter,mem_odd]

private theorem linear_cut {a : ℝ} (ha : 0≤a) {K : ℝ} (hK : 0<K) : a≤K+a^4/K^3 := by
  by_cases h : a≤K
  · linarith [div_nonneg (pow_nonneg ha 4) (pow_nonneg hK.le 3)]
  · have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hK.le (le_of_not_ge h) 3) ha
    have hb : a≤a^4/K^3 := (le_div_iff₀ (pow_pos hK 3)).mpr (by nlinarith only [hp])
    linarith

theorem fourth_lower {q : ℕ} [NeZero q] (hq : 5≤q) (hd : defect q≤1/1024) :
    (q.totient:ℝ)/65536 ≤ ∑ χ∈good q,‖LFunction χ 1‖^4 := by
  classical
  let bad := oddChars q \ good q
  have hs : good q⊆oddChars q := filter_subset ..
  have hbad : bad⊆deficient q := by
    intro χ hχ
    obtain ⟨hodd,hnot⟩ := mem_sdiff.mp hχ
    exact mem_filter.mpr ⟨mem_univ _,fun hp => hnot ((mem_good χ).mpr ⟨(mem_odd χ).mp hodd,hp⟩)⟩
  have hc : (bad.card:ℝ)≤(q.totient:ℝ)/1024 := by
    calc _ ≤ ((deficient q).card:ℝ) := by exact_mod_cast card_le_card hbad
         _ ≤ _ := count
         _ ≤ _ := by rw [div_eq_mul_one_div]; gcongr
  have hsum := ThetaLValueMoment.moment bad (fun χ hχ => ne_one ((mem_odd χ).mp (mem_sdiff.mp hχ).1))
  have hH := pow_le_pow_left₀ (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    ThetaLValueMoment.H_bound 3
  change ThetaLValueMoment.H^3≤4^3 at hH
  have h520 : ∑ χ∈bad,‖LFunction χ 1‖^4 ≤ 520*(q.totient:ℝ) := by
    apply hsum.trans
    nlinarith only [mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg q.totient)]
  have hb : ∑ χ∈bad,(LFunction χ 1).re ≤ (q.totient:ℝ)/16 := by
    have hh := sum_le_sum (s:=bad) (fun χ _ =>
      (re_le_norm (LFunction χ 1)).trans (linear_cut (norm_nonneg _) (by norm_num : (0:ℝ)<32)))
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_div] at hh
    linarith [Nat.cast_nonneg (α:=ℝ) q.totient]
  have hgc : ((good q).card:ℝ)≤q.totient := by
    have h := card_le_univ (good q)
    rw [←Nat.card_eq_fintype_card,card_eq_totient_of_hasEnoughRootsOfUnity ℂ q] at h
    exact_mod_cast h
  have hg := sum_le_sum (s:=good q) (fun χ _ =>
      (re_le_norm (LFunction χ 1)).trans (linear_cut (norm_nonneg _) (by norm_num : (0:ℝ)<1/16)))
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_div] at hg
  have HE := sum_sdiff hs (f:=fun χ => (LFunction χ 1).re)
  change ∑ χ∈bad,(LFunction χ 1).re + ∑ χ∈good q,(LFunction χ 1).re = _ at HE
  norm_num at hg
  have hl := ThetaOddCharacterMean.lower hq
  linarith only [hl,HE,hg,hgc,hb,Nat.cast_nonneg (α:=ℝ) q.totient]

#print axioms fourth_lower
end
end Arxiv.«2501.03234».ThetaPrimitiveMomentLower
