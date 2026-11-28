import Erdos478TetrahedralQuartic
import Erdos478TetrahedralSpans
import Erdos478SexticSplittingDegree

/-! # Identifying the splitting fields of the quartic and the sixth factorial gap -/

namespace Erdos478.TetrahedralGap
open Polynomial IntermediateField SexticGap SplittingDensity
noncomputable section

private theorem signed_coordinates (L : Type) [Field L] [Algebra ℚ L] [IsAlgClosed L] :
    ∃ a b c : L, a^2+b^2+c^2=35 ∧ a^2*b^2+a^2*c^2+b^2*c^2=259 ∧ a*b*c=17 ∧
      (cub L).toPoly=(X-C (a^2))*(X-C (b^2))*(X-C (c^2)) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have lead : (cub ℚ).a≠0 := by decide
  obtain ⟨u,v,w,roots⟩ := (Cubic.splits_iff_roots_eq_three (φ:=algebraMap ℚ L) lead).mp (IsAlgClosed.splits _)
  have su := Cubic.b_eq_three_roots lead roots
  have pa := Cubic.c_eq_three_roots lead roots
  have pr := Cubic.d_eq_three_roots lead roots
  have f := Cubic.eq_prod_three_roots lead roots
  norm_num [cub] at su pa pr
  rw [Cubic.map_toPoly,cub_map] at f
  have factor : (cub L).toPoly=(X-C u)*(X-C v)*(X-C w) := by simpa [cub] using f
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq u (by decide : 0<2)
  obtain ⟨b,hb⟩ := IsAlgClosed.exists_pow_nat_eq v (by decide : 0<2)
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq w (by decide : 0<2)
  have sign : (a*b*z)^2=(17:L)^2 := by rw [mul_pow,mul_pow,ha,hb,hz]; linear_combination -pr
  have finish (c : L) (hc : c^2=w) (h : a*b*c=17) :
      a^2+b^2+c^2=35 ∧ a^2*b^2+a^2*c^2+b^2*c^2=259 ∧ a*b*c=17 ∧
        (cub L).toPoly=(X-C (a^2))*(X-C (b^2))*(X-C (c^2)) := by
    rw [ha,hb,hc]
    exact ⟨by linear_combination su,pa.symm,h,factor⟩
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp sign with h|h
  · exact ⟨a,b,z,finish z hz h⟩
  · exact ⟨a,b,-z,finish (-z) (by simpa using hz) (by rw [mul_neg,h,neg_neg])⟩

private theorem centred_pair {L : Type*} [Field L] [CharZero L] (x a : L) :
    (2*x-5)^2=a^2 ↔ x=(5+a)/2 ∨ x=(5-a)/2 := by
  rw [sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h|h)
    · left; rw [eq_div_iff (by norm_num)]; linear_combination h
    · right; rw [eq_div_iff (by norm_num)]; linear_combination h
  · rintro (rfl|rfl)
    · left; ring
    · right; ring

/-- One set of signed coordinates simultaneously enumerates all roots of both polynomials. -/
theorem coordinate_root_sets (L : Type) [Field L] [Algebra ℚ L] [IsAlgClosed L] :
    ∃ a b c : L, (quartic ℚ).rootSet L=vertices a b c ∧
      ((gapPoly 6).map (Int.castRingHom ℚ)).rootSet L=edgePoints a b c := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  obtain ⟨a,b,c,h₁,h₂,h₃,hc⟩ := signed_coordinates L
  have vs : (quartic ℚ).rootSet L=vertices a b c := by
    ext x
    rw [(quartic_monic ℚ).mem_rootSet,← eval_map_algebraMap,quartic_map,quartic_factor h₁ h₂ h₃]
    simp [vertices,sub_eq_zero,or_assoc]
  have es : ((gapPoly 6).map (Int.castRingHom ℚ)).rootSet L=edgePoints a b c := by
    ext x
    have gap : x∈((gapPoly 6).map (Int.castRingHom ℚ)).rootSet L ↔ (cub L).toPoly.eval ((2*x-5)^2)=0 := by
      rw [((gap_degree (by decide : 0<6)).monic.map _).mem_rootSet,gap_transform,← eval_map_algebraMap]
      simp [gapPoly]
    rw [gap,hc]
    simp [edgePoints,sub_eq_zero,centred_pair,or_assoc]
  exact ⟨a,b,c,vs,es⟩

/-- Equality as subfields of a common algebraic closure, with the ordinary
factorial endpoint coordinate x recovered by (5±a)/2. -/
theorem quartic_sextic_adjoin (L : Type) [Field L] [Algebra ℚ L] [IsAlgClosed L] :
    adjoin ℚ ((quartic ℚ).rootSet L)=adjoin ℚ (((gapPoly 6).map (Int.castRingHom ℚ)).rootSet L) := by
  obtain ⟨a,b,c,vs,es⟩ := coordinate_root_sets L
  rw [vs,es,equal_spans]

/-- The quartic bound of 4! is attained over the rationals. -/
theorem quartic_splitting_degree : Module.finrank ℚ (quartic ℚ).SplittingField=24 := by
  let L := AlgebraicClosure ℚ
  let q := quartic ℚ
  let f := (gapPoly 6).map (Int.castRingHom ℚ)
  let A := adjoin ℚ (q.rootSet L)
  let B := adjoin ℚ (f.rootSet L)
  let : IsSplittingField ℚ A q := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  let : IsSplittingField ℚ B f := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  calc
    _ = Module.finrank ℚ A := (IsSplittingField.algEquiv A q).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℚ B := congrArg (fun T : IntermediateField ℚ L => Module.finrank ℚ T)
      (quartic_sextic_adjoin L)
    _ = Module.finrank ℚ f.SplittingField := (IsSplittingField.algEquiv B f).toLinearEquiv.finrank_eq
    _ = 24 := sextic_splitting_degree

#print axioms coordinate_root_sets
#print axioms quartic_splitting_degree
#print axioms quartic_sextic_adjoin
end
end Erdos478.TetrahedralGap
