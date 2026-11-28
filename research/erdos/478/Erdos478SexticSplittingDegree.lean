import Erdos478SexticSquareClasses
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The splitting degree of the sixth factorial gap

Two square roots over the cubic splitting field generate the six endpoints.
Their square classes are independent: the product of all three cubic roots
is `17^2`, and each root stays nonsquare in that field.
-/

namespace Erdos478.SexticGap
open Polynomial IntermediateField SplittingDensity SquareClasses
noncomputable section

private theorem gap_root_iff {L : Type} [Field L] [Algebra ℚ L] [CharZero L] (x : L) :
    x∈((gapPoly 6).map (Int.castRingHom ℚ)).rootSet L ↔
      (cub L).toPoly.eval ((2*x-5)^2)=0 := by
  rw [((gap_degree (by decide : 0<6)).monic.map _).mem_rootSet,gap_transform,← eval_map_algebraMap]
  simp [gapPoly]

private theorem sqrt_integral {F L : Type*} [Field F] [Field L] [Algebra F L] {a : F} {x : L}
    (h : x^2=algebraMap F L a) : IsIntegral F x :=
  ⟨X^2-C a,monic_X_pow_sub_C _ (by decide),by simp [h]⟩

private theorem third_square {F : Type*} [Field F] [CharZero F] {u v w a b : F}
    (h : u*v*w=17^2) (ha : a^2=u) (hb : b^2=v) : (17/(a*b))^2=w := by
  have hab : a*b≠0 := by
    intro he
    have hz : u*v=0 := by rw [← ha,← hb,← mul_pow,he]; norm_num
    rw [hz,zero_mul] at h
    norm_num at h
  rw [div_pow,div_eq_iff (pow_ne_zero 2 hab),mul_pow,ha,hb]
  linear_combination -h

attribute [-instance] DivisionRing.toRatAlgebra in
set_option backward.isDefEq.respectTransparency false in
theorem sextic_splitting_degree : Module.finrank ℚ (SplitField (gapPoly 6))=24 := by
  classical
  let L := AlgebraicClosure ℚ
  let F := (gapPoly 6).map (Int.castRingHom ℚ)
  let A := adjoin ℚ (F.rootSet L)
  let K := adjoin ℚ ((cub ℚ).toPoly.rootSet L)
  let : IsSplittingField ℚ K (cub ℚ).toPoly := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  let : IsSplittingField ℚ A F := adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  let : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K (cub ℚ).toPoly
  obtain ⟨u,v,w,hpoly,hprod,_⟩ := cub_root_data K (IsSplittingField.splits K _)
  have hru : (cub K).toPoly.eval u=0 := by simp [hpoly]
  have hrv : (cub K).toPoly.eval v=0 := by simp [hpoly]
  have hrw : (cub K).toPoly.eval w=0 := by simp [hpoly]
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (u:L) (by decide : 0<2)
  obtain ⟨b,hb⟩ := IsAlgClosed.exists_pow_nat_eq (v:L) (by decide : 0<2)
  let B := K⟮a⟯
  let D := B⟮b⟯
  have hA2 : Module.finrank K B=2 := sqrt_adjoin_degree (root_nonsquare K hru) ha
  let : FiniteDimensional K B := adjoin.finiteDimensional (sqrt_integral ha)
  have hBns : ∀ t : B, t^2 ≠ algebraMap K B v := by
    intro t ht
    have hgen : (AdjoinSimple.gen K a)^2=algebraMap K B u := Subtype.ext ha
    obtain ⟨e,he⟩|⟨e,he⟩ := square_descent (root_nonsquare K hru) hgen hA2 ht
    · exact root_nonsquare K hrv e he
    · have hne : e≠0 := by
        rintro rfl
        have he' : u*v=0 := by simpa [mul_comm] using he.symm
        rw [he',zero_mul] at hprod
        norm_num at hprod
      apply root_nonsquare K hrw (17/e)
      rw [div_pow,div_eq_iff (pow_ne_zero 2 hne),he]
      linear_combination -hprod
  have hb' : b^2=algebraMap B L (algebraMap K B v) := hb
  have hB2 : Module.finrank B D=2 := sqrt_adjoin_degree hBns hb'
  let : FiniteDimensional B D := adjoin.finiteDimensional (sqrt_integral hb')
  let D₀ := (D.restrictScalars K).restrictScalars ℚ
  have hD₀ : D₀=K ⊔ adjoin ℚ {a,b} := by
    change (K⟮a⟯⟮b⟯.restrictScalars K).restrictScalars ℚ=_
    rw [adjoin_simple_adjoin_simple,restrictScalars_adjoin_eq_sup]
  have hfac : (cub L).toPoly=(X-C (u:L))*(X-C (v:L))*(X-C (w:L)) := by
    simpa only [cub_map,Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,IntermediateField.algebraMap_apply]
      using congrArg (Polynomial.map (algebraMap K L)) hpoly
  have hr (x : L) : x ∈ F.rootSet L ↔
      (2*x-5)^2=(u:L) ∨ (2*x-5)^2=(v:L) ∨ (2*x-5)^2=(w:L) := by
    rw [gap_root_iff,hfac]
    simp [or_assoc,sub_eq_zero]
  have hsubset {z : L} (hz : z∈(cub ℚ).toPoly.rootSet L) :
      z=(u:L) ∨ z=(v:L) ∨ z=(w:L) := by
    rw [(cub_monic ℚ).mem_rootSet,← eval_map_algebraMap,cub_map,hfac] at hz
    simpa [or_assoc,sub_eq_zero] using hz
  have hmem {t : L} (ht : t^2=(u:L) ∨ t^2=(v:L) ∨ t^2=(w:L)) : t ∈ A := by
    have hrt : (t+5)/2 ∈ F.rootSet L := (hr _).mpr (by rwa [show 2*((t+5)/2)-5=t by ring])
    have htop : (t+5)/2 ∈ A := subset_adjoin ℚ _ hrt
    rw [show t=2*((t+5)/2)-5 by ring]
    exact A.sub_mem (A.mul_mem (A.natCast_mem _) htop) (A.natCast_mem _)
  let c : L := 17/(a*b)
  have hw : c^2=(w:L) := third_square (by simpa only [map_mul,map_pow,map_ofNat,IntermediateField.algebraMap_apply] using congrArg (algebraMap K L) hprod) ha hb
  have hKA : K≤A := by
    apply adjoin_le_iff.mpr
    intro z hz
    change z∈A
    rcases hsubset hz with rfl|rfl|rfl
    · exact ha ▸ pow_mem (hmem (Or.inl ha)) 2
    · exact hb ▸ pow_mem (hmem (Or.inr (Or.inl hb))) 2
    · exact hw ▸ pow_mem (hmem (Or.inr (Or.inr hw))) 2
  have heq : A=D₀ := by
    apply le_antisymm
    · have hab : a∈D₀ ∧ b∈D₀ := by
        rw [hD₀]
        have hle : adjoin ℚ ({a,b} : Set L) ≤ K ⊔ adjoin ℚ {a,b} := le_sup_right
        exact ⟨hle (subset_adjoin ℚ _ (by simp)),hle (subset_adjoin ℚ _ (by simp))⟩
      have hc : c∈D₀ := D₀.div_mem (D₀.natCast_mem _) (D₀.mul_mem hab.1 hab.2)
      apply adjoin_le_iff.mpr
      intro x hx
      have htx {s : L} (hs : s ∈ D₀) (he : (2*x-5)^2=s^2) : 2*x-5 ∈ D₀ := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h|h
        · simpa only [h] using hs
        · rw [h]; exact D₀.neg_mem hs
      have ht : 2*x-5∈D₀ := by
        rcases (hr x).mp hx with hu|hv|hz
        · exact htx hab.1 (hu.trans ha.symm)
        · exact htx hab.2 (hv.trans hb.symm)
        · exact htx hc (hz.trans hw.symm)
      rw [show x=((2*x-5)+5)/2 by ring]
      exact D₀.div_mem (D₀.add_mem ht (D₀.natCast_mem _)) (D₀.natCast_mem _)
    · rw [hD₀]
      refine sup_le hKA (adjoin_le_iff.mpr ?_)
      rw [Set.insert_subset_iff,Set.singleton_subset_iff]
      change a ∈ A ∧ b ∈ A
      exact ⟨hmem (Or.inl ha), hmem (Or.inr (Or.inl hb))⟩
  calc
    Module.finrank ℚ (SplitField (gapPoly 6)) = Module.finrank ℚ A :=
      (IsSplittingField.algEquiv A F).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℚ D₀ := congrArg (fun T : IntermediateField ℚ L => Module.finrank ℚ T) heq
    _ = 24 := by
      change Module.finrank ℚ D=24
      rw [← Module.finrank_mul_finrank ℚ K D,← Module.finrank_mul_finrank K B D,
        cub_field_degree K,hA2,hB2]

#print axioms sextic_splitting_degree
end
end Erdos478.SexticGap
