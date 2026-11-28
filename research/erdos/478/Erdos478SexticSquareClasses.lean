import Erdos478SexticResolvent
import Erdos478GapSplittingTest
import Mathlib.RingTheory.Norm.Basic

/-!
# Nonsquareness of the three cubic roots in their normal closure

A cubic root has norm `17^2`. In its cubic field it cannot be a square:
a square root would produce a factorial-gap root of degree six. Twisting
by the discriminant square class is ruled out by the rational norm.
-/

namespace Erdos478.SexticGap
open Polynomial IntermediateField SplittingDensity SquareClasses
noncomputable section

theorem lifted_gap_root {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] {w s : K}
    (hw : (cub K).toPoly.eval w=0) (hs : s^2=w) :
    aeval ((s+5)/2) ((gapPoly 6).map (Int.castRingHom ℚ))=0 := by
  have he := gap_transform ((s+5)/2)
  rw [show 2*((s+5)/2)-5=s by ring,hs,hw] at he
  rw [← eval_map_algebraMap]
  simp only [gapPoly,Polynomial.map_sub,descPochhammer_map,Polynomial.map_one,eval_sub,eval_one]
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

attribute [-instance] DivisionRing.toRatAlgebra in
set_option backward.isDefEq.respectTransparency false in
theorem root_nonsquare (K : Type) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (cub ℚ).toPoly] {w : K} (hw : (cub K).toPoly.eval w=0)
    (y : K) : y^2≠w := by
  have : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K (cub ℚ).toPoly
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let k := ℚ⟮w⟯
  let u : k := AdjoinSimple.gen ℚ w
  have hmin : (cub ℚ).toPoly=minpoly ℚ w := minpoly.eq_of_irreducible_of_monic cub_irreducible
    (by rwa [← eval_map_algebraMap,cub_map]) (cub_monic _)
  have hi := IsIntegral.of_finite ℚ w
  have : FiniteDimensional ℚ k := adjoin.finiteDimensional hi
  have h3 : Module.finrank ℚ k=3 := by rw [adjoin.finrank hi,← hmin,cub_degree]
  have h2 := Module.finrank_mul_finrank ℚ k K
  rw [h3,cub_field_degree K] at h2
  have hrel : Module.finrank k K=2 := by omega
  have hd : ∀ b : k, b^2 ≠ 1957 := by
    intro b hb
    have h := congrArg (Algebra.norm ℚ) hb
    rw [map_pow,show Algebra.norm ℚ (1957:k)=1957^3 by
      rw [← h3]; exact Algebra.norm_natCast ℚ (S:=k) 1957] at h
    apply discr_nonsquare (Algebra.norm ℚ b/1957)
    rw [div_pow,h]
    norm_num
  have hn : Algebra.norm ℚ u=289 := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hi)
    rw [adjoin.powerBasis_gen,adjoin.powerBasis_dim,minpoly_gen,← hmin,cub_degree,Cubic.coeff_eq_d] at h
    norm_num [cub] at h
    exact h
  obtain ⟨x₁,x₂,x₃,_,_,ht⟩ := cub_root_data K (IsSplittingField.splits K _)
  intro hy
  obtain ⟨b,hb⟩|⟨b,hb⟩ := square_descent (F:=k) (a:=u) hd
    (by rw [map_ofNat]; exact ht) hrel (y:=y) hy
  · have hu : (cub k).toPoly.eval u=0 := by
      apply (algebraMap k K).injective
      rw [← eval_map_apply,cub_map]
      exact hw
    let F := (gapPoly 6).map (Int.castRingHom ℚ)
    have hir : Irreducible F := by
      simpa [F,gapPoly] using GapFamilies.irreducible_gap_rat (by decide : 0<6)
    have hg := gap_degree (by decide : 0<6)
    have he := minpoly.eq_of_irreducible_of_monic hir (lifted_gap_root hu hb) (hg.monic.map _)
    have h6 := minpoly.degree_dvd (IsIntegral.of_finite ℚ ((b+5)/2))
    rw [← he,hg.monic.natDegree_map,hg.natDegree_eq,h3] at h6
    omega
  · have h := congrArg (Algebra.norm ℚ) hb
    rw [map_pow,map_mul,hn,show Algebra.norm ℚ (1957:k)=1957^3 by
      rw [← h3]; exact Algebra.norm_natCast ℚ (S:=k) 1957] at h
    apply discr_nonsquare (Algebra.norm ℚ b/(1957*17))
    rw [div_pow,h]
    norm_num

#print axioms lifted_gap_root
#print axioms root_nonsquare
end
end Erdos478.SexticGap
