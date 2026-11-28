import Erdos478QuadraticSquareClasses
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Data.Finite.Perm
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Rat.Sqrt

/-!
# The three squared reflection coordinates of the sixth factorial gap

For a factorial endpoint `x`, the coordinate `w=(2*x-5)^2` satisfies
a cubic with root product `17^2` and discriminant `64^2*1957`.
-/

namespace Erdos478.SexticGap
open Polynomial IntermediateField SquareClasses
noncomputable section

def cub (R : Type*) [Ring R] : Cubic R := ⟨1,-35,259,-289⟩

theorem cub_monic (R : Type*) [Field R] : (cub R).toPoly.Monic :=
  Cubic.monic_of_a_eq_one rfl

theorem cub_degree (R : Type*) [Field R] : (cub R).toPoly.natDegree=3 :=
  natDegree_eq_of_degree_eq_some (Cubic.degree_of_a_ne_zero (by simp [cub]))

theorem cub_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    (cub R).toPoly.map φ = (cub S).toPoly := by
  simp [cub,Cubic.toPoly,map_ofNat]

theorem cub_eval {R : Type*} [CommRing R] (w : R) :
    (cub R).toPoly.eval w=w^3-35*w^2+259*w-289 := by
  simp [cub,Cubic.toPoly]
  ring

theorem gap_transform {R : Type*} [CommRing R] (x : R) :
    (cub R).toPoly.eval ((2*x-5)^2) = 64*((descPochhammer R 6).eval x-1) := by
  rw [cub_eval]
  norm_num [show (6:ℕ)=5+1 by rfl,show (5:ℕ)=4+1 by rfl,show (4:ℕ)=3+1 by rfl,
    show (3:ℕ)=2+1 by rfl,show (2:ℕ)=1+1 by rfl,descPochhammer_succ_right]
  ring

theorem cub_irreducible : Irreducible (cub ℚ).toPoly := by
  let f := (cub ℤ).toPoly
  have hm : f.Monic := Cubic.monic_of_a_eq_one rfl
  have hu : Irreducible (cub (ZMod 3)).toPoly := by
    have hd := cub_degree (ZMod 3)
    apply ((cub_monic _).irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro x hx
    have h := (mem_roots (cub_monic _).ne_zero).mp hx
    change (cub _).toPoly.eval x=0 at h
    rw [cub_eval] at h
    exact (by decide : ∀ x : ZMod 3, x^3-35*x^2+259*x-289≠0) x h
  have hi : Irreducible f := Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3)) f hm
    (by simpa [f,cub_map] using hu)
  rw [← cub_map (algebraMap ℤ ℚ)]
  exact (hm.irreducible_iff_irreducible_map_fraction_map).mp hi

theorem cub_root_data (K : Type) [Field K] [Algebra ℚ K]
    (hs : ((cub ℚ).toPoly.map (algebraMap ℚ K)).Splits) :
    ∃ x y z : K, (cub K).toPoly = (X-C x)*(X-C y)*(X-C z) ∧
      x*y*z=17^2 ∧ ((x-y)*(x-z)*(y-z)/64)^2=1957 := by
  have h : (cub ℚ).a≠0 := by decide
  obtain ⟨x,y,z,hxyz⟩ := (Cubic.splits_iff_roots_eq_three h).mp hs
  refine ⟨x,y,z,?_,?_,?_⟩
  · have he := Cubic.eq_prod_three_roots h hxyz
    rw [Cubic.map_toPoly,cub_map] at he
    simpa [cub] using he
  · have he := Cubic.d_eq_three_roots h hxyz
    norm_num [cub] at he ⊢
    linear_combination -he
  · have he := Cubic.discr_eq_prod_three_roots h hxyz
    norm_num [cub,Cubic.discr] at he
    have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    field_simp
    linear_combination -he

theorem discr_nonsquare (x : ℚ) : x^2 ≠ 1957 := by
  intro h
  have H := (Rat.exists_mul_self 1957).mp ⟨x,by simpa [pow_two] using h⟩
  rw [show Rat.sqrt 1957=44 by rw [Rat.sqrt_ofNat]; norm_num] at H
  norm_num at H

theorem cub_field_degree (K : Type) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (cub ℚ).toPoly] : Module.finrank ℚ K = 6 := by
  let F := (cub ℚ).toPoly
  let e := IsSplittingField.algEquiv K F
  let L := F.SplittingField
  have hs := SplittingField.splits F
  obtain ⟨x,y,z,_,_,ht⟩ := cub_root_data L hs
  let t := (x-y)*(x-z)*(y-z)/64
  have h2 := minpoly.degree_dvd (IsIntegral.of_finite ℚ t)
  have hm := sqrt_minpoly (s:=t) discr_nonsquare (by simpa [t] using ht)
  rw [hm,natDegree_X_pow_sub_C] at h2
  have h3 := cub_irreducible.natDegree_dvd_finrank hs
  rw [cub_degree] at h3
  let : Fact ((F.map (algebraMap ℚ L)).Splits) := ⟨hs⟩
  have H := Nat.card_le_card_of_injective _ (Gal.galActionHom_injective F L)
  rw [Nat.card_perm,Nat.card_coe_set_eq,Gal.card_of_separable cub_irreducible.separable] at H
  have h6 : Module.finrank ℚ L ≤ 6 :=
    H.trans (Nat.factorial_le ((F.ncard_rootSet_le L).trans_eq (cub_degree ℚ)))
  have hp := Module.finrank_pos (R:=ℚ) (M:=L)
  rw [e.toLinearEquiv.finrank_eq]
  change Module.finrank ℚ L=6
  change 3 ∣ Module.finrank ℚ L at h3
  omega

#print axioms gap_transform
#print axioms cub_irreducible
#print axioms cub_root_data
#print axioms cub_field_degree
end
end Erdos478.SexticGap
