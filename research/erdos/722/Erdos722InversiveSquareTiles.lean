import Erdos722CoordinateStripeDeletion
import Erdos722ProjectiveSublines
import Mathlib.Tactic

/-!
# The line–line tile in a quadratic field extension

Label the finite points of the inversive plane by two coordinates over
the small field. Each row and each column, augmented by infinity, is an
affine projective image of the subfield line.
-/

namespace Erdos722.PointedProduct
open Finset Matrix OnePoint
open scoped Classical
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F]

private theorem affine_stripe (L : (F × F) ≃ₗ[F] K) (f : F × F → F) (a : F)
    (v b : F × F) (hv : v≠0) (line : ∀ p, f p=a ↔ ∃ t : F, t • v+b=p) :
    stripe f a∈Sublines.blocks (algebraMap F K) L.toEquiv.optionCongr := by
  let label : Grid F F ≃ OnePoint K := L.toEquiv.optionCongr
  let M : Matrix (Fin 2) (Fin 2) K := !![L v,L b;0,1]
  let g := GeneralLinearGroup.mkOfDetNeZero M (by simpa [M,det_fin_two] using mt L.map_eq_zero_iff.mp hv)
  have gi : g • (∞ : OnePoint K)=∞ := by simp [g,M,smul_infty_eq_ite]
  have gt (t : F) : g • ((algebraMap F K t : K) : OnePoint K)=(L (t • v+b) : OnePoint K) := by
    rw [map_add,L.map_smul]
    simp [g,M,smul_some_eq_ite,Algebra.smul_def,mul_comm]
  suffices he : stripe f a=Sublines.subline (algebraMap F K) label g by
    exact mem_filter.mpr ⟨mem_univ _,g,he⟩
  have mem (w : Grid F F) : w∈Sublines.subline (algebraMap F K) label g ↔
      ∃ t : OnePoint F, g • t.map (algebraMap F K)=label w := by
    simp [Sublines.subline,Equiv.symm_apply_eq]
  ext w
  rw [mem]
  cases w with
  | none => exact ⟨fun _ => ⟨∞,gi⟩,fun _ => none_mem_stripe ..⟩
  | some p =>
    rw [some_mem_stripe,line]
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨(t : OnePoint F),gt t⟩
    · rintro ⟨t,ht⟩
      cases t with
      | infty =>
        change g • (∞ : OnePoint K)=(L p : OnePoint K) at ht
        rw [gi] at ht
        cases ht
      | coe t =>
        change g • ((algebraMap F K t : K) : OnePoint K)=(L p : OnePoint K) at ht
        exact ⟨t,L.injective (OnePoint.coe_eq_coe.mp ((gt t).symm.trans ht))⟩

/-- The square tile over a finite field of characteristic p, including order two. -/
def inversive_line_line (F : Type*) [Field F] [DecidableEq F] [Fintype F] (p : ℕ)
    [Fact p.Prime] [CharP F p] : RectangleCover (Fintype.card F) .line .line F F := by
  classical
  let K := FiniteField.Extension F p 2
  let L : (F × F) ≃ₗ[F] K := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_prod,Module.finrank_self,FiniteField.finrank_extension])
  apply stripe_deletion _ (Sublines.blocks_isBlockDesign (algebraMap F K) L.toEquiv.optionCongr)
  · intro a
    apply affine_stripe L Prod.fst a (0,1) (a,0) (by simp)
    rintro ⟨x,y⟩
    simp [Prod.ext_iff,eq_comm]
  · intro a
    apply affine_stripe L Prod.snd a (1,0) (0,a) (by simp)
    rintro ⟨x,y⟩
    simp [Prod.ext_iff,eq_comm]

#print axioms inversive_line_line
end
end Erdos722.PointedProduct
