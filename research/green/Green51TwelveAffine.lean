import Green51FlatSections
import Green51AffineEvaluation
import Green51NineteenLabels

/-! # Twenty-five points force an affine three-space in dimension twelve -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51TwelveAffine
local notation "F" => ZMod 2
local notation "V" => Cube 12

/-- Evaluating affine linear functionals on a hypothetical flat-free set gives
a binary code of dimension thirteen and minimum distance at least seven. -/
theorem twenty_five (A : Finset V) (size : A.card = 25) : ∃ p, FlatAt A p := by
  classical
  by_contra avoid
  let e : Fin 25 ≃ ↥A := (finCongr size.symm).trans A.equivFin.symm
  let pick : Fin 25 ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  let E : Module.Dual F (F × V) →ₗ[F] Cube 25 :=
    { toFun := fun l i => l (1, pick i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have vanishes (l : Module.Dual F (F × V)) (few : (supp (E l)).card ≤ 6) : l = 0 := by
    let B := (supp (E l))ᶜ.map pick
    have sub : B ⊆ A := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := mem_map.mp hx
      exact (e i).property
    have large : 19 ≤ B.card := by
      dsimp only [B]
      rw [card_map, card_compl, Fintype.card_fin]
      omega
    have full := Green51FlatSections.columns_span Green51NineteenLabels.nineteen_affine
      (by decide) B large (fun ⟨p,h⟩ => avoid ⟨p, Green51FlatSections.flat_mono sub h⟩)
    have le : Submodule.span F ((fun x:V => ((1:F),x)) '' (B:Set V)) ≤ l.ker := by
      rw [Submodule.span_le]
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
      change l (1, pick i) = 0
      have := mem_compl.mp hi
      simpa [supp, E] using this
    rw [full, top_le_iff] at le
    exact LinearMap.ker_eq_top.mp le
  have inj : Function.Injective E := by
    intro l m eq
    apply sub_eq_zero.mp
    apply vanishes
    rw [map_sub, eq, sub_self]
    simp [supp]
  have rank := Green51AffineEvaluation.rank_of_seven E.range (by
    intro z nz
    obtain ⟨l, hl⟩ := z.property
    by_contra! small
    have zl := vanishes l (by rw [hl]; omega)
    apply nz
    apply Subtype.ext
    rw [←hl, zl, map_zero]
    rfl)
  rw [E.finrank_range_of_inj inj] at rank
  simp [Module.finrank_prod, Cube] at rank

end Green51TwelveAffine
#print axioms Green51TwelveAffine.twenty_five
