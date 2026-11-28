import Erdos722UniqueAffineStarSystems

/-! # Recovering every parameter and excluding all nonidentity point isomorphisms -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
variable {d : ℕ} {hd : 6≤d}

/-- On every protected block the offset changes by the measured fibre translation. -/
theorem translated_exterior (L : Layout d hd) (a b : Choices L) (t : Base d → Fibre)
    (iso : (pointForm (1 : Perm (Base d)) 1 t).finsetCongr.finsetCongr (starRule L a).blocks=(starRule L b).blocks) :
    b.2.out=a.2.out+measurements L t := by
  let Q := cubeRule (d+2)
  let M := matching d hd
  let C := colours d hd
  let u := outerOffset L a.2
  let v := outerOffset L b.2
  let W := u+weightedGradient Q C t
  let e := pointForm (1 : Perm (Base d)) 1 t
  have ez (i : Base d) : e (i,0)=(i,t i) := by simp [e,pointForm,move_zero]
  funext B
  obtain ⟨i,j,k,hB⟩ := block_triple Q (L.sub B.prop)
  have off : baseQuad Q i j k ∉ interior L := fun h => (mem_sdiff.mp h).2 (hB ▸ B.prop)
  have baseChange := completion_of_blocks (fallback L a.2) (colouredRule Q M C W) e
    (translation_coloured_blocks M C u t) (i,0) (j,0) (k,0)
  have change := completion_of_blocks (starRule L a) (starRule L b) e iso (i,0) (j,0) (k,0)
  rw [ez,ez,ez] at baseChange change
  have left := patch_outside Q (fallback L a.2) (localLaw L a.1) (interior_size L)
    (fallback_compatible L a.2).project (i,0) (j,0) (k,0) off
  have right := patch_outside Q (fallback L b.2) (localLaw L b.1) (interior_size L)
    (fallback_compatible L b.2).project (i,t i) (j,t j) (k,t k) off
  have same := baseChange.symm.trans ((congrArg e left.symm).trans (change.trans right))
  have first := coloured_completion M C W i j k (t i) (t j) (t k)
  have second := coloured_completion M C v i j k (t i) (t j) (t k)
  dsimp only at first second
  rw [same] at first
  have offsets := add_left_cancel (second.symm.trans first)
  change offsetAt Q v (baseQuad Q i j k)=offsetAt Q W (baseQuad Q i j k) at offsets
  rw [hB] at offsets
  have block : B.val∈Q.blocks := L.sub B.prop
  change b.2.out B=a.2.out B+weightedGradient Q C t ⟨B.val,block⟩
  simpa only [offsetAt,dif_pos block,W,u,v,Pi.add_apply,outerOffset,dif_pos B.prop] using offsets

theorem recover_cubes (L : Layout d hd) (a b : Choices L) (same : (starRule L a).blocks=(starRule L b).blocks) :
    a.1=b.1 := by
  apply localCube_injective L
  funext B
  let Q := cubeRule (d+2)
  obtain ⟨i,j,k,hB⟩ := block_triple Q (mem_sdiff.mp B.prop).1
  have m : baseQuad Q i j k∈interior L := hB ▸ B.prop
  have obj : (⟨_,m⟩ : interior L)=B := Subtype.ext hB
  apply cubeLaw_recovers (blockOrder L B) symbols
  intro f
  have g (c : Choices L) := patch_graph Q (fallback L c.2) (localLaw L c.1) (interior_size L)
    (fallback_compatible L c.2).project i j k m f
  have p := g a
  have r := g b
  rw [obj] at p r
  change ((starRule L a).complete _ _ _=_) ↔ _ at p
  rw [completion_determined (starRule L a) (starRule L b) same] at p
  exact p.symm.trans r

/-- With offset representatives fixed, an unrestricted point isomorphism implies parameter equality
and is itself the identity. -/
theorem star_isomorphism (L : Layout d hd) (a b : Choices L) (e : Perm (Base d × Fibre))
    (iso : e.finsetCongr.finsetCongr (starRule L a).blocks=(starRule L b).blocks) : a=b ∧ e=1 := by
  obtain ⟨t,form⟩ := star_translation L a b e iso
  have eq := iso
  rw [form] at eq
  obtain ⟨offset,zero⟩ := offset_rigidity L a.2 b.2 t (translated_exterior L a b t eq)
  have id : e=1 := by
    rw [form,zero]
    apply Equiv.ext
    rintro ⟨i,x⟩
    simp [pointForm,move_one]
  rw [id] at iso
  change (Equiv.refl _).finsetCongr.finsetCongr _=_ at iso
  rw [Equiv.finsetCongr_refl,Equiv.finsetCongr_refl,Equiv.refl_apply] at iso
  exact ⟨Prod.ext (recover_cubes L a b iso) offset,id⟩

#print axioms translated_exterior
#print axioms recover_cubes
#print axioms star_isomorphism
end
end Erdos722.AffineStar
