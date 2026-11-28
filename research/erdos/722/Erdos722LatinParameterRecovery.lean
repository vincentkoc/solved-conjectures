import Erdos722LatinCosetSystems

/-! # Recovering the local cubes and exterior offsets from the block set -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint QuadSwitch Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

variable {I : Type*} [DecidableEq I] [Fintype I]

theorem block_triple (Q : Rule I) {B : Finset I} (hb : B∈Q.blocks) :
    ∃ i j k, baseQuad Q i j k=B := by
  obtain ⟨size,closed⟩ := (Q.mem_blocks B).mp hb
  obtain ⟨i,j,k,z,ij,ik,_,jk,_,_,eq⟩ := card_eq_four.mp size
  have sub : ({i,j,k}:Finset I) ⊆ B := by rw [eq]; simp
  have mem := closed i (sub (by simp)) j (sub (by simp)) k (sub (by simp))
  have fresh := Q.fresh ij ik jk
  rw [eq] at mem
  simp only [mem_insert,mem_singleton,not_or] at mem fresh
  have fourth : Q.complete i j k=z := by tauto
  refine ⟨i,j,k,?_⟩
  ext x
  simp only [baseQuad,fourth,eq,mem_insert,mem_singleton]
  tauto

theorem coloured_eq_at (Q : Rule I) (M : Matching I) (C : IncidenceColours Q) (u v : BlockOffsets Q)
    (i j k : I) (x y z : Fibre) (same : transversalOffset Q u i j k=transversalOffset Q v i j k) :
    (colouredRule Q M C u).complete (i,x) (j,y) (k,z)=(colouredRule Q M C v).complete (i,x) (j,y) (k,z) := by
  apply Prod.ext
  · rfl
  apply (blockChart Q (linearCoordinates C) (baseQuad Q i j k) (Q.complete i j k)).injective
  exact (coloured_completion M C u i j k x y z).trans
    ((congrArg (_+·) same).trans (coloured_completion M C v i j k x y z).symm)

theorem baseline_recovers (d : ℕ) (hd : 6≤d) (u v : OutsideOffsets d) (B : outsideBlocks d)
    {i j k : Base d} (hb : baseQuad (cubeRule (d+2)) i j k=B.val)
    (same : (baseline d hd u).complete (i,0) (j,0) (k,0)=(baseline d hd v).complete (i,0) (j,0) (k,0)) :
    u B=v B := by
  let Q := cubeRule (d+2)
  have orig := coloured_completion (matching d hd) (colours d hd) (extendOffset d u) i j k 0 0 0
  have dst := coloured_completion (matching d hd) (colours d hd) (extendOffset d v) i j k 0 0 0
  dsimp only at orig dst
  rw [show (colouredRule Q (matching d hd) (colours d hd) (extendOffset d u)).complete (i,0) (j,0) (k,0)=_
    from same] at orig
  have off := add_left_cancel (orig.symm.trans dst)
  change offsetAt Q (extendOffset d u) (baseQuad Q i j k)=offsetAt Q (extendOffset d v) (baseQuad Q i j k) at off
  have block : B.val∈Q.blocks := (mem_sdiff.mp B.prop).1
  rw [hb] at off
  simpa only [offsetAt,dif_pos block,extendOffset,dif_pos B.prop] using off

theorem parameters_recovered (d : ℕ) (hd : 6≤d) (a b : Parameters d)
    (same : (latinRule d hd a).blocks=(latinRule d hd b).blocks) : a=b := by
  let Q := cubeRule (d+2)
  have ops := completion_determined (latinRule d hd a) (latinRule d hd b) same
  apply Prod.ext
  · funext B
    obtain ⟨i,j,k,hb⟩ := block_triple Q (region_sub d B.prop)
    have mem : baseQuad Q i j k∈region d := hb ▸ B.prop
    have obj : (⟨_,mem⟩ : region d)=B := Subtype.ext hb
    apply cubeLaw_recovers (numbering d B) symbols
    intro f
    have qa := patch_graph Q (baseline d hd a.2) (laws d a.1) (region_size d)
      (baseline_compatible d hd a.2).project i j k mem f
    have qb := patch_graph Q (baseline d hd b.2) (laws d b.1) (region_size d)
      (baseline_compatible d hd b.2).project i j k mem f
    rw [obj] at qa qb
    change ((latinRule d hd a).complete _ _ _=_) ↔ _ at qa
    rw [ops] at qa
    exact qa.symm.trans qb
  · funext B
    obtain ⟨block,off⟩ := mem_sdiff.mp B.prop
    obtain ⟨i,j,k,hb⟩ := block_triple Q block
    have clear : baseQuad Q i j k ∉ region d := fun h => off (hb ▸ h)
    apply baseline_recovers d hd _ _ B hb
    exact (patch_outside Q _ (laws d a.1) (region_size d) (baseline_compatible d hd a.2).project
      (i,0) (j,0) (k,0) clear).symm.trans ((ops ..).trans
      (patch_outside Q _ (laws d b.1) (region_size d) (baseline_compatible d hd b.2).project
        (i,0) (j,0) (k,0) clear))

#print axioms block_triple
#print axioms coloured_eq_at
#print axioms baseline_recovers
#print axioms parameters_recovered
end
end Erdos722.LatinFillings
