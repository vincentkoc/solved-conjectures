import Erdos722CubeMarkedCoefficients
import Erdos722TwistedCubeFamilies

/-! # A codimension-two coset of base blocks disjoint from the marked affine basis -/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec

/-- Prefixing two ones embeds the smaller affine quadruple system. -/
def cosetPoint (d : ℕ) : Cube d ↪ Cube (d+2) where
  toFun x := Fin.cons 1 (Fin.cons 1 x)
  inj' := by
    intro x y eq
    funext i
    exact congrFun eq i.succ.succ

theorem coset_complete (d : ℕ) (x y z : Cube d) :
    cosetPoint d ((cubeRule d).complete x y z)=
      (cubeRule (d+2)).complete (cosetPoint d x) (cosetPoint d y) (cosetPoint d z) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
  all_goals change (1:ZMod 2)=1+1+1; decide

def cosetPoints (d : ℕ) : Finset (Cube (d+2)) := univ.map (cosetPoint d)

theorem coset_points_card (d : ℕ) : (cosetPoints d).card=2^d := by simp [cosetPoints,Cube]

theorem coset_avoids_basis (d : ℕ) {x : Cube (d+2)} (hx : x∈cosetPoints d) :
    x∉affineBasisMarks (d+2) := by
  obtain ⟨a,_,rfl⟩ := mem_map.mp hx
  have h₀ : cosetPoint d a 0=1 := rfl
  have h₁ : cosetPoint d a (0 : Fin (d+1)).succ=1 := rfl
  intro h
  simp only [affineBasisMarks,mem_insert,mem_image] at h
  rcases h with z|e
  · rw [z] at h₀
    exact zero_ne_one h₀
  · obtain ⟨i,_,hi⟩ := e
    rw [← hi,Pi.basisFun_apply] at h₀ h₁
    by_cases eq : i=0
    · subst i
      simp at h₁
    · simp [Ne.symm eq] at h₀

def cosetBlock (d : ℕ) : (cubeRule d).blocks ↪ (cubeRule (d+2)).blocks where
  toFun B := ⟨B.val.map (cosetPoint d),(cubeRule d).map_block _ _ (coset_complete d) B.prop⟩
  inj' := fun _ _ e => Subtype.ext (map_injective _ (congrArg Subtype.val e))

def cosetBlocks (d : ℕ) : Finset (cubeRule (d+2)).blocks := univ.map (cosetBlock d)

theorem coset_blocks_card (d : ℕ) : (cosetBlocks d).card=blockNumber (2^d) := by
  rw [cosetBlocks,card_map,card_univ,Fintype.card_coe,base_block_count (cubeRule d).isBlockDesign]
  simp [blockNumber,Cube]

theorem coset_block_points (d : ℕ) {B : (cubeRule (d+2)).blocks} (hB : B∈cosetBlocks d) :
    B.val⊆cosetPoints d := by
  obtain ⟨A,_,rfl⟩ := mem_map.mp hB
  exact map_subset_map.mpr (subset_univ A.val)

theorem private_outside_coset (d : ℕ) (hd : 6≤d+2) (q : affineBasisMarks (d+2)) :
    cubePrivateBlocks (d+2) hd q ∉ cosetBlocks d := by
  intro h
  exact coset_avoids_basis d (coset_block_points d h (cubePrivateBlocks_incident (d+2) hd q)) q.prop

/-- More than half of the base points avoid both the variable coset and all
private blocks. This leaves a common clean point under any base permutation. -/
def protectedSupport (d : ℕ) (hd : 6≤d+2) :=
  cosetPoints d ∪ markedSupport (cubePrivateBlocks (d+2) hd)

private theorem coset_room (d : ℕ) (hd : 6≤d) : 4*(d+3)<2^d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

theorem coset_common_anchor (d : ℕ) (hd : 6≤d) (b : Equiv.Perm (Cube (d+2))) :
    ∃ o, o∉protectedSupport d (by omega) ∧ b o∉protectedSupport d (by omega) := by
  let S := protectedSupport d (by omega)
  let T := S.map b.symm.toEmbedding
  have count : (affineBasisMarks (d+2)).card≤d+3 := affineBasisMarks_bound _
  have bnd := card_union_le (cosetPoints d) (markedSupport (cubePrivateBlocks (d+2) (by omega)))
  have marks := markedSupport_bound (cubePrivateBlocks (d+2) (by omega))
  rw [coset_points_card] at bnd
  have room := coset_room d hd
  have cover := card_union_le S T
  have eq : T.card=S.card := card_map ..
  have ss : S.card≤2^d+4*(d+3) := by
    change (cosetPoints d ∪ markedSupport (cubePrivateBlocks (d+2) _)).card≤_
    omega
  have small : (S∪T).card<(univ : Finset (Cube (d+2))).card := by
    simpa only [card_univ,Cube,Fintype.card_fun,Fintype.card_fin,ZMod.card,pow_succ] using
      (show (S∪T).card<2^d*2*2 by omega)
  obtain ⟨o,_,miss⟩ := exists_mem_notMem_of_card_lt_card small
  simp only [mem_union,not_or] at miss
  exact ⟨o,miss.1,fun h => miss.2 (mem_map.mpr ⟨b o,h,b.symm_apply_apply o⟩)⟩

#print axioms cosetPoint
#print axioms coset_complete
#print axioms cosetPoints
#print axioms coset_points_card
#print axioms coset_avoids_basis
#print axioms cosetBlock
#print axioms cosetBlocks
#print axioms coset_blocks_card
#print axioms coset_block_points
#print axioms private_outside_coset
#print axioms protectedSupport
#print axioms coset_common_anchor
end
end Erdos722.FourPoint
