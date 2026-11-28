import Erdos722RigidPathMatching
import Erdos722FourFibreSpectrum

/-! # Realizing the rigid array in the normalized, labelled cube family -/

namespace Erdos722.FourPoint
open Finset QuadCompletion
noncomputable section
attribute [local instance] cubeOrder cubeDec

private theorem matching_ext {I : Type*} {A B : Matching I} (h : A.transport=B.transport) : A=B := by
  cases A; cases B; cases h; rfl

theorem matching_from_edges {I : Type*} [LinearOrder I] [Fintype I] (M : Matching I) {o : I}
    (star : Normalized M o) :
    edgeMatching o (fun e => M.transport e.val.1 e.val.2)=M := by
  apply matching_ext
  funext i j
  simp only [edgeMatching,edgeMove]
  split
  · rfl
  · split
    · rw [M.reverse i j,inv_inv]
    · rename_i a b
      by_cases io : i=o
      · subst i; exact (star j).symm
      by_cases jo : j=o
      · subst j; rw [M.reverse o i,star,inv_one]
      have eq : i=j := by
        rcases lt_trichotomy i j with lt|eq|gt
        · exact (a ((mem_edges ..).mpr ⟨⟨io,jo⟩,lt⟩)).elim
        · exact eq
        · exact (b ((mem_edges ..).mpr ⟨⟨jo,io⟩,gt⟩)).elim
      subst j; exact (M.diagonal i).symm

theorem noFix_edge_iff {I : Type*} [LinearOrder I] [Fintype I] (o : I) (w : edges o → Colour) :
    (¬∃ a : Direction, ∀ i j, (edgeMatching o w).transport i j a=a) ↔ w∈noDirectionWords ↥(edges o) := by
  rw [mem_noDirectionWords,card_eq_zero,eq_empty_iff_forall_notMem]
  constructor
  · intro h a ha
    apply h
    have full := (invariant_iff_edges o w (some a)).mpr (fun e => congrArg some ((mem_survivors w a).mp ha e))
    exact ⟨a,fun i j => Option.some.inj (full i j)⟩
  · rintro h ⟨a,ha⟩
    have edge := (invariant_iff_edges o w (some a)).mp (fun i j => congrArg some (ha i j))
    exact h a ((mem_survivors w a).mpr fun e => Option.some.inj (edge e))

private theorem enough (d : ℕ) (hd : 2≤d) : 4≤2^d :=
  Nat.pow_le_pow_right (by decide : 0<2) hd

/-- Label the root by zero and the other vertices by their positions on the path. -/
def pathLabels (d : ℕ) (hd : 2≤d) : Cube d ≃ Fin ((2^d-4)+4) := by
  let e : Cube d ≃ Fin ((2^d-4)+4) := Fintype.equivFinOfCardEq (by
    simp only [Cube,Fintype.card_pi,Fintype.card_fin,ZMod.card,Finset.prod_const,Finset.card_univ]
    have := enough d hd
    omega)
  exact e.trans (Equiv.swap (e 0) ⟨0,by omega⟩)

def rigidWord (d : ℕ) (hd : 2≤d) : EdgeWord d :=
  fun a => (pathMatching (pathLabels d hd)).transport a.val.1 a.val.2

theorem rigidWord_matching (d : ℕ) (hd : 2≤d) :
    edgeMatching (0 : Cube d) (rigidWord d hd)=pathMatching (pathLabels d hd) := by
  apply matching_from_edges
  have h := path_star (pathLabels d hd)
  have he : (pathLabels d hd).symm ⟨0,by omega⟩=0 := by
    apply (pathLabels d hd).injective
    rw [Equiv.apply_symm_apply]
    simp [pathLabels]
  rwa [he] at h

theorem rigidWord_top (d : ℕ) (hd : 2≤d) : rigidWord d hd∈noDirectionWords (CubeEdge d) := by
  apply (noFix_edge_iff ..).mp
  rw [rigidWord_matching]
  exact path_noFix _

#print axioms matching_from_edges
#print axioms noFix_edge_iff
#print axioms pathLabels
#print axioms rigidWord
#print axioms rigidWord_matching
#print axioms rigidWord_top
end
end Erdos722.FourPoint
