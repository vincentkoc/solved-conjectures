import Erdos722FourFibreSpectrum

/-!
# The sharp worst-case rank guarantee over all compatible transversal fillings

The underlying four-point construction specializes Construction II(s) of D. V. Zinoviev
and V. A. Zinoviev, *Steiner quadruple systems of a fixed corank* (OC2013).
Here the three matchings at each fibre are labelled. We minimize over all choices of
a compatible transversal rule for each normalized word of matching permutations.
-/

namespace Erdos722.FourPoint
open Finset QuadCompletion QuadSwitch
noncomputable section
open scoped Classical
attribute [local instance] cubeOrder cubeDec
local instance : Fintype Colour := fintypePerm

/-- Choose the transversal rule separately for every matching word. -/
structure FillingFamily (d : ℕ) where
  rule : EdgeWord d → Rule (Cube d × Fibre)
  compatible (w) : Compatible (cubeRule d) (edgeMatching 0 w) (rule w)

def FillingFamily.system {d : ℕ} (F : FillingFamily d) (w : EdgeWord d) :=
  labelledBlocks d (F.rule w)

theorem FillingFamily.injective {d : ℕ} (F : FillingFamily d) : Function.Injective F.system := by
  intro w v eq
  have same := (fourLabels d).finsetCongr.finsetCongr.injective eq
  funext e
  apply Equiv.ext
  intro a
  let i := e.val.1
  let j := e.val.2
  have h := completion_determined (F.rule w) (F.rule v) same (i,0) (i,vector a) (j,0)
  rw [(F.compatible w).pair,(F.compatible v).pair] at h
  have eqv := congrArg Prod.snd h
  simpa only [zero_add,i,j,edge_forward,move_vector,direction_vector] using congrArg direction eqv

def FillingFamily.topSystems {d : ℕ} (F : FillingFamily d) :=
  (univ.image F.system).filter fun D => (binaryIncidence D).rank+(d+1)=4*2^d

theorem FillingFamily.system_count {d : ℕ} (F : FillingFamily d) :
    (univ.image F.system).card=6^numberEdges d := by
  rw [card_image_of_injective _ F.injective,card_univ,Fintype.card_fun,cubeEdge_card,
    show Fintype.card Colour=6 by decide +kernel]

theorem FillingFamily.top_lower_bound {d : ℕ} (F : FillingFamily d) :
    6^numberEdges d-(1+3*(2^numberEdges d-1))≤F.topSystems.card := by
  have sub : noDirectionWords (CubeEdge d)⊆univ.filter
      (fun w => (binaryIncidence (F.system w)).rank+(d+1)=4*2^d) := by
    intro w h
    exact mem_filter.mpr ⟨mem_univ _,(arbitrary_filling_rank d h _ (F.compatible w)).2⟩
  have le := card_le_card sub
  rwa [FillingFamily.topSystems,filter_image,card_image_of_injective _ F.injective,
    ← cubeEdge_card d,← noDirectionWords_card]

def splitFilling (d : ℕ) : FillingFamily d where
  rule w := fourRule (cubeRule d) (edgeMatching 0 w)
  compatible _ := fourRule_compatible ..

theorem split_attains_bound (d : ℕ) :
    (splitFilling d).topSystems.card=6^numberEdges d-(1+3*(2^numberEdges d-1)) := by
  rw [FillingFamily.topSystems,filter_image,card_image_of_injective _ (splitFilling d).injective,
    ← cubeEdge_card d,← noDirectionWords_card]
  congr 1
  ext w
  simp only [mem_filter,mem_univ,true_and]
  exact (rank_tests d w).1

/-- Optimize the number of labelled top-rank systems over every admissible
choice of transversals. The zero-sum filling attains the minimum. -/
theorem least_top_count (d : ℕ) :
    IsLeast (Set.range fun F : FillingFamily d => F.topSystems.card)
      (6^numberEdges d-(1+3*(2^numberEdges d-1))) :=
  ⟨⟨splitFilling d,split_attains_bound d⟩,fun _ ⟨F,h⟩ => h ▸ F.top_lower_bound⟩

end

#print axioms FillingFamily
#print axioms FillingFamily.system
#print axioms FillingFamily.injective
#print axioms FillingFamily.topSystems
#print axioms FillingFamily.system_count
#print axioms FillingFamily.top_lower_bound
#print axioms splitFilling
#print axioms split_attains_bound
#print axioms least_top_count
end Erdos722.FourPoint
