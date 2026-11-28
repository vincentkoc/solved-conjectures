import Erdos722MovedMatchingRow
import Erdos722MatchingFrameCounts

/-! # A quantitative exceptional set for minimum automorphisms -/

namespace Erdos722.FourPoint
open Finset Equiv
open scoped Classical
noncomputable section
attribute [local instance] cubeOrder cubeDec
local instance : Fintype Colour := fintypePerm
local instance (d : ℕ) : Fintype (Perm (Cube d)) := fintypePerm

def Typical (d : ℕ) (w : EdgeWord d) :=
  (∀ x,Normalized (edgeMatching 0 w) x → x=0) ∧
  ∀ b∈rootedBases d,∀ s,Frame (edgeMatching 0 w) (edgeMatching 0 w) b s → b=1 ∧ s=1

def exceptionalWords (d : ℕ) := (univ : Finset (EdgeWord d)).filter fun w => ¬Typical d w

/-- Three terms allow for a second identity star, a moved rooted base
permutation, and a pure colour symmetry. -/
def exceptionalBound (d : ℕ) :=
  let n := 2^d
  let m := numberEdges d
  (n-1)*6^(m-(n-2)) + n^d*(6*6^(m-(n-3))) + 5*3^m

private theorem bounded_union {A V : Type*} [DecidableEq V] (S : Finset A) (f : A → Finset V) (k : ℕ)
    (h : ∀ a∈S,(f a).card≤k) : (S.biUnion f).card≤S.card*k :=
  card_biUnion_le.trans ((sum_le_sum h).trans_eq (by simp))

theorem exceptional_words_bound (d : ℕ) : (exceptionalWords d).card≤exceptionalBound d := by
  let n := 2^d
  let m := numberEdges d
  let stars (x : Cube d) := (univ : Finset (EdgeWord d)).filter fun w => Normalized (edgeMatching 0 w) x
  let fixed (b : Perm (Cube d)) (s : Colour) := (univ : Finset (EdgeWord d)).filter fun w =>
    Frame (edgeMatching 0 w) (edgeMatching 0 w) b s
  let X := (univ : Finset (Cube d)).erase 0
  let B := (rootedBases d).erase 1
  let C := (univ : Finset Colour).erase 1
  let A := X.biUnion stars
  let F := B.biUnion fun b => univ.biUnion (fixed b)
  let P := C.biUnion (fixed 1)
  have subset : exceptionalWords d ⊆ (A∪F)∪P := by
    intro w hw
    by_contra h
    apply (mem_filter.mp hw).2
    have hA : w∉A := fun he => h (mem_union_left _ (mem_union_left _ he))
    have hF : w∉F := fun he => h (mem_union_left _ (mem_union_right _ he))
    have hP : w∉P := fun he => h (mem_union_right _ he)
    constructor
    · intro x hx
      by_contra ne
      exact hA (mem_biUnion.mpr ⟨x,mem_erase.mpr ⟨ne,mem_univ _⟩,mem_filter.mpr ⟨mem_univ _,hx⟩⟩)
    · intro b hb s hf
      have id : b=1 := by
        by_contra ne
        exact hF (mem_biUnion.mpr ⟨b,mem_erase.mpr ⟨ne,hb⟩,mem_biUnion.mpr
          ⟨s,mem_univ _,mem_filter.mpr ⟨mem_univ _,hf⟩⟩⟩)
      refine ⟨id,?_⟩
      subst b
      by_contra ne
      exact hP (mem_biUnion.mpr ⟨s,mem_erase.mpr ⟨ne,mem_univ _⟩,mem_filter.mpr ⟨mem_univ _,hf⟩⟩)
  have size : Fintype.card (Cube d)=n := by simp [Cube,n]
  have alph : Fintype.card Colour=6 := by decide +kernel
  have a : A.card≤(n-1)*6^(m-(n-2)) := by
    have ha := bounded_union X stars (6^(m-(n-2))) (fun x hx => by
      simpa only [stars,size,m,numberEdges,n] using (second_star_count (o:=(0:Cube d)) (mem_erase.mp hx).1).le)
    simpa only [X,card_erase_of_mem (mem_univ _),card_univ,size] using ha
  have f : F.card≤n^d*(6*6^(m-(n-3))) := by
    have hb := bounded_union B (fun b => univ.biUnion (fixed b)) (6*6^(m-(n-3))) (by
      intro b hb
      have mem : b∈rootedBases d := (mem_erase.mp hb).2
      have ne : b≠1 := (mem_erase.mp hb).1
      have root := ((mem_rootedBases d b).mp mem).1
      have each := bounded_union (univ : Finset Colour) (fixed b) (6^(m-(n-3))) (fun s _ => by
        simpa only [fixed,size,m,numberEdges,n] using rooted_frame_bound (0:Cube d) b s root ne)
      simpa only [card_univ,alph] using each)
    exact hb.trans (Nat.mul_le_mul_right _ ((card_le_card (erase_subset ..)).trans (rooted_bases_card d)))
  have p : P.card≤5*3^m := by
    have hc := bounded_union C (fixed 1) (3^m) (fun s hs => by
      simpa only [fixed,size,m,numberEdges,n] using colour_frame_bound (0:Cube d) s (mem_erase.mp hs).1)
    simpa only [C,card_erase_of_mem (mem_univ _),card_univ,alph] using hc
  exact (card_le_card subset).trans ((card_union_le ..).trans (Nat.add_le_add
    ((card_union_le ..).trans (Nat.add_le_add a f)) p))

#print axioms Typical
#print axioms exceptionalWords
#print axioms exceptionalBound
#print axioms exceptional_words_bound
end
end Erdos722.FourPoint
