import Green51DenseDirectionRank

/-! # Small fibres realize very few of the stable affine classes -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

theorem low_dimension_fibre_classes {s r h D : ℕ} (hs : 5 ≤ s) (small : h<2^r)
    (large : 10≤h) (cut : 64*h*(Nat.log 2 h+2) ≤ D^2) (low : 2*r+D≤h) :
    2^(D^2/8)*fibreClasses s r h ≤ universalDefectNumber h := by
  classical
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  rw [count_omission_words hs small (stable_omission_margin hs small) ref size full]
  let W := wordSetoid ↥B (𝔽₂ r) h
  let A (q : Quotient W) := q.out.val
  apply far_rank_presentations_rare large cut A (fun q => q.out.property)
  · intro q
    left
    have rank := Submodule.finrank_le (rowDirectionSpace (A q))
    have dim : Module.finrank F (𝔽₂ r)=r := by simp [𝔽₂,𝔽]
    rw [dim] at rank
    omega
  · intro p q w
    have eq : Quotient.mk W p.out=Quotient.mk W q.out := Quotient.sound w
    exact p.out_eq.symm.trans (eq.trans q.out_eq)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.low_dimension_fibre_classes
