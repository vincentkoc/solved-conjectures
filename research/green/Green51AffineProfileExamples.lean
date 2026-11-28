import Green51AffineProfileTable

/-! # Dimension-sixteen affine class counts at the endpoints of the missing-count band -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51MissingMasks Green51Hyperplane

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem table_16 : (List.range' 41 20).map (fun k => (profileTable 15 k).card)=
    [136,123,103,91,75,64,51,44,33,28,21,17,12,10,6,5,3,2,1,1] := by decide +kernel

private theorem level : threshold 12=(25376:ℝ)/65536 := by
  norm_num [threshold,halfLayer,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem classes_in_dimension_sixteen :
    (List.range' 41 20).map (fun k =>
      Nat.card (Quotient (affineSetoid (countedDoubles 16 k ((25376:ℝ)/65536))))) =
    [136,123,103,91,75,64,51,44,33,28,21,17,12,10,6,5,3,2,1,1] := by
  rw [←table_16,←level]
  apply List.map_congr_left
  intro k hk
  have lower : 41 ≤ k := by
    obtain ⟨i,_,h⟩ := List.mem_range'.mp hk
    omega
  exact table_eq_classes (s := 6) (by decide) (by omega)

theorem classes_at_forty_one :
    Nat.card (Quotient (affineSetoid (countedDoubles 16 41 ((25376:ℝ)/65536))))=136 := by
  exact congrArg (fun l : List ℕ => l.getD 0 0) classes_in_dimension_sixteen

theorem classes_at_fifty_eight :
    Nat.card (Quotient (affineSetoid (countedDoubles 16 58 ((25376:ℝ)/65536))))=2 := by
  exact congrArg (fun l : List ℕ => l.getD 17 0) classes_in_dimension_sixteen

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.classes_in_dimension_sixteen
#print axioms Green51FrameIsomorphisms.classes_at_forty_one
#print axioms Green51FrameIsomorphisms.classes_at_fifty_eight
