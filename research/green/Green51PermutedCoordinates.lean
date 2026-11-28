import Green51PermutedPairs

/-! # Independent coordinates of the symmetric binary quadratic graph -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise symmDiff
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

abbrev PairCoordinate (n:ℕ) := {p:Fin n × Fin n // p.1≤p.2}
abbrev Packed (n:ℕ) := PairCoordinate n → F
def pack (x:Cube n) : Packed n := fun i => x i.val.1*x i.val.2
private def ordered (i j:Fin n) : PairCoordinate n :=
  if h:i≤j then ⟨(i,j),h⟩ else ⟨(j,i),le_of_not_ge h⟩
private def entry (c:Packed n) : Coordinates n → Coordinates n → F
  | none,none => 0
  | none,some j => c ⟨(j,j),le_rfl⟩
  | some i,none => c ⟨(i,i),le_rfl⟩
  | some i,some j => c (ordered i j)
def expand (n:ℕ) : Packed n →ₗ[F] Target n where
  toFun := entry
  map_add' := by
    intro x y;ext i j
    change entry (x+y) i j=entry x i j+entry y i j
    cases i <;> cases j <;> simp [entry,Pi.add_apply]
  map_smul' := by
    intro s x;ext i j
    change entry (s • x) i j=s • entry x i j
    cases i <;> cases j <;> simp [entry,Pi.smul_apply]
theorem expand_inj (n:ℕ) : Function.Injective (expand n) := by
  intro a b eq
  funext ⟨⟨i,j⟩,h⟩
  have e:=congrFun (congrFun eq (some i)) (some j)
  change entry a (some i) (some j)=entry b (some i) (some j) at e
  simpa [entry,ordered,h] using e
theorem expand_pack (x:Cube n) : quad 0+expand n (pack x)=quad x := by
  ext i j
  have sq (v:F) : v*v=v := (show ∀ a:F,a*a=a from by decide) v
  change homogeneous (0:Cube n) i*homogeneous 0 j+entry (pack x) i j=homogeneous x i*homogeneous x j
  cases i <;> cases j <;> simp [homogeneous,entry,pack,sq]
  unfold ordered
  split <;> simp_all [mul_comm]

end Green51PermutedPairs

#print axioms Green51PermutedPairs.expand_inj
#print axioms Green51PermutedPairs.expand_pack
