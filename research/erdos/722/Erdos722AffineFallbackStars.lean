import Erdos722AffineTransversalGraphs
import Erdos722LatinParameterRecovery

/-! # Affine stars of the unmodified transversal laws -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings Equiv
open scoped Classical
noncomputable section
variable {I : Type*} [DecidableEq I] [Fintype I]

/-- Independent chart permutations and a block offset preserve ternary closure. -/
theorem blockwise_closed (Q : Rule I) (M : Matching I) (u : BlockOffsets Q)
    (D : BlockCoordinates Q) {i j k : I} (ij : i≠j) (ik : i≠k) (jk : j≠k) :
    Closed (OnGraph Q (blockwiseRule Q M (twistedRule Q M u) (twisted_compatible ..) D) i j k) := by
  let R := blockwiseRule Q M (twistedRule Q M u) (twisted_compatible ..) D
  let B : Q.blocks := ⟨_,completed_block Q ij ik jk⟩
  let w := Q.complete i j k
  have chart (f : I → Fibre) : OnGraph Q R i j k f ↔
      D B w (f w)=D B i (f i)+D B j (f j)+D B k (f k)+u B := by
    have eq := blockwise_transversal Q M u D ij ik jk (f i) (f j) (f k)
    change D B w (R.complete (i,f i) (j,f j) (k,f k)).2=_ at eq
    constructor
    · intro h
      exact (congrArg (D B w) (congrArg Prod.snd h)).symm.trans eq
    · intro h
      exact Prod.ext ((blockwise_compatible ..).project ..) ((D B w).injective (eq.trans h.symm))
  intro f g h hf hg hh
  apply (chart _).mpr
  simp only [fibre_mix_perm,(chart f).mp hf,(chart g).mp hg,(chart h).mp hh]
  have trip (a : Fibre) : a+a+a=a := (show ∀ a : Fibre,a+a+a=a by decide +kernel) a
  calc
    _ = (D B i (f i)+D B i (g i)+D B i (h i)) + (D B j (f j)+D B j (g j)+D B j (h j)) +
      (D B k (f k)+D B k (g k)+D B k (h k)) + (u B+u B+u B) := by ac_rfl
    _ = _ := by rw [trip]

omit [Fintype I] in
theorem off_graph (Q : Rule I) (R : Rule (I × Fibre)) {S : Finset (Finset I)}
    (L : Laws S Fibre) (sizes : ∀ B∈S,B.card=4)
    (proj : ∀ a b c, (R.complete a b c).1=Q.complete a.1 b.1 c.1)
    {i j k : I} (off : baseQuad Q i j k ∉ S) :
    Closed (OnGraph Q (patch Q R L sizes proj) i j k) ↔ Closed (OnGraph Q R i j k) := by
  apply closed_congr
  intro f
  simp only [OnGraph,patch_outside Q R L sizes proj (i,f i) (j,f j) (k,f k) off]

attribute [local instance] cubeOrder cubeDec

/-- A point outside the coset in the preceding family has an affine star, including
when some incident blocks use nonidentity chart permutations. -/
theorem coset_affine_star (d : ℕ) (hd : 6≤d) (a : Parameters d) {o : Base d}
    (off : o∉cosetPoints d) : HasAffineStar (cubeRule (d+2)) (latinRule d hd a) o := by
  intro i j k ij ik jk mem
  have outside : baseQuad (cubeRule (d+2)) i j k ∉ region d := fun h => off (region_points d h mem)
  apply (off_graph (cubeRule (d+2)) (baseline d hd a.2) (laws d a.1) (region_size d)
    (baseline_compatible d hd a.2).project outside).mpr
  exact blockwise_closed (cubeRule (d+2)) (matching d hd) (extendOffset d a.2)
    (linearCoordinates (colours d hd)) ij ik jk

#print axioms blockwise_closed
#print axioms off_graph
#print axioms coset_affine_star
end
end Erdos722.AffineStar
