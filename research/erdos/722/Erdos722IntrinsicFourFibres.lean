import Erdos722FourFibreChecks
import Erdos722FourFibreCube

/-! # Recognizing the four-point fibres from the block family -/

namespace Erdos722.FourPoint
open QuadCompletion QuadSwitch
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The coordinate evaluations are separating checks on the binary affine base. -/
theorem cube_separates (d : ℕ) [DecidableEq (Cube d)] : Separates (cubeRule d).blocks := by
  intro x y same
  funext k
  exact same (fun i => i k) ((check_iff_complete _ _).mpr fun _ _ _ => rfl)

/-- Whenever the normalized matchings have no common direction, two points
agree on every binary check precisely when they belong to the same fibre.
The transversal filling can be arbitrary. -/
theorem sameChecks_four {Q : Rule I} {M : Matching I} {R : Rule (I × Fibre)}
    (sep : Separates Q.blocks) (h : Compatible Q M R) {o : I} (star : Normalized M o)
    (noFix : ¬∃ d : Direction, ∀ i j, M.transport i j d=d) (a b : I × Fibre) :
    SameChecks R.blocks a b ↔ a.1=b.1 := by
  constructor
  · intro same
    apply sep
    intro f hf
    apply same (fun x => f x.1)
    apply (check_iff_complete R _).mpr
    intro x y z
    rw [h.project]
    exact (check_iff_complete Q _).mp hf _ _ _
  · rcases a with ⟨i,x⟩
    rcases b with ⟨j,y⟩
    intro eq f hf
    change i=j at eq
    subst j
    obtain ⟨⟨c,hc⟩,hh⟩ := restrict_check h star (⟨f,hf⟩ : Checks R.blocks)
    cases c with
    | none => simpa only [character,add_zero] using (hh i x).trans (hh i y).symm
    | some d => exact (noFix ⟨d,fun u v => Option.some.inj (hc u v)⟩).elim

/-- A point bijection preserving the partition in both directions has a base
bijection and independent within-fibre permutations. -/
theorem fibre_coordinates {A B F : Type*} (o : F) (e : (A × F) ≃ (B × F))
    (same : ∀ i j x y, i=j ↔ (e (i,x)).1=(e (j,y)).1) :
    ∃ (b : A ≃ B) (v : A → Equiv.Perm F), ∀ i x, e (i,x)=(b i,v i x) := by
  let f (i : A) := (e (i,o)).1
  have proj (i : A) (x : F) : (e (i,x)).1=f i := (same i i x o).mp rfl
  have hf : Function.Bijective f := by
    constructor
    · exact fun i j => (same i j o o).mpr
    · intro j
      obtain ⟨⟨i,x⟩,he⟩ := e.surjective (j,o)
      exact ⟨i,(proj i x).symm.trans (congrArg Prod.fst he)⟩
  let b := Equiv.ofBijective f hf
  let v (i : A) (x : F) := (e (i,x)).2
  have hb (i : A) : Function.Bijective (v i) := by
    constructor
    · intro x y eq
      exact congrArg Prod.snd (e.injective (Prod.ext ((proj i x).trans (proj i y).symm) eq))
    · intro y
      obtain ⟨⟨j,x⟩,he⟩ := e.surjective (b i,y)
      have projected := congrArg Prod.fst he
      have ji : j=i := hf.1 ((proj j x).symm.trans projected)
      subst j
      exact ⟨x,congrArg Prod.snd he⟩
  exact ⟨b,fun i => Equiv.ofBijective _ (hb i),fun i x => Prod.ext (proj i x) rfl⟩

#print axioms fibre_coordinates
#print axioms cube_separates
#print axioms sameChecks_four
end Erdos722.FourPoint
