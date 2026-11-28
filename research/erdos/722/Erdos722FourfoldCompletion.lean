import Erdos722FourfoldBridge
import Erdos722QuadCompletion

/-!
# Completing triples in four columns with two common points

Triples within a column use the source quadruple system. Two columns in
one half use synchronized one-factors. A pair from opposite halves uses
the involution determined by the cyclic edge colouring.
-/

namespace Erdos722.Fourfold
open QuadCompletion
variable {k : ℕ}

def put (h i : Bit) : Bit ⊕ Label k → Point k
  | .inl s => .stem s
  | .inr x => .pt h i x

variable (Q : Rule (Bit ⊕ Label k))

def pureCol (h i : Bit) (a b c : Bit ⊕ Label k) := put h i (Q.complete a b c)

noncomputable def flank (h j : Bit) (x y z : Label k) : Point k :=
  .pt h j ((parallel k).mate ((parallel k).row x y) z)

theorem flank_comm (h j : Bit) (x y z : Label k) : flank h j x y z = flank h j y x z := by
  simp only [flank,(parallel k).symm x y]

noncomputable def inside (h i : Bit) (x : Label k) (j : Bit) (y : Label k)
    (l : Bit) (z : Label k) : Point k :=
  if i=j then
    if i=l then pureCol Q h i (.inr x) (.inr y) (.inr z) else flank h l x y z
  else if i=l then flank h j x z y else flank h i y z x

def one (s h i : Bit) (x : Label k) (g j : Bit) (y : Label k) : Point k :=
  if g=h then
    if j=i then pureCol Q h i (.inl s) (.inr x) (.inr y) else hole h i x y s
  else cross h i j x y (.stem s)

noncomputable def three (h i : Bit) (x : Label k) (g j : Bit) (y : Label k)
    (t l : Bit) (z : Label k) : Point k :=
  if g=h then
    if t=h then inside Q h i x j y l z else cross h i l x z (.pt h j y)
  else cross h i j x y (.pt t l z)

noncomputable def complete : Point k → Point k → Point k → Point k
  | .stem a, .stem b, .stem c => pureCol Q 0 0 (.inl a) (.inl b) (.inl c)
  | .stem s, .stem t, .pt h i x | .stem s, .pt h i x, .stem t |
    .pt h i x, .stem s, .stem t => pureCol Q h i (.inl s) (.inl t) (.inr x)
  | .stem s, .pt h i x, .pt g j y | .pt h i x, .stem s, .pt g j y |
    .pt h i x, .pt g j y, .stem s => one Q s h i x g j y
  | .pt h i x, .pt g j y, .pt t l z => three Q h i x g j y t l z

private theorem inside_swap₁ (h i j l : Bit) (x y z : Label k) :
    inside Q h i x j y l z = inside Q h j y i x l z := by
  by_cases hij : i=j
  · subst j
    simp [inside,pureCol,Q.swap₁,flank_comm]
  · have he : i=flip j := eq_flip _ _ hij
    rcases eq_or_ne l i with rfl|hl
    · simp [inside,hij,Ne.symm hij]
    · have hj : l=j := (eq_flip _ _ hl).trans (by simp [he])
      simp [inside,hij,Ne.symm hij,hj]

private theorem inside_swap₂ (h i j l : Bit) (x y z : Label k) :
    inside Q h i x j y l z = inside Q h i x l z j y := by
  by_cases hij : i=j <;> by_cases hil : i=l <;>
    simp_all [inside,pureCol,Q.swap₂,flank_comm]

private theorem one_comm (s h i g j : Bit) (x y : Label k) :
    one Q s h i x g j y = one Q s g j y h i x := by
  by_cases hh : g=h
  · subst g
    rcases eq_or_ne j i with rfl|hi
    · simp [one,pureCol,Q.swap₂]
    · simp [one,eq_flip _ _ hi,hole_swap,Ne.symm (flip_ne _)]
  · simp [one,eq_flip _ _ hh,cross_rev,Ne.symm (flip_ne _)]

private theorem three_swap₁ (h i g j t l : Bit) (x y z : Label k) :
    three Q h i x g j y t l z = three Q g j y h i x t l z := by
  rcases eq_or_ne g h with rfl|hg
  · simp [three,inside_swap₁,cross_face]
  · simp [three,eq_flip _ _ hg,cross_rev,Ne.symm (flip_ne _)]

private theorem three_swap₂ (h i g j t l : Bit) (x y z : Label k) :
    three Q h i x g j y t l z = three Q h i x t l z g j y := by
  by_cases hg : g=h
  · subst g
    by_cases ht : t=h
    · subst t; simp [three,inside_swap₂]
    · simp [three,ht]
  · by_cases ht : t=h
    · subst t; simp [three,hg]
    · simp [three,eq_flip _ _ hg,eq_flip _ _ ht,cross_face_other]

theorem complete_swap₁ (a b c : Point k) : complete Q a b c = complete Q b a c := by
  cases a <;> cases b <;> cases c <;> simp only [complete,pureCol,Q.swap₁,one_comm,three_swap₁]

theorem complete_swap₂ (a b c : Point k) : complete Q a b c = complete Q a c b := by
  cases a <;> cases b <;> cases c <;> simp only [complete,pureCol,Q.swap₁,Q.swap₂,one_comm,three_swap₂]

theorem complete_put (h i : Bit) (a b c : Bit ⊕ Label k) :
    complete Q (put h i a) (put h i b) (put h i c) = put h i (Q.complete a b c) := by
  rcases a with s|x <;> rcases b with t|y <;> rcases c with u|z
  · have hp : ∀ s t u : Bit, s=t ∨ s=u ∨ t=u := by decide +kernel
    rcases hp s t u with rfl|rfl|rfl
    · simp [put,complete,pureCol,Q.repeated]
    · simp only [put,complete,pureCol,Q.swap₂ _ (.inl t) (.inl s),Q.repeated]
    · simp only [put,complete,pureCol,Q.swap₁ (.inl s) (.inl t),Q.swap₂ _ (.inl s) (.inl t),Q.repeated]
  all_goals simp only [put,complete,one,three,inside,pureCol,↓reduceIte]
  all_goals (congr 1; grind only [= Q.swap₁,= Q.swap₂])

theorem complete_cross (h i j : Bit) (x z : Label k) (a : Point k) :
    complete Q (.pt h i x) (.pt (flip h) j z) a = cross h i j x z a := by
  cases a <;> simp [complete,one,three]

theorem complete_repeated (a b : Point k) : complete Q a a b = b := by
  cases a with
  | stem s =>
    cases b with
    | stem t => exact (complete_put Q 0 0 (.inl s) (.inl s) (.inl t)).trans (congrArg _ (Q.repeated ..))
    | pt h i y => exact (complete_put Q h i (.inl s) (.inl s) (.inr y)).trans (congrArg _ (Q.repeated ..))
  | pt h i x =>
    cases b with
    | stem s => exact (complete_put Q h i (.inr x) (.inr x) (.inl s)).trans (congrArg _ (Q.repeated ..))
    | pt g j y =>
      by_cases hg : g=h
      · subst g
        by_cases hj : j=i
        · subst j
          exact (complete_put Q h i (.inr x) (.inr x) (.inr y)).trans (congrArg _ (Q.repeated ..))
        · have he : (parallel k).mate ((parallel k).row x x) y = y := by
            rw [parallel_diag,← parallel_diag k y,(parallel k).mate_colour]
          simp [complete,three,inside,Ne.symm hj,flank,he]
      · simp [complete,three,eq_flip _ _ hg,cross]

#print axioms complete_put
#print axioms complete_repeated

end Erdos722.Fourfold
