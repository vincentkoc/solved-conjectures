import Erdos722FourfoldCompletion

/-!
# The fourfold Steiner quadruple completion rule

Every fixed pair acts by an involution. Pairs in opposite halves use the
crossing construction. For a pair in a single half, two successive
crossing involutions identify the fourth point whenever both other
points lie in the opposite half.
-/

namespace Erdos722.Fourfold
open QuadCompletion Point
variable {k : ℕ} (Q : Rule (Bit ⊕ Label k))

private abbrev Cancels (a b c : Point k) := complete Q a b (complete Q a b c) = c

private theorem cancel_swap {a b c : Point k} (he : Cancels Q a b c) : Cancels Q b a c := by
  simpa only [Cancels,complete_swap₁ Q b a] using he

private theorem cancel_put (h i : Bit) (a b c : Bit ⊕ Label k) : Cancels Q (put h i a) (put h i b) (put h i c) := by
  rw [Cancels,complete_put,complete_put,Q.cancel]

private theorem across_inv (h i j : Bit) (x z : Label k) :
    Function.Involutive (complete Q (.pt h i x) (.pt (flip h) j z)) := by
  intro a
  rw [complete_cross,complete_cross]
  exact cross_involutive h i j x z a

private theorem transfer (h i j l : Bit) (x z w : Label k) (b : Point k)
    (he : complete Q (.pt h i x) b (.pt (flip h) j z) = .pt (flip h) l w) :
    Cancels Q (.pt h i x) b (.pt (flip h) j z) := by
  let a := pt h i x
  let c := pt (flip h) j z
  let d := pt (flip h) l w
  change complete Q a b (complete Q a b c) = c
  change complete Q a b c = d at he
  have h₁ : complete Q a c (complete Q a c b) = b := across_inv Q h i j x z b
  have h₂ : complete Q a d (complete Q a d c) = c := across_inv Q h i l x w c
  rw [complete_swap₂ Q a c b,he,complete_swap₂ Q a c d] at h₁
  rw [h₁] at h₂
  rw [he,complete_swap₂ Q a b d,h₂]

private theorem stem_inside (s h i : Bit) (x y : Label k) :
    complete Q (.pt h i x) (.stem s) (.pt h (flip i) y) = hole h i x y s := by
  simp [complete,one]

private theorem two_stem (s h i : Bit) (x y : Label k) :
    complete Q (.pt h i x) (.pt h (flip i) y) (.stem s) = hole h i x y s := by
  simp [complete,one]

private theorem two_across (h i j : Bit) (x y z : Label k) :
    complete Q (.pt h i x) (.pt h (flip i) y) (.pt (flip h) j z) = wing h i j x z y := by
  simp [complete,three,cross]

private theorem cancel_stem_inside (s h i : Bit) (x y : Label k) :
    Cancels Q (.pt h i x) (.stem s) (.pt h (flip i) y) := by
  generalize he : hole h i x y s = d
  cases d with
  | stem t => simp [hole] at he
  | pt g j z =>
    obtain rfl : flip h = g := (Point.pt.inj he).1
    have hw := (wing_stem h i j x z y s).mpr he
    have hc := cross_wing h i j x z y
    rw [hw] at hc
    rw [Cancels,stem_inside,he,complete_swap₂,complete_cross,hc]

private theorem cancel_two_stem (s h i : Bit) (x y : Label k) :
    Cancels Q (.pt h i x) (.pt h (flip i) y) (.stem s) := by
  generalize he : hole h i x y s = d
  cases d with
  | stem t => simp [hole] at he
  | pt g j z =>
    obtain rfl : flip h = g := (Point.pt.inj he).1
    rw [Cancels,two_stem,he,two_across,(wing_stem ..).mpr he]

private theorem cancel_stem_outside (s h i j : Bit) (x z : Label k) :
    Cancels Q (.pt h i x) (.stem s) (.pt (flip h) j z) := by
  have hc : complete Q (.pt h i x) (.stem s) (.pt (flip h) j z) = cross h i j x z (.stem s) :=
    (complete_swap₂ ..).trans (complete_cross ..)
  by_cases hs : s=stamp h i j x z
  · let y := untag j x ((crossing k).row z z)
    have he : complete Q (.pt h i x) (.stem s) (.pt (flip h) j z) = .pt h (flip i) y := by
      rw [hc]; simp [cross,hs,back,y]
    rw [Cancels,he,stem_inside]
    exact (hole_characterization ..).mpr ⟨(tag_untag ..).trans (crossing_diag ..),hs.symm⟩
  · apply transfer Q h i j (flip j) x z (untag i z ((crossing k).row x x))
    rw [hc]; simp [cross,hs,back]

private theorem cancel_same_across (h i j : Bit) (x y z : Label k) :
    Cancels Q (.pt h i x) (.pt h i y) (.pt (flip h) j z) := by
  by_cases hy : y=x
  · subst y
    rw [Cancels,complete_repeated,complete_repeated]
  · apply transfer Q h i j (flip j) x z (untag i z ((crossing k).row x y))
    simp [complete,three,cross,hy,back]

private theorem cancel_two_across (h i j : Bit) (x y z : Label k) :
    Cancels Q (.pt h i x) (.pt h (flip i) y) (.pt (flip h) j z) := by
  by_cases he : (crossing k).mate (tag j x y) z = z
  · have hw : wing h i j x z y = .stem (stamp h i j x z) := by simp [wing,he]
    rw [Cancels,two_across,hw,two_stem,(wing_stem ..).mp hw]
  · apply transfer Q h i j j x z ((crossing k).mate (tag j x y) z)
    rw [two_across]; simp [wing,he]

private theorem cancel_inside (h i j l : Bit) (x y z : Label k) :
    Cancels Q (.pt h i x) (.pt h j y) (.pt h l z) := by
  by_cases hj : j=i
  · subst j
    by_cases hl : l=i
    · subst l; exact cancel_put Q h i (.inr x) (.inr y) (.inr z)
    · simp [Cancels,complete,three,inside,flank,Ne.symm hl]
  · by_cases hl : l=i
    · subst l; simp [Cancels,complete,three,inside,flank,Ne.symm hj]
    · have he : l=j := (eq_flip _ _ hl).trans (eq_flip _ _ hj).symm
      subst l; simp [Cancels,complete,three,inside,flank,Ne.symm hj]

private theorem cancel_stem (s h i : Bit) (x : Label k) (a : Point k) : Cancels Q (.pt h i x) (.stem s) a := by
  cases a with
  | stem t => exact cancel_put Q h i (.inr x) (.inl s) (.inl t)
  | pt g j z =>
    by_cases hg : g=h
    · subst g
      by_cases hj : j=i
      · subst j; exact cancel_put Q h i (.inr x) (.inl s) (.inr z)
      · rw [eq_flip _ _ hj]; exact cancel_stem_inside Q s h i x z
    · rw [eq_flip _ _ hg]; exact cancel_stem_outside Q s h i j x z

private theorem cancel_same_half (h i j : Bit) (x y : Label k) (a : Point k) :
    Cancels Q (.pt h i x) (.pt h j y) a := by
  cases a with
  | stem s =>
    by_cases hj : j=i
    · subst j; exact cancel_put Q h i (.inr x) (.inr y) (.inl s)
    · rw [eq_flip _ _ hj]; exact cancel_two_stem Q s h i x y
  | pt g l z =>
    by_cases hg : g=h
    · subst g; exact cancel_inside Q h i j l x y z
    · rw [eq_flip _ _ hg]
      by_cases hj : j=i
      · subst j; exact cancel_same_across Q h i l x y z
      · rw [eq_flip _ _ hj]; exact cancel_two_across Q h i l x y z

/-- The quadruple operation supplied by four filled columns on two stems. -/
noncomputable def rule : Rule (Point k) where
  complete := complete Q
  swap₁ := complete_swap₁ Q
  swap₂ := complete_swap₂ Q
  repeated := complete_repeated Q
  cancel := by
    intro a b c
    cases a with
    | stem s =>
      cases b with
      | stem t =>
        cases c with
        | stem u => exact cancel_put Q 0 0 (.inl s) (.inl t) (.inl u)
        | pt h i z => exact cancel_put Q h i (.inl s) (.inl t) (.inr z)
      | pt h i x => exact cancel_swap Q (cancel_stem Q s h i x c)
    | pt h i x =>
      cases b with
      | stem t => exact cancel_stem Q t h i x c
      | pt g j y =>
        by_cases hg : g=h
        · subst g; exact cancel_same_half Q h i j x y c
        · rw [eq_flip _ _ hg]; exact across_inv Q h i j x y c

#print axioms rule

end Erdos722.Fourfold
