import Erdos722FourfoldColours

/-!
# Crossing pairs in the four-column quadruple construction

Fix one point in each half. Points in the other column of the first half
are matched bijectively to the column of the second point. The mate that
would equal this second point is replaced by one stem point. Reversing
the halves uses the other stem point.
-/

namespace Erdos722.Fourfold

inductive Point (k : ℕ) where
  | stem (s : Bit)
  | pt (h i : Bit) (x : Label k)
  deriving DecidableEq, Fintype

abbrev flip (i : Bit) : Bit := 1+i

@[simp] theorem flip_flip : ∀ i : Bit, flip (flip i) = i := by decide +kernel
@[simp] theorem flip_ne : ∀ i : Bit, flip i ≠ i := by decide +kernel
theorem eq_flip : ∀ i j : Bit, i ≠ j → i = flip j := by decide +kernel

variable {k : ℕ}

/-- The column and the two label bits select a perfect or deficient
matching. The reduced coordinates select its index. -/
def tag (j : Bit) (x y : Label k) : Label k := (x.1+y.1+j,x.2+y.2)

def untag (j : Bit) (x t : Label k) : Label k := (t.1-j-x.1,t.2-x.2)

theorem tag_comm (j : Bit) (x y : Label k) : tag j x y = tag j y x := by
  simp only [tag,add_comm x.1 y.1,add_comm x.2 y.2]

@[simp] theorem tag_untag (j : Bit) (x t : Label k) : tag j x (untag j x t) = t := by
  ext <;> simp only [tag,untag] <;> abel

@[simp] theorem untag_tag (j : Bit) (x y : Label k) : untag j x (tag j x y) = y := by
  ext <;> simp only [tag,untag] <;> abel

def stamp (h i j : Bit) (x z : Label k) : Bit := h+x.1+z.1+i*j

theorem stamp_rev (h i j : Bit) (x z : Label k) :
    stamp (flip h) j i z x = flip (stamp h i j x z) := by
  have hbit : ∀ h i j a b : Bit, flip h+b+a+j*i = flip (h+a+b+i*j) := by decide +kernel
  exact hbit ..

theorem stamp_hole (h i j : Bit) (x y z : Label k) (he : tag j x y = (0,z.2)) :
    stamp h (flip i) j y z = stamp h i j x z := by
  have hh : x.1+y.1+j = 0 := congrArg Prod.fst he
  have aux : ∀ h i j a b d : Bit, a+b+j=0 → h+b+d+flip i*j=h+a+d+i*j := by decide +kernel
  exact aux _ _ _ _ _ _ hh

def wing (h i j : Bit) (x z y : Label k) : Point k :=
  let w := (crossing k).mate (tag j x y) z
  if w=z then .stem (stamp h i j x z) else .pt (flip h) j w

def back (h i j : Bit) (x z w : Label k) : Point k :=
  .pt h (flip i) (untag j x ((crossing k).row z w))

/-- For a fixed pair in opposite halves, pair up all possible third points. -/
def cross (h i j : Bit) (x z : Label k) : Point k → Point k
  | .stem s =>
    if s=stamp h i j x z then back h i j x z z else back (flip h) j i z x x
  | .pt g l y =>
    if g=h then
      if l=i then
        if y=x then .pt (flip h) j z else back (flip h) j i z x y
      else wing h i j x z y
    else
      if l=j then
        if y=z then .pt h i x else back h i j x z y
      else wing (flip h) j i z x y

theorem cross_rev (h i j : Bit) (x z : Label k) (a : Point k) :
    cross (flip h) j i z x a = cross h i j x z a := by
  cases a with
  | stem s =>
    by_cases hs : s=stamp h i j x z
    · simp [cross,hs,stamp_rev,Ne.symm (flip_ne _)]
    · simp [cross,stamp_rev,eq_flip _ _ hs]
  | pt g l y =>
    by_cases hg : g=h
    · simp [cross,hg,Ne.symm (flip_ne _)]
    · simp [cross,eq_flip _ _ hg]

theorem cross_wing (h i j : Bit) (x z y : Label k) :
    cross h i j x z (wing h i j x z y) = .pt h (flip i) y := by
  unfold wing
  dsimp only
  split <;> rename_i he
  · have ht : (crossing k).row z z = tag j x y := by
      simpa only [he] using (crossing k).colour_mate (tag j x y) z
    simp [cross,back,ht]
  · simp [cross,he,back]

theorem cross_back (h i j : Bit) (x z w : Label k) :
    cross h i j x z (back h i j x z w) =
      (if w=z then .stem (stamp h i j x z) else .pt (flip h) j w) := by
  simp [cross,back,wing]

theorem cross_involutive (h i j : Bit) (x z : Label k) : Function.Involutive (cross h i j x z) := by
  intro a
  cases a with
  | stem s =>
    by_cases hs : s=stamp h i j x z
    · rw [show cross h i j x z (.stem s) = back h i j x z z by simp [cross,hs],cross_back,if_pos rfl,hs]
    · rw [show cross h i j x z (.stem s) = back (flip h) j i z x x by simp [cross,hs],
          ← cross_rev,cross_back,if_pos rfl,stamp_rev,← eq_flip _ _ hs]
  | pt g l y =>
    by_cases hg : g=h
    · subst g
      by_cases hl : l=i
      · subst l
        by_cases hy : y=x
        · simp [cross,hy]
        · rw [show cross h i j x z (.pt h i y) = back (flip h) j i z x y by simp [cross,hy],
              ← cross_rev,cross_back,if_neg hy,flip_flip]
      · rw [show cross h i j x z (.pt h l y) = wing h i j x z y by simp [cross,hl],
            cross_wing,← eq_flip _ _ hl]
    · have hg' := eq_flip _ _ hg
      subst g
      by_cases hl : l=j
      · subst l
        by_cases hy : y=z
        · simp [cross,hy]
        · rw [show cross h i j x z (.pt (flip h) j y) = back h i j x z y by simp [cross,hy],
              cross_back,if_neg hy]
      · rw [show cross h i j x z (.pt (flip h) l y) = wing (flip h) j i z x y by simp [cross,hl],
            ← cross_rev,cross_wing,← eq_flip _ _ hl]

/-- The opposite column and label for a specified stem. -/
def hole (h i : Bit) (x y : Label k) (s : Bit) : Point k :=
  let j := x.1+y.1
  .pt (flip h) j (s-h-x.1-i*j,x.2+y.2)

theorem hole_characterization (h i j : Bit) (x y z : Label k) (s : Bit) :
    hole h i x y s = .pt (flip h) j z ↔
      tag j x y = (0,z.2) ∧ stamp h i j x z = s := by
  rcases x with ⟨a,u⟩
  rcases y with ⟨b,v⟩
  rcases z with ⟨d,w⟩
  have hb : ∀ a b j : Bit, a+b=j ↔ a+b+j=0 := by decide +kernel
  have hd : ∀ h i j a d s : Bit, s-h-a-i*j=d ↔ h+a+d+i*j=s := by decide +kernel
  simp only [hole,tag,stamp,Point.pt.injEq,true_and,Prod.mk.injEq]
  constructor
  · rintro ⟨rfl,e,g⟩
    exact ⟨⟨(hb ..).mp rfl,g⟩,(hd ..).mp e⟩
  · rintro ⟨⟨p,g⟩,e⟩
    obtain rfl := (hb ..).mpr p
    exact ⟨rfl,(hd ..).mpr e,g⟩

theorem hole_swap (h i : Bit) (x y : Label k) (s : Bit) :
    hole h (flip i) y x s = hole h i x y s := by
  generalize he : hole h i x y s = w
  cases w with
  | stem t => simp [hole] at he
  | pt g j z =>
    obtain rfl : flip h = g := (Point.pt.inj he).1
    obtain ⟨ht,hs⟩ := (hole_characterization ..).mp he
    exact (hole_characterization ..).mpr ⟨(tag_comm ..).trans ht,(stamp_hole _ _ _ _ _ _ ht).trans hs⟩

theorem wing_stem (h i j : Bit) (x z y : Label k) (s : Bit) :
    wing h i j x z y = .stem s ↔ hole h i x y s = .pt (flip h) j z := by
  rw [hole_characterization]
  have eqv : (crossing k).mate (tag j x y) z = z ↔ tag j x y = (0,z.2) := by
    rw [← crossing_diag]
    exact ((crossing k).row z).symm_apply_eq
  simp only [wing]
  split <;> rename_i he
  · simp [eqv.mp he]
  · simp [show tag j x y ≠ (0,z.2) from fun ht => he (eqv.mpr ht)]

theorem cross_face (h i j l : Bit) (x z y : Label k) :
    cross h i j x z (.pt h l y) = cross h l j y z (.pt h i x) := by
  by_cases hl : l=i
  · subst l
    by_cases hy : y=x
    · subst y; rfl
    · simp [cross,hy,Ne.symm hy,back,(crossing k).symm x y]
  · rw [eq_flip _ _ hl]
    rw [show cross h i j x z (.pt h (flip i) y) = wing h i j x z y by simp [cross],
        show cross h (flip i) j y z (.pt h i x) = wing h (flip i) j y z x by simp [cross,Ne.symm (flip_ne _)] ]
    simp only [wing,tag_comm j y x]
    split <;> rename_i he
    · have hw := (crossing k).colour_mate (tag j x y) z
      rw [he,crossing_diag] at hw
      rw [stamp_hole _ _ _ _ _ _ hw.symm]
    · rfl

theorem cross_face_other (h i j l : Bit) (x z y : Label k) :
    cross h i j x z (.pt (flip h) l y) = cross h i l x y (.pt (flip h) j z) := by
  rw [← cross_rev,← cross_rev h i l,cross_face]

#print axioms cross_involutive

end Erdos722.Fourfold
