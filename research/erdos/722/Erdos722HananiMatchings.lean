import Erdos722HananiSlots

/-!
# A uniform matching decomposition of Hanani's residual pairs

Reserve one odd translation between the two parity layers. Reflect each
layer in the sum of its two reduced coordinates. Whenever a reflection
fixes a coordinate, switch layers along the reserved edge.
-/

namespace Erdos722.HananiMatchings
open ThreeColumn HananiSlots

section Double
variable {E : Type*} [AddCommGroup E] [DecidableEq E]

private def aligned (x y : Bool × E) : Prop := x.1 = y.1 ∨ x.2 = y.2

private def reflect (c : E) (x : Bool × E) : Bool × E :=
  (if c-x.2 = x.2 then !x.1 else x.1,c-x.2)

private theorem reflect_inv (c : E) : Function.Involutive (reflect c) := by
  rintro ⟨p,x⟩
  by_cases he : c-x=x
  · simp [reflect, he]
  · have h : c-(c-x)=x := by abel
    simp [reflect,h,he,Ne.symm he]

private theorem reflect_iff (c : E) (x y : Bool × E) :
    reflect c x = y ↔ c = x.2+y.2 ∧ x ≠ y ∧ aligned x y := by
  rcases x with ⟨p,x⟩
  rcases y with ⟨q,y⟩
  cases p <;> cases q <;>
    by_cases he : c-x=x <;> simp_all [reflect,aligned,sub_eq_iff_eq_add,add_comm] <;> grind

private def lane (c : Option E) (x : Bool × E) := c.elim x (fun a => reflect a x)

private theorem lane_inv (c : Option E) : Function.Involutive (lane c) := by
  cases c with
  | none => exact fun _ => rfl
  | some c => exact reflect_inv c

private theorem lane_hits (x y : Bool × E) : aligned x y ↔ ∃! c, lane c x = y := by
  constructor
  · intro h
    by_cases he : x=y
    · subst y
      refine ⟨none,rfl,?_⟩
      rintro (_|a) ha
      · rfl
      · exact (((reflect_iff a x x).mp ha).2.1 rfl).elim
    · refine ⟨some (x.2+y.2),(reflect_iff ..).mpr ⟨rfl,he,h⟩,?_⟩
      rintro (_|a) ha
      · exact (he ha).elim
      · exact congrArg some ((reflect_iff ..).mp ha).1
  · rintro ⟨(_|c),hc,_⟩
    · change x=y at hc
      exact Or.inl (congrArg Prod.fst hc)
    · exact ((reflect_iff ..).mp hc).2.2

private theorem lane_aligned (c : Option E) (x : Bool × E) : aligned x (lane c x) := by
  cases c with
  | none => exact Or.inl rfl
  | some c => exact ((reflect_iff c x _).mp rfl).2.2

end Double

variable {r : ℕ}

private abbrev Layer (r : ℕ) := (parity r).toAddMonoidHom.ker

private theorem odd_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide +kernel

private def coord (b : Labels r) (hb : parity r b = 1) : Labels r ≃ Bool × Layer r where
  toFun x := if hx : parity r x = 0 then (false,⟨x,hx⟩) else
    (true,⟨x-b, by change parity r (x-b) = 0; rw [map_sub,odd_of_ne_zero _ hx,hb,sub_self]⟩)
  invFun p := if p.1 then p.2.val+b else p.2.val
  left_inv x := by
    by_cases he : parity r x = 0 <;> simp [he]
  right_inv := by
    rintro ⟨p,⟨u,hu⟩⟩
    change parity r u = 0 at hu
    cases p <;> simp [hu,hb]

private theorem coord_bit (b : Labels r) (hb : parity r b = 1) (x : Labels r) :
    (coord b hb x).1 = decide (parity r x ≠ 0) := by
  by_cases he : parity r x = 0 <;> simp [coord,he]

private def jump (b x : Labels r) : Labels r := if parity r x = 0 then x+b else x-b

private theorem jump_inv {b : Labels r} (hb : parity r b = 1) : Function.Involutive (jump b) := by
  intro x
  by_cases he : parity r x = 0
  · simp [jump,he,hb]
  · simp [jump,odd_of_ne_zero _ he,hb]

private theorem jump_bit {b : Labels r} (hb : parity r b = 1) (x : Labels r) :
    parity r (jump b x) ≠ parity r x := by
  by_cases he : parity r x = 0 <;> simp [jump,he,hb,odd_of_ne_zero _]

private theorem coord_jump (b : Labels r) (hb : parity r b = 1) (x : Labels r) :
    coord b hb (jump b x) = (!(coord b hb x).1,(coord b hb x).2) := by
  by_cases he : parity r x = 0
  · simp [coord,jump,he,hb]
  · simp [coord,jump,odd_of_ne_zero _ he,hb]

private theorem coord_aligned (b : Labels r) (hb : parity r b = 1) (x y : Labels r) :
    aligned (coord b hb x) (coord b hb y) ↔ parity r x = parity r y ∨ y = jump b x := by
  have bits : (coord b hb x).1 = (coord b hb y).1 ↔ parity r x = parity r y := by
    rw [coord_bit,coord_bit]
    generalize parity r x = p
    generalize parity r y = q
    decide +revert +kernel
  constructor
  · rintro (he|he)
    · exact Or.inl (bits.mp he)
    · by_cases h : (coord b hb x).1 = (coord b hb y).1
      · exact Or.inl (bits.mp h)
      · right
        apply (coord b hb).injective
        rw [coord_jump]
        have hh : ∀ p q : Bool, p ≠ q → q = !p := by decide
        exact Prod.ext (hh _ _ h) he.symm
  · rintro (h|rfl)
    · exact Or.inl (bits.mpr h)
    · exact Or.inr (congrArg Prod.snd (coord_jump b hb x)).symm

private theorem sum_bij {X Y Z : Type*} (f : X → Z) (g : Y → Z)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (apart : ∀ x y, f x ≠ g y) (cover : ∀ z, (∃ x, f x = z) ∨ (∃ y, g y = z)) :
    Function.Bijective (Sum.elim f g) := by
  constructor
  · rintro (x|x) (y|y) he
    · exact congrArg Sum.inl (hf he)
    · exact (apart x y he).elim
    · exact (apart y x he.symm).elim
    · exact congrArg Sum.inr (hg he)
  · intro z
    rcases cover z with ⟨x,hx⟩|⟨y,hy⟩
    · exact ⟨.inl x,hx⟩
    · exact ⟨.inr y,hy⟩

private theorem jump_inj (x : Labels r) : Function.Injective (fun u => jump u x) := by
  intro u v he
  by_cases h : parity r x = 0 <;> simpa [jump,h] using he

private def crossOffset (x y : Labels r) := if parity r x = 0 then y-x else x-y

private theorem reach (x y : Labels r) : jump (crossOffset x y) x = y := by
  by_cases h : parity r x = 0 <;> simp [crossOffset,jump,h]

private theorem cross_odd {x y : Labels r} (h : parity r x ≠ parity r y) :
    parity r (crossOffset x y) = 1 := by
  by_cases e : parity r x = 0
  · have hy : parity r y ≠ 0 := fun he => h (e.trans he.symm)
    simp [crossOffset,e,odd_of_ne_zero _ hy]
  · have hx := odd_of_ne_zero _ e
    have hy : parity r y = 0 := by
      by_contra g
      exact h (hx.trans (odd_of_ne_zero _ g).symm)
    simp [crossOffset,hx,hy]

private abbrev Cross (b : Labels r) := {u : Labels r // parity r u = 1 ∧ u ≠ b}

private def along (b : Labels r) (hb : parity r b = 1) (c : Option (Layer r)) (x : Labels r) :=
  (coord b hb).symm (lane c (coord b hb x))

private theorem along_inv (b : Labels r) (hb : parity r b = 1) (c : Option (Layer r)) :
    Function.Involutive (along b hb c) := by
  intro x
  simp [along,lane_inv c _]

private theorem cross_layer (b : Labels r) (hb : parity r b = 1) (x : Labels r) :
    Function.Bijective (Sum.elim (fun c : Cross b => jump c.val x) (fun c => along b hb c x)) := by
  apply sum_bij
  · exact fun _ _ he => Subtype.ext (jump_inj x he)
  · intro c e he
    have hu := ((lane_hits (coord b hb x) (lane c (coord b hb x))).mp (lane_aligned ..))
    apply hu.unique (show lane c (coord b hb x) = lane c (coord b hb x) from rfl)
    exact (coord b hb).symm.injective he.symm
  · intro u c he
    have ha : aligned (coord b hb x) (coord b hb (along b hb c x)) := by simp [along,lane_aligned]
    rw [← he] at ha
    rcases (coord_aligned b hb x _).mp ha with h|h
    · exact jump_bit u.property.1 x h.symm
    · exact u.property.2 (jump_inj x h)
  · intro y
    by_cases ha : aligned (coord b hb x) (coord b hb y)
    · right
      obtain ⟨c,hc,_⟩ := (lane_hits ..).mp ha
      exact ⟨c,(coord b hb).symm_apply_eq.mpr hc⟩
    · rw [coord_aligned,not_or] at ha
      have hne : crossOffset x y ≠ b := fun he => ha.2 (he ▸ (reach x y).symm)
      exact Or.inl ⟨⟨crossOffset x y,cross_odd ha.1,hne⟩,reach x y⟩

section Colors

variable {d : ℕ} (hr : 2*d+1 ≤ r)
private abbrev baseShift := @shift d r (by omega)
private abbrev bridge := reserved d r
private abbrev Free := {u : Cross (bridge (d := d) (r := r)) // ∀ a, baseShift hr a ≠ u.val}
private abbrev Colors := Free hr ⊕ Option (Layer r)

private def oriented (x : Labels r) : Dir d ≃ Dir d :=
  if parity r x = 0 then Equiv.refl _ else Equiv.sumComm _ _

private def shortCross (x : Labels r) (a : Dir d) : Cross (bridge (d := d) (r := r)) :=
  ⟨baseShift hr (oriented x a),parity_shift ..,shift_ne_reserved hr _⟩

private theorem jump_short (x : Labels r) (a : Dir d) :
    jump (shortCross hr x a).val x = x + baseShift hr a := by
  by_cases he : parity r x = 0
  · simp [jump,shortCross,oriented,he]
  · have hf : oriented x a = flip a := by simp [oriented,he,HananiSlots.flip]
    simp [jump,shortCross,he,hf,baseShift,shift_flip]

private theorem odd_colors (x : Labels r) : Function.Bijective
    (Sum.elim (shortCross hr x) (Subtype.val : Free hr → Cross (bridge (d := d) (r := r)))) := by
  apply sum_bij
  · exact fun _ _ he => (oriented x).injective ((baseShift hr).injective (congrArg Subtype.val he))
  · exact Subtype.val_injective
  · exact fun a u he => u.property (oriented x a) (congrArg Subtype.val he)
  · intro u
    by_cases he : ∃ a, baseShift hr a = u.val
    · obtain ⟨a,ha⟩ := he
      exact Or.inl ⟨(oriented x).symm a,Subtype.ext (by simpa [shortCross] using ha)⟩
    · exact Or.inr ⟨⟨u,fun a ha => he ⟨a,ha⟩⟩,rfl⟩

private def partner : Colors hr → Labels r → Labels r
  | .inl f => jump f.val.val
  | .inr c => along (bridge (d := d)) (parity_reserved d r) c

private theorem partner_inv (c : Colors hr) : Function.Involutive (partner hr c) := by
  cases c with
  | inl f => exact jump_inv f.val.property.1
  | inr c => exact along_inv _ _ c

private theorem neighbors (x : Labels r) :
    Function.Bijective (Scheme.neighbor (baseShift hr) (partner hr) x) := by
  let oddColors := Equiv.ofBijective _ (odd_colors hr x)
  let allColors := Equiv.ofBijective _ (cross_layer _ (parity_reserved d r) x)
  let e := ((Equiv.sumAssoc (Dir d) (Free hr) (Option (Layer r))).symm.trans
    (Equiv.sumCongr oddColors (Equiv.refl _))).trans allColors
  have he : Scheme.neighbor (baseShift hr) (partner hr) x = e := by
    funext v
    rcases v with a|(f|c)
    · exact (jump_short hr x a).symm
    · rfl
    · rfl
  rw [he]
  exact e.bijective

/-- The shared-stem scheme for a cyclic column of order twice its layer size. -/
noncomputable def scheme {h : ℕ} [NeZero (2*r)] (hsize : h+6*d=2*r) :
    Scheme (Fin h) (Labels r) (Colors hr) :=
  Scheme.ofCoordinates (slot hsize) (baseShift hr) (partner hr) (neighbors hr) flip
    (shift_flip _) (slot_flip hsize _) (partner_inv hr) (.inr none)
    (fun x => (coord _ _).symm_apply_apply x)

#print axioms scheme

end Colors

end Erdos722.HananiMatchings
