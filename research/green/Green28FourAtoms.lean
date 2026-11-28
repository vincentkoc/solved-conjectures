import Mathlib

/-! Singleton representations in ordered four-by-four sum tables. -/

namespace Green28FourAtoms

def Alone {n m : ℕ} (a : Fin n → ℤ) (b : Fin m → ℤ) (i : Fin n) (j : Fin m) : Prop :=
  ∀ k l, a i+b j = a k+b l → i=k ∧ j=l

private theorem all4 {p : Fin 4 → Prop} :
    (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 ∧ p 3 :=
  ⟨fun h => ⟨h 0,h 1,h 2,h 3⟩, fun h i => by fin_cases i <;> tauto⟩

private theorem some4 {p : Fin 4 → Prop} :
    (∃ i, p i) ↔ p 0 ∨ p 1 ∨ p 2 ∨ p 3 := by
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i <;> tauto
  · rintro (h|h|h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · exact ⟨3,h⟩

private def cross {m n : ℕ} (i : Fin m) (j : Fin n) (k : Fin m) (l : Fin n) : Prop :=
  (k < i ∧ j < l) ∨ (i < k ∧ l < j)

private theorem pattern {m n : ℕ} {a : Fin m → ℤ} {b : Fin n → ℤ}
    (ha : StrictMono a) (hb : StrictMono b) (u : Fin m → Prop) (v : Fin n → Prop)
    (rect : ∀ i j, Alone a b i j ↔ u i ∧ v j) (i : Fin m) (j : Fin n) :
    ((u i ∧ v j) → ∀ k l, cross i j k l → a i+b j ≠ a k+b l) ∧
    (¬(u i ∧ v j) → ∃ k l, cross i j k l ∧ ¬(u k ∧ v l) ∧ a i+b j = a k+b l) := by
  classical
  constructor
  · intro unit k l hc eq
    obtain ⟨rfl,rfl⟩ := (rect i j).mpr unit k l eq
    simp [cross] at hc
  · intro bad
    have coll : ¬ Alone a b i j := fun h => bad ((rect i j).mp h)
    unfold Alone at coll
    push Not at coll
    obtain ⟨k,l,eq,ne⟩ := coll
    refine ⟨k,l,?_,?_,eq⟩
    · rcases lt_trichotomy k i with ki|ki|ki
      · left; refine ⟨ki,?_⟩
        apply hb.lt_iff_lt.mp; have := ha ki; omega
      · subst k; have := hb.injective (add_left_cancel eq); tauto
      · right; refine ⟨ki,?_⟩
        apply hb.lt_iff_lt.mp; have := ha ki; omega
    · intro u'
      obtain ⟨e,f⟩ := (rect k l).mpr u' i j eq.symm
      tauto

set_option maxHeartbeats 1200000 in
theorem four_grid (a b : Fin 4 → ℤ) (ha : StrictMono a) (hb : StrictMono b)
    (u v : Fin 4 → Prop) (rect : ∀ i j, Alone a b i j ↔ u i ∧ v j)
    (u0 : u 0) (u3 : u 3) (v0 : v 0) (v3 : v 3) :
    (∀ i, u i) ∨ (∀ j, v j) := by
  classical
  have h := pattern ha hb u v rect
  have a01 := ha (by decide : (0 : Fin 4)<1)
  have a12 := ha (by decide : (1 : Fin 4)<2)
  have a23 := ha (by decide : (2 : Fin 4)<3)
  have b01 := hb (by decide : (0 : Fin 4)<1)
  have b12 := hb (by decide : (1 : Fin 4)<2)
  have b23 := hb (by decide : (2 : Fin 4)<3)
  by_cases u1 : u 1 <;> by_cases u2 : u 2 <;>
    by_cases v1 : v 1 <;> by_cases v2 : v 2
  all_goals simp [all4,u0,u1,u2,u3,v0,v1,v2,v3]
  all_goals simp +decide [all4,some4,cross,u0,u1,u2,u3,v0,v1,v2,v3] at h
  all_goals omega

private theorem all3 {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 :=
  ⟨fun h => ⟨h 0,h 1,h 2⟩, fun h i => by fin_cases i <;> tauto⟩

private theorem some3 {p : Fin 3 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 ∨ p 2 := by
  constructor
  · rintro ⟨i,hi⟩; fin_cases i <;> tauto
  · rintro (h|h|h)
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩

private theorem endpoints {m : ℕ} (hm : m ≤ 1) (u : Fin (m+1) → Prop)
    (h0 : u 0) (hl : u (Fin.last m)) : ∀ i, u i := by
  intro i
  have hi : i=0 ∨ i=Fin.last m := by
    by_cases z : i.val=0
    · exact Or.inl (Fin.ext (by simpa using z))
    · exact Or.inr (Fin.ext (by simp only [Fin.val_last]; omega))
  rcases hi with rfl|rfl <;> assumption

set_option maxHeartbeats 1200000 in
theorem small_grid {m n : ℕ} (hm : m ≤ 3) (hn : n ≤ 3)
    (a : Fin (m+1) → ℤ) (b : Fin (n+1) → ℤ) (ha : StrictMono a) (hb : StrictMono b)
    (u : Fin (m+1) → Prop) (v : Fin (n+1) → Prop)
    (rect : ∀ i j, Alone a b i j ↔ u i ∧ v j)
    (u0 : u 0) (ul : u (Fin.last m)) (v0 : v 0) (vl : v (Fin.last n)) :
    (∀ i, u i) ∨ (∀ j, v j) := by
  classical
  by_cases ma : m ≤ 1
  · exact Or.inl (endpoints ma _ u0 ul)
  by_cases nb : n ≤ 1
  · exact Or.inr (endpoints nb _ v0 vl)
  have mc : m=2 ∨ m=3 := by omega
  have nc : n=2 ∨ n=3 := by omega
  rcases mc with rfl|rfl <;> rcases nc with rfl|rfl
  case inr.inr => exact four_grid a b ha hb u v rect u0 ul v0 vl
  all_goals
    have h := pattern ha hb u v rect
    have a01 := ha (show 0 < 1 by decide)
    have a12 := ha (show 1 < 2 by decide)
    have b01 := hb (show 0 < 1 by decide)
    have b12 := hb (show 1 < 2 by decide)
    try have a23 := ha (show 2 < 3 by decide)
    try have b23 := hb (show 2 < 3 by decide)
    by_cases u1 : u 1 <;> by_cases u2 : u 2 <;> by_cases v1 : v 1 <;> by_cases v2 : v 2
  all_goals first | contradiction | simp [all3,all4,u0,v0,u1,u2,v1,v2]
  all_goals simp +decide [all3,all4,some3,some4,cross,u0,v0,u1,u2,v1,v2] at h
  all_goals omega

#print axioms four_grid
#print axioms small_grid

end Green28FourAtoms
