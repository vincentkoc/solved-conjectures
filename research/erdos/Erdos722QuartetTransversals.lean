import Erdos722QuartetCovers

/-!
# Truncated transversal designs

Evaluate affine-linear functions in several full columns; a further column
records their slopes and may be truncated to any subset. Unit differences
of evaluation points suffice over a commutative ring.
-/

namespace Erdos722.Quartet
open Finset

namespace Transversal

variable {a : ℕ} {R L : Type*} [CommRing R] [Fintype L]

abbrev Point (a : ℕ) (R L : Type*) := (Fin a × R) ⊕ L

def column : Point a R L → Option (Fin a)
  | .inl (i,_) => some i
  | .inr _ => none

private def evalGraph (c : Fin a → R) (p : R × R) : Fin a ↪ (Fin a × R) :=
  ⟨fun i => (i,p.1*c i + p.2),fun _ _ h => congrArg Prod.fst h⟩

private noncomputable def last (e : L ↪ R) (m : R) : Finset L := by
  classical exact univ.filter (fun x => e x = m)

noncomputable def line (c : Fin a → R) (e : L ↪ R) (p : R × R) :
    Finset (Point a R L) := (univ.map (evalGraph c p)).disjSum (last e p.1)

@[simp] private theorem mem_left (c : Fin a → R) (e : L ↪ R) (p : R × R) (i : Fin a) (x : R) :
    Sum.inl (i,x) ∈ line c e p ↔ p.1*c i + p.2 = x := by
  rw [line,inl_mem_disjSum,mem_map]
  change (∃ j ∈ univ, (j,p.1*c j+p.2) = (i,x)) ↔ _
  simp

@[simp] private theorem mem_right (c : Fin a → R) (e : L ↪ R) (p : R × R) (l : L) :
    Sum.inr l ∈ line c e p ↔ e l = p.1 := by classical simp [line,last]

private theorem two_values (c : Fin a → R) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    {i j : Fin a} (hij : i ≠ j) (x y : R) :
    ∃! p : R × R, p.1*c i + p.2 = x ∧ p.1*c j + p.2 = y := by
  obtain ⟨u,hu⟩ := hc i j hij
  obtain ⟨m,hm,unique⟩ := (u.mulRight.bijective.existsUnique (x-y))
  change m * (u : R) = x-y at hm
  rw [hu,mul_sub] at hm
  refine ⟨(m,x-m*c i),⟨by ring,by dsimp; linear_combination -hm⟩,?_⟩
  rintro ⟨n,b⟩ ⟨h1,h2⟩
  change n*c i+b=x at h1
  change n*c j+b=y at h2
  have hn : n = m := unique n (by change n*(u:R)=x-y; rw [hu,mul_sub]; linear_combination h1-h2)
  subst n
  congr 1
  linear_combination h1

omit [Fintype L] in
private theorem slope_value (c : Fin a → R) (e : L ↪ R) (i : Fin a) (x : R) (l : L) :
    ∃! p : R × R, p.1*c i + p.2 = x ∧ e l = p.1 := by
  refine ⟨(e l,x-e l*c i),⟨by ring,rfl⟩,?_⟩
  rintro ⟨m,b⟩ ⟨hx,hm⟩
  change e l = m at hm
  subst m
  congr 1
  change e l*c i+b=x at hx
  linear_combination hx

private theorem unique_line (c : Fin a → R) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (e : L ↪ R) (x y : Point a R L) (h : column x ≠ column y) :
    ∃! p, x ∈ line c e p ∧ y ∈ line c e p := by
  rcases x with ⟨i,x⟩ | l <;> rcases y with ⟨j,y⟩ | l'
  · simpa only [mem_left] using two_values c hc (fun he => h (congrArg some he)) x y
  · simpa only [mem_left,mem_right] using slope_value c e i x l'
  · simpa only [mem_left,mem_right,and_comm] using slope_value c e j y l
  · exact (h rfl).elim

private theorem sound_line (c : Fin a → R) (e : L ↪ R) (p : R × R)
    (x : Point a R L) (hx : x ∈ line c e p) (y : Point a R L) (hy : y ∈ line c e p)
    (hne : x ≠ y) : column x ≠ column y := by
  rcases x with ⟨i,x⟩ | l <;> rcases y with ⟨j,y⟩ | l' <;> simp_all [column]
  · rintro rfl
    exact hne rfl (hx.symm.trans hy)
  · exact hne (e.injective (hx.trans hy.symm))

private theorem card_line (c : Fin a → R) (e : L ↪ R) (p : R × R) :
    (line c e p).card = a + (last e p.1).card := by simp [line]

omit [CommRing R] in
private theorem card_last (e : L ↪ R) (m : R) : (last e m).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro x hx y hy
  simp only [last,mem_filter,mem_univ,true_and] at hx hy
  exact e.injective (hx.trans hy.symm)

noncomputable def truncated (c : Fin a → R) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j))
    (e : L ↪ R) : Cover (Point a R L) (fun x y => column x ≠ column y)
      (fun n => n = a ∨ n = a+1) :=
  Cover.ofLines (line c e) (by intro p; rw [card_line]; have := card_last e p.1; omega)
    (sound_line c e) (fun x y _ => unique_line c hc e x y)

noncomputable def full [Fintype R] (c : Fin a → R) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) :
    Cover (Point a R R) (fun x y => column x ≠ column y) (· = a+1) := by
  classical
  let e := Function.Embedding.refl R
  apply Cover.ofLines (line c e) _ (sound_line c e) (fun x y _ => unique_line c hc e x y)
  intro p
  rw [card_line]
  have : last e p.1 = {p.1} := by ext x; simp [last,e]
  simp [this]


def finiteFiber (i : Fin a) : R ≃ {x : Point a R L // column x = some i} where
  toFun x := ⟨.inl (i,x),rfl⟩
  invFun x := match x with | ⟨.inl (_,r),_⟩ => r
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨j,r⟩ | l,h⟩
    · change some j = some i at h
      cases Option.some.inj h
      rfl
    · contradiction

def lastFiber : L ≃ {x : Point a R L // column x = none} where
  toFun l := ⟨.inr l,rfl⟩
  invFun x := match x with | ⟨.inr l,_⟩ => l
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨j,r⟩ | l,h⟩ <;> first | rfl | contradiction

#print axioms truncated
#print axioms full

end Transversal
end Erdos722.Quartet
