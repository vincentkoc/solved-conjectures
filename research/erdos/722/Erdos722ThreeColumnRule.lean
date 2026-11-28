import Erdos722QuadCompletion
import Mathlib.Data.ZMod.Basic

/-!
# A completion rule for Hanani's three-column constructions

The shared points are the stem. A sum of three ordinary labels determines
a stem point or the column and displacement of a fourth ordinary point.
The remaining differences within a column use synchronized perfect matchings.
-/

namespace Erdos722.ThreeColumn

open QuadCompletion

abbrev Col := ZMod 3
abbrev Point (S A : Type*) := S ⊕ (Col × A)

private def other (i j : Col) := -i-j

private theorem other_comm (i j : Col) : other i j = other j i := by unfold other; abel
private theorem other_inv (i j : Col) : other i (other i j) = j := by unfold other; abel
private theorem other_left : ∀ i j : Col, i ≠ j → other i j ≠ i := by decide +kernel
private theorem other_right : ∀ i j : Col, i ≠ j → other i j ≠ j := by decide +kernel
private theorem other_eq : ∀ i j k : Col, i ≠ j → i ≠ k → j ≠ k → other i j = k := by decide +kernel
private theorem exhaust : ∀ i j k t : Col, i ≠ j → i ≠ k → j ≠ k → t = i ∨ t = j ∨ t = k := by decide +kernel

structure Scheme (S A M : Type*) [AddCommGroup A] where
  route : A → S ⊕ (Col × A)
  stemSum : S → A
  pair : Col → A → A → A ⊕ M
  partner : M → A → A
  stem_iff (u s) : route u = .inl s ↔ u = stemSum s
  short_iff (i x y u) : pair i x y = .inl u ↔ route u = .inr (i,y-x)
  reverse (u i d) : route u = .inr (i,d) → route (u+d) = .inr (i,-d)
  match_iff (i x y c) : pair i x y = .inr c ↔ partner c x = y
  invol (c) : Function.Involutive (partner c)
  diagonal (i x) : ∃ c, pair i x x = .inr c ∧ ∀ z, partner c z = z

namespace Scheme

variable {S A M : Type*} [AddCommGroup A] (F : Scheme S A M)

private def pt (i : Col) (x : A) : Point S A := .inr (i,x)

private def across (i : Col) (x : A) (j : Col) (y : A) (k : Col) (z : A) : Point S A :=
  match F.route (x+y+z) with
  | .inl s => .inl s
  | .inr (t,d) => pt t ((if t=i then x else if t=j then y else if t=k then z else 0)+d)

private def withStem (s : S) (i : Col) (x : A) (j : Col) (y : A) : Point S A :=
  pt (other i j) (F.stemSum s-x-y)

private def double (i : Col) (x y : A) (j : Col) (z : A) : Point S A :=
  match F.pair i x y with
  | .inl u => pt (other i j) (u-x-z)
  | .inr c => pt j (F.partner c z)

private theorem withStem_comm (s : S) (i j : Col) (x y : A) :
    F.withStem s i x j y = F.withStem s j y i x := by
  unfold withStem
  rw [other_comm]
  congr 1
  abel

private theorem across_swap₁ {i j k : Col} (hij : i ≠ j) (x y z : A) :
    F.across i x j y k z = F.across j y i x k z := by
  unfold across
  rw [add_comm x y]
  cases F.route (y+x+z) with
  | inl => rfl
  | inr p =>
    obtain ⟨t,d⟩ := p
    by_cases ht : t=i <;> by_cases hu : t=j <;> simp_all

private theorem across_swap₂ {i j k : Col} (hjk : j ≠ k) (x y z : A) :
    F.across i x j y k z = F.across i x k z j y := by
  unfold across
  rw [add_right_comm x y z]
  cases F.route (x+z+y) with
  | inl => rfl
  | inr p =>
    obtain ⟨t,d⟩ := p
    by_cases ht : t=j <;> by_cases hu : t=k <;> simp_all

private theorem double_comm (i j : Col) (x y z : A) :
    F.double i x y j z = F.double i y x j z := by
  unfold double
  cases h : F.pair i x y with
  | inl u =>
    have hr := F.reverse _ _ _ ((F.short_iff ..).mp h)
    rw [show -(y-x) = x-y by abel] at hr
    rw [(F.short_iff ..).mpr hr]
    abel_nf
  | inr c =>
    have hp := (F.match_iff ..).mp h
    have hq : F.partner c y = x := hp ▸ F.invol c x
    rw [(F.match_iff ..).mpr hq]

private theorem double_diag (i j : Col) (x z : A) :
    F.double i x x j z = pt j z := by
  obtain ⟨c,hc,he⟩ := F.diagonal i x
  simp [double,hc,he]

variable (Q : Rule (S ⊕ A))

/-- Embed one filled column, keeping its stem points fixed. -/
def put (i : Col) : S ⊕ A → Point S A
  | .inl s => .inl s
  | .inr x => pt i x

private def pureCol (i : Col) (a b c : S ⊕ A) : Point S A :=
  put i (Q.complete a b c)

private def one (s : S) (i : Col) (x : A) (j : Col) (y : A) : Point S A :=
  if i=j then pureCol Q i (.inl s) (.inr x) (.inr y) else F.withStem s i x j y

private def cols (i : Col) (x : A) (j : Col) (y : A) (k : Col) (z : A) : Point S A :=
  if i=j then
    if i=k then pureCol Q i (.inr x) (.inr y) (.inr z) else F.double i x y k z
  else if i=k then F.double i x z j y
  else if j=k then F.double j y z i x
  else F.across i x j y k z

private def solve : Point S A → Point S A → Point S A → Point S A
  | .inl s, .inl t, .inl u => pureCol Q 0 (.inl s) (.inl t) (.inl u)
  | .inl s, .inl t, .inr (i,x) | .inl s, .inr (i,x), .inl t |
    .inr (i,x), .inl s, .inl t => pureCol Q i (.inl s) (.inl t) (.inr x)
  | .inl s, .inr (i,x), .inr (j,y) | .inr (i,x), .inl s, .inr (j,y) |
    .inr (i,x), .inr (j,y), .inl s => F.one Q s i x j y
  | .inr (i,x), .inr (j,y), .inr (k,z) => F.cols Q i x j y k z

private theorem one_comm (s : S) (i j : Col) (x y : A) :
    F.one Q s i x j y = F.one Q s j y i x := by
  by_cases h : i=j
  · subst j
    simp [one,pureCol,Q.swap₂]
  · simp [one,h,Ne.symm h,withStem_comm]

private theorem cols_swap₁ (i j k : Col) (x y z : A) :
    F.cols Q i x j y k z = F.cols Q j y i x k z := by
  by_cases h : i=j
  · subst j
    by_cases h : i=k <;> simp [cols,h,pureCol,Q.swap₁,double_comm]
  · by_cases hik : i=k
    · subst k
      simp [cols,h,Ne.symm h]
    · by_cases hjk : j=k
      · subst k
        simp [cols,h,Ne.symm h]
      · simp [cols,h,Ne.symm h,hik,hjk,across_swap₁ F h]

private theorem cols_swap₂ (i j k : Col) (x y z : A) :
    F.cols Q i x j y k z = F.cols Q i x k z j y := by
  by_cases h : j=k
  · subst k
    by_cases h : i=j <;> simp [cols,h,pureCol,Q.swap₂,double_comm]
  · by_cases hij : i=j <;> by_cases hik : i=k <;>
      simp_all [cols,Ne.symm h,across_swap₂ F h]

private theorem solve_swap₁ (a b c : Point S A) :
    F.solve Q a b c = F.solve Q b a c := by
  rcases a with a|⟨i,x⟩ <;> rcases b with b|⟨j,y⟩ <;> rcases c with c|⟨k,z⟩ <;>
    simp only [solve,pureCol,Q.swap₁,one_comm,cols_swap₁]

private theorem solve_swap₂ (a b c : Point S A) :
    F.solve Q a b c = F.solve Q a c b := by
  rcases a with a|⟨i,x⟩ <;> rcases b with b|⟨j,y⟩ <;> rcases c with c|⟨k,z⟩ <;>
    simp only [solve,pureCol,Q.swap₁,Q.swap₂,one_comm,cols_swap₂]

/-- Completions of three stem points stay in the stem. -/
def StemClosed : Prop := ∀ s t u : S, ∃ w : S, Q.complete (.inl s) (.inl t) (.inl u) = .inl w

private theorem solve_put (hQ : StemClosed Q) (i : Col) (a b c : S ⊕ A) :
    F.solve Q (put i a) (put i b) (put i c) = put i (Q.complete a b c) := by
  rcases a with s|x <;> rcases b with t|y <;> rcases c with u|z
  · obtain ⟨w,hw⟩ := hQ s t u
    simp [put,solve,pureCol,hw]
  all_goals simp only [put,pt,solve,one,cols,pureCol]
  all_goals congr 1 <;> grind only [= Q.swap₁,= Q.swap₂]

private theorem pure_cancel (hQ : StemClosed Q) (i : Col) (a b c : S ⊕ A) :
    F.solve Q (put i a) (put i b) (F.solve Q (put i a) (put i b) (put i c)) = put i c := by
  rw [F.solve_put Q hQ,F.solve_put Q hQ,Q.cancel]

private theorem cols_same {i j : Col} (h : i ≠ j) (x y z : A) :
    F.solve Q (pt i x) (pt i y) (pt j z) = F.double i x y j z := by simp [pt,solve,cols,h]

private theorem cols_left {i j : Col} (h : i ≠ j) (x y z : A) :
    F.solve Q (pt i x) (pt j y) (pt i z) = F.double i x z j y := by simp [pt,solve,cols,h]

private theorem cols_right {i j : Col} (h : i ≠ j) (x y z : A) :
    F.solve Q (pt i x) (pt j y) (pt j z) = F.double j y z i x := by simp [pt,solve,cols,h]

private theorem cols_diff {i j k : Col} (h : i ≠ j) (g : i ≠ k) (l : j ≠ k) (x y z : A) :
    F.solve Q (pt i x) (pt j y) (pt k z) = F.across i x j y k z := by simp [pt,solve,cols,h,g,l]

private theorem cols_stem {i j : Col} (h : i ≠ j) (s : S) (x y : A) :
    F.solve Q (pt i x) (pt j y) (.inl s) = F.withStem s i x j y := by simp [pt,solve,one,h]

private theorem stem_cols {i j : Col} (h : i ≠ j) (s : S) (x y : A) :
    F.solve Q (.inl s) (pt i x) (pt j y) = F.withStem s i x j y := by simp [pt,solve,one,h]

private theorem cancel_stem_col {i j : Col} (h : i ≠ j) (s : S) (x y : A) :
    F.solve Q (.inl s) (pt i x) (F.solve Q (.inl s) (pt i x) (pt j y)) = pt j y := by
  rw [F.stem_cols Q h,withStem,F.stem_cols Q (other_left i j h).symm,withStem,other_inv]
  congr 1
  abel

private theorem cancel_same {i j : Col} (h : i ≠ j) (x y z : A) :
    F.solve Q (pt i x) (pt i y) (F.solve Q (pt i x) (pt i y) (pt j z)) = pt j z := by
  rw [F.cols_same Q h,double]
  cases he : F.pair i x y with
  | inl u =>
    rw [F.cols_same Q (other_left i j h).symm,double,he]
    dsimp only
    rw [other_inv]
    congr 1
    abel
  | inr c =>
    rw [F.cols_same Q h,double,he]
    exact congrArg (pt j) (F.invol c z)

private theorem cancel_cols_stem {i j : Col} (h : i ≠ j) (x y : A) (s : S) :
    F.solve Q (pt i x) (pt j y) (F.solve Q (pt i x) (pt j y) (.inl s)) = .inl s := by
  rw [F.cols_stem Q h,withStem,F.cols_diff Q h (other_left i j h).symm (other_right i j h).symm,across]
  rw [show x+y+(F.stemSum s-x-y) = F.stemSum s by abel, (F.stem_iff ..).mpr rfl]

private theorem cancel_left {i j : Col} (h : i ≠ j) (x y z : A) :
    F.solve Q (pt i x) (pt j y) (F.solve Q (pt i x) (pt j y) (pt i z)) = pt i z := by
  rw [F.cols_left Q h,double]
  cases he : F.pair i x z with
  | inl u =>
    rw [F.cols_diff Q h (other_left i j h).symm (other_right i j h).symm,across]
    rw [show x+y+(u-x-y) = u by abel,(F.short_iff ..).mp he]
    simp
  | inr c =>
    rw [F.cols_right Q h,double,(F.match_iff j y (F.partner c y) c).mpr rfl]
    exact congrArg (pt i) ((F.match_iff ..).mp he)

private theorem cancel_right {i j : Col} (h : i ≠ j) (x y z : A) :
    F.solve Q (pt i x) (pt j y) (F.solve Q (pt i x) (pt j y) (pt j z)) = pt j z := by
  rw [F.solve_swap₁ Q (pt i x) (pt j y),F.solve_swap₁ Q (pt i x) (pt j y)]
  exact F.cancel_left Q h.symm y x z

private theorem cancel_across {i j k : Col} (h : i ≠ j) (g : i ≠ k) (l : j ≠ k) (x y z : A) :
    F.solve Q (pt i x) (pt j y) (F.solve Q (pt i x) (pt j y) (pt k z)) = pt k z := by
  rw [F.cols_diff Q h g l,across]
  cases he : F.route (x+y+z) with
  | inl s =>
    rw [F.cols_stem Q h,withStem,← (F.stem_iff ..).mp he,other_eq i j k h g l]
    congr 1
    abel
  | inr p =>
    obtain ⟨t,d⟩ := p
    dsimp only
    rcases exhaust i j k t h g l with ht|ht|ht <;> subst t
    · simp only [ite_true]
      rw [F.cols_left Q h,double]
      have hh : F.pair i x (x+d) = .inl (x+y+z) :=
        (F.short_iff ..).mpr (by simpa only [add_sub_cancel_left] using he)
      rw [hh]
      dsimp only
      rw [other_eq i j k h g l]
      congr 1
      abel
    · simp only [if_neg h.symm,ite_true]
      rw [F.cols_right Q h,double]
      have hh : F.pair j y (y+d) = .inl (x+y+z) :=
        (F.short_iff ..).mpr (by simpa only [add_sub_cancel_left] using he)
      rw [hh]
      dsimp only
      rw [other_eq j i k h.symm l g]
      congr 1
      abel
    · simp only [if_neg g.symm,if_neg l.symm,ite_true]
      rw [F.cols_diff Q h g l,across,← add_assoc,F.reverse _ _ _ he]
      simp [g.symm,l.symm]

private theorem rep_put (hQ : StemClosed Q) (i : Col) (a b : S ⊕ A) :
    F.solve Q (put i a) (put i a) (put i b) = put i b := by rw [F.solve_put Q hQ,Q.repeated]

private theorem repeated (hQ : StemClosed Q) (a b : Point S A) : F.solve Q a a b = b := by
  rcases a with s|⟨i,x⟩ <;> rcases b with t|⟨j,y⟩
  · exact F.rep_put Q hQ 0 (.inl s) (.inl t)
  · exact F.rep_put Q hQ j (.inl s) (.inr y)
  · exact F.rep_put Q hQ i (.inr x) (.inl t)
  · by_cases h : i=j
    · subst j
      exact F.rep_put Q hQ i (.inr x) (.inr y)
    · exact (F.cols_same Q h x x y).trans (F.double_diag i j x y)

private theorem cancel (hQ : StemClosed Q) (a b c : Point S A) :
    F.solve Q a b (F.solve Q a b c) = c := by
  rcases a with s|⟨i,x⟩ <;> rcases b with t|⟨j,y⟩ <;> rcases c with u|⟨k,z⟩
  · exact F.pure_cancel Q hQ 0 (.inl s) (.inl t) (.inl u)
  · exact F.pure_cancel Q hQ k (.inl s) (.inl t) (.inr z)
  · exact F.pure_cancel Q hQ j (.inl s) (.inr y) (.inl u)
  · by_cases h : j=k
    · subst k
      exact F.pure_cancel Q hQ j (.inl s) (.inr y) (.inr z)
    · exact F.cancel_stem_col Q h s y z
  · exact F.pure_cancel Q hQ i (.inr x) (.inl t) (.inl u)
  · by_cases h : i=k
    · subst k
      exact F.pure_cancel Q hQ i (.inr x) (.inl t) (.inr z)
    · rw [F.solve_swap₁ Q (.inr (i,x)) (.inl t),F.solve_swap₁ Q (.inr (i,x)) (.inl t)]
      exact F.cancel_stem_col Q h t x z
  · by_cases h : i=j
    · subst j
      exact F.pure_cancel Q hQ i (.inr x) (.inr y) (.inl u)
    · exact F.cancel_cols_stem Q h x y u
  · by_cases h : i=j
    · subst j
      by_cases g : i=k
      · subst k
        exact F.pure_cancel Q hQ i (.inr x) (.inr y) (.inr z)
      · exact F.cancel_same Q g x y z
    · by_cases g : i=k
      · subst k
        exact F.cancel_left Q h x y z
      · by_cases l : j=k
        · subst k
          exact F.cancel_right Q h x y z
        · exact F.cancel_across Q h g l x y z

/-- Complete the shared-stem three-column design from its sum and matching data. -/
def rule (hQ : StemClosed Q) : Rule (Point S A) where
  complete := F.solve Q
  swap₁ := F.solve_swap₁ Q
  swap₂ := F.solve_swap₂ Q
  repeated := F.repeated Q hQ
  cancel := F.cancel Q hQ

/-- Every filled column is embedded as a subsystem. -/
theorem rule_put (hQ : StemClosed Q) (i : Col) (a b c : S ⊕ A) :
    (F.rule Q hQ).complete (put i a) (put i b) (put i c) = put i (Q.complete a b c) :=
  F.solve_put Q hQ i a b c

#print axioms rule
#print axioms rule_put

section Coordinates

variable {D : Type*} (slot : S ⊕ (Col × D) ≃ A) (shift : D ↪ A)
  (mate : M → A → A)

/-- At an ordinary point, short differences and matching colors enumerate its possible partners. -/
def neighbor (x : A) : D ⊕ M → A := Sum.elim (fun d => x + shift d) (fun c => mate c x)

private def decode (u : A) : S ⊕ (Col × A) :=
  (slot.symm u).map id (fun p => (p.1,shift p.2))

omit [AddCommGroup A] in
private theorem decode_stem (u : A) (s : S) : decode slot shift u = .inl s ↔ u = slot (.inl s) := by
  obtain ⟨v,rfl⟩ := slot.surjective u
  cases v <;> simp [decode]

omit [AddCommGroup A] in
private theorem decode_shift (u : A) (i : Col) (z : A) :
    decode slot shift u = .inr (i,z) ↔ ∃ d, u = slot (.inr (i,d)) ∧ z = shift d := by
  obtain ⟨v,rfl⟩ := slot.surjective u
  rcases v with s|⟨j,e⟩ <;> simp [decode,eq_comm,and_comm]

variable (hN : ∀ x, Function.Bijective (neighbor shift mate x))
include hN in
private noncomputable def lookup (x : A) := (Equiv.ofBijective _ (hN x)).symm

private theorem lookup_eq (x y : A) (v : D ⊕ M) :
    lookup shift mate hN x y = v ↔ y = neighbor shift mate x v :=
  (Equiv.symm_apply_eq (Equiv.ofBijective _ (hN x)))

private def encodePair (i : Col) (v : D ⊕ M) : A ⊕ M :=
  v.map (fun d => slot (.inr (i,d))) id

/-- A partition of sums, reversible shifts, and a complementary matching decomposition
supply all data for the three-column completion. -/
noncomputable def ofCoordinates
    (rev : D → D) (hrev : ∀ d, shift (rev d) = -shift d)
    (hslot : ∀ i d, slot (.inr (i,rev d)) = slot (.inr (i,d)) + shift d)
    (hinv : ∀ c, Function.Involutive (mate c)) (c₀ : M) (h₀ : ∀ x, mate c₀ x = x) :
    Scheme S A M where
  route := decode slot shift
  stemSum s := slot (.inl s)
  pair i x y := encodePair slot i (lookup shift mate hN x y)
  partner := mate
  stem_iff := decode_stem slot shift
  short_iff i x y u := by
    rw [decode_shift]
    cases he : lookup shift mate hN x y with
    | inl d =>
      have hy := (lookup_eq shift mate hN x y _).mp he
      change y = x + shift d at hy
      simp [encodePair,hy,eq_comm]
    | inr c =>
      simp only [encodePair,Sum.map_inr,id_eq,Sum.inr_ne_inl,false_iff,not_exists,not_and]
      intro d _ hd
      have h := (lookup_eq shift mate hN x y (.inl d)).mpr (by
        change y = x + shift d
        rw [← hd]
        abel)
      simp [he] at h
  reverse u i z he := by
    obtain ⟨d,rfl,rfl⟩ := (decode_shift ..).mp he
    exact (decode_shift ..).mpr ⟨rev d,(hslot i d).symm,(hrev d).symm⟩
  match_iff i x y c := by
    have he : encodePair slot i (lookup shift mate hN x y) = .inr c ↔
        lookup shift mate hN x y = .inr c := by cases lookup shift mate hN x y <;> simp [encodePair]
    exact he.trans ((lookup_eq shift mate hN x y (.inr c)).trans eq_comm)
  invol := hinv
  diagonal i x := by
    refine ⟨c₀,?_,h₀⟩
    rw [(lookup_eq shift mate hN x x (.inr c₀)).mpr (h₀ x).symm]
    rfl

end Coordinates

#print axioms ofCoordinates

end Scheme
end Erdos722.ThreeColumn
