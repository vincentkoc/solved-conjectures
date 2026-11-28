import Green28FourAtomLaws

/-! Finite collision certificates for strictly ordered sum tables with five columns. -/

namespace Green28FiveSiteCertificate

open Green28FourAtoms

private def deficient (p q i j : ℕ) : Bool :=
  (2*p).testBit i || (2*q).testBit j

private def partners (n m p q i j : ℕ) : List (ℕ × ℕ) :=
  ((List.range n).flatMap fun k => (List.range m).map fun l => (k,l)).filter fun (k,l) =>
    decide ((k < i ∧ j < l) ∨ (i < k ∧ l < j)) && deficient p q k l

private def collision (a b : ℕ → ℤ) (i j : ℕ) : List (ℕ × ℕ) → Prop
  | [] => False
  | (k,l)::rest => a i+b j = a k+b l ∨ collision a b i j rest

private structure Table (n m p q : ℕ) (a b : ℕ → ℤ) : Prop where
  row (i : ℕ) : i+1 < n → a i < a (i+1)
  col (j : ℕ) : j+1 < m → b j < b (j+1)
  avoid (i j k l : ℕ) : i < n → j < m → k < n → l < m → deficient p q i j=false → i≠k →
    a i+b j ≠ a k+b l
  collide (i j : ℕ) : i < n → j < m → deficient p q i j=true →
    collision a b i j (partners n m p q i j)

/-- A preorder traversal. Zero closes by strict order, positive values below 626
identify a forced collision at a high cell, and 626 plus a cell index requests
its alternative representations. All coordinates are digits in base five. -/
private def certificate : ℕ → ℕ → ℕ → List ℕ
  | 3,1,1 => [632]
  | 3,1,2 => [633]
  | 3,1,3 => [627,632,633,253]
  | 3,1,4 => [634]
  | 3,1,5 => [627,632,634,254]
  | 3,1,6 => [633,634,639,109]
  | 3,1,7 => [627,639,632,633,113,109,112]
  | 4,1,1 => [632]
  | 4,1,2 => [633]
  | 4,1,3 => [627,632,633,253,378]
  | 4,1,4 => [634]
  | 4,1,5 => [627,632,644,117]
  | 4,1,6 => [633,644,118]
  | 4,1,7 => [627,644,632,633,118,253,109,117]
  | 4,2,1 => [637]
  | 4,2,2 => [638]
  | 4,2,3 => [627,638,378]
  | 4,2,4 => [639]
  | 4,2,5 => [627,639,379]
  | 4,2,6 => [639,644,628,379,404]
  | 4,2,7 => [627,644,639,379,638,114,239,378]
  | 4,3,1 => [631,632,640,385]
  | 4,3,2 => [631,640,632,0,633,0,410]
  | 4,3,3 => [627,632,638,87,112,387,640,385,633,0,380,378,631,0,0]
  | 4,3,4 => [631,639,111]
  | 4,3,5 => [627,632,639,112,387,639,109,384,631,0,0]
  | 4,3,6 => [631,639,644,0,632,0,112,387,640,0,632,0,387,633,109,0,409,639,111,640,0,632,0,0,633,0,0,409]
  | 4,3,7 => [627,644,640,0,0,0,634,385,380,632,117,639,112,109,112,639,109,384,109,379,639,632,633,113,388,109,113,112,109,0,0,631,0,0,0]
  | 5,1,1 => [632]
  | 5,1,2 => [633]
  | 5,1,3 => [627,632,648,97,122]
  | 5,1,4 => [634]
  | 5,1,5 => [627,632,649,122]
  | 5,1,6 => [633,649,123]
  | 5,1,7 => [627,649,632,633,123,253,378,109,122]
  | 5,2,1 => [637]
  | 5,2,2 => [638]
  | 5,2,3 => [627,632,637,0,638,378,503,0]
  | 5,2,4 => [639]
  | 5,2,5 => [627,649,632,637,0,247,0]
  | 5,2,6 => [649,638,123,248]
  | 5,2,7 => [627,649,638,123,248,378,503]
  | 5,3,1 => [631,632,640,385,510]
  | 5,3,2 => [631,632,0,633,0,638,82,107]
  | 5,3,3 => [627,632,637,0,638,83,108,383,508,86,111,633,0,638,83,108,383,508,378,503,631,0,0]
  | 5,3,4 => [631,639,111]
  | 5,3,5 => [627,632,649,122,639,112,387,109,639,109,384,509,631,0,0]
  | 5,3,6 => [631,649,632,0,530,633,123,0,638,639,0,409,534,530,0,638,123,505,111,649,505,632,0,0,633,0,0,639,107,409,534]
  | 5,3,7 => [627,649,640,0,0,0,0,0,0,637,632,0,0,633,644,118,0,518,118,0,0,378,109,122,628,0,638,123,122,108,383,109,632,638,123,122,108,383,109,644,117,0,517,638,0,117,639,0,0,379,0,0,109,108,638,123,122,108,383,109,0,0,0,505,111,631,0,0,0]
  | 5,4,1 => [642]
  | 5,4,2 => [643]
  | 5,4,3 => [627,643,503]
  | 5,4,4 => [644]
  | 5,4,5 => [627,644,504]
  | 5,4,6 => [644,649,628,504,529]
  | 5,4,7 => [627,649,644,504,643,119,244,369,503]
  | 5,5,1 => [631,632,645,510]
  | 5,5,2 => [631,645,632,0,633,0,535]
  | 5,5,3 => [627,632,643,92,117,517,645,510,643,83,108,508,631,0,0]
  | 5,5,4 => [631,644,116]
  | 5,5,5 => [627,632,644,117,517,644,109,509,631,0,0]
  | 5,5,6 => [631,644,649,0,632,0,117,517,645,0,632,0,517,633,109,0,534,644,116,645,0,632,0,0,633,0,0,534]
  | 5,5,7 => [627,649,645,0,0,0,632,643,123,122,117,373,109,644,117,109,633,0,253,509,504,503,644,109,509,633,109,253,0,504,503,631,0,0,0]
  | 5,6,1 => [637,645,515]
  | 5,6,2 => [645,638,515,540]
  | 5,6,3 => [627,645,632,637,0,638,643,217,242,0,510,0,515,0,510,638,515,505,503,645,505,632,637,0,643,217,242,108,0,0,0]
  | 5,6,4 => [644,645,636,116,241]
  | 5,6,5 => [627,644,649,0,632,637,0,242,114,0,109,645,0,632,109,0,509,644,645,505,632,637,0,242,0,0,0,504]
  | 5,6,6 => [644,649,0,638,118,243,518,543,645,0,638,114,239,514,539]
  | 5,6,7 => [627,649,645,0,0,0,639,515,505,648,0,0,0,644,637,122,117,247,242,114,632,637,0,114,244,117,514,109,0,509,637,122,117,247,242,114,637,122,117,247,242,114,0,504,644,638,118,243,518,632,109,108,0,109,503,0,0,636,0,0,0,0,0,0]
  | 5,7,1 => [631,645,632,637,57,82,107,515,510]
  | 5,7,2 => [631,645,638,86,111,515,540]
  | 5,7,3 => [631,645,648,0,0,0,0,0,0,633,632,637,0,0,83,108,644,114,109,109,0,0,0,636,0,632,638,83,108,515,510,508,638,83,108,515,510,508,644,109,638,108,508,0,509,643,0,0,82,0,0,509,0,638,83,108,515,510,508,0,0,0,510,505,503,627,0,0,0]
  | 5,7,4 => [631,645,644,116,639,111,109,540,565]
  | 5,7,5 => [631,645,649,0,0,0,632,644,117,637,0,61,116,111,109,109,639,109,515,510,565,509,644,109,637,117,61,107,111,0,509,627,0,0,0]
  | 5,7,6 => [631,645,649,0,0,0,643,123,505,116,640,0,0,0,633,109,510,535,509,534,644,632,0,117,633,114,0,535,109,509,517,633,109,510,535,509,534,633,109,510,535,509,534,0,644,0,0,638,114,632,0,112,112,512,111,108,539,628,0,0,0,0,0,0]
  | 5,7,7 => [627,645,649,0,0,0,649,0,0,0,632,643,123,122,117,647,0,0,503,504,505,108,109,0,109,633,514,510,505,637,0,114,114,117,0,114,509,0,0,648,0,0,0,0,0,633,109,637,0,515,0,109,108,108,116,509,504,503,0,109,644,117,637,0,0,639,108,515,109,505,508,504,116,111,109,109,628,0,0,633,0,0,639,108,515,509,505,508,0,509,0,0,0,504,0,0,639,109,515,510,635,0,107,108,109,0,116,109,633,114,0,505,514,509,503,505,0,0,509,640,0,0,0,637,633,503,0,0,114,109,503,117,504,116,107,109,0,0,0,644,109,636,0,633,117,0,639,508,0,509,505,638,118,108,643,0,0,0,0,0,0,0,108,0,504,0,0,0,107,0,0,0,0,509,633,109,0,643,119,109,108,505,107,508,0,504,503,631,0,0,0,631,0,0,0]
  | _,_,_ => []

open Lean Elab Tactic Meta

private def digit (n : ℕ) : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩

/-- Replay one node against the current goal and return the unused suffix.
The arithmetic leaves receive only gap comparisons and equalities on this branch. -/
private partial def replay (n m p q depth : ℕ) (g : Ident) (code : List ℕ) : TacticM (List ℕ) := do
  let op :: tail := code | throwError "incomplete collision certificate"
  if op == 0 then
    evalTactic (← `(tactic| omega))
    return tail
  if op < 626 then
    let v := op-1
    let i := digit (v/125)
    let j := digit (v/25%5)
    let k := digit (v/5%5)
    let l := digit (v%5)
    evalTactic (← `(tactic| exact (Table.avoid $g $i $j $k $l (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)) (by omega)))
    return tail
  let i := (op-626)/5
  let j := (op-626)%5
  let clause := mkIdent (.mkSimple s!"choices{depth}")
  let eqn := mkIdent (.mkSimple s!"pair{depth}")
  evalTactic (← `(tactic| have $clause := Table.collide $g $(digit i) $(digit j)
    (by decide) (by decide) (by decide)))
  let mut rest := tail
  let a := mkIdent `a
  let b := mkIdent `b
  for (k,l) in partners n m p q i j do
    evalTactic (← `(tactic| rcases $clause:ident with $eqn:ident | $clause:ident))
    evalTactic (← `(tactic| change $a $(digit i)+$b $(digit j) = $a $(digit k)+$b $(digit l) at $eqn:ident))
    rest ← replay n m p q (depth+1) g rest
  evalTactic (← `(tactic| exact $clause))
  return rest

private def runCertificate (g : Ident) : TacticM Unit := withMainContext do
  let typ ← inferType (← Term.elabTerm g none)
  let args := typ.getAppArgs
  let mut sizes := #[]
  for t in args[:4] do
    let some k ← getNatValue? t | throwError "expected a numerical table shape"
    sizes := sizes.push k
  let n := sizes[0]!
  let m := sizes[1]!
  let p := sizes[2]!
  let q := sizes[3]!
  let a := mkIdent `a
  let b := mkIdent `b
  for v in [:n-1] do
    let h := mkIdent (.mkSimple s!"rowGap{v}")
    evalTactic (← `(tactic| have $h : $a $(digit v) < $a $(digit (v+1)) := Table.row $g $(digit v) (by decide)))
  for v in [:m-1] do
    let h := mkIdent (.mkSimple s!"colGap{v}")
    evalTactic (← `(tactic| have $h : $b $(digit v) < $b $(digit (v+1)) := Table.col $g $(digit v) (by decide)))
  let rest ← replay n m p q 0 g (certificate n p q)
  unless rest.isEmpty do throwError "unused collision certificate nodes"

elab "close_five_table" g:ident : tactic => runCertificate g

set_option maxHeartbeats 4500000 in
private theorem impossible (n p q : ℕ) (a b : ℕ → ℤ) (g : Table n 5 p q a b)
    (lo : 3 ≤ n) (hi : n ≤ 5) (pl : 1 ≤ p) (pu : p < 2^(n-2)) (ql : 1 ≤ q) (qu : q ≤ 7) :
    False := by
  interval_cases n <;> norm_num at pu <;> interval_cases p <;> interval_cases q <;>
    close_five_table g

private theorem collide_of_member {a b : ℕ → ℤ} {i j k l : ℕ} {ps : List (ℕ×ℕ)}
    (mem : (k,l) ∈ ps) (eq : a i+b j = a k+b l) : collision a b i j ps := by
  induction ps with
  | nil => simp at mem
  | cons head tail ih =>
    rcases head with ⟨k',l'⟩
    rcases List.mem_cons.mp mem with e|inside
    · cases e; exact Or.inl eq
    · exact Or.inr (ih inside)

private theorem table_of_rectangle {n m p q : ℕ} {a : Fin n → ℤ} {b : Fin m → ℤ}
    (ha : StrictMono a) (hb : StrictMono b)
    (rect : ∀ i j, Alone a b i j ↔ deficient p q i.val j.val=false) :
    ∃ A B : ℕ → ℤ, Table n m p q A B := by
  let A (i : ℕ) : ℤ := if h : i < n then a ⟨i,h⟩ else 0
  let B (j : ℕ) : ℤ := if h : j < m then b ⟨j,h⟩ else 0
  refine ⟨A,B,?_,?_,?_,?_⟩
  · intro i hi
    simpa only [A,dif_pos hi,dif_pos (by omega : i < n)] using
      ha (show (⟨i,by omega⟩ : Fin n) < ⟨i+1,hi⟩ by exact Nat.lt_succ_self _)
  · intro j hj
    simpa only [B,dif_pos hj,dif_pos (by omega : j < m)] using
      hb (show (⟨j,by omega⟩ : Fin m) < ⟨j+1,hj⟩ by exact Nat.lt_succ_self _)
  · intro i j k l hi hj hk hl high ne eq
    have unique := (rect ⟨i,hi⟩ ⟨j,hj⟩).mpr high
    obtain ⟨same,_⟩ := unique ⟨k,hk⟩ ⟨l,hl⟩ (by simpa only [A,B,dif_pos hi,dif_pos hj,dif_pos hk,dif_pos hl] using eq)
    exact ne (congrArg Fin.val same)
  · intro i j hi hj low
    let r : Fin n := ⟨i,hi⟩
    let s : Fin m := ⟨j,hj⟩
    have coll : ¬Alone a b r s := by
      intro single
      exact Bool.noConfusion (low.symm.trans ((rect r s).mp single))
    unfold Alone at coll
    push Not at coll
    obtain ⟨k,l,eq,ne⟩ := coll
    have cross : (k.val < i ∧ j < l.val) ∨ (i < k.val ∧ l.val < j) := by
      rcases lt_trichotomy k r with h|e|h
      · left
        refine ⟨h,?_⟩
        have lt := ha h
        exact hb.lt_iff_lt.mp (show b s < b l by omega)
      · subst k
        have equal := hb.injective (add_left_cancel eq)
        exact (ne rfl equal).elim
      · right
        refine ⟨h,?_⟩
        have lt := ha h
        exact hb.lt_iff_lt.mp (show b l < b s by omega)
    have low' : deficient p q k.val l.val=true := by
      cases e : deficient p q k.val l.val with
      | true => rfl
      | false =>
        obtain ⟨kr,ls⟩ := (rect k l).mpr e r s eq.symm
        exact (ne kr.symm ls.symm).elim
    apply collide_of_member (k := k.val) (l := l.val)
    · apply List.mem_filter.mpr
      refine ⟨List.mem_flatMap.mpr ⟨k.val,List.mem_range.mpr k.isLt,
        List.mem_map.mpr ⟨l.val,List.mem_range.mpr l.isLt,rfl⟩⟩,?_⟩
      simp [cross,low']
    · simpa only [A,B,dif_pos hi,dif_pos hj,dif_pos k.isLt,dif_pos l.isLt] using eq

local macro "try_mask " k:num : tactic => `(tactic|
  (refine ⟨$k,?_,?_,?_⟩
   · decide
   · decide
   · intro i
     fin_cases i <;> first
       | (apply iff_of_true <;> first | assumption | decide)
       | (apply iff_of_false <;> first | assumption | decide)))

private theorem flags (n : ℕ) (lo : 3 ≤ n) (hi : n ≤ 5) (u : Fin n → Prop)
    (first : u ⟨0,by omega⟩) (last : u ⟨n-1,by omega⟩) (someLow : ¬ ∀ i, u i) :
    ∃ p : ℕ, 1 ≤ p ∧ p < 2^(n-2) ∧ ∀ i, u i ↔ (2*p).testBit i.val=false := by
  classical
  interval_cases n
  all_goals
    first | change u 2 at last | change u 3 at last | change u 4 at last
    change u 0 at first
    by_cases h1 : u 1 <;> by_cases h2 : u 2 <;> by_cases h3 : u 3
    all_goals first
      | contradiction
      | (exfalso; apply someLow; intro i; fin_cases i <;> assumption)
      | try_mask 1 | try_mask 2 | try_mask 3 | try_mask 4
      | try_mask 5 | try_mask 6 | try_mask 7

open Green28FourAtomLaws

private theorem five_columns {m : ℕ} (bound : m ≤ 4) : GridTest m 4 := by
  classical
  intro a b ha hb u v rect first last first' last'
  by_cases rows : ∀ i, u i
  · exact Or.inl rows
  by_cases cols : ∀ j, v j
  · exact Or.inr cols
  have lo : 2 ≤ m := by
    by_contra! small
    apply rows
    intro i
    have index : i=0 ∨ i=Fin.last m := by
      by_cases h : i.val=0
      · left; exact Fin.ext (by simpa using h)
      · right; exact Fin.ext (by simp only [Fin.val_last]; omega)
    rcases index with rfl|rfl <;> assumption
  obtain ⟨p,pl,pu,hp⟩ := flags (m+1) (by omega) (by omega) u first last rows
  obtain ⟨q,ql,qu,hq⟩ := flags 5 (by decide) (by decide) v first' last' cols
  have mask (i j) : Alone a b i j ↔ deficient p q i.val j.val=false := by
    rw [rect,hp,hq]
    simp [deficient]
  obtain ⟨A,B,g⟩ := table_of_rectangle ha hb mask
  exact (impossible (m+1) p q A B g (by omega) (by omega) pl pu ql (by norm_num at qu; omega)).elim

private theorem transpose_test {m n : ℕ} (test : GridTest m n) : GridTest n m := by
  intro a b ha hb u v rect first last first' last'
  have flip (j i) : Alone b a j i ↔ Alone a b i j := by
    constructor
    · intro h k l eq
      exact (h l k (by simpa only [add_comm] using eq)).symm
    · intro h l k eq
      exact (h k l (by simpa only [add_comm] using eq)).symm
  have rect' (j i) : Alone b a j i ↔ v j ∧ u i := by rw [flip,rect,and_comm]
  exact (test b a hb ha v u rect' first' last' first last).symm

/-- With at most five ordered sites on each side and maximal end sites, a
rectangle of singleton representations contains all rows or all columns. -/
theorem five_grid {m n : ℕ} (hm : m ≤ 4) (hn : n ≤ 4) : GridTest m n := by
  by_cases nc : n=4
  · subst n; exact five_columns hm
  by_cases mc : m=4
  · subst m; exact transpose_test (five_columns hn)
  exact small_grid (by omega) (by omega)

/-- The original independent integer sum with arbitrary weights and gaps. -/
theorem uniform_of_at_most_five_atoms {P Q : PMF ℤ}
    (sum : Green28.IsUniformOnSupport (Green28.indepSum P Q))
    (pc : P.support.ncard ≤ 5) (qc : Q.support.ncard ≤ 5) :
    Green28.IsUniformOnSupport P ∧ Green28.IsUniformOnSupport Q := by
  apply uniform_of_grid sum
  intro m n pm qn
  exact five_grid (by omega) (by omega)

#print axioms five_grid
#print axioms uniform_of_at_most_five_atoms

end Green28FiveSiteCertificate
