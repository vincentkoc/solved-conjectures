import Mathlib

/-! # Finite obstructions for sixteen binary coordinates partitioned into two eights -/

namespace Green51FourSpace.Certificate
def planes : List Nat := [21845, 43690, 13107, 52428, 39321, 26214, 3855, 61680, 42405, 23130, 50115, 15420, 26985, 38550, 255, 65280, 43605, 21930, 52275, 13260, 26265, 39270, 61455, 4080, 23205, 42330, 15555, 49980, 38505, 27030]

private def nibbleWeight (x : Nat) := (155746543670344 >>> (3*(x%16))) % 8
def byteWeight (x : Nat) := nibbleWeight x + nibbleWeight (x/16)
def admissible (u v : Nat) : Bool :=
  let w := byteWeight u + byteWeight v
  let s := 256*u+v
  s == 0 || (w%2 == 0 && (decide (8≤w) || (w == 6 && planes.any (fun p => s &&& p == s))))
def allowed (u v : Nat) : Bool :=
  !v.testBit 5 && admissible u v && admissible u (v ^^^ 63)

def extendPairs (seen : List (Nat × Nat)) (u v : Nat) :=
  seen ++ seen.map (fun (x,y) => (u ^^^ x,v ^^^ y))

def search (seen : List (Nat × Nat)) : List Nat → Bool
  | [] => true
  | u :: rest => (List.range 256).any (fun v =>
      seen.all (fun (x,y) => allowed (u ^^^ x) (v ^^^ y)) &&
        search (extendPairs seen u v) rest)


/-- Every linear choice of compatible offsets survives each step of the finite search. -/
theorem search_sound (R : Set Nat) (f : Nat → Nat)
    (closed : ∀ u∈R, ∀ v∈R,u ^^^ v ∈ R)
    (add : ∀ u∈R, ∀ v∈R,f (u ^^^ v)=f u ^^^ f v)
    (bound : ∀ u∈R,f u<256) (valid : ∀ u∈R,allowed u (f u)=true)
    (seen : List (Nat × Nat)) (remaining : List Nat)
    (correct : ∀ p∈seen,p.1∈R ∧ p.2=f p.1) (active : ∀ u∈remaining,u∈R) :
    search seen remaining = true := by
  induction remaining generalizing seen with
  | nil => rfl
  | cons u rest ih =>
    have hu := active u (List.mem_cons_self)
    apply List.any_eq_true.mpr
    refine ⟨f u,List.mem_range.mpr (bound u hu),Bool.and_eq_true_iff.mpr ⟨?_,?_⟩⟩
    · apply List.all_eq_true.mpr
      rintro ⟨x,y⟩ member
      obtain ⟨hx,hy⟩ : x∈R ∧ y=f x := correct _ member
      subst y
      change allowed (u ^^^ x) (f u ^^^ f x)=true
      rw [←add u hu x hx]
      exact valid _ (closed _ hu _ hx)
    · apply ih
      · intro p hp
        rcases List.mem_append.mp hp with old|new
        · exact correct p old
        · obtain ⟨⟨x,y⟩,inSeen,rfl⟩ := List.mem_map.mp new
          obtain ⟨hx,hy⟩ : x∈R ∧ y=f x := correct _ inSeen
          subst y
          exact ⟨closed _ hu _ hx,(add _ hu _ hx).symm⟩
      · exact fun x hx => active x (List.mem_cons_of_mem _ hx)

def templates : List (List Nat) := [[5,17], [3,5], [3,20], [5,11], [5,10], [3,13],
  [5,80], [5,18], [5,96], [5,19,99], [23,45,78], [3,12,53,81], [3,12,48,192]]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem templates_fail : templates.all (fun b => !(search [(0,0)] b)) = true := by decide +kernel

end Green51FourSpace.Certificate
#print axioms Green51FourSpace.Certificate.search_sound
#print axioms Green51FourSpace.Certificate.templates_fail
