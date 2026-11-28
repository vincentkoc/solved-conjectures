import Mathlib.Data.List.Basic

/-! # Difference orbits of the fifteen-point binary simplex configuration -/

namespace Green51SimplexDirections

def directions : List ℕ := [103,124,151,186,221,235,271,313,350,371,430,437,457,466,
  484,511,622,629,670,691,724,738,797,811,844,865,906,913]

def matrix : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a::as,x => (if x%2=1 then a else 0) ^^^ matrix as (x/2)

def first := matrix [18,66,258,2,3,6,10,34,130,514]
def second := matrix [681,687,684,653,701,677,749,173,941,557]

private def thin {α : Type} (index : α→ℕ) (seen : ℕ) : List α → List α
  | [] => []
  | x::xs => if seen.testBit (index x) then thin index seen xs
    else x::thin index (seen ||| (1 <<< index x)) xs

private theorem thin_sub {α : Type} (index : α→ℕ) {seen : ℕ} {x : α} {xs : List α}
    (h : x ∈ thin index seen xs) : x∈xs := by
  induction xs generalizing seen with
  | nil => simp [thin] at h
  | cons a as ih =>
    rw [thin] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

private def grow {α : Type} (key : α→ℕ) (f g : α→α) (s : List α) : ℕ → List α
  | 0 => s
  | k+1 =>
    let prev := grow key f g s k
    thin key 0 (prev ++ prev.map f ++ prev.map g)

private theorem grow_sound {α : Type} (P : α→Prop) (key : α→ℕ) (f g : α→α)
    (s : List α) (start : ∀ x∈s, P x) (hf : ∀ x, P x→P (f x)) (hg : ∀ x, P x→P (g x))
    (k : ℕ) : ∀ x∈grow key f g s k, P x := by
  induction k with
  | zero => exact start
  | succ k ih =>
    intro x hx
    have m := thin_sub key hx
    simp only [List.mem_append,List.mem_map] at m
    rcases m with (h|⟨y,h,rfl⟩)|⟨y,h,rfl⟩
    · exact ih _ h
    · exact hf _ (ih _ h)
    · exact hg _ (ih _ h)

private def singles := grow id first second [1,7,13,27,91] 22
def pairAction (f : ℕ→ℕ) (p : ℕ×ℕ) := (f p.1,f p.2)
private def pairs := grow (fun (p:ℕ×ℕ) => 28*directions.idxOf p.1+directions.idxOf p.2)
  (pairAction first) (pairAction second) [(103,124)] 22

private def excludedPairs : List (ℕ×ℕ) := directions.flatMap (fun u =>
  (directions.filter (fun w => u != w && !directions.contains (u ^^^ w))).map (u,·))

private def bits : List ℕ → ℕ
  | [] => 0
  | x::xs => (2^x) ||| bits xs

private theorem test_bits (xs : List ℕ) (i : ℕ) : (bits xs).testBit i = true ↔ i∈xs := by
  induction xs with
  | nil => simp [bits]
  | cons x xs ih =>
    simp only [bits,Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq,ih,List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private def code (p : ℕ×ℕ) := 28*directions.idxOf p.1+directions.idxOf p.2

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem single_cover : bits (0 :: (directions ++ singles)) = 2^1024-1 := by decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem pair_cover : bits (pairs.map code) = bits (excludedPairs.map code) := by decide +kernel

private theorem stable : directions.all (fun x => directions.contains (first x) &&
    directions.contains (second x)) = true := by decide +kernel

private theorem pair_good {p : ℕ×ℕ} (hp : p∈pairs) : p.1∈directions ∧ p.2∈directions := by
  have hs {x : ℕ} (hx : x∈directions) : first x ∈ directions ∧ second x ∈ directions := by
    simpa using List.all_eq_true.mp stable x hx
  apply grow_sound (fun p : ℕ×ℕ => p.1∈directions ∧ p.2∈directions) _ _ _ _ _ _ _ 22 p hp
  · simp only [List.mem_singleton]
    rintro _ rfl
    decide +kernel
  · exact fun _ h => ⟨(hs h.1).1,(hs h.2).1⟩
  · exact fun _ h => ⟨(hs h.1).2,(hs h.2).2⟩

set_option exponentiation.threshold 1024 in
/-- Five nonzero orbit representatives and the twenty-eight listed directions
cover the ten-dimensional binary difference space. -/
theorem single_orbits (P : ℕ→Prop) (start : ∀ x∈([1,7,13,27,91]:List ℕ), P x)
    (hf : ∀ x, P x→P (first x)) (hg : ∀ x, P x→P (second x))
    {x : ℕ} (lo : x≠0) (hi : x<1024) (missing : x∉directions) : P x := by
  have h : x∈0::(directions++singles) := (test_bits _ _).mp (by
    rw [single_cover,Nat.testBit_two_pow_sub_one]; exact decide_eq_true hi)
  have m : x∈singles := by simpa [lo,missing] using h
  exact grow_sound P id first second _ start hf hg 22 x m

/-- Pairs of listed directions whose sum is absent form one orbit. -/
theorem pair_orbits (P : ℕ×ℕ→Prop) (start : P (103,124))
    (hf : ∀ x, P x→P (pairAction first x)) (hg : ∀ x, P x→P (pairAction second x))
    {u w : ℕ} (hu : u∈directions) (hw : w∈directions)
    (ne : u≠w) (missing : u ^^^ w∉directions) : P (u,w) := by
  have h : (u,w)∈excludedPairs := List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr
    ⟨w, List.mem_filter.mpr ⟨hw,by simp [ne,missing]⟩,rfl⟩⟩
  have bit := (test_bits _ _).mpr (List.mem_map_of_mem (f:=code) h)
  rw [←pair_cover] at bit
  obtain ⟨⟨i,j⟩,ij,eq⟩ := List.mem_map.mp ((test_bits _ _).mp bit)
  obtain ⟨si,sj⟩ := pair_good ij
  change i∈directions at si
  change j∈directions at sj
  have jsmall := List.idxOf_lt_length_iff.mpr sj
  have wsmall := List.idxOf_lt_length_iff.mpr hw
  change directions.idxOf j < 28 at jsmall
  change directions.idxOf w < 28 at wsmall
  change 28*directions.idxOf i+directions.idxOf j=28*directions.idxOf u+directions.idxOf w at eq
  have iu : i=u := (List.idxOf_inj (y:=u) si).mp (by omega)
  have jw : j=w := (List.idxOf_inj (y:=w) sj).mp (by omega)
  have m : (u,w)∈pairs := iu ▸ jw ▸ ij
  exact grow_sound P _ _ _ [(103,124)] (by simpa) hf hg 22 _ m

end Green51SimplexDirections
#print axioms Green51SimplexDirections.single_orbits
#print axioms Green51SimplexDirections.pair_orbits
