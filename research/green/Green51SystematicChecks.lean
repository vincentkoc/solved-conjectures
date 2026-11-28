import Green51SmallWitnesses

/-! # Checking extra binary columns against a coordinate simplex -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51SystematicChecks
local notation "F" => ZMod 2

def point (n a : ℕ) : Cube n := fun i => if a.testBit i.val then 1 else 0

/-- Decode a list of binary labels in dimension `n`. -/
def rows (n : ℕ) : List ℕ → Finset (Cube n)
  | [] => ∅
  | r::rs => insert (point n r) (rows n rs)

/-- Membership of a decoded list is witnessed by an input mask. -/
theorem mem_rows {n : ℕ} {x : Cube n} (rs : List ℕ) :
    x ∈ rows n rs ↔ ∃ v ∈ rs, point n v = x := by
  induction rs with
  | nil => simp [rows]
  | cons v rs ih =>
    rw [rows, mem_insert, ih]
    constructor
    · rintro (rfl | ⟨w, hw, eq⟩)
      · exact ⟨v, List.mem_cons_self, rfl⟩
      · exact ⟨w, List.mem_cons_of_mem v hw, eq⟩
    · rintro ⟨w, hw, eq⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inl eq.symm
      · exact Or.inr ⟨w, hw, eq⟩

private theorem point_xor (n v r : ℕ) : point n (v ^^^ r)=point n v+point n r := by
  funext i
  cases h:v.testBit i.val <;> cases j:r.testBit i.val <;>
    simp [point,Nat.testBit_xor,h,j,show (1:F)+1=0 by decide]

private def bitCount (v : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => bitCount v n + if v.testBit n then 1 else 0

private theorem bitCount_sum (v n : ℕ) :
    (∑ i:Fin n, if v.testBit i.val then 1 else 0)=bitCount v n := by
  induction n with
  | zero => simp [bitCount]
  | succ n ih => simp only [Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last,bitCount,ih]

private theorem point_weight (n v : ℕ) : (supp (point n v)).card=bitCount v n := by
  rw [←bitCount_sum,supp,card_filter]
  apply sum_congr rfl
  intro i _
  cases h : v.testBit i.val <;> simp [point,h]

/-- Exclude low-weight cancellations of the extra columns with unit labels. -/
def test (n v k : ℕ) : List ℕ → Bool
  | [] => decide (k=0 ∨ 6<k+bitCount v n)
  | r::rs => test n v k rs && test n (v ^^^ r) (k+1) rs

/-- Every subset of the extra columns passes the corresponding weight bound. -/
theorem test_sound (n : ℕ) (rs : List ℕ) (v k : ℕ) (ok : test n v k rs=true)
    (U : Finset (Cube n)) (sub : U⊆rows n rs) :
    k+U.card=0 ∨ 6<k+U.card+(supp (point n v+∑ u∈U,u)).card := by
  induction rs generalizing v k U with
  | nil =>
    have e : U=∅ := subset_empty.mp sub
    subst U
    simpa [test,point_weight] using ok
  | cons r rs ih =>
    have both : test n v k rs=true ∧ test n (v ^^^ r) (k+1) rs=true := by simpa [test] using ok
    obtain ⟨left,right⟩ := both
    by_cases h : point n r∈U
    · have rest : U.erase (point n r)⊆rows n rs := by
        intro u hu
        exact (mem_insert.mp (sub (mem_erase.mp hu).2)).resolve_left (mem_erase.mp hu).1
      have bound := ih (v ^^^ r) (k+1) right (U.erase (point n r)) rest
      have count : k+1+(U.erase (point n r)).card=k+U.card := by
        have := card_erase_add_one h; omega
      have sum : point n r+(∑ u∈U.erase (point n r),u)=∑ u∈U,u := U.add_sum_erase id h
      rw [count,point_xor,add_assoc (point n v),sum] at bound
      exact bound
    · apply ih v k left U
      intro u hu
      exact (mem_insert.mp (sub hu)).resolve_left (fun e => h (e ▸ hu))

end Green51SystematicChecks
#print axioms Green51SystematicChecks.test_sound
#print axioms Green51SystematicChecks.mem_rows
