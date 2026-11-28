import Green51ElevenRelations

/-! # Golay witnesses for the affine and linear thresholds in dimension eleven -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51GolayWitnesses
local notation "F" => ZMod 2
local notation "V" => Cube 11

private def point (a : ℕ) : V := fun i => if a.testBit i.val then 1 else 0

private def rows : List ℕ → Finset V
  | [] => ∅
  | r::rs => insert (point r) (rows rs)

private theorem point_xor (v r : ℕ) : point (v ^^^ r)=point v+point r := by
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

private theorem point_weight (v : ℕ) : (supp (point v)).card=bitCount v 11 := by
  rw [←bitCount_sum,supp,card_filter]
  apply sum_congr rfl
  intro i _
  cases h : v.testBit i.val <;> simp [point,h]

private def test (v k : ℕ) : List ℕ → Bool
  | [] => decide (k=0 ∨ 6<k+bitCount v 11)
  | r::rs => test v k rs && test (v ^^^ r) (k+1) rs

private theorem test_sound (rs : List ℕ) (v k : ℕ) (ok : test v k rs=true)
    (U : Finset V) (sub : U⊆rows rs) :
    k+U.card=0 ∨ 6<k+U.card+(supp (point v+∑ u∈U,u)).card := by
  induction rs generalizing v k U with
  | nil =>
    have e : U=∅ := subset_empty.mp sub
    subst U
    simpa [test,point_weight] using ok
  | cons r rs ih =>
    have both : test v k rs=true ∧ test (v ^^^ r) (k+1) rs=true := by simpa [test] using ok
    obtain ⟨left,right⟩ := both
    by_cases h : point r∈U
    · have rest : U.erase (point r)⊆rows rs := by
        intro u hu
        exact (mem_insert.mp (sub (mem_erase.mp hu).2)).resolve_left (mem_erase.mp hu).1
      have bound := ih (v ^^^ r) (k+1) right (U.erase (point r)) rest
      have count : k+1+(U.erase (point r)).card=k+U.card := by
        have := card_erase_add_one h; omega
      have sum : point r+(∑ u∈U.erase (point r),u)=∑ u∈U,u := U.add_sum_erase id h
      rw [count,point_xor,add_assoc (point v),sum] at bound
      exact bound
    · apply ih v k left U
      intro u hu
      exact (mem_insert.mp (sub hu)).resolve_left (fun e => h (e ▸ hu))

private def units : List ℕ := [0,1,2,4,8,16,32,64,128,256,512,1024]
private def extra : List ℕ := [1393,1993,996,1595,797,1607,1258,1468,734,367,183,1938]
private def shortExtra : List ℕ := [1393,1468,734,367,183,1938]

/-- The 24 parity-check labels of the extended binary Golay code, with the
constant coordinate suppressed. -/
def full : Finset V := rows units ∪ rows extra

/-- The 18 columns retained after shortening at six coordinates. -/
def shortened : Finset V := rows units ∪ rows shortExtra

set_option maxHeartbeats 4000000 in
private theorem checked : test 0 0 extra=true := by decide +kernel

private theorem distance (U : Finset V) (sub : U⊆rows extra) (non : U.Nonempty) :
    6<U.card+(supp (∑ u∈U,u)).card := by
  have b := test_sound extra 0 0 checked U sub
  have z : point 0=0 := by funext i; simp [point]
  simpa only [Nat.zero_add,z,zero_add,show U.card≠0 from ne_of_gt (card_pos.mpr non),
    false_or] using b

theorem sizes : full.card=24 ∧ shortened.card=18 := by decide +kernel

theorem no_linear : ¬FlatAt full 0 := by
  have unitsIn : ∀u∈rows units,(supp u).card≤1 := by decide +kernel
  have sub : full ⊆ ball 11 1 ∪ rows extra := by
    apply union_subset_union _ (Subset.rfl)
    intro u hu
    exact mem_filter.mpr ⟨mem_univ _,unitsIn u hu⟩
  intro h
  obtain ⟨T,hT,sz,zero⟩ := (Green51SparseDimensions.linear_three_iff full (by rw [sizes.1];decide)).mp
    ((flat_zero full).mp h)
  exact Green51SmallWitnesses.add_labels_of_distance _ distance T (hT.trans sub) sz zero

theorem no_affine : ¬∃p, FlatAt shortened p := by
  have sub : shortened⊆full := by decide +kernel
  have avoid : ¬FlatAt shortened 0 := by
    rintro ⟨W,d,h⟩
    exact no_linear ⟨W,d,fun _ hx => add_subset_add sub sub (h hx)⟩
  rintro ⟨p,flat⟩
  obtain ⟨B,hB,sz,sum⟩ := Green51PairedTypes.sixteen_relation avoid flat
  have card : (shortened\B).card=2 := by rw [card_sdiff_of_subset hB,sizes.2,sz]
  obtain ⟨x,y,ne,eq⟩ := card_eq_two.mp card
  have hx : x∈shortened := sdiff_subset (eq ▸ mem_insert_self x {y})
  have hy : y∈shortened := sdiff_subset (eq ▸ mem_insert_of_mem (mem_singleton_self y))
  have total : (∑ t∈shortened,t)=point 934 := by decide +kernel
  have missing : ∀x∈shortened,∀y∈shortened,x+y≠point 934 := by decide +kernel
  have summed := sum_sdiff hB (f:=id)
  rw [eq,sum_pair ne] at summed
  exact missing x hx y hy (by simpa only [id_eq,sum,add_zero,total] using summed)

end Green51GolayWitnesses
#print axioms Green51GolayWitnesses.sizes
#print axioms Green51GolayWitnesses.no_linear
#print axioms Green51GolayWitnesses.no_affine
