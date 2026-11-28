import Green51ElevenRelations
import Green51SystematicChecks

/-! # Golay witnesses for the affine and linear thresholds in dimension eleven -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51GolayWitnesses
local notation "F" => ZMod 2
local notation "V" => Cube 11

private abbrev point := Green51SystematicChecks.point 11

/-- Decode a list of eleven-bit labels. -/
def rows (rs : List ℕ) : Finset V := Green51SystematicChecks.rows 11 rs

/-- Exclude low-weight cancellations of extra columns with unit labels. -/
def test (v k : ℕ) (rs : List ℕ) : Bool := Green51SystematicChecks.test 11 v k rs

/-- Zero and the eleven coordinate unit vectors. -/
def units : List ℕ := [0,1,2,4,8,16,32,64,128,256,512,1024]
private def extra : List ℕ := [1393,1993,996,1595,797,1607,1258,1468,734,367,183,1938]
private def shortExtra : List ℕ := [1393,1468,734,367,183,1938]

/-- The 24 parity-check labels of the extended binary Golay code, with the
constant coordinate suppressed. -/
def full : Finset V := rows units ∪ rows extra

/-- The 18 columns retained after shortening at six coordinates. -/
def shortened : Finset V := rows units ∪ rows shortExtra

set_option maxHeartbeats 4000000 in
private theorem checked : test 0 0 extra=true := by decide +kernel

theorem sizes : full.card=24 ∧ shortened.card=18 := by decide +kernel

/-- The branch test excludes every subset of the extra columns that can
cancel with at most six of the full collection of columns. -/
theorem avoids_of_certificate (rs : List ℕ) (oc : test 0 0 rs = true)
    (large : 5 ≤ (rows units ∪ rows rs).card) : ¬FlatAt (rows units ∪ rows rs) 0 := by
  have dist (U : Finset V) (sub : U ⊆ rows rs) (inh : U.Nonempty) :
      6 < U.card+(supp (∑ u∈U,u)).card := by
    have b := Green51SystematicChecks.test_sound 11 rs 0 0 oc U sub
    have z : point 0 = 0 := by funext i; simp [point, Green51SystematicChecks.point]
    simpa only [Nat.zero_add,z,zero_add,show U.card≠0 from ne_of_gt (card_pos.mpr inh),false_or] using b
  have checks : units.all (fun v => decide ((supp (point v)).card ≤ 1)) = true := by decide +kernel
  have base (x) (hx : x ∈ rows units) : (supp x).card ≤ 1 := by
    obtain ⟨v,hv,rfl⟩ := (Green51SystematicChecks.mem_rows units).mp hx
    simpa using List.all_eq_true.mp checks v hv
  have inside : rows units ∪ rows rs ⊆ ball 11 1 ∪ rows rs := union_subset_union
    (fun u hu => mem_filter.mpr ⟨mem_univ _,base u hu⟩) Subset.rfl
  intro flat
  obtain ⟨T,sub,sz,sum⟩ := (Green51SparseDimensions.linear_three_iff _ large).mp ((flat_zero _).mp flat)
  exact Green51SmallWitnesses.add_labels_of_distance _ dist T (sub.trans inside) sz sum

theorem no_linear : ¬FlatAt full 0 :=
  avoids_of_certificate extra checked (by change 5 ≤ full.card;rw [sizes.1];decide)

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
  let input := units ++ shortExtra
  have represents (a : V) (ha : a∈shortened) : ∃ x∈input, point x=a := by
    rcases mem_union.mp ha with hu|hs
    · obtain ⟨x,mem,eq⟩ := (Green51SystematicChecks.mem_rows units).mp hu
      exact ⟨x,List.mem_append_left _ mem,eq⟩
    · obtain ⟨x,mem,eq⟩ := (Green51SystematicChecks.mem_rows shortExtra).mp hs
      exact ⟨x,List.mem_append_right _ mem,eq⟩
  have direct : input.all (fun x => input.all (fun y => decide (point x + point y ≠ point 934))) = true := by
    decide +kernel
  have missing (a) (ha : a∈shortened) (b) (hb : b∈shortened) : a+b≠point 934 := by
    obtain ⟨x,hx,rfl⟩ := represents a ha
    obtain ⟨y,hy,rfl⟩ := represents b hb
    simpa using List.all_eq_true.mp (List.all_eq_true.mp direct x hx) y hy
  have summed := sum_sdiff hB (f:=id)
  rw [eq,sum_pair ne] at summed
  exact missing x hx y hy (by simpa only [id_eq,sum,add_zero,total] using summed)

end Green51GolayWitnesses
#print axioms Green51GolayWitnesses.sizes
#print axioms Green51GolayWitnesses.no_linear
#print axioms Green51GolayWitnesses.no_affine
#print axioms Green51GolayWitnesses.avoids_of_certificate
