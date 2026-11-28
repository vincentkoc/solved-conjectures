import Green51PerfectPacking
/-! # Intersection parity of the octads -/
open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise symmDiff
namespace Green51PerfectColumns
local notation "F" => ZMod 2
local notation "V" => Cube 11
theorem intersect_moment {A O:Finset V} (os:O∈octadFamily A) {j m:ℕ}
    (constant:∀T∈O.powersetCard j, ((octadFamily A).filter (T⊆·)).card=m) :
    (∑U∈octadFamily A,(U∩O).card.choose j)=(8:ℕ).choose j*m := by
  have sz := (mem_powersetCard.mp (mem_filter.mp os).1).2
  have counts (U:Finset V) : (U∩O).card.choose j=
      ∑ T∈O.powersetCard j,if T⊆U then (1:ℕ) else 0 := by
    rw [sum_boole,←card_powersetCard]
    congr 1
    ext T
    simp only [mem_filter,mem_powersetCard,subset_inter_iff]
    tauto
  calc
    _ = ∑ U∈octadFamily A,∑ T∈O.powersetCard j,if T⊆U then (1:ℕ) else 0 :=
      sum_congr rfl fun U _ => counts U
    _ = ∑ T∈O.powersetCard j,∑ U∈octadFamily A,if T⊆U then (1:ℕ) else 0 := sum_comm
    _ = ∑ _T∈O.powersetCard j,m := by simp only [sum_boole];exact sum_congr rfl constant
    _ = _ := by simp [card_powersetCard,sz]

theorem intersection_bound {A O U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ho:O∈octadFamily A) (hu:U∈octadFamily A) (ne:U≠O) : (U∩O).card≤4 := by
  by_contra! high
  obtain ⟨T,sub,sz⟩ := exists_subset_card_eq (show 5≤(U∩O).card by omega)
  have tU:=sub.trans inter_subset_left
  have tO:=sub.trans inter_subset_right
  have ta:=tO.trans (mem_powersetCard.mp (mem_filter.mp ho).1).1
  exact ne ((unique_octad size avoid T ta sz).unique ⟨hu,tU⟩ ⟨ho,tO⟩)

private def parityIndicator (n:ℕ) : ℤ :=
  (n:ℤ)-2*(n.choose 2:ℤ)+4*(n.choose 3:ℤ)-8*(n.choose 4:ℤ)

theorem octad_even {A O U:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ho:O∈octadFamily A) (hu:U∈octadFamily A) : 2∣(U∩O).card := by
  classical
  obtain ⟨oa,oz⟩ := mem_powersetCard.mp (mem_filter.mp ho).1
  let H:=octadFamily A
  let n (B:Finset V) := (B∩O).card
  have moms (j:ℕ) (hj:j≤5) (m:ℕ) (val:(8-j).choose (5-j)*m=(24-j).choose (5-j)) :
      (∑ B∈H,(n B).choose j)=(8:ℕ).choose j*m := by
    apply intersect_moment ho
    intro T ht
    obtain ⟨ts,sz⟩ := mem_powersetCard.mp ht
    have tally := flags size avoid T (ts.trans oa) (by omega)
    rw [sz,←val] at tally
    exact Nat.eq_of_mul_eq_mul_left (Nat.choose_pos (by omega)) tally
  have m1 := moms 1 (by decide) 253 (by decide)
  have m2 := moms 2 (by decide) 77 (by decide)
  have m3 := moms 3 (by decide) 21 (by decide)
  have m4 := moms 4 (by decide) 5 (by decide)
  have e1 : (∑ B∈H,(n B:ℤ))=2024 := by exact_mod_cast (show _ from by simpa using m1)
  have e2 : (∑ B∈H,((n B).choose 2:ℤ))=2156 := by exact_mod_cast m2
  have e3 : (∑ B∈H,((n B).choose 3:ℤ))=1176 := by exact_mod_cast m3
  have e4 : (∑ B∈H,((n B).choose 4:ℤ))=350 := by exact_mod_cast m4
  have total : (∑ B∈H,parityIndicator (n B)) = -384 := by
    simp only [parityIndicator,sum_sub_distrib,sum_add_distrib,←mul_sum,e1,e2,e3,e4];decide
  have self : parityIndicator (n O) = -384 := by
    rw [show n O=8 by simp [n,oz]];decide
  have zero : (∑ B∈H.erase O,parityIndicator (n B))=0 := by
    have sum := H.add_sum_erase (fun B => parityIndicator (n B)) ho
    rw [total,self] at sum;omega
  by_cases eq:U=O
  · subst U;rw [inter_self,oz];decide
  have pos (B:Finset V) (hb:B∈H.erase O) : 0≤parityIndicator (n B) := by
    obtain ⟨ne,mem⟩:=mem_erase.mp hb
    have sz := intersection_bound size avoid ho mem ne
    change n B≤4 at sz
    generalize h:n B=t at sz ⊢
    interval_cases t <;> decide
  have val := (sum_eq_zero_iff_of_nonneg pos).mp zero U (mem_erase.mpr ⟨eq,hu⟩)
  have bound := intersection_bound size avoid ho hu eq
  change n U≤4 at bound
  change 2∣n U
  generalize h:n U=t at val bound ⊢
  interval_cases t <;> first | decide | exact absurd val (by decide)

end Green51PerfectColumns
#print axioms Green51PerfectColumns.intersect_moment
#print axioms Green51PerfectColumns.octad_even
