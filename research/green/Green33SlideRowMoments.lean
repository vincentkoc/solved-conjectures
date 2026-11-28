import Green33OddQuotientSlides
import Green33SlideOverlapEnergy

/-! Finite second moments for physical shifts of odd quotient layers. -/
open Finset
namespace Green33SlideConcentration
variable {G I:Type*} [AddCommGroup G] [Fintype G] [Fintype I] [DecidableEq G]

/-- Counting pairs of missing targets by their difference gives the second moment. -/
theorem second_moment_pairs (M:I→Finset G) :
    ∑ h:I,(M h).card^2=∑ d:G,(univ.filter fun p:G×I => p.1∈M p.2 ∧ p.1+d∈M p.2).card := by
  classical
  have at_x (h:I) (x:G) :
      ∑ d:G,(if x∈M h ∧ x+d∈M h then 1 else 0:ℕ)=if x∈M h then (M h).card else 0 := by
    by_cases hit:x∈M h
    · simp only [hit,true_and,if_true]
      have e:=Equiv.sum_comp (Equiv.addLeft x) (fun y => (if y∈M h then 1 else 0:ℕ))
      exact e.trans (by simp)
    · simp [hit]
  have each (d:G):(univ.filter fun p:G×I => p.1∈M p.2 ∧ p.1+d∈M p.2).card=
      ∑ h:I,∑ x:G,if x∈M h ∧ x+d∈M h then 1 else 0 := by
    rw [card_filter,Fintype.sum_prod_type,sum_comm]
  simp_rw [each]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  rw [sum_comm]
  simp_rw [at_x]
  simp [pow_two]
#print axioms second_moment_pairs
end Green33SlideConcentration

open Finset Green33LayerSlides
open scoped Pointwise
namespace Green33SlideConcentration
variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
theorem row_miss_iff {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (c:ZMod m) (t:H) (row:π t=c+c) (h:ZMod m→π.ker) (x:π.ker) :
    t+(x:H)∉displaced π A h+displaced π A h ↔
    x-(h c+h c)∈(rowSupport π A t c c)ᶜ ∧ ∀ j:positiveHalf m,
      x-(h (c+j.val)+h (c-j.val))∈(rowSupport π A t (c+j.val) (c-j.val))ᶜ := by
  let P (i j:ZMod m) := t+((x-(h i+h j):π.ker):H)∈layer π A i+layer π A j
  have sym (i j:ZMod m):P i j↔P j i := by
    simp only [P];rw [add_comm (h i) (h j),add_comm (layer π A i) (layer π A j)]
  rw [displaced_sum,row,row_cases odd c P sym]
  simp [P,rowSupport]

/-- Two target points separated by a fixed kernel displacement must both
miss every block. The difference is shared by all blocks. -/
theorem two_row_misses {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (c:ZMod m) (t:H) (row:π t=c+c) (d:π.ker) :
    let S (a b:ZMod m):=(rowSupport π A t a b)ᶜ
    let both (U:Finset π.ker):=U.filter fun z => z+d∈U
    (univ.filter fun p:π.ker×(ZMod m→π.ker) =>
      t+(p.1:H)∉displaced π A p.2+displaced π A p.2 ∧
      t+((p.1+d:π.ker):H)∉displaced π A p.2+displaced π A p.2).card =
      (Fintype.card π.ker)^((positiveHalf m).card+1) * (both (S c c)).card *
        ∏ j:positiveHalf m,(both (S (c+j.val) (c-j.val))).card := by
  classical
  intro S both
  let e:=labelEquiv odd c
  have law:=quotient_row_count π.ker (positiveHalf m) e (both (S c c)) (fun j => both (S (c+j.val) (c-j.val)))
  rw [Fintype.card_coe] at law
  apply Eq.trans _ law
  congr 1
  ext p
  have d0:e (.inl ())=c:=by change c+0=c;exact add_zero _
  have pl (j:positiveHalf m):e (.inr (.inl j))=c+j.val:=rfl
  have mi (j:positiveHalf m):e (.inr (.inr j))=c-j.val:=by change c+-j.val=c-j.val;abel
  simp only [mem_filter,mem_univ,true_and,row_miss_iff odd π A c t row,both,S,d0,pl,mi]
  simp_rw [show ∀ y:π.ker,p.1+d-y=(p.1-y)+d by intro y;abel]
  constructor
  · rintro ⟨⟨s,h⟩,v,g⟩
    exact ⟨⟨s,v⟩,fun j => ⟨h j,g j⟩⟩
  · rintro ⟨⟨s,v⟩,h⟩
    exact ⟨⟨s,fun j => (h j).1⟩,v,fun j => (h j).2⟩
#print axioms two_row_misses
def missSet {m:ℕ+} (π:H→+ZMod m) (A:Finset H) (t:H) (h:ZMod m→π.ker):Finset π.ker :=
  univ.filter fun x => t+(x:H)∉displaced π A h+displaced π A h

theorem physical_second_moment {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (c:ZMod m) (t:H) (row:π t=c+c) :
    let S (a b:ZMod m):=(rowSupport π A t a b)ᶜ
    (∑ h:ZMod m→π.ker,(dens (missSet π A t h))^2)/(Fintype.card π.ker:ℝ)^m.val =
      (∑ d:π.ker,overlapRate (S c c) d*∏ j:positiveHalf m,overlapRate (S (c+j.val) (c-j.val)) d)/
        (Fintype.card π.ker:ℝ) := by
  classical
  intro S
  let M:=missSet π A t
  let r:ℕ:=(positiveHalf m).card
  let k:ℝ:=Fintype.card π.ker
  let raw (d:π.ker):ℝ:=(overlap (S c c) d:ℝ)*∏ j:positiveHalf m,(overlap (S (c+j.val) (c-j.val)) d:ℝ)
  have kp:0<k:=by dsimp [k];positivity
  have pair (d:π.ker):
      (univ.filter fun p:π.ker×(ZMod m→π.ker) => p.1∈M p.2 ∧ p.1+d∈M p.2).card =
        (Fintype.card π.ker)^(r+1)*overlap (S c c) d*∏ j:positiveHalf m,overlap (S (c+j.val) (c-j.val)) d := by
    simpa only [M,missSet,mem_filter,mem_univ,true_and,overlap,r,S] using two_row_misses odd π A c t row d
  have total:=second_moment_pairs M
  simp_rw [pair] at total
  have totalR:(∑ h,((M h).card:ℝ)^2)=∑ d:π.ker,k^(r+1)*raw d:=by
    dsimp [raw,k]
    simp only [←mul_assoc]
    exact_mod_cast total
  rw [←mul_sum] at totalR
  have one (d:π.ker):
      overlapRate (S c c) d*(∏ j:positiveHalf m,overlapRate (S (c+j.val) (c-j.val)) d)=raw d/(k*k^r) := by
    simp only [overlapRate,prod_div_distrib,prod_const,card_univ,Fintype.card_coe,div_mul_div_comm]
    rfl
  simp only [dens,div_pow,←sum_div,one]
  change ((∑ h,((M h).card:ℝ)^2)/k^2)/k^m.val=((∑ d,raw d)/(k*k^r))/k
  rw [totalR]
  have half:m.val=(r+1)+r:=by have h:=half_count odd;dsimp [r];omega
  have power:k^m.val=k^(r+1)*k^r:=by rw [half,pow_add]
  rw [power]
  field_simp [kp.ne']
#print axioms physical_second_moment
end Green33SlideConcentration
