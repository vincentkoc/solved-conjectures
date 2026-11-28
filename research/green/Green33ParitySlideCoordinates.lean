import Green33ParityDeviation
import Green33SingerBlockingLayers
import Green33SidonLayerRepairs

open Finset Green33SingerBlockingLayers Green33ReflectedLayers Green33TailEnergy
open scoped Pointwise
namespace Green33ParitySlides
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private theorem shift_univ (t:G) : ({t}:Finset G)+univ=univ := by
  apply eq_univ_of_card
  simp [card_singleton_add]

private theorem union_bounds (U W : Finset G) (t:G) (full : U∪W=univ) :
    Fintype.card G + diffReps U t ≤ (U∪({t}+W)).card + U.card ∧
    (U∪({t}+W)).card + U.card ≤ Fintype.card G + diffReps U t + (U∩W).card := by
  let X := U∪({t}+W)
  let Y := {t}+U
  have total : X∪Y=univ := by
    change U∪({t}+W)∪({t}+U)=_
    rw [union_assoc,←add_union,union_comm W U,full,shift_univ];simp
  have counts:=card_union_add_card_inter X Y
  rw [total,card_univ,show Y.card=U.card from card_singleton_add _ _] at counts
  have pair : (U∩Y).card=diffReps U t := by
    rw [show Y=t +ᵥ U from singleton_add _ ,card_inter_vadd]
    exact (card_sub_eq U U t).symm
  have eqn : X∩Y=(U∩Y)∪({t}+(W∩U)) := by
    rw [singleton_add_inter,←union_inter_distrib_right]
  have lo:=card_le_card (subset_union_left (s₁:=U∩Y) (s₂:={t}+(W∩U)))
  have hi:=card_union_le (U∩Y) ({t}+(W∩U))
  rw [←eqn,pair] at lo hi
  rw [card_singleton_add,inter_comm W U] at hi
  change Fintype.card G+diffReps U t ≤ X.card+U.card ∧ X.card+U.card ≤ _
  omega

private theorem as_images {v : ℕ+} (E B : Finset (ZMod v)) :
    split E B = E.image (doubleHom v) ∪ ({1}+B.image (doubleHom v)) := by
  unfold split
  congr 1
  ext x
  simp only [mem_image,mem_add,mem_singleton]
  constructor
  · rintro ⟨b,hb,rfl⟩;exact ⟨1,rfl,_,⟨b,hb,rfl⟩,rfl⟩
  · rintro ⟨_,rfl,_,⟨b,hb,rfl⟩,rfl⟩;exact ⟨b,hb,rfl⟩

/-- Exact compressed coordinates of the double sumset, including its carry. -/
theorem split_sums {v : ℕ+} (A B : Finset (ZMod v)) :
    split A B + split A B = split ((A+A)∪({1}+(B+B))) (A+B) := by
  let f := doubleHom v
  have two : f 1=1+1 := by simpa [f] using (double_coordinates v 0).2.2
  simp only [as_images,image_union,image_add,image_singleton,union_add,add_union]
  change _ = _ ∪ ({f 1} + _) ∪ _
  rw [two,←singleton_add_singleton]
  generalize A.image f = P
  generalize B.image f = Q
  have middle : ({1}+Q)+P = P+({1}+Q) := add_comm _ _
  have sum : ({1}+Q)+({1}+Q) = ({1}+{1})+(Q+Q) := by ac_rfl
  have mixed : P+({1}+Q)={1}+(P+Q) := by ac_rfl
  rw [middle,sum,mixed]
  ext x
  simp only [mem_union]
  tauto

theorem full_layers {v : ℕ+} (A B : Finset (ZMod v)) (h : split A B+split A B=univ) :
    A+B=univ ∧ (A+A)∪({1}+(B+B))=univ := by
  rw [split_sums] at h
  have c:=congrArg card h
  simp only [split_card,card_univ,ZMod.card] at c
  have bound (S : Finset (ZMod v)) : S.card ≤ v.val := by simpa using card_le_univ S
  constructor <;> apply eq_univ_of_card <;> rw [ZMod.card] <;>
    have := bound (A+B) <;> have := bound ((A+A)∪({1}+(B+B))) <;> omega

/-- Move the odd class by h in the quotient, or 2h in the original cyclic group. -/
def slide {v : ℕ+} (A B : Finset (ZMod v)) (h:ZMod v) := split A ({h}+B)

theorem slide_card {v : ℕ+} (A B : Finset (ZMod v)) (h:ZMod v)
    (full : split A B+split A B=univ) :
    let U := A+A
    let W := {1}+(B+B)
    let S := slide A B h
    2*v.val + diffReps U (h+h) ≤ (S+S).card+U.card ∧
      (S+S).card+U.card ≤ 2*v.val+diffReps U (h+h)+(U∩W).card := by
  obtain ⟨mixed,even⟩ := full_layers A B full
  have bounds:=union_bounds (A+A) ({1}+(B+B)) (h+h) even
  rw [ZMod.card] at bounds
  have m : A+({h}+B)={h}+(A+B) := by ac_rfl
  have e : {1}+(({h}+B)+({h}+B))={h+h}+({1}+(B+B)) := by
    rw [←singleton_add_singleton];ac_rfl
  dsimp only [slide]
  rw [split_sums,split_card,m,mixed,shift_univ,card_univ,ZMod.card,e]
  omega
#print axioms split_sums
#print axioms slide_card

/-- Doubling has at most two preimages, including for even v. -/
theorem double_bad {v : ℕ+} (T : Finset (ZMod v)) :
    (univ.filter fun h : ZMod v => h+h ∈ T).card ≤ 2*T.card := by
  apply card_le_mul_card_image_of_maps_to (f:=fun h => h+h) (fun h hh => (mem_filter.mp hh).2)
  intro b _
  let S := (univ.filter fun h : ZMod v => h+h∈T).filter fun h => h+h=b
  have val (x : ZMod v) (hx:x∈S) : x.val+x.val=b.val ∨ x.val+x.val=b.val+v.val := by
    have eq:=congrArg ZMod.val (mem_filter.mp hx).2
    rw [ZMod.val_add] at eq
    have lt:=ZMod.val_lt x
    by_cases h:x.val+x.val<v.val
    · left; rwa [Nat.mod_eq_of_lt h] at eq
    · right
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)] at eq
      omega
  have bound:=card_le_card_of_injOn (s:=S) (t:=(univ:Finset Bool))
    (fun x : ZMod v => decide (x.val+x.val=b.val)) (fun _ _ => mem_univ _)
    (by
      intro x hx y hy eq
      apply ZMod.val_injective
      have xx:=val x hx
      have yy:=val y hy
      by_cases b' : x.val+x.val=b.val <;> by_cases c' : y.val+y.val=b.val <;>
        simp [b',c'] at eq <;> omega)
  simpa [S] using bound
#print axioms double_bad

/-- Every subset of a cyclic group of even order has these coordinates. -/
theorem exists_split {v : ℕ+} (T : Finset (ZMod (2*v.val))) :
    ∃ A B : Finset (ZMod v), T=split A B := by
  let f:=doubleHom v
  let A:=univ.filter fun x => f x∈T
  let B:=univ.filter fun x => 1+f x∈T
  have surj : split (univ:Finset (ZMod v)) univ=univ := by
    apply eq_univ_of_card
    rw [split_card,card_univ,ZMod.card,ZMod.card];omega
  refine ⟨A,B,?_⟩
  ext x
  constructor
  · intro hx
    have all : x ∈ split (univ:Finset (ZMod v)) univ := surj ▸ mem_univ _
    rcases mem_union.mp all with ha|hb
    · obtain ⟨a,_,rfl⟩ := mem_image.mp ha
      exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hx⟩))
    · obtain ⟨b,_,rfl⟩ := mem_image.mp hb
      exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hx⟩))
  · intro hx
    rcases mem_union.mp hx with ha|hb
    · obtain ⟨a,ha',rfl⟩ := mem_image.mp ha
      exact (mem_filter.mp ha').2
    · obtain ⟨b,hb',rfl⟩ := mem_image.mp hb
      exact (mem_filter.mp hb').2
#print axioms exists_split
end Green33ParitySlides
