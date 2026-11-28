import Green51AffineMatchings

/-! # Third moments and the support of a binary quadratic form -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51ElevenDimensions
local notation "F" => ZMod 2

/-- A nonzero binary quadratic form takes the value one at least one quarter of the time. -/
theorem quadratic_quarter {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (q : V→F) (qzero:q 0=0) (non:∃a,q a=1)
    (second:∀ x a b, q x+q (x+a)+q (x+b)+q (x+a+b)=q 0+q a+q b+q (a+b)) :
    Fintype.card V≤4*(univ.filter (fun x=>q x=1)).card := by
  classical
  let S:=univ.filter (fun x=>q x=1)
  obtain ⟨a,ha⟩:=non
  have bit (x:F): x=0 ∨ x=1 := (show ∀ x:F,x=0 ∨ x=1 from by decide) x
  have shift (t:V) : (S.image (fun x=>x-t)).card=S.card := card_image_of_injective _ (fun _ _ h=>sub_left_inj.mp h)
  have into {x t:V} (h:q (x+t)=1) : x∈S.image (fun v=>v-t) :=
    mem_image.mpr ⟨x+t,mem_filter.mpr ⟨mem_univ _,h⟩,add_sub_cancel_right ..⟩
  by_cases pair:∀x,q x+q (x+a)=1
  · have cover : (univ:Finset V) ⊆ S∪S.image (fun x=>x-a) := by
      intro x _
      rcases bit (q x) with h|h
      · exact mem_union_right _ (into (by simpa only [h,zero_add] using pair x))
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
    have h:=(card_le_card cover).trans (card_union_le _ _)
    rw [card_univ,shift] at h
    change _≤4*S.card
    omega
  push Not at pair
  obtain ⟨b,hb⟩:=pair
  have zb:q b+q (b+a)=0 := (bit _).resolve_right hb
  have val (x:V) : q x+q (x+a)+q (x+b)+q (x+a+b)=1 := by
    rw [second,qzero,zero_add,ha,add_assoc,add_comm a b,zb,add_zero]
  let A:=S.image (fun x=>x-a)
  let B:=S.image (fun x=>x-b)
  let C:=S.image (fun x=>x-(a+b))
  have cover : (univ:Finset V) ⊆ (S∪A)∪(B∪C) := by
    intro x _
    by_cases x1:q x=1
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,x1⟩))
    by_cases a1:q (x+a)=1
    · exact mem_union_left _ (mem_union_right _ (into a1))
    by_cases b1:q (x+b)=1
    · exact mem_union_right _ (mem_union_left _ (into b1))
    have c1:=val x
    rw [(bit _).resolve_right x1,(bit _).resolve_right a1,(bit _).resolve_right b1,
      zero_add,zero_add,zero_add,add_assoc] at c1
    exact mem_union_right _ (mem_union_right _ (into c1))
  have h:=(card_le_card cover).trans (card_union_le _ _)
  have l:=card_union_le S A
  have r:=card_union_le B C
  rw [card_univ] at h
  rw [show A.card=S.card from shift a] at l
  rw [show B.card=S.card from shift b,show C.card=S.card from shift (a+b)] at r
  change _≤4*S.card
  omega

/-- Second elementary symmetric function of the coordinate bits. -/
def pairParity {n:ℕ} (x:Cube n) : F :=
  ∑ T∈(univ:Finset (Fin n)).powersetCard 2, ∏ i∈T,x i

theorem pairParity_eq {n:ℕ} (x:Cube n) :
    pairParity x=((supp x).card.choose 2:ℕ) := by
  classical
  have term (T:Finset (Fin n)) : (∏ i∈T,x i) = if T⊆supp x then (1:F) else 0 := by
    by_cases sub:T⊆supp x
    · rw [if_pos sub]
      apply prod_eq_one
      intro i hi
      have nz:x i≠0:= (mem_filter.mp (sub hi)).2
      exact ((show ∀ a:F,a=0 ∨ a=1 from by decide) _).resolve_left nz
    · rw [if_neg sub]
      obtain ⟨i,hi,off⟩:=Finset.not_subset.mp sub
      exact prod_eq_zero hi (by simpa [supp] using off)
  rw [pairParity]
  simp_rw [term]
  rw [sum_boole]
  have eq:((univ:Finset (Fin n)).powersetCard 2).filter (·⊆supp x)=(supp x).powersetCard 2 := by
    ext T;simp [mem_powersetCard,and_comm]
  rw [eq,card_powersetCard]

theorem pairParity_second {n:ℕ} (x a b:Cube n) :
    pairParity x+pairParity (x+a)+pairParity (x+b)+pairParity (x+a+b)=
      pairParity (0:Cube n)+pairParity a+pairParity b+pairParity (a+b) := by
  classical
  simp only [pairParity,←sum_add_distrib]
  apply sum_congr rfl
  intro T ht
  obtain ⟨i,j,ne,rfl⟩:=card_eq_two.mp (mem_powersetCard.mp ht).2
  simp only [prod_pair ne,Pi.add_apply,Pi.zero_apply,zero_mul,zero_add]
  exact (show ∀ x y a b u v:F,x*y+(x+a)*(y+b)+(x+u)*(y+v)+(x+a+u)*(y+b+v)=
    a*b+u*v+(a+u)*(b+v) from by decide) _ _ _ _ _ _

end Green51ElevenDimensions

#print axioms Green51ElevenDimensions.quadratic_quarter
#print axioms Green51ElevenDimensions.pairParity_eq
#print axioms Green51ElevenDimensions.pairParity_second
