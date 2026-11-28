import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-!
# Pair weights whose sums vanish on all blocks

A four-block exchange characterizes the relations among pair weights.
-/

namespace Erdos722.PairLattice
open Finset
variable {α G : Type*} [DecidableEq α] [AddCommGroup G]

private def blockSum (g : Finset α → G) (B : Finset α) : G :=
  ∑ e ∈ B.powersetCard 2, g e

private theorem blockSum_insert (g : Finset α → G) {B : Finset α} {i : α} (hi : i∉B) :
    blockSum g (insert i B) = blockSum g B + ∑ j∈B, g {i,j} := by
  classical
  have hs : (B.powersetCard 1).image (insert i) = B.image (fun j => {i,j}) := by
    ext e
    simp [powersetCard_one]
  have hinj : Set.InjOn (fun j : α => ({i,j} : Finset α)) B := by
    intro a ha b hb hab
    have ha' : a≠i := fun h => hi (h ▸ ha)
    have : a∈({i,b} : Finset α) := by
      rw [← show ({i,a} : Finset α)={i,b} from hab]
      simp
    simpa [ha'] using this
  unfold blockSum
  rw [powersetCard_succ_insert hi 1, hs, sum_union, sum_image hinj]
  rw [disjoint_left]
  intro e he hm
  obtain ⟨j,_,rfl⟩ := mem_image.mp hm
  exact hi ((mem_powersetCard.mp he).1 (by simp))

private theorem tetrad [Fintype α] {k : ℕ} (hk : 2≤k) (hv : k+2≤Fintype.card α)
    (g : Finset α → G) (hzero : ∀ B : Finset α, B.card=k → blockSum g B=0)
    (i j a b : α) (hij : i≠j) (hia : i≠a) (hib : i≠b) (hja : j≠a) (hjb : j≠b) (hab : a≠b) :
    g {i,j}+g {a,b}=g {i,a}+g {j,b} := by
  classical
  let D : Finset α := {i,j,a,b}
  have hd : D.card=4 := by simp [D,hij,hia,hib,hja,hjb,hab]
  have hroom : k-2 ≤ (univ \ D).card := by
    rw [card_sdiff,inter_univ,card_univ,hd]
    omega
  obtain ⟨F,hF,hcard⟩ := exists_subset_card_eq hroom
  have outside (x) (hx : x∈D) : x∉F := fun h => (mem_sdiff.mp (hF h)).2 hx
  let sum (x : α) := ∑ z∈F, g {x,z}
  have pair (x y : α) (hx : x∈D) (hy : y∈D) (hxy : x≠y) :
      g {x,y}= -(blockSum g F) - sum x - sum y := by
    have hx' : x∉insert y F := by simp [hxy,outside x hx]
    have hy' := outside y hy
    have hc : (insert x (insert y F)).card=k := by
      rw [card_insert_of_notMem hx',card_insert_of_notMem hy',hcard]
      omega
    have h := hzero _ hc
    rw [blockSum_insert g hx',blockSum_insert g hy',sum_insert hy'] at h
    change blockSum g F + sum y + (g {x,y}+sum x) = 0 at h
    rw [← add_left_cancel_iff (a:=blockSum g F+sum y+sum x)]
    calc
      _ = blockSum g F + sum y + (g {x,y}+sum x) := by abel
      _ = 0 := h
      _ = _ := by abel
  rw [pair i j (by simp [D]) (by simp [D]) hij,
    pair a b (by simp [D]) (by simp [D]) hab,
    pair i a (by simp [D]) (by simp [D]) hia,
    pair j b (by simp [D]) (by simp [D]) hjb]
  abel

private theorem outside_pair [Fintype α] (hv : 3≤Fintype.card α) (i j : α) :
    ∃ t : α, t≠i ∧ t≠j := by
  classical
  let D : Finset α := {i,j}
  have hd : D.card≤2 := (card_insert_le i {j}).trans_eq (by simp)
  have hroom : 0<(univ \ D).card := by rw [card_sdiff,inter_univ,card_univ]; omega
  obtain ⟨t,ht⟩ := card_pos.mp hroom
  exact ⟨t,by simpa [D,not_or] using (mem_sdiff.mp ht).2⟩

private theorem potentials [Fintype α] {k : ℕ} (hk : 2≤k) (hv : k+2≤Fintype.card α)
    (g : Finset α → G) (hzero : ∀ B : Finset α, B.card=k → blockSum g B=0) :
    ∃ a : α, ∃ x : α → G, ∃ c : G, x a=0 ∧ ∀ i j : α, i≠j → g {i,j}=x i+x j+c := by
  classical
  have hv' : 3≤Fintype.card α := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0<Fintype.card α)
  choose t ht using fun i => outside_pair hv' a i
  let x (i : α) := g {i,t i} - g {a,t i}
  have hxa : x a=0 := sub_self _
  have from_anchor (i j : α) (hij : i≠j) (hja : j≠a) : g {i,j}=x i+g {a,j} := by
    by_cases hia : i=a
    · subst i; simp [hxa]
    by_cases htj : j=t i
    · subst j; simp [x]
    have he := tetrad hk hv g hzero i j (t i) a hij (ht i).2.symm hia htj hja (ht i).1
    rw [pair_comm (t i) a,pair_comm j a] at he
    calc
      g {i,j} = (g {i,j}+g {a,t i})-g {a,t i} := by abel
      _ = _ := by rw [he]; dsimp [x]; abel
  obtain ⟨b,hba,_⟩ := outside_pair hv' a a
  let c := g {a,b}-x b
  have anchor (j : α) (hja : j≠a) : g {a,j}=x j+c := by
    by_cases hjb : j=b
    · subst j; dsimp [c]; abel
    have he : x b+g {a,j}=x j+g {a,b} := by
      rw [← from_anchor b j (Ne.symm hjb) hja,pair_comm b j,from_anchor j b hjb hba]
    calc
      g {a,j} = (x b+g {a,j})-x b := by abel
      _ = _ := by rw [he]; dsimp [c]; abel
  refine ⟨a,x,c,hxa,?_⟩
  intro i j hij
  by_cases hja : j=a
  · subst j; rw [pair_comm i a,anchor i hij,hxa,add_zero]
  · rw [from_anchor i j hij hja,anchor j hja,add_assoc]

private theorem vertex_sum (B : Finset α) (x : α → G) :
    (∑ e∈B.powersetCard 2, ∑ i∈e, x i)=(B.card-1) • ∑ i∈B, x i := by
  classical
  calc
    _ = ∑ e∈B.powersetCard 2, ∑ i∈B, if i∈e then x i else 0 := by
      apply sum_congr rfl
      intro e he
      rw [← sum_filter]
      congr 1
      ext i
      simp only [mem_filter]
      exact ⟨fun h => ⟨(mem_powersetCard.mp he).1 h,h⟩,And.right⟩
    _ = ∑ i∈B, ∑ e∈B.powersetCard 2, if i∈e then x i else 0 := sum_comm
    _ = _ := by
      rw [Finset.smul_sum]
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter,sum_const]
      congr 1
      simpa using card_filter_powersetCard_subset {i} B 2 (singleton_subset_iff.mpr hi) (by simp)

private theorem block_potential (g : Finset α → G) (x : α → G) (c : G)
    (h : ∀ i j : α, i≠j → g {i,j}=x i+x j+c) (B : Finset α) :
    blockSum g B=(B.card-1) • (∑ i∈B, x i) + B.card.choose 2 • c := by
  classical
  unfold blockSum
  calc
    _ = ∑ e∈B.powersetCard 2, ((∑ i∈e, x i)+c) := by
      apply sum_congr rfl
      intro e he
      obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
      simp [hij,h i j hij]
    _ = _ := by rw [sum_add_distrib,vertex_sum,sum_const,card_powersetCard]

/-- In any abelian group, vanishing on all k-point blocks implies vanishing
on every set whose order passes the two pair-design divisibility tests. -/
theorem scaled_pair_sum_zero [Fintype α] {k : ℕ} (hk : 2≤k) (hv : k+2≤Fintype.card α)
    (g : Finset α → G) (hzero : ∀ B : Finset α, B.card=k → (∑ e∈B.powersetCard 2, g e)=0)
    (V : Finset α) (l : ℕ) (h₁ : k-1 ∣ l*(V.card-1)) (h₂ : k.choose 2 ∣ l*V.card.choose 2) :
    l • (∑ e∈V.powersetCard 2, g e)=0 := by
  classical
  obtain ⟨a,x,c,hxa,he⟩ := potentials hk hv g hzero
  have H (B : Finset α) (hb : B.card=k) : (k-1) • (∑ i∈B, x i)+k.choose 2 • c=0 := by
    simpa only [hb] using (block_potential g x c he B).symm.trans (hzero B hb)
  have hx (i : α) : (k-1) • x i = 0 := by
    let D : Finset α := {i,a}
    have hd : D.card≤2 := (card_insert_le i {a}).trans_eq (by simp)
    have hr : k-1≤(univ \ D).card := by rw [card_sdiff,inter_univ,card_univ]; omega
    obtain ⟨F,hF,hcard⟩ := exists_subset_card_eq hr
    have out (j : α) (hj : j∈D) : j∉F := fun h => (mem_sdiff.mp (hF h)).2 hj
    have one (j : α) (hj : j∈D) := H (insert j F) (by rw [card_insert_of_notMem (out j hj),hcard]; omega)
    have h := one i (by simp [D])
    have z := one a (by simp [D])
    rw [sum_insert (out a (by simp [D])),hxa,zero_add] at z
    rw [sum_insert (out i (by simp [D])),nsmul_add,add_assoc,z,add_zero] at h
    exact h
  have hsum (B : Finset α) : (k-1) • (∑ i∈B, x i)=0 := by simp [Finset.smul_sum,hx]
  obtain ⟨B,_,hb⟩ := exists_subset_card_eq (s:=(univ : Finset α)) (n:=k) (by rw [card_univ]; omega)
  have hc := H B hb
  rw [hsum,zero_add] at hc
  change l • blockSum g V=0
  obtain ⟨d,hd⟩ := h₁
  obtain ⟨b,hb⟩ := h₂
  rw [block_potential g x c he,nsmul_add,← mul_smul,← mul_smul,hd,hb,Nat.mul_comm _ d,Nat.mul_comm _ b,mul_smul,mul_smul,hsum,hc]
  simp

#print axioms scaled_pair_sum_zero
end Erdos722.PairLattice
