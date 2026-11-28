import Green33TailEnergy
import FormalConjecturesForMathlib.Combinatorics.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! Cyclic Sidon sets and their order-two quotient representation profiles. -/

open Finset Filter Green33Multiplicity Green33TailEnergy
open scoped Pointwise Topology

namespace Green33SidonProfile

private def graphPoint {F : Type*} [Field F] (a : Fˣ) : Additive Fˣ × F :=
  (Additive.ofMul a, (a : F))

/-- Ruzsa's multiplicative graph is a Sidon set, since the sum and product
in the field determine each unordered pair of nonzero elements. -/
theorem graph_sidon (F : Type*) [Field F] [Fintype Fˣ] [DecidableEq F] :
    IsSidon (↑((univ : Finset Fˣ).image graphPoint) : Set (Additive Fˣ × F)) := by
  intro x hx y hy z hz w hw he
  obtain ⟨a,_,rfl⟩ := mem_image.mp hx
  obtain ⟨b,_,rfl⟩ := mem_image.mp hy
  obtain ⟨c,_,rfl⟩ := mem_image.mp hz
  obtain ⟨d,_,rfl⟩ := mem_image.mp hw
  have ha : (a : F)+c=b+d := congrArg Prod.snd he
  have hp : (a : F)*c=b*d := congrArg (fun g : Additive Fˣ × F => (g.1.toMul : F)) he
  have hroot : ((a : F)-b)*((a : F)-d)=0 := by
    linear_combination (a : F)*ha-hp
  rcases mul_eq_zero.mp hroot with h | h
  · have hab : a=b := Units.ext (sub_eq_zero.mp h)
    subst b
    have hcd : c=d := Units.ext (add_left_cancel ha)
    exact Or.inl ⟨rfl,congrArg graphPoint hcd⟩
  · have had : a=d := Units.ext (sub_eq_zero.mp h)
    subst d
    have hcb : c=b := Units.ext (by linear_combination ha)
    exact Or.inr ⟨rfl,congrArg graphPoint hcb⟩

/-- Ruzsa's cyclic seed has exactly p−1 labels in the group of order p(p−1). -/
theorem cyclic_sidon_seed (p : ℕ) [hp : Fact p.Prime] :
    ∃ A : Finset (ZMod ((p-1)*p)), A.card=p-1 ∧ IsSidon (A : Set (ZMod ((p-1)*p))) := by
  classical
  let U := (ZMod p)ˣ
  have hcard : Nat.card (Additive U) = p-1 := by
    change Nat.card (ZMod p)ˣ = p-1
    rw [Nat.card_eq_fintype_card,ZMod.card_units]
  let f : ZMod (p-1) ≃+ Additive U := hcard ▸ zmodAddCyclicAddEquiv (inferInstance : IsAddCyclic (Additive U))
  have hc : (p-1).Coprime p := (Nat.coprime_self_sub_left hp.out.one_le).mpr (by simp)
  let e : ZMod ((p-1)*p) ≃+ Additive U × ZMod p :=
    (ZMod.chineseRemainder hc).toAddEquiv.trans (f.prodCongr (AddEquiv.refl _))
  let B := (univ : Finset U).image graphPoint
  have hi : Function.Injective (graphPoint (F := ZMod p)) :=
    fun _ _ h => Units.ext (congrArg Prod.snd h)
  refine ⟨B.map e.symm.toEmbedding,?_,?_⟩
  · rw [card_map,show B.card = (univ : Finset U).card from card_image_of_injective _ hi]
    rw [card_univ]
    exact ZMod.card_units p
  · intro x hx y hy z hz w hw he
    have hmem {v : ZMod ((p-1)*p)} (hv : v ∈ B.map e.symm.toEmbedding) : e v ∈ B := by
      obtain ⟨b,hb,rfl⟩ := mem_map.mp hv
      simpa using hb
    have hh := graph_sidon (ZMod p) _ (hmem hx) _ (hmem hy) _ (hmem hz) _ (hmem hw)
      (by rw [←map_add,←map_add,he])
    simpa only [e.injective.eq_iff] using hh

section Projection

variable {G H : Type*} [AddCommGroup G] [DecidableEq G]
  [AddCommGroup H] [DecidableEq H]

private theorem sidon_sum_cap {A : Finset G} (hA : IsSidon (A : Set G)) (z : G) :
    reps A z ≤ 2 := by
  let D := (A ×ˢ A).filter (fun p => p.1+p.2=z)
  change D.card≤2
  by_cases hD : D.Nonempty
  · obtain ⟨⟨a,b⟩,hab⟩ := hD
    obtain ⟨⟨ha,hb⟩,hs⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
    apply (card_le_card (t := {(a,b),(b,a)}) ?_).trans card_le_two
    rintro ⟨u,v⟩ huv
    obtain ⟨⟨hu,hv⟩,ht⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp huv
    rcases hA u hu a ha v hv b hb (ht.trans hs.symm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · simp [not_nonempty_iff_eq_empty.mp hD]

private theorem sidon_diff_cap {A : Finset G} (hA : IsSidon (A : Set G)) {z : G} (hz : z≠0) :
    diffReps A z ≤ 1 := by
  apply card_le_one.mpr
  rintro ⟨a,b⟩ hab ⟨u,v⟩ huv
  obtain ⟨⟨ha,hb⟩,hs⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
  obtain ⟨⟨hu,hv⟩,ht⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp huv
  have h : a+v=u+b := sub_eq_sub_iff_add_eq_add.mp (hs.trans ht.symm)
  rcases hA a ha u hu v hv b hb h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · simp_all

private lemma projected_count [Fintype G] (f : G →+ H) (A : Finset G) (z : H) (n : ℕ)
    (g : G → G → G) (h : H → H → H) (hmap : ∀ a b, f (g a b)=h (f a) (f b))
    (hcap : ∀ t, f t=z → ((A ×ˢ A).filter (fun p => g p.1 p.2=t)).card ≤ n) :
    (((A.image f) ×ˢ (A.image f)).filter (fun p => h p.1 p.2=z)).card ≤
      n * (univ.filter (fun t => f t=z)).card := by
  let D := (A ×ˢ A).filter (fun p => f (g p.1 p.2)=z)
  have sub : ((A.image f ×ˢ A.image f).filter (fun p => h p.1 p.2=z)) ⊆
      D.image (Prod.map f f) := by
    rintro ⟨a,b⟩ hab
    obtain ⟨⟨ha,hb⟩,he⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hb
    exact mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,(hmap x y).trans he⟩,rfl⟩
  apply ((card_le_card sub).trans card_image_le).trans
  apply card_le_mul_card_image_of_maps_to (f := fun p : G × G => g p.1 p.2) _ n _
  · intro p hp
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
  · intro t ht
    exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (hcap t (mem_filter.mp ht).2)

end Projection

/-- The quotient homomorphism from order 2M to order M. -/
def projection (M : ℕ+) : ZMod (2*M.val) →+ ZMod M :=
  (ZMod.castHom (dvd_mul_left M.val 2) (ZMod M)).toAddMonoidHom

private lemma two_lifts (M : ℕ+) (a : ZMod (2*M.val)) (z : ZMod M) (h : projection M a=z) :
    a=(z.val : ZMod (2*M.val)) ∨ a=((z.val+M.val : ℕ) : ZMod (2*M.val)) := by
  have hv : a.val%M.val=z.val := by
    change ZMod.cast a = z at h
    rw [ZMod.cast_eq_val] at h
    rw [← ZMod.val_natCast M a.val,h]
  have hd : a.val/M.val < 2 := (Nat.div_lt_iff_lt_mul M.pos).mpr a.val_lt
  have hr := Nat.mod_add_div a.val M.val
  rw [hv] at hr
  have classify (d : ℕ) (hd : d<2) : d=0 ∨ d=1 := by omega
  rcases classify _ hd with he | he
  · left
    rw [he,Nat.mul_zero,Nat.add_zero] at hr
    rw [hr,ZMod.natCast_zmod_val]
  · right
    rw [he,Nat.mul_one] at hr
    rw [hr,ZMod.natCast_zmod_val]

/-- Reducing a cyclic Sidon set modulo half the order preserves its cardinality.
Ordered sums have at most four representations and nonzero differences at most two. -/
theorem quotient_caps (M : ℕ+) {A : Finset (ZMod (2*M.val))}
    (hA : IsSidon (A : Set (ZMod (2*M.val)))) :
    ∃ B : Finset (ZMod M), B=A.image (projection M) ∧ B.card=A.card ∧
      (∀ s, reps B s≤4) ∧ ∀ s≠0, diffReps B s≤2 := by
  let f := projection M
  have hfib (z : ZMod M) : (univ.filter (fun a => f a=z)).card≤2 := by
    apply (card_le_card (t := {(z.val : ZMod (2*M.val)),↑(z.val+M.val)}) ?_).trans card_le_two
    intro a ha
    simpa only [mem_insert,mem_singleton] using two_lifts M a z (mem_filter.mp ha).2
  have hdbl (a : ZMod (2*M.val)) (z : ZMod M) (h : f a=z) : a+a=(z.val : ZMod (2*M.val))+z.val := by
    rcases two_lifts M a z h with rfl | he
    · rfl
    · rw [he,Nat.cast_add]
      have hzero : (M.val : ZMod (2*M.val)) + M.val = 0 := by
        rw [← Nat.cast_add,← two_mul,ZMod.natCast_self]
      linear_combination hzero
  refine ⟨A.image f,rfl,card_image_of_injOn ?_,?_,?_⟩
  · intro x hx y hy he
    have h := hA x hx y hy x hx y hy ((hdbl x _ he).trans (hdbl y _ rfl).symm)
    rcases h with h | h <;> exact h.1
  · intro s
    have h := projected_count f A s 2 (·+·) (·+·) (map_add f)
      (fun t _ => sidon_sum_cap hA t)
    exact h.trans (Nat.mul_le_mul_left 2 (hfib s))
  · intro s hs
    have h := projected_count f A s 1 (·-·) (·-·) (map_sub f)
      (fun t ht => sidon_diff_cap hA (by rintro rfl; simp_all))
    exact h.trans (by simpa using hfib s)

/-- Unordered representation count with diagonal pairs included once. -/
def unorderedReps {G : Type*} [AddCommMonoid G] (A : Finset G) [DecidableEq G] (x : G) : ℕ :=
  (A.sym2.filter (fun v => Sym2.lift ⟨(·+·),add_comm⟩ v=x)).card

private lemma quotient_unordered (M : ℕ+) {A : Finset (ZMod (2*M.val))}
    (hA : IsSidon (A : Set (ZMod (2*M.val)))) (z : ZMod M) :
    unorderedReps (A.image (projection M)) z ≤ 2 := by
  classical
  let f := projection M
  let plus {G : Type} [AddCommMonoid G] : Sym2 G → G := Sym2.lift ⟨(·+·),add_comm⟩
  let D := A.sym2.filter (fun v => f (plus v)=z)
  have sub : ((A.image f).sym2.filter (fun v => plus v=z)) ⊆ D.image (Sym2.map f) := by
    intro v hv
    obtain ⟨hin,he⟩ := mem_filter.mp hv
    rw [sym2_image] at hin
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hin
    exact mem_image.mpr ⟨_,mem_filter.mpr ⟨hab,(map_add f a b).trans he⟩,rfl⟩
  apply ((card_le_card sub).trans card_image_le).trans
  let T : Finset (ZMod (2*M.val)) := {↑z.val,↑(z.val+M.val)}
  have maps (v) (hv : v ∈ D) : plus v ∈ T := by
    simpa only [T,mem_insert,mem_singleton] using two_lifts M (plus v) z (mem_filter.mp hv).2
  apply (card_le_mul_card_image_of_maps_to (f := plus) maps 1 ?_).trans
    (by rw [one_mul]; exact card_le_two)
  intro t _
  apply card_le_one.mpr
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd
  obtain ⟨hab',ht⟩ := mem_filter.mp hab
  obtain ⟨hcd',ht'⟩ := mem_filter.mp hcd
  obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp (mem_filter.mp hab').1
  obtain ⟨hc,hd⟩ := mk_mem_sym2_iff.mp (mem_filter.mp hcd').1
  rcases hA a ha c hc b hb d hd (ht.trans ht'.symm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact Sym2.eq_swap

section Profile

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

/-- Number of residues with exactly j ordered representations. -/
def countAt (A : Finset G) (j : ℕ) : ℕ := (univ.filter (fun x => reps A x=j)).card

private theorem odd_count (A : Finset G) {j : ℕ} (hj : Odd j) : countAt A j ≤ A.card := by
  classical
  let e := Fintype.equivFin G
  let U := A.image (fun a => a+a)
  have even_off (x : G) (hx : x∉U) : Even (reps A x) := by
    let D := (A ×ˢ A).filter (fun p => p.1+p.2=x)
    let lt (p : G × G) := e p.1 < e p.2
    have hne (a b : G) (ha : a ∈ A) (hs : a+b=x) : e a≠e b := by
      intro h
      obtain rfl := e.injective h
      exact hx (hs ▸ mem_image_of_mem _ ha)
    have heq : (D.filter lt).card=(D.filter (fun p => ¬lt p)).card := by
      apply card_equiv (Equiv.prodComm G G)
      rintro ⟨a,b⟩
      simp only [D,lt,mem_filter,mem_product,Equiv.prodComm_apply,Prod.swap_prod_mk]
      constructor
      · rintro ⟨⟨⟨ha,hb⟩,hs⟩,hlt⟩
        exact ⟨⟨⟨hb,ha⟩,(add_comm b a).trans hs⟩,not_lt_of_ge hlt.le⟩
      · rintro ⟨⟨⟨hb,ha⟩,hs⟩,hlt⟩
        have hs' := (add_comm a b).trans hs
        exact ⟨⟨⟨ha,hb⟩,hs'⟩,lt_of_le_of_ne (not_lt.mp hlt) (hne a b ha hs')⟩
    change Even D.card
    rw [← card_filter_add_card_filter_not lt, ← heq]
    exact Even.add_self _
  have hsub : univ.filter (fun x => reps A x=j) ⊆ U := by
    intro x hx
    by_contra hn
    exact (Nat.not_even_iff_odd.mpr hj) ((mem_filter.mp hx).2 ▸ even_off x hn)
  exact (card_le_card hsub).trans card_image_le

private lemma total_reps (A : Finset G) :
    ∑ x, (reps A x : ℝ) = (A.card : ℝ)^2 := by
  have h := sum_card_fiberwise_eq_card_filter (A ×ˢ A) (univ : Finset G) (fun p => p.1+p.2)
  have h' : ∑ x, reps A x = A.card^2 := by simpa [reps,sq] using h
  exact_mod_cast h'

private lemma variance_upper (A : Finset G) (hd : ∀ x≠0, diffReps A x≤2) :
    ∑ x, ((reps A x : ℝ)-2)^2 ≤ 4*Fintype.card G-(A.card : ℝ)^2-2*A.card := by
  rw [centered_energy_eq]
  let D (x : G) := (diffReps A x : ℝ)
  have hzero : D 0=(A.card : ℝ) := by simp [D,diffReps,← diag_eq_filter,sub_eq_zero]
  have hs : ∑ x, D x=(A.card : ℝ)^2 := by
    have h := sum_card_fiberwise_eq_card_filter (A ×ˢ A) (univ : Finset G) (fun p => p.1-p.2)
    have h' : ∑ x, diffReps A x=A.card^2 := by simpa [diffReps,sq] using h
    dsimp only [D]
    exact_mod_cast h'
  have hpoint : ∑ x ∈ univ.erase 0, (D x-2)^2 ≤ ∑ x ∈ univ.erase 0, 2*(2-D x) := by
    apply sum_le_sum
    intro x hx
    have hx' : D x≤2 := by dsimp only [D]; exact_mod_cast hd x (mem_erase.mp hx).1
    have hx0 : 0≤D x := Nat.cast_nonneg _
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx')]
  have h₁ := sum_erase_add univ (fun x => (D x-2)^2) (mem_univ (0 : G))
  have h₂ := sum_erase_add univ (fun x => 2*(2-D x)) (mem_univ (0 : G))
  simp only [←mul_sum,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,hs,hzero] at h₂ hpoint
  rw [hzero] at h₁
  change ∑ x, (D x-2)^2 ≤ _
  linarith

private lemma histogram (A : Finset G) (hc : ∀ x, reps A x≤4) (w : ℕ → ℝ) :
    ∑ x, w (reps A x) = (countAt A 0 : ℝ)*w 0 + (countAt A 1 : ℝ)*w 1 +
      (countAt A 2 : ℝ)*w 2 + (countAt A 3 : ℝ)*w 3 + (countAt A 4 : ℝ)*w 4 := by
  calc
    _ = ∑ i ∈ range 5, ∑ x ∈ univ.filter (fun x => reps A x=i), w (reps A x) :=
      (sum_fiberwise_of_maps_to (fun x _ => mem_range.mpr (Nat.lt_succ_of_le (hc x))) _).symm
    _ = ∑ i ∈ range 5, (countAt A i : ℝ)*w i := by
      apply sum_congr rfl
      intro i _
      calc
        _ = ∑ x ∈ univ.filter (fun x => reps A x=i), w i :=
          sum_congr rfl (fun x hx => congrArg w (mem_filter.mp hx).2)
        _ = _ := by simp [countAt]
    _ = _ := by simp [sum_range_succ]

/-- Uniform finite errors for the three even multiplicity classes. When
k² is close to 2|G|, the respective proportions approach 1/4, 1/2, 1/4. -/
theorem profile_error (A : Finset G) (hs : ∀ x, reps A x≤4) (hd : ∀ x≠0, diffReps A x≤2) :
    let m := (Fintype.card G : ℝ)
    let k := (A.card : ℝ)
    let E := 4*|k^2-2*m|+10*k+4
    |4*(countAt A 0 : ℝ)-m| ≤ E ∧ |2*(countAt A 2 : ℝ)-m| ≤ E ∧
      |4*(countAt A 4 : ℝ)-m| ≤ E := by
  dsimp only
  have h₀ := histogram A hs (fun _ => (1 : ℝ))
  have h₁ := histogram A hs (fun j => (j : ℝ))
  have hv := histogram A hs (fun j => ((j : ℝ)-2)^2)
  norm_num at h₀ h₁ hv
  rw [total_reps] at h₁
  have hlo := variance_floor A 2
  have hup := variance_upper A hd
  rw [hv] at hlo hup
  have o₁ : (countAt A 1 : ℝ) ≤ A.card := by exact_mod_cast odd_count A (by decide : Odd 1)
  have o₃ : (countAt A 3 : ℝ) ≤ A.card := by exact_mod_cast odd_count A (by decide : Odd 3)
  have n₁ := Nat.cast_nonneg (α := ℝ) (countAt A 1)
  have n₃ := Nat.cast_nonneg (α := ℝ) (countAt A 3)
  have hp := le_abs_self ((A.card : ℝ)^2-2*Fintype.card G)
  have hn := neg_le_abs ((A.card : ℝ)^2-2*Fintype.card G)
  have hk := Nat.cast_nonneg (α := ℝ) A.card
  refine ⟨abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩,abs_le.mpr ⟨?_,?_⟩⟩ <;> linarith

private lemma hole_count (A : Finset G) : countAt A 0 = (A+A)ᶜ.card := by
  unfold countAt
  congr 1
  ext x
  simp only [mem_filter,mem_univ,true_and,mem_compl,reps,card_eq_zero,←not_nonempty_iff_eq_empty,
    filter_nonempty_iff,Finset.mem_add]
  apply not_congr
  constructor
  · rintro ⟨⟨a,b⟩,hab,hs⟩
    exact ⟨a,(mem_product.mp hab).1,b,(mem_product.mp hab).2,hs⟩
  · rintro ⟨a,ha,b,hb,hs⟩
    exact ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,hs⟩

/-- Each newly covered sum uses a label of B outside A. Deletions are unrestricted. -/
theorem repair_cost (A B : Finset G) :
    countAt A 0 ≤ countAt B 0 + (B \ A).card * B.card := by
  have hsub : B+B ⊆ (A+A) ∪ ((B \ A)+B) := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
    by_cases h₁ : a∈A
    · by_cases h₂ : b∈A
      · exact mem_union_left _ (add_mem_add h₁ h₂)
      · exact mem_union_right _ ((add_comm b a) ▸ add_mem_add (mem_sdiff.mpr ⟨hb,h₂⟩) ha)
    · exact mem_union_right _ (add_mem_add (mem_sdiff.mpr ⟨ha,h₁⟩) hb)
  have hsum : ((B \ A)+B).card ≤ (B \ A).card * B.card := Finset.card_add_le ..
  have h := (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_left hsum _))
  have hA := card_le_univ (A+A)
  have hB := card_le_univ (B+B)
  rw [hole_count,hole_count,card_compl,card_compl]
  omega

end Profile

private lemma normalized_profile {N : ℕ → ℕ+} (A : (i : ℕ) → Finset (ZMod (N i)))
    (hN : Tendsto (fun i => (N i).val) atTop atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/(N i : ℝ)) atTop (𝓝 0))
    (hk₂ : Tendsto (fun i => ((A i).card : ℝ)^2/(N i : ℝ)) atTop (𝓝 2))
    (hs : ∀ i x, reps (A i) x≤4) (hd : ∀ i x, x≠0 → diffReps (A i) x≤2) :
    Tendsto (fun i => (countAt (A i) 0 : ℝ)/(N i : ℝ)) atTop (𝓝 (1/4)) ∧
    Tendsto (fun i => (countAt (A i) 2 : ℝ)/(N i : ℝ)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun i => (countAt (A i) 4 : ℝ)/(N i : ℝ)) atTop (𝓝 (1/4)) := by
  let m (i : ℕ) := (N i : ℝ)
  let k (i : ℕ) := ((A i).card : ℝ)
  let E (i : ℕ) := 4*|k i^2-2*m i|+10*k i+4
  have hm (i : ℕ) : 0<m i := by dsimp only [m]; exact_mod_cast (N i).pos
  have he : Tendsto (fun i => E i/m i) atTop (𝓝 0) := by
    have ht := (((tendsto_const_nhds (x := (4:ℝ))).mul
      ((hk₂.sub (tendsto_const_nhds (x := (2:ℝ)))).abs)).add
      ((tendsto_const_nhds (x := (10:ℝ))).mul hk)).add
      ((tendsto_const_nhds (x := (4:ℝ))).div_atTop (tendsto_natCast_atTop_atTop.comp hN))
    norm_num at ht
    refine ht.congr (fun i => ?_)
    change 4*|k i^2/m i-2|+10*(k i/m i)+4/m i=E i/m i
    have heq : k i^2/m i-2=(k i^2-2*m i)/m i := by field_simp [(hm i).ne']
    rw [heq,abs_div,abs_of_pos (hm i)]
    dsimp [E]; ring
  have ratio (c : ℝ) (hc : 0<c) (f : ℕ → ℕ) (hf : ∀ i, |c*(f i : ℝ)-m i|≤E i) :
      Tendsto (fun i => (f i : ℝ)/m i) atTop (𝓝 (1/c)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h := he.div_const c
    rw [zero_div] at h
    apply squeeze_zero (fun _ => dist_nonneg) _ h
    intro i
    rw [Real.dist_eq,show (f i : ℝ)/m i-1/c=(c*(f i : ℝ)-m i)/m i/c by
      field_simp [(hm i).ne',hc.ne'],abs_div,abs_div,abs_of_pos (hm i),abs_of_pos hc]
    gcongr
    exact hf i
  have H (i : ℕ) := profile_error (A i) (hs i) (hd i)
  simp only [ZMod.card] at H
  exact ⟨ratio 4 (by norm_num) _ (fun i => (H i).1),
    ratio 2 (by norm_num) _ (fun i => (H i).2.1),
    ratio 4 (by norm_num) _ (fun i => (H i).2.2)⟩

/-- Every sequence of dense cyclic Sidon seeds has the same three main
multiplicities after reduction by a subgroup of order two. -/
theorem projected_profile {N : ℕ → ℕ+} (A : (i : ℕ) → Finset (ZMod (2*(N i).val)))
    (hA : ∀ i, IsSidon (A i : Set (ZMod (2*(N i).val))))
    (hN : Tendsto (fun i => (N i).val) atTop atTop)
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2))) :
    let B := fun i => (A i).image (projection (N i))
    Tendsto (fun i => (countAt (B i) 0 : ℝ)/(N i : ℝ)) atTop (𝓝 (1/4)) ∧
    Tendsto (fun i => (countAt (B i) 2 : ℝ)/(N i : ℝ)) atTop (𝓝 (1/2)) ∧
    Tendsto (fun i => (countAt (B i) 4 : ℝ)/(N i : ℝ)) atTop (𝓝 (1/4)) := by
  choose B hB hcard hs hd using (fun i => quotient_caps (N i) (hA i))
  obtain ⟨hl,hu⟩ := card_limits N (fun i => (A i).card) hN hk
  have hx := normalized_profile B hN (by simpa only [hcard] using hl) (by simpa only [hcard] using hu) hs hd
  simpa only [hB] using hx

/-- Ruzsa's seed gives explicit moduli attaining the three limiting proportions.
The absolute errors in the three scaled counts are at most 14(p−1)+4. -/
theorem prime_quotient (p : ℕ) (hp : p.Prime) (hp₂ : 2<p) :
    ∃ M : ℕ+, 2*M.val=(p-1)*p ∧ ∃ B : Finset (ZMod M), B.card=p-1 ∧
      (∀ x, unorderedReps B x≤2) ∧ (∀ x, reps B x≤4) ∧ (∀ x≠0, diffReps B x≤2) ∧
      |4*(countAt B 0 : ℝ)-(M : ℝ)| ≤ 14*(p-1 : ℕ)+4 ∧
      |2*(countAt B 2 : ℝ)-(M : ℝ)| ≤ 14*(p-1 : ℕ)+4 ∧
      |4*(countAt B 4 : ℝ)-(M : ℝ)| ≤ 14*(p-1 : ℕ)+4 := by
  let : Fact p.Prime := ⟨hp⟩
  have heven : Even (p-1) := by
    obtain ⟨a,ha⟩ := hp.odd_of_ne_two (by omega)
    exact ⟨a,by omega⟩
  obtain ⟨a,ha⟩ := heven
  have ha' : 0<a := by omega
  let M : ℕ+ := ⟨a*p,Nat.mul_pos ha' hp.pos⟩
  have hM : 2*M.val=(p-1)*p := by dsimp [M]; rw [ha]; ring
  have hseed : ∃ S : Finset (ZMod (2*M.val)), S.card=p-1 ∧ IsSidon (S : Set (ZMod (2*M.val))) := by
    rw [hM]
    exact cyclic_sidon_seed p
  obtain ⟨S,hS,hsidon⟩ := hseed
  obtain ⟨B,heq,hB,hs,hd⟩ := quotient_caps M hsidon
  rw [hS] at hB
  refine ⟨M,hM,B,hB,fun x => heq ▸ quotient_unordered M hsidon x,hs,hd,?_⟩
  have hrel : ((p-1 : ℕ) : ℝ)^2-2*(M : ℝ) = -((p-1 : ℕ) : ℝ) := by
    have hmul : 2*(M : ℝ)=((p-1 : ℕ) : ℝ)*p := by exact_mod_cast hM
    rw [hmul,Nat.cast_sub hp.one_le,Nat.cast_one]; ring
  have h := profile_error B hs hd
  simpa only [ZMod.card,hB,hrel,abs_neg,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (p-1)),
    show ∀ x : ℝ, 4*x+10*x+4=14*x+4 by intro x; ring] using h

/-- An infinite family of cyclic B₂[2] sets with one quarter of residues missing
and limiting ordered multiplicity proportions 1/4, 1/2 and 1/4. -/
theorem sharp_cyclic_profile : ∃ M : ℕ → ℕ+, Tendsto (fun i => (M i).val) atTop atTop ∧
    ∃ B : (i : ℕ) → Finset (ZMod (M i)), (∀ i x, unorderedReps (B i) x≤2) ∧
      (∀ i x, reps (B i) x≤4) ∧
      Tendsto (fun i => ((B i).card : ℝ)/Real.sqrt (M i)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun i => (countAt (B i) 0 : ℝ)/(M i : ℝ)) atTop (𝓝 (1/4)) ∧
      Tendsto (fun i => (countAt (B i) 2 : ℝ)/(M i : ℝ)) atTop (𝓝 (1/2)) ∧
      Tendsto (fun i => (countAt (B i) 4 : ℝ)/(M i : ℝ)) atTop (𝓝 (1/4)) := by
  choose p hl hp using fun i : ℕ => Nat.exists_infinite_primes (i+3)
  have hlarge (i : ℕ) : 2<p i := by have := hl i; omega
  choose M hM B hk hu hs hd hprof using fun i => prime_quotient (p i) (hp i) (hlarge i)
  have hpt : Tendsto p atTop atTop :=
    tendsto_atTop_mono (fun i => (show i≤p i by have := hl i; omega)) tendsto_id
  have hmt : Tendsto (fun i => (M i).val) atTop atTop := by
    apply tendsto_atTop_mono _ hpt
    intro i
    have hh := Nat.mul_le_mul_right (p i) (show 2≤p i-1 by have := hlarge i; omega)
    have := hM i
    omega
  have hm (i : ℕ) : 0<(M i : ℝ) := by exact_mod_cast (M i).pos
  have hpr (i : ℕ) : 0<(p i : ℝ) := by exact_mod_cast (hp i).pos
  have hmul (i : ℕ) : 2*(M i : ℝ)=((B i).card : ℝ)*p i := by
    rw [hk]; exact_mod_cast hM i
  have hr (i : ℕ) : ((B i).card : ℝ)=(p i : ℝ)-1 := by
    rw [hk,Nat.cast_sub (hp i).one_le,Nat.cast_one]
  have h₁ : Tendsto (fun i => ((B i).card : ℝ)/(M i : ℝ)) atTop (𝓝 0) := by
    apply ((tendsto_const_nhds (x := (2:ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop.comp hpt)).congr
    intro i
    exact (div_eq_div_iff (hpr i).ne' (hm i).ne').mpr (hmul i)
  have h₂ : Tendsto (fun i => ((B i).card : ℝ)^2/(M i : ℝ)) atTop (𝓝 2) := by
    have ht := (tendsto_const_nhds (x := (2:ℝ))).sub h₁
    rw [sub_zero] at ht
    apply ht.congr
    intro i
    field_simp [(hm i).ne']
    nlinarith [hmul i,hr i]
  have hsize := (Real.continuous_sqrt.tendsto (2:ℝ)).comp h₂
  refine ⟨M,hmt,B,hu,hs,?_,normalized_profile B hmt h₁ h₂ hs hd⟩
  simpa only [Function.comp_def,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
    using hsize

/-- If the seed misses a fraction h>0 and the candidate has normalized size c,
inserting o(√M) new labels leaves an asymptotic lower bound of h on its hole fraction. -/
theorem small_repairs {M : ℕ → ℕ+} (A B : (i : ℕ) → Finset (ZMod (M i))) {c h : ℝ}
    (hA : Tendsto (fun i => (countAt (A i) 0 : ℝ)/(M i : ℝ)) atTop (𝓝 h))
    (hB : Tendsto (fun i => ((B i).card : ℝ)/Real.sqrt (M i)) atTop (𝓝 c))
    (hedit : Tendsto (fun i => (((B i) \ (A i)).card : ℝ)/Real.sqrt (M i)) atTop (𝓝 0))
    {t : ℝ} (ht : t<h) :
    ∀ᶠ i in atTop, t<(countAt (B i) 0 : ℝ)/(M i : ℝ) := by
  have he := hA.sub (hedit.mul hB)
  rw [zero_mul,sub_zero] at he
  filter_upwards [he.eventually_const_lt ht] with i hi
  have hm : 0<(M i : ℝ) := by exact_mod_cast (M i).pos
  have hc : (countAt (A i) 0 : ℝ) ≤ countAt (B i) 0 +
      (((B i) \ (A i)).card : ℝ) * (B i).card := by exact_mod_cast repair_cost (A i) (B i)
  apply hi.trans_le
  rw [div_mul_div_comm,← sq,Real.sq_sqrt hm.le,← sub_div]
  exact (div_le_div_iff_of_pos_right hm).mpr (by linarith)

#print axioms graph_sidon
#print axioms cyclic_sidon_seed
#print axioms quotient_caps
#print axioms profile_error
#print axioms projected_profile
#print axioms prime_quotient
#print axioms sharp_cyclic_profile
#print axioms repair_cost
#print axioms small_repairs

end Green33SidonProfile
