import Green28PrimitiveSupport
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Typical output supports in Green 28

Bienvenu and Geroldinger, *On algebraic properties of power monoids of numerical
monoids*, Theorem 6.2, prove exponential rarity of decomposable integer interval
subsets. We use their sparse, small-summand, and many-translates cases in finite
abelian groups, counting choices on disjoint translates. Reduction modulo the
interval length transfers the group count to the original integer PMFs.
-/

namespace Green28TypicalSupports

open Finset
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A maximal disjoint family of translates controls the whole center set
by translates of the difference set, as in Ruzsa's covering lemma. -/
private theorem pack_translates (A D : Finset G) (ne : D.Nonempty) :
    ∃ F ⊆ A, (F : Set G).PairwiseDisjoint (fun a => a +ᵥ D) ∧ A.card ≤ F.card*(D.card*D.card) := by
  classical
  let C := A.powerset.filter (fun F : Finset G => (F : Set G).PairwiseDisjoint (fun a => a +ᵥ D))
  obtain ⟨F,hmax⟩ := C.exists_maximal (filter_nonempty_iff.mpr
    ⟨∅,empty_mem_powerset _,by simp [coe_empty]⟩)
  simp only [C,mem_filter,mem_powerset] at hmax
  obtain ⟨sub,disj⟩ := hmax.1
  have cover : A ⊆ F+(D-D) := by
    intro a ha
    by_cases ain : a ∈ F
    · exact subset_add_left _ ne.zero_mem_sub ain
    by_cases! h : ∀ b ∈ F, Disjoint (a +ᵥ D) (b +ᵥ D)
    · apply (hmax.not_gt ?_ (ssubset_insert ain)).elim
      rw [insert_subset_iff,coe_insert]
      exact ⟨⟨ha,sub⟩,disj.insert fun b hb _ => h b hb⟩
    simp_rw [not_disjoint_iff,←neg_vadd_mem_iff] at h
    obtain ⟨b,hb,c,ha',hb'⟩ := h
    exact mem_add.mpr ⟨b,hb,-b+a,mem_sub.mpr ⟨_,hb',_,ha',by simp⟩,by abel⟩
  exact ⟨F,sub,disj,(card_le_card cover).trans
    (card_add_le.trans (Nat.mul_le_mul_left _ card_sub_le))⟩

private noncomputable def avoiding {α ι : Type*} [DecidableEq α] (U : Finset α) (T : Finset ι)
    (D P : ι → Finset α) : Finset (Finset α) := by
  classical
  exact U.powerset.filter (fun S => ∀ i ∈ T, S∩D i ≠ P i)

/-- On disjoint blocks of size `k`, forbidding one pattern per block leaves
at most `2^k-1` choices on each block. -/
private theorem count_avoiding {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (T : Finset ι) (D P : ι → Finset α) (k : ℕ)
    (incl : ∀ i ∈ T, D i ⊆ U) (pat : ∀ i ∈ T, P i ⊆ D i) (size : ∀ i ∈ T, (D i).card=k)
    (disj : (T:Set ι).PairwiseDisjoint D) :
    (avoiding U T D P).card ≤ 2^(U.card-T.card*k)*(2^k-1)^T.card := by
  classical
  induction T using Finset.induction_on generalizing U with
  | empty => simp [avoiding]
  | @insert i T fresh ih =>
    have di := incl i (mem_insert_self _ _)
    have pi := pat i (mem_insert_self _ _)
    have si := size i (mem_insert_self _ _)
    have sep (j : ι) (hj : j ∈ T) : Disjoint (D i) (D j) :=
      disj (mem_insert_self _ _) (mem_insert_of_mem hj) (fun e => fresh (e ▸ hj))
    have sub (j : ι) (hj : j ∈ T) : D j ⊆ U \ D i := fun x hx =>
      mem_sdiff.mpr ⟨incl j (mem_insert_of_mem hj) hx, fun h => disjoint_left.mp (sep j hj) h hx⟩
    have tail := ih (U \ D i) sub (fun j hj => pat j (mem_insert_of_mem hj))
      (fun j hj => size j (mem_insert_of_mem hj)) (fun _ ha _ hb => disj (mem_insert_of_mem ha) (mem_insert_of_mem hb))
    let choices := (D i).powerset.erase (P i)
    have maps : (avoiding U (insert i T) D P).card ≤ (choices ×ˢ avoiding (U \ D i) T D P).card := by
      apply card_le_card_of_injOn (fun S : Finset α => (S∩D i,S \ D i))
      · intro S hS
        obtain ⟨hU,hA⟩ := (mem_filter.mp hS)
        have sU := mem_powerset.mp hU
        apply mem_product.mpr
        refine ⟨mem_erase.mpr ⟨hA i (mem_insert_self _ _),mem_powerset.mpr inter_subset_right⟩,?_⟩
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr (fun _ hx => mem_sdiff.mpr ⟨sU (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩),?_⟩
        intro j hj
        have eq : (S \ D i)∩D j=S∩D j := by
          ext x; simp only [mem_inter,mem_sdiff]; grind [disjoint_left.mp (sep j hj)]
        rw [eq]
        exact hA j (mem_insert_of_mem hj)
      · intro A _ B _ eq
        have ha := congrArg Prod.fst eq
        have hb := congrArg Prod.snd eq
        ext x; by_cases h : x ∈ D i
        · simpa [h] using congrArg (fun W : Finset α => x ∈ W) ha
        · simpa [h] using congrArg (fun W : Finset α => x ∈ W) hb
    have num : choices.card=2^k-1 := by dsimp only [choices]; rw [card_erase_of_mem (mem_powerset.mpr pi),card_powerset,si]
    rw [card_product,num] at maps
    refine maps.trans ((Nat.mul_le_mul_left _ tail).trans_eq ?_)
    rw [card_sdiff_of_subset di,si,card_insert_of_notMem fresh,Nat.succ_mul,pow_succ]
    rw [Nat.sub_sub,add_comm k]
    ring

/-- Every occupied point of a sumset with summand `C` has an occupied
neighbor in a fixed set of at most `|C|+1` offsets. -/
private theorem neighbor_offsets (C : Finset G) (two : 2 ≤ C.card) :
    ∃ E : Finset G, 0 ∈ E ∧ E.card ≤ C.card+1 ∧
      ∀ (B : Finset G) (x : G), x ∈ B+C → ∃ e ∈ E, e ≠ 0 ∧ x+e ∈ B+C := by
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp (by omega : 1<C.card)
  let E := insert (v-u) (C.image (fun z => u-z))
  refine ⟨E,mem_insert_of_mem (mem_image.mpr ⟨u,hu,sub_self u⟩),?_,?_⟩
  · exact (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)
  · intro B x hx
    obtain ⟨b,hb,c,hc,rfl⟩ := mem_add.mp hx
    by_cases cu : c=u
    · subst c
      exact ⟨v-u,mem_insert_self _ _,sub_ne_zero.mpr uv.symm,
        by rw [show b+u+(v-u)=b+v by abel]; exact add_mem_add hb hv⟩
    · exact ⟨u-c,mem_insert_of_mem (mem_image.mpr ⟨c,hc,rfl⟩),sub_ne_zero.mpr (Ne.symm cu),
        by rw [show b+c+(u-c)=b+u by abel]; exact add_mem_add hb hu⟩

private noncomputable def with_summand [Fintype G] (C : Finset G) : Finset (Finset G) := by
  classical
  exact univ.filter (fun S : Finset G => ∃ B : Finset G, S=B+C)

private theorem small_summand_blocks [Fintype G] (C : Finset G) (two : 2 ≤ C.card) :
    ∃ k l : ℕ, 0<k ∧ k ≤ C.card+1 ∧ l*k ≤ Fintype.card G ∧ Fintype.card G ≤ l*(k*k) ∧
      (with_summand C).card ≤ 2^(Fintype.card G-l*k)*(2^k-1)^l := by
  classical
  obtain ⟨E,zero,le,neighbor⟩ := neighbor_offsets C two
  obtain ⟨F,_,disj,pack⟩ := pack_translates univ E ⟨0,zero⟩
  let D (i : G) := i +ᵥ E
  let P (i : G) : Finset G := {i}
  have mem (i : G) : i ∈ D i := by simpa only [D,vadd_eq_add,add_zero] using vadd_mem_vadd_finset (a:=i) zero
  have n := (card_le_univ (F+E))
  rw [card_add_iff.mpr (pairwiseDisjoint_vadd_iff.mp disj)] at n
  refine ⟨E.card,F.card,card_pos.mpr ⟨0,zero⟩,le,n,by simpa using pack,?_⟩
  have count := count_avoiding (univ:Finset G) F D P E.card (fun _ _ => subset_univ _)
    (fun i _ => singleton_subset_iff.mpr (mem i)) (fun i _ => card_vadd_finset i E) disj
  apply (card_le_card (t:=avoiding univ F D P) ?_).trans (by simpa using count)
  intro S hS
  obtain ⟨B,rfl⟩ := (mem_filter.mp hS).2
  simp only [avoiding,mem_filter,mem_powerset]
  refine ⟨subset_univ _,?_⟩
  intro i _ eq
  have hmem : i ∈ (B+C)∩D i := by rw [eq]; exact mem_singleton_self i
  have hi : i ∈ B+C := (mem_inter.mp hmem).1
  obtain ⟨e,he,nz,hit⟩ := neighbor B i hi
  have h : i+e ∈ (B+C)∩D i := mem_inter.mpr ⟨hit,vadd_mem_vadd_finset (a:=i) he⟩
  rw [eq] at h
  exact nz (by simpa [P] using h)

private noncomputable def supersets [Fintype G] (A : Finset G) : Finset (Finset G) :=
  univ.filter (fun S : Finset G => A ⊆ S)

omit [AddCommGroup G] in
private theorem count_supersets [Fintype G] (A : Finset G) :
    (supersets A).card ≤ 2^(Fintype.card G-A.card) := by
  have inj : (supersets A).card ≤ ((univ \ A).powerset).card := by
    apply card_le_card_of_injOn (fun S : Finset G => S \ A)
    · intro S _
      exact mem_powerset.mpr (fun x hx => mem_sdiff.mpr ⟨mem_univ x,(mem_sdiff.mp hx).2⟩)
    · intro S hs T ht eq
      have s := (mem_filter.mp hs).2
      have t := (mem_filter.mp ht).2
      ext x; by_cases h : x ∈ A
      · exact iff_of_true (s h) (t h)
      · simpa [h] using congrArg (fun X : Finset G => x ∈ X) eq
  simpa only [card_powerset,card_sdiff_of_subset (subset_univ A),card_univ] using inj

private noncomputable def packings [Fintype G] (D : Finset G) (k : ℕ) : Finset (Finset G) := by
  classical
  exact ((univ.powersetCard k).filter (fun F : Finset G => (F : Set G).PairwiseDisjoint (fun a => a +ᵥ D))).biUnion
    (fun F => supersets (F+D))

private theorem count_packings [Fintype G] (D : Finset G) (k : ℕ) :
    (packings D k).card ≤ (Fintype.card G).choose k * 2^(Fintype.card G-k*D.card) := by
  classical
  let sets := (univ.powersetCard k).filter (fun F : Finset G => (F : Set G).PairwiseDisjoint (fun a => a +ᵥ D))
  have every (F : Finset G) (h : F ∈ sets) :
      (supersets (F+D)).card ≤ 2^(Fintype.card G-k*D.card) := by
    obtain ⟨size,disj⟩ := mem_filter.mp h
    simpa only [card_add_iff.mpr (pairwiseDisjoint_vadd_iff.mp disj),(mem_powersetCard.mp size).2]
      using count_supersets (F+D)
  have num : sets.card ≤ (Fintype.card G).choose k := by
    simpa only [card_powersetCard,card_univ] using card_filter_le (univ.powersetCard k) (fun F : Finset G =>
      (F:Set G).PairwiseDisjoint (fun a => a +ᵥ D))
  exact card_biUnion_le.trans ((sum_le_card_nsmul sets _ _ every).trans (Nat.mul_le_mul_right _ num))

/-- A dense summand supplies enough disjoint translates of a 16-point subset
from the other summand. Each chosen translate must lie inside the output. -/
private theorem large_shape [Fintype G] (B C : Finset G) (b : Fintype.card G ≤ 32*B.card)
    (c : 16 ≤ C.card) :
    ∃ D ∈ (univ : Finset G).powersetCard 16, B+C ∈ packings D (Fintype.card G/8192) := by
  classical
  obtain ⟨D,subD,size⟩ := exists_subset_card_eq c
  have ne : D.Nonempty := card_pos.mp (by omega)
  obtain ⟨F,subF,disj,bnd⟩ := pack_translates B D ne
  rw [size] at bnd
  obtain ⟨T,subT,num⟩ := exists_subset_card_eq (by omega : Fintype.card G/8192 ≤ F.card)
  refine ⟨D,mem_powersetCard.mpr ⟨subset_univ _,size⟩,?_⟩
  apply mem_biUnion.mpr
  refine ⟨T,?_,?_⟩
  · apply mem_filter.mpr
    exact ⟨mem_powersetCard.mpr ⟨subset_univ _,num⟩,fun _ hx _ hy => disj (subT hx) (subT hy)⟩
  · exact mem_filter.mpr ⟨mem_univ _,add_subset_add (subT.trans subF) subD⟩

private theorem subset_weights {α : Type*} [DecidableEq α] (U : Finset α) (t : ℝ) :
    ∑ S ∈ U.powerset, t^S.card=(1+t)^U.card := by
  simpa [add_comm t 1] using (prod_add (fun _ : α => t) (fun _ => (1:ℝ)) U).symm

private noncomputable def small_sets {α : Type*} [DecidableEq α] (U : Finset α) (k : ℕ) :=
  U.powerset.filter (fun S => S.card ≤ k)

private theorem count_small_sets {α : Type*} [DecidableEq α] (U : Finset α) (k : ℕ) :
    ((small_sets U k).card : ℝ) ≤ 4^k*(5/4:ℝ)^U.card := by
  classical
  let W := small_sets U k
  have bound (S : Finset α) (h : S ∈ W) : (1:ℝ) ≤ 4^k*(1/4:ℝ)^S.card := by
    rw [div_pow,one_pow,mul_one_div,le_div_iff₀ (by positivity),one_mul]
    exact pow_le_pow_right₀ (by norm_num) (mem_filter.mp h).2
  calc
    (W.card:ℝ) = ∑ _S ∈ W, (1:ℝ) := by simp
    _ ≤ ∑ S ∈ W, 4^k*(1/4:ℝ)^S.card := sum_le_sum bound
    _ = 4^k * ∑ S ∈ W, (1/4:ℝ)^S.card := (mul_sum ..).symm
    _ ≤ 4^k * ∑ S ∈ U.powerset, (1/4:ℝ)^S.card := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by rw [subset_weights]; norm_num

private theorem choose_weight (n k : ℕ) (t : ℝ) (ht : 0 ≤ t) : n.choose k*t^k ≤ (1+t)^n := by
  classical
  let U := range n
  calc
    (n.choose k : ℝ)*t^k = ∑ S ∈ U.powersetCard k, t^S.card := by
      rw [sum_congr rfl (g:=fun _ => t^k) (fun S h => by rw [(mem_powersetCard.mp h).2])]
      simp [U]
    _ ≤ ∑ S ∈ U.powerset, t^S.card := sum_le_sum_of_subset_of_nonneg
      (fun S h => mem_powerset.mpr (mem_powersetCard.mp h).1) (fun _ _ _ => by positivity)
    _ = _ := by rw [subset_weights]; simp [U]

/-- A single base works in all three counting estimates. -/
private noncomputable def rate : ℝ := 1-1/16777216

private theorem rate_pos : 0 < rate := by norm_num [rate]
private theorem rate_lt_one : rate < 1 := by norm_num [rate]

private theorem sparse_bound (n : ℕ) :
    (4^(n/32)*(5/4:ℝ)^n)^2 ≤ (2*rate)^n := by
  have h : (4:ℝ)^(n/32) ≤ (11/10:ℝ)^n := calc
    _ ≤ ((11/10:ℝ)^32)^(n/32) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = _ ^ (32*(n/32)) := (pow_mul ..).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ ((11/10:ℝ)^n*(5/4:ℝ)^n)^2 := by gcongr
    _ = ((11/10:ℝ)*(5/4))^(2*n) := by rw [←mul_pow,←pow_mul]; congr 1; omega
    _ = (((11/10:ℝ)*(5/4))^2)^n := pow_mul ..
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num [rate]) _

/-- Each forbidden pattern saves a factor of at least `2⁻¹⁶` on its block. -/
private theorem block_bound (n k l : ℕ) (small : k ≤ 16) (fit : l*k ≤ n) (pack : n ≤ l*(k*k)) :
    ((2^(n-l*k)*(2^k-1)^l : ℕ) : ℝ) ≤ (2*rate)^n := by
  have den : 1 ≤ 2^k := Nat.one_le_two_pow
  have scale : (2:ℝ)^k ≤ 65536 := by
    simpa only [show (2:ℝ)^16=65536 by norm_num] using (pow_le_pow_right₀ (by norm_num) small : (2:ℝ)^k ≤ 2^16)
  have bern := one_add_mul_le_pow (a:=-(1/16777216:ℝ)) (by norm_num) 256
  have q : (1-1/65536:ℝ) ≤ rate^256 := by
    change _ ≤ (1+ -(1/16777216:ℝ))^256
    exact le_trans (by norm_num : (1-1/65536:ℝ) ≤ 1+(256:ℝ)* -(1/16777216:ℝ)) bern
  have oneblock : (2:ℝ)^k-1 ≤ 2^k*rate^256 :=
    (show (2:ℝ)^k-1 ≤ 2^k*(1-1/65536) by linarith).trans
      (mul_le_mul_of_nonneg_left q (by positivity))
  have fit' : n ≤ 256*l := pack.trans (by nlinarith [Nat.mul_le_mul small small])
  push_cast [Nat.cast_sub den]
  calc
    _ ≤ (2:ℝ)^(n-l*k)*(2^k*rate^256)^l := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (sub_nonneg.mpr (by exact_mod_cast den)) oneblock _
    _ = 2^n * rate^(256*l) := by
      rw [mul_pow,←pow_mul,←pow_mul,←mul_assoc,←pow_add,show n-l*k+k*l=n by rw [Nat.mul_comm k l,Nat.sub_add_cancel fit]]
    _ ≤ 2^n*rate^n := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one rate_pos.le rate_lt_one.le fit') (by positivity)
    _ = _ := (mul_pow ..).symm

private theorem dense_bound (n : ℕ) :
    ((n.choose (n/8192) * 2^(n-(n/8192)*16) : ℕ) : ℝ) ≤ 8*(2*rate)^n := by
  let k := n/8192
  have slots : k*16 ≤ n := by dsimp [k]; omega
  have block : (1+1/4096:ℝ)^8192 ≤ 8 := calc
    _ ≤ (Real.exp (1/4096))^8192 := pow_le_pow_left₀ (by norm_num)
      (by simpa only [add_comm] using Real.add_one_le_exp (1/4096)) _
    _ = Real.exp 1 ^ 2 := by rw [←Real.exp_nat_mul,←Real.exp_nat_mul]; norm_num
    _ ≤ 8 := by nlinarith [Real.exp_one_lt_d9,Real.exp_pos 1,
      pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2]
  have growth : (1+1/8192:ℝ)^n ≤ 8^(k+1)*rate^n := calc
    _ ≤ ((1+1/4096:ℝ)*rate)^n := pow_le_pow_left₀ (by norm_num) (by norm_num [rate]) _
    _ = (1+1/4096:ℝ)^n*rate^n := mul_pow ..
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg rate_pos.le _)
      calc
        _ ≤ (1+1/4096:ℝ)^(8192*(k+1)) := pow_le_pow_right₀ (by norm_num) (by dsimp [k]; omega)
        _ = ((1+1/4096:ℝ)^8192)^(k+1) := pow_mul ..
        _ ≤ _ := pow_le_pow_left₀ (by positivity) block _
  have weights := (choose_weight n k (1/8192) (by norm_num)).trans growth
  have cost : (2:ℝ)^(k*16)*(1/8192:ℝ)^k = 8^k := by
    rw [Nat.mul_comm k 16,pow_mul,←mul_pow]; norm_num
  have extpow : (2:ℝ)^(n-k*16)*2^(k*16)=2^n := by rw [←pow_add,Nat.sub_add_cancel slots]
  change (↑(n.choose k * 2^(n-k*16)):ℝ) ≤ _
  push_cast
  rw [mul_pow]
  apply le_of_mul_le_mul_right (a:=(1/8192:ℝ)^k) _ (by positivity)
  calc
    _ = ((n.choose k:ℝ)*(1/8192:ℝ)^k)*2^(n-k*16) := by ring
    _ ≤ (8^(k+1)*rate^n)*2^(n-k*16) := mul_le_mul_of_nonneg_right weights (by positivity)
    _ = _ := by rw [pow_succ,←cost,←extpow]; ring

/-- Supports admitting a sumset decomposition with two summands of size at least two. -/
noncomputable def nontrivialSumsets (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G] :
    Finset (Finset G) := by
  classical
  exact univ.filter (fun S : Finset G => ∃ B C : Finset G, 2 ≤ B.card ∧ 2 ≤ C.card ∧ S=B+C)

private theorem count_small_shapes [Fintype G] :
    ((small_sets (univ:Finset G) 15).filter (fun C => 2 ≤ C.card)).card ≤ 16*(Fintype.card G)^16 := by
  classical
  let n := Fintype.card G
  let U := (univ:Finset G)
  have bound (j : ℕ) (hj : j ∈ range 16) : (U.powersetCard j).card ≤ n^16 := by
    rw [card_powersetCard]
    exact (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_right Fintype.card_pos (by have := mem_range.mp hj; omega))
  have incl : ((small_sets U 15).filter (fun C => 2 ≤ C.card)) ⊆ (range 16).biUnion U.powersetCard := by
    intro C h
    have hc := (mem_filter.mp (mem_filter.mp h).1).2
    exact mem_biUnion.mpr ⟨C.card,mem_range.mpr (by omega),mem_powersetCard.mpr ⟨subset_univ _,rfl⟩⟩
  exact (card_le_card incl).trans <| card_biUnion_le.trans <| by
    simpa using sum_le_card_nsmul (range 16) _ _ bound

private theorem finite_bound [Fintype G] :
    ((nontrivialSumsets G).card:ℝ) ≤ 25*(Fintype.card G:ℝ)^16*(2*rate)^(Fintype.card G) := by
  classical
  let n := Fintype.card G
  let U := (univ:Finset G)
  let sparse := small_sets U (n/32)
  -- Sparse pairs, small summands, and dense translate packings cover all decompositions.
  let A := (sparse ×ˢ sparse).image (fun p : Finset G × Finset G => p.1+p.2)
  let small := (small_sets U 15).filter (fun C => 2 ≤ C.card)
  let B := small.biUnion with_summand
  let C := (U.powersetCard 16).biUnion (fun D => packings D (n/8192))
  have cover (X Y : Finset G) (two : 2 ≤ Y.card) (ord : Y.card ≤ X.card) : X+Y ∈ (A∪B)∪C := by
    by_cases little : Y.card ≤ 15
    · apply mem_union_left
      apply mem_union_right
      exact mem_biUnion.mpr ⟨Y,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),little⟩,two⟩,
        mem_filter.mpr ⟨mem_univ _,X,rfl⟩⟩
    by_cases large : n ≤ 32*X.card
    · exact mem_union_right _ (mem_biUnion.mpr (large_shape X Y large (by omega)))
    · have x : X ∈ sparse := mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),by omega⟩
      have y : Y ∈ sparse := mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),by omega⟩
      exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨(X,Y),mem_product.mpr ⟨x,y⟩,rfl⟩))
  have incl : nontrivialSumsets G ⊆ (A∪B)∪C := by
    intro S h
    obtain ⟨X,Y,hX,hY,rfl⟩ := (mem_filter.mp h).2
    rcases le_total Y.card X.card with h|h
    · exact cover X Y hY h
    · rw [add_comm]; exact cover Y X hX h
  have total : (nontrivialSumsets G).card ≤ A.card+B.card+C.card :=
    (card_le_card incl).trans <| (card_union_le (A∪B) C).trans (Nat.add_le_add_right (card_union_le A B) _)
  have sa : (A.card:ℝ) ≤ (2*rate)^n := calc
    _ ≤ (sparse.card:ℝ)^2 := by exact_mod_cast
      (card_image_le.trans_eq (by rw [card_product,pow_two]) : A.card ≤ sparse.card^2)
    _ ≤ _ := (pow_le_pow_left₀ (by positivity) (by simpa only [U,card_univ] using count_small_sets U (n/32)) 2).trans
      (sparse_bound n)
  have npos : 1 ≤ n := Fintype.card_pos
  have power : (1:ℝ) ≤ (n:ℝ)^16 := one_le_pow₀ (by exact_mod_cast npos)
  have sb : (B.card:ℝ) ≤ 16*(n:ℝ)^16*(2*rate)^n := calc
    _ ≤ ∑ D ∈ small, ((with_summand D).card:ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _D ∈ small, (2*rate)^n := by
      apply sum_le_sum
      intro D hd
      obtain ⟨hD,two⟩ := mem_filter.mp hd
      have sz := (mem_filter.mp hD).2
      obtain ⟨k,l,_,hk,fit,pack,bnd⟩ := small_summand_blocks D two
      exact (show ((with_summand D).card:ℝ)≤ _ by exact_mod_cast bnd).trans
        (block_bound n k l (by omega) fit pack)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast count_small_shapes (G:=G))
        (pow_nonneg (mul_nonneg (by norm_num) rate_pos.le) _)
  have sc : (C.card:ℝ) ≤ (n:ℝ)^16*(8*(2*rate)^n) := calc
    _ ≤ ∑ D ∈ U.powersetCard 16, ((packings D (n/8192)).card:ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _D ∈ U.powersetCard 16, 8*(2*rate)^n := by
      apply sum_le_sum
      intro D hD
      have bnd := count_packings D (n/8192)
      rw [(mem_powersetCard.mp hD).2] at bnd
      exact (show ((packings D (n/8192)).card:ℝ)≤ _ by exact_mod_cast bnd).trans (dense_bound n)
    _ ≤ _ := by
      simp only [sum_const,nsmul_eq_mul,card_powersetCard,U,card_univ]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_pow n 16)
        (by have := rate_pos; positivity)
  have total' : ((nontrivialSumsets G).card:ℝ) ≤ A.card+B.card+C.card := by exact_mod_cast total
  have z : 0 ≤ (2*rate)^n := by have := rate_pos; positivity
  exact total'.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr power) z])

/-- An explicit finite upper bound uniform in the isomorphism type of the group. -/
theorem card_nontrivialSumsets_le [Fintype G] :
    ((nontrivialSumsets G).card:ℝ) ≤
      25*(Fintype.card G:ℝ)^16*(2-1/8388608:ℝ)^(Fintype.card G) := by
  simpa only [show 2*rate=2-1/8388608 by norm_num [rate]] using finite_bound (G:=G)

open Filter
open scoped Topology

/-- For some absolute `c<2` and all sufficiently large orders `n`, at most
`c^n` of the `2^n` subsets of any abelian group of order `n` split nontrivially. -/
theorem exponentially_few_sumsets :
    ∃ c : ℝ, 0<c ∧ c<2 ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : Type*) [AddCommGroup G] [DecidableEq G] [Fintype G], Fintype.card G=n →
        ((nontrivialSumsets G).card:ℝ) ≤ c^n := by
  let c := 1+rate
  have cpos : 0<c := by dsimp [c]; linarith [rate_pos]
  have gap : 2*rate/c < 1 := (div_lt_one cpos).mpr (by dsimp [c]; linarith [rate_lt_one])
  have conv := (tendsto_pow_const_mul_const_pow_of_lt_one 16
    (div_nonneg (by linarith [rate_pos]) cpos.le) gap).const_mul (25:ℝ)
  have ev := conv.eventually_lt_const (show (25:ℝ)*0<1 by norm_num)
  refine ⟨c,cpos,by dsimp [c]; linarith [rate_lt_one],?_⟩
  filter_upwards [ev] with n hn
  intro G _ _ _ eq
  have h := finite_bound (G:=G)
  rw [eq] at h
  refine h.trans ?_
  change 25*((n:ℝ)^16*(2*rate/c)^n) < 1 at hn
  rw [div_pow,←mul_div_assoc,←mul_div_assoc,div_lt_one (pow_pos cpos _)] at hn
  linarith [hn.le]


open Green28

/-- The canonical representatives of a cyclic subset, shifted into an integer interval. -/
def integerSites {n : ℕ} (d : ℤ) (T : Finset (ZMod n)) : Finset ℤ :=
  T.image (fun x => d+(x.val:ℤ))

private theorem support_sum_iff (P Q : PMF ℤ) (z : ℤ) :
    z ∈ (indepSum P Q).support ↔ ∃ x ∈ P.support, ∃ y ∈ Q.support, x+y=z := by
  change z ∈ (P.bind (fun x => Q.bind (fun y => PMF.pure (x+y)))).support ↔ _
  simp only [PMF.mem_support_bind_iff,PMF.mem_support_pure_iff,eq_comm (a:=z)]

private theorem pure_of_subsingleton (P : PMF ℤ) (h : P.support.Subsingleton) :
    ∃ x, P=PMF.pure x := by
  obtain ⟨x,hx⟩ := P.support_nonempty
  refine ⟨x,PMF.ext fun y => ?_⟩
  by_cases eq : y=x
  · subst y
    simpa only [PMF.pure_apply_self] using (P.apply_eq_one_iff x).mpr (h.eq_singleton_of_mem hx)
  · rw [(P.apply_eq_zero_iff y).mpr (fun hy => eq (h hy hx))]
    simp [PMF.pure_apply,eq]

private noncomputable def reduced {n : ℕ} [NeZero n] (P : PMF ℤ) (f : ℤ → ZMod n) :
    Finset (ZMod n) := (f '' P.support).toFinite.toFinset

private theorem mem_reduced {n : ℕ} [NeZero n] {P : PMF ℤ} {f : ℤ → ZMod n} {z : ZMod n} :
    z ∈ reduced P f ↔ ∃ x ∈ P.support, f x=z := Set.Finite.mem_toFinset _

private theorem two_reduced {n : ℕ} [NeZero n] (P : PMF ℤ) (f : ℤ → ZMod n)
    (inj : Set.InjOn f P.support) (nonpure : ¬∃ x, P=PMF.pure x) : 2 ≤ (reduced P f).card := by
  by_contra! small
  apply nonpure
  apply pure_of_subsingleton
  intro x hx y hy
  apply inj hx hy
  apply (Finset.card_le_one.mp (by omega : (reduced P f).card ≤ 1))
  · exact mem_reduced.mpr ⟨x,hx,rfl⟩
  · exact mem_reduced.mpr ⟨y,hy,rfl⟩

/-- Outside the cyclic exceptional family, every independent integer sum whose
support is exactly the shifted set of representatives has a point-mass summand.
The weights may be arbitrary. -/
theorem pure_of_typical_support {n : ℕ} [NeZero n] (d : ℤ) {T : Finset (ZMod n)}
    (good : T ∉ nontrivialSumsets (ZMod n)) {P Q : PMF ℤ}
    (out : (indepSum P Q).support = (integerSites d T:Set ℤ)) :
    (∃ x, P=PMF.pure x) ∨ (∃ y, Q=PMF.pure y) := by
  classical
  by_contra! both
  let f (x : ℤ) : ZMod n := (x-d:ℤ)
  let g (y : ℤ) : ZMod n := y
  have inverse (t : ZMod n) : f (d+(t.val:ℤ))=t := by simp [f]
  have inj : Set.InjOn f (indepSum P Q).support := by
    intro x hx y hy eq
    rw [out] at hx hy
    obtain ⟨s,_,rfl⟩ := mem_image.mp hx
    obtain ⟨t,_,rfl⟩ := mem_image.mp hy
    rw [inverse,inverse] at eq
    rw [eq]
  have adds (x y : ℤ) : f (x+y)=f x+g y := by simp [f,g]; abel
  have sum_mem {x y : ℤ} (hx : x ∈ P.support) (hy : y ∈ Q.support) :=
    (support_sum_iff P Q (x+y)).mpr ⟨x,hx,y,hy,rfl⟩
  have fi : Set.InjOn f P.support := by
    obtain ⟨b,hb⟩ := Q.support_nonempty
    intro x hx y hy eq
    exact add_right_cancel (inj (sum_mem hx hb) (sum_mem hy hb) (by simp only [adds,eq]))
  have gi : Set.InjOn g Q.support := by
    obtain ⟨a,ha⟩ := P.support_nonempty
    intro x hx y hy eq
    exact add_left_cancel (inj (sum_mem ha hx) (sum_mem ha hy) (by simp only [adds,eq]))
  apply good
  apply mem_filter.mpr
  refine ⟨mem_univ _,reduced P f,reduced Q g,two_reduced P f fi (by simpa using both.1),
    two_reduced Q g gi (by simpa using both.2),?_⟩
  ext z
  constructor
  · intro hz
    have mem : d+(z.val:ℤ) ∈ (indepSum P Q).support := by
      rw [out]; exact mem_image.mpr ⟨z,hz,rfl⟩
    obtain ⟨x,hx,y,hy,eq⟩ := (support_sum_iff P Q _).mp mem
    refine mem_add.mpr ⟨f x,mem_reduced.mpr ⟨x,hx,rfl⟩,
      g y,mem_reduced.mpr ⟨y,hy,rfl⟩,?_⟩
    rw [←adds,eq,inverse]
  · intro hz
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hz
    obtain ⟨x,hx,rfl⟩ := mem_reduced.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_reduced.mp hb
    have mem := sum_mem hx hy
    rw [out] at mem
    obtain ⟨t,ht,eq⟩ := mem_image.mp mem
    rwa [←adds,←eq,inverse]

/-- For all large interval lengths, at most exponentially few supports can evade
the point-mass conclusion. In particular Green's two uniformity conclusions
hold on all remaining supports, in every translate of the interval. -/
theorem typical_green_28 :
    ∃ c : ℝ, 0<c ∧ c<2 ∧ ∀ᶠ n : ℕ in atTop, ∀ [NeZero n],
      ∃ E : Finset (Finset (ZMod n)), (E.card:ℝ) ≤ c^n ∧
        ∀ T ∉ E, ∀ d : ℤ, ∀ P Q : PMF ℤ,
          (indepSum P Q).support = (integerSites d T:Set ℤ) →
            ((∃ x, P=PMF.pure x) ∨ (∃ y, Q=PMF.pure y)) ∧
            (IsUniformOnSupport (indepSum P Q) → IsUniformOnSupport P ∧ IsUniformOnSupport Q) := by
  obtain ⟨c,pos,lt,ev⟩ := exponentially_few_sumsets.{0}
  refine ⟨c,pos,lt,?_⟩
  filter_upwards [ev] with n hn
  intro inst
  refine ⟨nontrivialSumsets (ZMod n),hn (ZMod n) (ZMod.card n),?_⟩
  intro T hT d P Q eq
  have pure := pure_of_typical_support d hT eq
  exact ⟨pure,fun flat => Green28PrimitiveSupport.uniform_of_pure_factor flat pure⟩

#print axioms card_nontrivialSumsets_le
#print axioms exponentially_few_sumsets
#print axioms pure_of_typical_support
#print axioms typical_green_28

end Green28TypicalSupports
