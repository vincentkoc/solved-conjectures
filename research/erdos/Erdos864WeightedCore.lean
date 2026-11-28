import FormalConjectures.ErdosProblems.«864»
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-! A weighted difference bound for interval sets with at most one repeated sum. -/

open Finset Filter
open scoped Topology

namespace Erdos864WeightedCore

/-- A center may be chosen arbitrarily when no sum repeats. -/
def OnlyAt (A : Finset ℕ) (c : ℕ) :=
  ∀ n, 1 < (Erdos864.sumRepresentations A n).card → n=c

theorem exists_center {A : Finset ℕ} (hA : Erdos864.HasAtMostOneRepeatedSum A) :
    ∃ c, OnlyAt A c := by
  by_cases h : ∃ n, 1 < (Erdos864.sumRepresentations A n).card
  · obtain ⟨c,hc⟩ := h
    exact ⟨c,fun n hn => hA n c hn hc⟩
  · exact ⟨0,fun n hn => False.elim (h ⟨n,hn⟩)⟩

/-- The subset whose reflection across c/2 stays inside A. -/
def core (A : Finset ℕ) (c : ℕ) := A.filter fun x => ∃ y ∈ A, x+y=c

noncomputable def weight (A : Finset ℕ) (c x : ℕ) : ℝ :=
  if x ∈ core A c then 1 else Real.sqrt 2

private lemma ordered_rep {A : Finset ℕ} {x y : ℕ} (hx : x∈A) (hy : y∈A) :
    (min x y,max x y) ∈ Erdos864.sumRepresentations A (x+y) := by
  by_cases h : x≤y
  · simp [Erdos864.sumRepresentations,hx,hy,h]
  · have h' := (Nat.lt_of_not_ge h).le
    simp [Erdos864.sumRepresentations,hx,hy,h',add_comm]

/-- Two distinct starts of the same positive difference pair up across the exceptional center. -/
private lemma cross_sum {A : Finset ℕ} {c t x y : ℕ} (hc : OnlyAt A c) (ht : 0<t)
    (hx : x∈A) (hxt : x+t ∈ A) (hy : y∈A) (hyt : y+t ∈ A) (hne : x≠y) :
    x+y+t=c := by
  apply hc
  apply one_lt_card.mpr
  refine ⟨_,(show x+t+y=x+y+t by omega) ▸ ordered_rep hxt hy,
    _,(show x+(y+t)=x+y+t by omega) ▸ ordered_rep hx hyt,?_⟩
  intro he
  have hlo := congrArg Prod.fst he
  have hhi := congrArg Prod.snd he
  change min (x+t) y = min x (y+t) at hlo
  change max (x+t) y = max x (y+t) at hhi
  omega

/-- Every positive shift carries total weighted difference mass at most two.
A reflected label has weight one and an unpaired label has weight √2. -/
theorem weighted_shift (A : Finset ℕ) {c : ℕ} (hc : OnlyAt A c) {t : ℕ} (ht : 0<t) :
    ∑ x ∈ A.filter (fun x => x+t∈A), weight A c x * weight A c (x+t) ≤ 2 := by
  classical
  let D := A.filter fun x => x+t∈A
  have hf {x y : ℕ} (hx : x∈D) (hy : y∈D) (hne : x≠y) : x+y+t=c :=
    cross_sum hc ht (mem_filter.mp hx).1 (mem_filter.mp hx).2
      (mem_filter.mp hy).1 (mem_filter.mp hy).2 hne
  by_cases hh : 1 < D.card
  · obtain ⟨x,hx,y,hy,hne⟩ := one_lt_card.mp hh
    have hxy := hf hx hy hne
    have hp : D = {x,y} := by
      ext z
      simp only [mem_insert,mem_singleton]
      constructor
      · intro hz
        by_cases he : z=x
        · exact Or.inl he
        · have h := hf hx hz (Ne.symm he)
          exact Or.inr (by omega)
      · rintro (rfl|rfl) <;> assumption
    have pair {a b : ℕ} (ha : a∈A) (hb : b∈A) (he : a+b=c) : weight A c a = 1 := by
      simp [weight,core,ha,show ∃ y ∈ A, a+y=c from ⟨b,hb,he⟩]
    have hx₁ := (mem_filter.mp hx).1
    have hx₂ := (mem_filter.mp hx).2
    have hy₁ := (mem_filter.mp hy).1
    have hy₂ := (mem_filter.mp hy).2
    change ∑ z ∈ D, _ ≤ _
    rw [hp,sum_pair hne]
    rw [pair hx₁ hy₂ (by omega),pair hx₂ hy₁ (by omega),
      pair hy₁ hx₂ (by omega),pair hy₂ hx₁ (by omega)]
    norm_num
  · have hw (a : ℕ) : 0 ≤ weight A c a ∧ weight A c a ≤ Real.sqrt 2 := by
      dsimp [weight]
      split <;> norm_num
    have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    calc
      _ ≤ ∑ _x ∈ D, (2:ℝ) := sum_le_sum (fun x _ => by
        have h := mul_le_mul (hw x).2 (hw (x+t)).2 (hw (x+t)).1 (Real.sqrt_nonneg 2)
        nlinarith)
      _ ≤ 2 := by
        simp only [sum_const,nsmul_eq_mul]
        have h : (D.card : ℝ) ≤ 1 := by exact_mod_cast Nat.le_of_not_gt hh
        linarith

private noncomputable def row (A : Finset ℕ) (c i x : ℕ) : ℝ :=
  if x ∈ A.image (· + i) then weight A c (x-i) else 0

private theorem row_sum {A : Finset ℕ} {N H : ℕ} (hA : A ⊆ Icc 1 N) (c i : ℕ)
    (hi : i<H) (g : ℕ → ℝ) :
    ∑ x ∈ Icc 1 (N+H), row A c i x * g x = ∑ a ∈ A, weight A c a * g (a+i) := by
  classical
  have sub : A.image (· + i) ⊆ Icc 1 (N+H) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp (hA ha)
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  rw [← sum_subset sub (fun x _ hx => by simp [row,hx]),sum_image (fun _ _ _ _ he => Nat.add_right_cancel he)]
  apply sum_congr rfl
  intro a ha
  simp [row,mem_image_of_mem (· + i) ha]

private theorem correlations {A : Finset ℕ} {c N H : ℕ} (hA : A ⊆ Icc 1 N)
    (hc : OnlyAt A c) {i j : ℕ} (hi : i<H) (hj : j<H) :
    ∑ x ∈ Icc 1 (N+H), row A c i x * row A c j x ≤
      if i=j then 2*(A.card : ℝ) else 2 := by
  classical
  have cross {a b : ℕ} (hab : a<b) (hb : b<H) :
      ∑ x ∈ Icc 1 (N+H), row A c b x * row A c a x ≤ 2 := by
    rw [row_sum hA c b hb]
    have same (x : ℕ) : row A c a (x+b) =
        if x+(b-a)∈A then weight A c (x+(b-a)) else 0 := by
      have he : x+b-a=x+(b-a) := by omega
      have hm : x+b ∈ A.image (· + a) ↔ x+(b-a)∈A := by
        constructor
        · intro h
          obtain ⟨y,hy,hy'⟩ := mem_image.mp h
          rwa [show x+(b-a)=y by omega]
        · intro h
          exact mem_image.mpr ⟨_,h,by omega⟩
      simp only [row,he,hm]
    simpa only [same,mul_ite,mul_zero,← sum_filter] using
      (show ∑ x ∈ A.filter (fun x => x+(b-a)∈A), weight A c x * weight A c (x+(b-a)) ≤ 2 from
        weighted_shift A hc (by omega))
  rcases lt_trichotomy i j with h | rfl | h
  · rw [if_neg h.ne]
    simpa only [mul_comm] using cross h hj
  · rw [if_pos rfl,row_sum hA c i hi]
    calc
      _ ≤ ∑ _a ∈ A, (2:ℝ) := by
        apply sum_le_sum
        intro a ha
        simp only [row,if_pos (mem_image_of_mem (· + i) ha),Nat.add_sub_cancel]
        dsimp only [weight]
        split <;> norm_num [← sq,Real.sq_sqrt]
      _ = _ := by simp [mul_comm]
  · rw [if_neg (Ne.symm h.ne)]
    exact cross h hi

/-- With H shifts, Cauchy–Schwarz bounds the weighted mass W by
H W² ≤ 2(N+H)(|A|+H−1). -/
theorem window_bound {A : Finset ℕ} {c N H : ℕ} (hA : A ⊆ Icc 1 N)
    (hc : OnlyAt A c) (hH : 0<H) :
    (H : ℝ) * (∑ a ∈ A, weight A c a)^2 ≤
      2*(N+H : ℕ)*((A.card : ℝ) + H - 1) := by
  classical
  let S := Icc 1 (N+H)
  let I := range H
  let f := row A c
  let W := ∑ a ∈ A, weight A c a
  have rows (i : ℕ) (hi : i∈I) : ∑ x ∈ S, f i x = W := by
    simpa only [mul_one] using row_sum hA c i (mem_range.mp hi) (fun _ => 1)
  have total : ∑ x ∈ S, ∑ i ∈ I, f i x = (H:ℝ)*W := by
    rw [sum_comm]
    calc
      _ = ∑ _i ∈ I, W := sum_congr rfl rows
      _ = _ := by simp [I]
  have inner (i : ℕ) (hi : i∈I) :
      ∑ j ∈ I, ∑ x ∈ S, f i x * f j x ≤ 2*((A.card : ℝ)+H-1) := by
    calc
      _ ≤ ∑ j ∈ I, (if i=j then 2*(A.card : ℝ) else 2) :=
        sum_le_sum (fun j hj => correlations hA hc (mem_range.mp hi) (mem_range.mp hj))
      _ = _ := by
        rw [← sum_erase_add _ _ hi]
        have he : ∑ j ∈ I.erase i, (if i=j then 2*(A.card : ℝ) else 2) =
            ∑ _j ∈ I.erase i, (2 : ℝ) :=
          sum_congr rfl (fun j hj => if_neg (Ne.symm (mem_erase.mp hj).1))
        rw [he,if_pos rfl,sum_const,card_erase_of_mem hi]
        simp only [I,card_range,nsmul_eq_mul,Nat.cast_sub hH,Nat.cast_one]
        ring
  have energy : ∑ x ∈ S, (∑ i ∈ I, f i x)^2 ≤ (H:ℝ)*(2*((A.card:ℝ)+H-1)) := by
    calc
      _ = ∑ x ∈ S, ∑ i ∈ I, ∑ j ∈ I, f i x * f j x := by
        apply sum_congr rfl
        intro x _
        rw [sq,sum_mul]
        simp only [mul_sum]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ S, f i x * f j x := by
        rw [sum_comm]
        exact sum_congr rfl (fun _ _ => sum_comm)
      _ ≤ ∑ _i ∈ I, 2*((A.card : ℝ)+H-1) := sum_le_sum inner
      _ = _ := by simp [I]
  have cs := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun x => ∑ i ∈ I, f i x)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,total] at cs
  have hs : S.card=N+H := by simp [S,Nat.card_Icc]
  rw [hs] at cs
  have h := cs.trans (mul_le_mul_of_nonneg_left energy (Nat.cast_nonneg _))
  have hp : 0<(H:ℝ) := by exact_mod_cast hH
  change (H:ℝ)*W^2 ≤ _
  apply le_of_mul_le_mul_left (a := (H:ℝ)) _ hp
  nlinarith only [h]

private lemma weight_sum (A : Finset ℕ) (c : ℕ) :
    ∑ x ∈ A, weight A c x = A.card + (Real.sqrt 2-1)*((A \ core A c).card : ℝ) := by
  have sub : core A c ⊆ A := filter_subset _ _
  have h := sum_sdiff sub (f := weight A c)
  have paired : ∑ x ∈ core A c, weight A c x = ((core A c).card : ℝ) := by
    calc
      _ = ∑ _x ∈ core A c, (1:ℝ) := sum_congr rfl (fun _ hx => if_pos hx)
      _ = _ := by simp
  have out : ∑ x ∈ A \ core A c, weight A c x = ((A \ core A c).card : ℝ)*Real.sqrt 2 := by
    calc
      _ = ∑ _x ∈ A \ core A c, Real.sqrt 2 :=
        sum_congr rfl (fun x hx => if_neg (mem_sdiff.mp hx).2)
      _ = _ := by simp
  have cards : ((A \ core A c).card : ℝ) + (core A c).card = A.card := by
    exact_mod_cast card_sdiff_add_card_eq_card sub
  rw [paired,out] at h
  linarith

/-- The weighted Erdős–Turán window bound optimized in the window length.
Every unpaired element costs an extra factor √2−1 on the left. -/
theorem unpaired_bound {N : ℕ} (A : Finset ℕ) (hA : A ⊆ Icc 1 N) {c : ℕ} (hc : OnlyAt A c) :
    (A.card : ℝ) + (Real.sqrt 2-1)*((A \ core A c).card : ℝ) ≤
      Real.sqrt 2 * (Real.sqrt N + Real.sqrt A.card) := by
  let n := Real.sqrt N
  let k := Real.sqrt A.card
  let H := ⌊n*k⌋₊ + 1
  let W := ∑ a ∈ A, weight A c a
  have hn : n^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hk : k^2=(A.card:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hnk : 0 ≤ n*k := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hu : (H:ℝ) ≤ n*k+1 := by dsimp [H]; push_cast; linarith [Nat.floor_le hnk]
  have hl : n*k < (H:ℝ) := by simpa [H] using Nat.lt_floor_add_one (n*k)
  have hH : 0<H := Nat.succ_pos _
  have h := window_bound hA hc hH
  push_cast at h
  have prod : (N:ℝ)*A.card ≤ (H:ℝ)*(n*k) := by
    rw [← hn,← hk]
    nlinarith only [mul_le_mul_of_nonneg_right hl.le hnk]
  have hv : W^2 ≤ 2*(n+k)^2 := by
    have hp : 0<(H:ℝ) := by exact_mod_cast hH
    apply le_of_mul_le_mul_left (a := (H:ℝ)) _ hp
    change (H:ℝ)*W^2 ≤ 2*((N:ℝ)+H)*((A.card:ℝ)+H-1) at h
    rw [← hn,← hk] at h prod
    nlinarith only [h,prod,mul_le_mul_of_nonneg_left hu hp.le,sq_nonneg n]
  rw [← weight_sum]
  change W ≤ Real.sqrt 2*(n+k)
  have hz : 0 ≤ Real.sqrt 2*(n+k) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have heq : (Real.sqrt 2*(n+k))^2 = 2*(n+k)^2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith only [hv,heq,hz,sq_nonneg (W-Real.sqrt 2*(n+k))]

private lemma core_single (A : Finset ℕ) (c : ℕ) (h : Erdos864.HasAtMostOneRepeatedSum A) :
    Erdos864.HasAtMostOneRepeatedSum (core A c) := by
  have sub := (show core A c ⊆ A from filter_subset _ _)
  have hm (n : ℕ) : Erdos864.sumRepresentations (core A c) n ⊆ Erdos864.sumRepresentations A n :=
    filter_subset_filter _ (product_subset_product sub sub)
  intro n m hn hμ
  exact h n m (hn.trans_le (card_le_card (hm n))) (hμ.trans_le (card_le_card (hm m)))

/-- Along any family at the √2 endpoint, deleting o(√N) labels leaves a
reflection-invariant set which still satisfies the pinned Erdős 864 predicate. -/
theorem endpoint_core {ι : Type*} {l : Filter ι} (N : ι → ℕ) (A : ι → Finset ℕ)
    (hN : Tendsto N l atTop) (hI : ∀ i, A i ⊆ Icc 1 (N i))
    (hA : ∀ i, Erdos864.HasAtMostOneRepeatedSum (A i))
    (hk : Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (N i)) l (𝓝 (Real.sqrt 2))) :
    ∃ c : ι → ℕ, (∀ i, OnlyAt (A i) (c i)) ∧
      (∀ i, Erdos864.HasAtMostOneRepeatedSum (core (A i) (c i))) ∧
      (∀ i x, x ∈ core (A i) (c i) → ∃ y ∈ core (A i) (c i), x+y=c i) ∧
      Tendsto (fun i => (((A i) \ core (A i) (c i)).card : ℝ)/Real.sqrt (N i)) l (𝓝 0) ∧
      Tendsto (fun i => ((core (A i) (c i)).card : ℝ)/Real.sqrt (N i)) l (𝓝 (Real.sqrt 2)) := by
  choose c hc using fun i => exists_center (hA i)
  let U (i : ι) := (((A i) \ core (A i) (c i)).card : ℝ)
  have hn := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hN
  have hw := Real.tendsto_sqrt_atTop.comp hn
  have hratio : Tendsto (fun i => ((A i).card : ℝ)/(N i : ℝ)) l (𝓝 0) := by
    apply (hk.div_atTop hw).congr
    intro i
    change ((A i).card : ℝ) / Real.sqrt (N i) / Real.sqrt (N i) = _
    rw [div_div,← sq,Real.sq_sqrt (Nat.cast_nonneg _)]
  have he := hratio.sqrt
  simp only [Real.sqrt_div (Nat.cast_nonneg _),Real.sqrt_zero] at he
  have v : 0 < Real.sqrt 2 - 1 := sub_pos.mpr ((Real.lt_sqrt (by norm_num)).mpr (by norm_num))
  have bound := (((tendsto_const_nhds (x := Real.sqrt 2)).add
      ((tendsto_const_nhds (x := Real.sqrt 2)).mul he)).sub hk).div_const (Real.sqrt 2-1)
  simp only [mul_zero,add_zero,sub_self,zero_div] at bound
  have herr : Tendsto (fun i => U i/Real.sqrt (N i)) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i =>
      div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) _ bound
    filter_upwards [hN.eventually_gt_atTop 0] with i hi
    have hw' := Real.sqrt_pos.mpr (show 0<(N i : ℝ) by exact_mod_cast hi)
    have h := unpaired_bound (A i) (hI i) (hc i)
    change ((A i).card : ℝ) + (Real.sqrt 2-1)*U i ≤ _ at h
    change U i/Real.sqrt (N i) ≤
      (Real.sqrt 2 + Real.sqrt 2*(Real.sqrt (A i).card/Real.sqrt (N i))-
        (A i).card/Real.sqrt (N i))/(Real.sqrt 2-1)
    apply (le_div_iff₀ v).mpr
    field_simp [hw'.ne']
    linarith
  refine ⟨c,hc,fun i => core_single (A i) (c i) (hA i),?_,herr,?_⟩
  · intro i x hx
    obtain ⟨hx,y,hy,heq⟩ := mem_filter.mp hx
    exact ⟨y,mem_filter.mpr ⟨hy,x,hx,(add_comm y x).trans heq⟩,heq⟩
  · have ht := hk.sub herr
    rw [sub_zero] at ht
    refine ht.congr (fun i => ?_)
    have h := card_sdiff_add_card_eq_card (show core (A i) (c i) ⊆ A i from filter_subset _ _)
    have hh : U i + ((core (A i) (c i)).card : ℝ) = (A i).card := by dsimp only [U]; exact_mod_cast h
    rw [← sub_div]
    congr 1
    linarith

/-- The affine three-sum obstruction for a half of a reflected set. -/
def AdmissibleHalf (B : Finset ℕ) (e : ℕ) : Prop :=
  IsSidon (B : Set ℕ) ∧ ∀ a ∈ B, ∀ b ∈ B, ∀ d ∈ B, ∀ x ∈ B, a+b+d ≠ x+e

private def reflectHalf (B : Finset ℕ) (m e : ℕ) : Finset ℕ :=
  B.image (fun x => m+x) ∪ B.image (fun x => m+e-x)

private lemma unique_away {A : Finset ℕ} {c : ℕ} : OnlyAt A c ↔
    ∀ a ∈ A, ∀ b ∈ A, ∀ x ∈ A, ∀ y ∈ A, a+b=x+y → a+b≠c →
      (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
  constructor
  · intro hc a ha b hb x hx y hy he hne
    have hp := ordered_rep ha hb
    have hq := he.symm ▸ ordered_rep hx hy
    have equal : (min a b,max a b) = (min x y,max x y) := by
      by_contra hn
      exact hne (hc _ (one_lt_card.mpr ⟨_,hp,_,hq,hn⟩))
    have h₁ := congrArg Prod.fst equal
    have h₂ := congrArg Prod.snd equal
    change min a b=min x y at h₁
    change max a b=max x y at h₂
    omega
  · intro h n hn
    by_contra hne
    obtain ⟨⟨a,b⟩,hab,⟨x,y⟩,hxy,hp⟩ := one_lt_card.mp hn
    obtain ⟨⟨ha,hb⟩,ho,he⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
    obtain ⟨⟨hx,hy⟩,ho',he'⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hxy
    have H := h a ha b hb x hx y hy (he.trans he'.symm) (he ▸ hne)
    exact hp (Prod.ext (by rcases H with h | h <;> omega) (by rcases H with h | h <;> omega))

private lemma half_card {B : Finset ℕ} {m e : ℕ} (he : e≤1)
    (hb : ∀ x ∈ B, 1≤x ∧ x ≤ m+e) : (reflectHalf B m e).card = 2*B.card := by
  let P := B.image (fun x => m+x)
  let Q := B.image (fun x => m+e-x)
  have disj : Disjoint P Q := by
    apply disjoint_left.mpr
    intro z hz hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨y,hy,hy'⟩ := mem_image.mp hp
    have := hb x hx
    have := hb y hy
    omega
  change (P ∪ Q).card = _
  rw [card_union_of_disjoint disj,show P.card=B.card from card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h)]
  have hq : Q.card=B.card := by
    apply card_image_of_injOn
    intro x hx y hy h
    have := hb x hx
    have := hb y hy
    change m+e-x=m+e-y at h
    omega
  omega

private lemma half_iff {B : Finset ℕ} {m e : ℕ} (he : e≤1)
    (hb : ∀ x ∈ B, 1≤x ∧ x ≤ m+e) :
    OnlyAt (reflectHalf B m e) (2*m+e) ↔ AdmissibleHalf B e := by
  rw [unique_away]
  have high (x) (hx : x∈B) : m+x ∈ reflectHalf B m e := mem_union_left _ (mem_image_of_mem _ hx)
  have low (x) (hx : x∈B) : m+e-x ∈ reflectHalf B m e := mem_union_right _ (mem_image_of_mem _ hx)
  constructor
  · intro h
    constructor
    · intro a ha x hx b hb' y hy hxy
      have ha' := hb a ha
      have hb'' := hb b hb'
      have hh := h _ (high a ha) _ (high b hb') _ (high x hx) _ (high y hy)
        (by omega) (by omega)
      omega
    · intro a ha b hb' d hd x hx hab
      have ha' := hb a ha
      have hb'' := hb b hb'
      have hd' := hb d hd
      have hh := h _ (high a ha) _ (high b hb') _ (high x hx) _ (low d hd)
        (by omega) (by omega)
      omega
  · rintro ⟨sid,avoid⟩ a ha b hb' x hx y hy heq hne
    have tags {z} (hz : z∈reflectHalf B m e) :
        ∃ u ∈ B, 1≤u ∧ u ≤ m+e ∧ (z=m+u ∨ z=m+e-u) := by
      rcases mem_union.mp hz with h | h
      · obtain ⟨u,hu,rfl⟩ := mem_image.mp h
        exact ⟨u,hu,(hb u hu).1,(hb u hu).2,Or.inl rfl⟩
      · obtain ⟨u,hu,rfl⟩ := mem_image.mp h
        exact ⟨u,hu,(hb u hu).1,(hb u hu).2,Or.inr rfl⟩
    obtain ⟨p,hp,hp₁,hp₂,ha'⟩ := tags ha
    obtain ⟨q,hq,hq₁,hq₂,hb''⟩ := tags hb'
    obtain ⟨r,hr,hr₁,hr₂,hx'⟩ := tags hx
    obtain ⟨s,hs,hs₁,hs₂,hy'⟩ := tags hy
    have h₁ := sid p hp r hr q hq s hs
    have h₂ := sid p hp r hr s hs q hq
    have h₃ := sid p hp s hs r hr q hq
    have t₁ := avoid p hp q hq r hr s hs
    have t₂ := avoid p hp q hq s hs r hr
    have t₃ := avoid r hr s hs p hp q hq
    have t₄ := avoid r hr s hs q hq p hp
    rcases ha' with rfl|rfl <;> rcases hb'' with rfl|rfl <;>
      rcases hx' with rfl|rfl <;> rcases hy' with rfl|rfl <;> omega

/-- Every reflected core is obtained from an admissible half in [1,⌊N/2⌋],
up to the possible fixed point at the midpoint. -/
theorem extract_half {A : Finset ℕ} {c N : ℕ} (hI : A ⊆ Icc 1 N) (hc : OnlyAt A c) :
    ∃ B ⊆ Icc 1 (N/2), AdmissibleHalf B (c%2) ∧
      2*B.card ≤ (core A c).card ∧ (core A c).card ≤ 2*B.card+1 := by
  let m := c/2
  let e := c%2
  have hme : c=2*m+e := by dsimp [m,e]; omega
  have he : e≤1 := by dsimp [e]; omega
  let B := (Icc 1 (N/2)).filter fun x => m+x∈A ∧ m+e-x∈A
  have hB (x) (hx : x∈B) : 1≤x ∧ x ≤ m+e := by
    obtain ⟨hr,_,hl⟩ := mem_filter.mp hx
    obtain ⟨h₁,_⟩ := mem_Icc.mp hr
    have hy := (mem_Icc.mp (hI hl)).1
    omega
  have hsub : reflectHalf B m e ⊆ core A c := by
    intro z hz
    rcases mem_union.mp hz with h | h <;> obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    · obtain ⟨_,hh,hl⟩ := mem_filter.mp hx
      have := hB x hx
      exact mem_filter.mpr ⟨hh,_,hl,by omega⟩
    · obtain ⟨_,hh,hl⟩ := mem_filter.mp hx
      have := hB x hx
      exact mem_filter.mpr ⟨hl,_,hh,by omega⟩
  have hu : OnlyAt (reflectHalf B m e) (2*m+e) := by
    apply unique_away.mpr
    intro a ha b hb x hx y hy hs hn
    exact (unique_away.mp hc) _ (mem_filter.mp (hsub ha)).1 _ (mem_filter.mp (hsub hb)).1
      _ (mem_filter.mp (hsub hx)).1 _ (mem_filter.mp (hsub hy)).1 hs (hme ▸ hn)
  have cover : core A c ⊆ insert m (reflectHalf B m e) := by
    intro z hz
    obtain ⟨hz,y,hy,hzy⟩ := mem_filter.mp hz
    obtain ⟨hz₁,hz₂⟩ := mem_Icc.mp (hI hz)
    obtain ⟨hy₁,hy₂⟩ := mem_Icc.mp (hI hy)
    have shift {p q : ℕ} (hp : p∈A) (hq : q∈A) (hp' : m<p) (hs : p+q=c) :
        p-m∈B := by
      obtain ⟨hp₁,hp₂⟩ := mem_Icc.mp (hI hp)
      obtain ⟨hq₁,hq₂⟩ := mem_Icc.mp (hI hq)
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by rwa [show m+(p-m)=p by omega],
        by rwa [show m+e-(p-m)=q by omega]⟩
    rcases lt_trichotomy z m with h|rfl|h
    · apply mem_insert_of_mem (mem_union_right _ ?_)
      exact mem_image.mpr ⟨y-m,shift hy hz (by omega) (by omega),by omega⟩
    · exact mem_insert_self ..
    · apply mem_insert_of_mem (mem_union_left _ ?_)
      exact mem_image.mpr ⟨z-m,shift hz hy h hzy,by omega⟩
  have hs := half_card he hB
  exact ⟨B,filter_subset _ _,(half_iff he hB).mp hu,hs ▸ card_le_card hsub,
    (card_le_card cover).trans ((card_insert_le ..).trans (by omega))⟩

/-- Conversely an admissible half in [1,L] doubles to an interval set with
one exceptional sum, with the parity convention encoded by e ∈ {0,1}. -/
theorem extend_half {B : Finset ℕ} {L e : ℕ} (hB : B ⊆ Icc 1 L)
    (he : e≤1) (ha : AdmissibleHalf B e) :
    ∃ A ⊆ Icc 1 (2*L+1), Erdos864.HasAtMostOneRepeatedSum A ∧ A.card=2*B.card := by
  let m := L+1
  have hb (x) (hx : x∈B) : 1≤x ∧ x ≤ m+e := by
    obtain ⟨hx₁,hx₂⟩ := mem_Icc.mp (hB hx)
    exact ⟨hx₁,by dsimp [m]; omega⟩
  refine ⟨reflectHalf B m e,?_,?_,half_card he hb⟩
  · intro z hz
    rcases mem_union.mp hz with h | h <;> obtain ⟨u,hu,rfl⟩ := mem_image.mp h <;>
      obtain ⟨h₁,h₂⟩ := mem_Icc.mp (hB hu) <;> dsimp [m] <;> exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n n' hn hn'
    have h := (half_iff he hb).mpr ha
    exact (h n hn).trans (h n' hn').symm

private lemma scale_limit {l : Filter ℕ} (L e : ℕ → ℕ) (hL : Tendsto L l atTop)
    (he : ∀ i, e i ≤ 1) :
    Tendsto (fun i => Real.sqrt (2*L i+e i : ℕ)/Real.sqrt (L i)) l (𝓝 (Real.sqrt 2)) := by
  have h₀ : Tendsto (fun i => (e i : ℝ)/(L i : ℝ)) l (𝓝 0) := by
    apply squeeze_zero (fun _ => by positivity) _ ((tendsto_const_nhds (x := (1:ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop.comp hL))
    intro i
    exact div_le_div_of_nonneg_right (by exact_mod_cast he i) (Nat.cast_nonneg _)
  have ht := ((tendsto_const_nhds (x := (2:ℝ))).add h₀).sqrt
  rw [add_zero] at ht
  apply ht.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with i hi
  rw [← Real.sqrt_div (Nat.cast_nonneg _)]
  congr 1
  push_cast
  field_simp [show (L i : ℝ) ≠ 0 by exact_mod_cast hi.ne']

/-- The √2 endpoint for arbitrary Erdős 864 interval sets occurs along
unbounded lengths iff one can find asymptotically maximal interval Sidon
sets avoiding the affine three-sum equation at parity zero or one. -/
theorem endpoint_iff_admissible :
    (∃ (N : ℕ → ℕ) (A : ℕ → Finset ℕ), Tendsto N atTop atTop ∧
      (∀ i, A i ⊆ Icc 1 (N i) ∧ Erdos864.HasAtMostOneRepeatedSum (A i)) ∧
      Tendsto (fun i => ((A i).card : ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2))) ↔
    ∃ (L e : ℕ → ℕ) (B : ℕ → Finset ℕ), Tendsto L atTop atTop ∧
      (∀ i, B i ⊆ Icc 1 (L i) ∧ e i ≤ 1 ∧ AdmissibleHalf (B i) (e i)) ∧
      Tendsto (fun i => ((B i).card : ℝ)/Real.sqrt (L i)) atTop (𝓝 1) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hroot : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  constructor
  · rintro ⟨N,A,hN,hA,hk⟩
    obtain ⟨c,hc,_,_,_,hR⟩ := endpoint_core N A hN (fun i => (hA i).1) (fun i => (hA i).2) hk
    choose B hI hAdm lo hi using fun i => extract_half (hA i).1 (hc i)
    let L (i : ℕ) := N i/2
    let e (i : ℕ) := c i%2
    have hL : Tendsto L atTop atTop := by
      apply tendsto_atTop.mpr
      intro n
      filter_upwards [hN.eventually_ge_atTop (2*n)] with i hi
      dsimp [L]; omega
    have hscale := scale_limit L (fun i => N i%2) hL (by intro i; omega)
    have heq (i : ℕ) : 2*L i + N i%2 = N i := by dsimp [L]; omega
    simp only [heq] at hscale
    let r (i : ℕ) := ((core (A i) (c i)).card : ℝ)
    let b (i : ℕ) := ((B i).card : ℝ)
    let w (i : ℕ) := Real.sqrt (N i)
    have hw := Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hN)
    have hOne : Tendsto (fun i => 1/w i) atTop (𝓝 0) := (tendsto_const_nhds (x := (1:ℝ))).div_atTop hw
    have hl := hR.sub hOne
    rw [sub_zero] at hl
    have hmid : Tendsto (fun i => 2*b i/w i) atTop (𝓝 (Real.sqrt 2)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hR
      · intro i
        change r i/w i-1/w i ≤ _
        rw [←sub_div]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        have h : r i ≤ 2*b i+1 := by dsimp [r,b]; exact_mod_cast hi i
        linarith
      · intro i
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        dsimp only [b]
        exact_mod_cast lo i
    refine ⟨L,e,B,hL,fun i => ⟨hI i,by dsimp [e]; omega,hAdm i⟩,?_⟩
    have ht := (hmid.mul hscale).div_const 2
    rw [←sq,hs] at ht
    norm_num at ht
    apply ht.congr'
    filter_upwards [hN.eventually_gt_atTop 0] with i hi
    change 2*b i/w i*(w i/Real.sqrt (L i))/2 = b i/Real.sqrt (L i)
    field_simp [show w i≠0 from (Real.sqrt_pos.mpr (by exact_mod_cast hi)).ne']
  · rintro ⟨L,e,B,hL,hB,hk⟩
    choose A hI hA hcard using fun i => extend_half (hB i).1 (hB i).2.1 (hB i).2.2
    have hscale := scale_limit L (fun _ => 1) hL (fun _ => le_rfl)
    refine ⟨fun i => 2*L i+1,A,tendsto_atTop_mono (fun i => by omega) hL,fun i => ⟨hI i,hA i⟩,?_⟩
    have ht := ((tendsto_const_nhds (x := (2:ℝ))).mul hk).div hscale hroot
    rw [mul_one,show 2/Real.sqrt 2=Real.sqrt 2 from (div_eq_iff hroot).mpr (by nlinarith)] at ht
    apply ht.congr'
    filter_upwards [hL.eventually_gt_atTop 0] with i hi
    change (2 * ((B i).card / Real.sqrt (L i))) / (Real.sqrt (2*L i+1 : ℕ) / Real.sqrt (L i)) = _
    rw [hcard,Nat.cast_mul,Nat.cast_ofNat]
    field_simp [show Real.sqrt (L i) ≠ 0 from (Real.sqrt_pos.mpr (by exact_mod_cast hi)).ne',
      show Real.sqrt (2*L i+1 : ℕ) ≠ 0 by positivity]

#print axioms exists_center
#print axioms weighted_shift
#print axioms window_bound
#print axioms unpaired_bound
#print axioms endpoint_core
#print axioms extract_half
#print axioms extend_half
#print axioms endpoint_iff_admissible

end Erdos864WeightedCore
