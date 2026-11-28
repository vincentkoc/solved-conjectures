import Green33ReflectedLayers
import Mathlib.Algebra.Order.Chebyshev

/-! Counting fresh sums when extending reflected layers of a dense Sidon set. -/

open Finset Filter Green33ReflectedLayers Green33Multiplicity Green33TailEnergy
open scoped Pointwise Topology

namespace Green33SidonLayerRepairs

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
private lemma neg_sidon {B : Finset G} (hB : IsSidon (B : Set G)) : IsSidon ((-B : Finset G) : Set G) := by
  intro a ha b hb c hc d hd he
  have hs := hB (-a) (by simpa using ha) (-b) (by simpa using hb)
    (-c) (by simpa using hc) (-d) (by simpa using hd) (by rw [← neg_add,← neg_add,he])
  simpa using hs

omit [Fintype G] in
private lemma energy_bound (U B : Finset G) (hB : IsSidon (B : Set G)) :
    U.addEnergy B ≤ U.card*B.card+U.card^2 := by
  let C (u v : G) := ((B ×ˢ B).filter fun p => u+p.1=v+p.2).card
  have bound (u v : G) : C u v ≤ (if u=v then B.card else 0) + 1 := by
    by_cases h : u=v
    · subst v
      have he : ((B ×ˢ B).filter fun p => u+p.1=u+p.2) = B.diag := by
        ext p; simp [Finset.mem_diag]; grind
      dsimp only [C]; rw [he]; simp
    · rw [if_neg h,zero_add]
      apply card_le_one.mpr
      rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd
      obtain ⟨⟨ha,hb⟩,hs⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
      obtain ⟨⟨hc,hd⟩,ht⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hcd
      have he : a+d=c+b := by grind
      rcases hB a ha c hc d hd b hb he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · rfl
      · exact (h (add_right_cancel hs)).elim
  have heq : U.addEnergy B = ∑ u∈U, ∑ v∈U, C u v := by
    simp only [addEnergy,C,card_eq_sum_ones,sum_filter,sum_product]
  rw [heq]
  calc
    _ ≤ ∑ u∈U, ∑ v∈U, ((if u=v then B.card else 0) + 1) :=
      sum_le_sum fun u _ => sum_le_sum fun v _ => bound u v
    _ = _ := by simp [sum_add_distrib,sum_ite_eq,sq]

private def loss (U B : Finset G) :=
  ((U ×ˢ B).filter fun p => p.1-p.2 ∉ B-B).card

private lemma loss_sq (U B : Finset G) (hB : IsSidon (B : Set G)) :
    (loss U B)^2 ≤ (B-B)ᶜ.card*(U.card*B.card+U.card^2) := by
  have he := card_sq_le_card_mul_addEnergy U (-B) (B-B)ᶜ
  have eqc : loss U B = ((U ×ˢ (-B)).filter fun p => p.1+p.2∈(B-B)ᶜ).card := by
    apply card_equiv ((Equiv.refl G).prodCongr (Equiv.neg G))
    rintro ⟨a,b⟩
    simp [sub_eq_add_neg]
  rw [eqc]
  exact he.trans (Nat.mul_le_mul_left _ (by simpa using energy_bound U (-B) (neg_sidon hB)))

omit [Fintype G] in
private lemma transfer (B : Finset G) (u : G) :
    ∑ b∈B, reps B (u+b) = ∑ b∈B, diffReps B (u-b) := by
  simp only [reps,diffReps,card_eq_sum_ones,sum_filter,sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro b _
  congr 1
  exact propext (by constructor <;> intro h <;> grind)

omit [Fintype G] in
private lemma diff_pos (B : Finset G) {x : G} (hx : x∈B-B) : 0 < diffReps B x := by
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hx
  exact card_pos.mpr ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,rfl⟩⟩

omit [Fintype G] in
private lemma rep_cap {B : Finset G} (hB : IsSidon (B : Set G)) (x : G) :
    reps B x ≤ (if x∈B+B then 2 else 0) := by
  let P := (B ×ˢ B).filter fun p => p.1+p.2=x
  change P.card ≤ _
  by_cases hx : x∈B+B
  · obtain ⟨a,ha,b,hb,he⟩ := mem_add.mp hx
    rw [if_pos hx]
    apply (card_le_card (t := {(a,b),(b,a)}) ?_).trans card_le_two
    rintro ⟨c,d⟩ hh
    obtain ⟨⟨hc,hd⟩,hs⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hh
    rcases hB c hc a ha d hd b hb (hs.trans he.symm) with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp
  · rw [if_neg hx,nonpos_iff_eq_zero,card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨a,b⟩ hh
    obtain ⟨⟨ha,hb⟩,he⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hh
    exact hx (he ▸ add_mem_add ha hb)

/-- At most half of the mixed pairs can give fresh sums, up to a Cauchy
error controlled by the number of missing differences of the Sidon seed. -/
theorem fresh_mixed_bound (U B : Finset G) (hB : IsSidon (B : Set G)) :
    ∃ e : ℕ, 2*((U+B) \ (B+B)).card ≤ U.card*B.card+e ∧
      e^2 ≤ (B-B)ᶜ.card*(U.card*B.card+U.card^2) := by
  let P := U ×ˢ B
  let good := P.filter fun p => p.1+p.2∈B+B
  let bad := P.filter fun p => p.1+p.2∉B+B
  have hnew : (U+B) \ (B+B) ⊆ bad.image (fun p => p.1+p.2) := by
    intro x hx
    obtain ⟨a,ha,b,hb,he⟩ := mem_add.mp (Finset.mem_sdiff.mp hx).1
    exact mem_image.mpr ⟨(a,b),mem_filter.mpr ⟨mem_product.mpr ⟨ha,hb⟩,he.symm ▸ (Finset.mem_sdiff.mp hx).2⟩,he⟩
  have hcard := (card_le_card hnew).trans card_image_le
  have hsplit : good.card+bad.card=U.card*B.card := by
    rw [← card_product]; exact card_filter_add_card_filter_not _
  have heq : ∑ p∈P, reps B (p.1+p.2) = ∑ p∈P, diffReps B (p.1-p.2) := by
    simp only [P,sum_product,transfer]
  have hlo : U.card*B.card ≤ loss U B + ∑ p∈P, diffReps B (p.1-p.2) := by
    rw [← card_product]
    change P.card ≤ (P.filter _).card + _
    simp only [card_eq_sum_ones,sum_filter,← sum_add_distrib]
    apply sum_le_sum
    intro p _
    by_cases h : p.1-p.2∈B-B
    · simp only [h,not_true_eq_false,if_false,zero_add]; have := diff_pos B h; omega
    · simp [h]
  have hhi : (∑ p∈P, reps B (p.1+p.2)) ≤ 2*good.card := by
    unfold good
    rw [card_eq_sum_ones,sum_filter,mul_sum]
    apply sum_le_sum
    intro p _
    simpa only [mul_ite,mul_one,mul_zero] using rep_cap hB (p.1+p.2)
  exact ⟨loss U B,by omega,loss_sq U B hB⟩

omit [Fintype G] in
private lemma sum_upper (W : Finset G) : 2*(W+W).card ≤ W.card^2+W.card := by
  let s : Sym2 G → G := Sym2.lift ⟨(·+·),add_comm⟩
  have sub : W+W ⊆ W.sym2.image s := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
    exact mem_image.mpr ⟨Sym2.mk a b,mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩
  have h := (card_le_card sub).trans card_image_le
  rw [card_sym2] at h
  have h' : ((W+W).card : ℝ) ≤ (↑((W.card+1).choose 2) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_choose_two,Nat.cast_add_one] at h'
  exact_mod_cast (show 2*((W+W).card : ℝ) ≤ (W.card : ℝ)^2+W.card by linarith)

section Layers

variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]

private def splitLayer (U V : Finset G) (f : G →+ K) (j : K) :=
  U.image f ∪ V.image (fun x => j-f x)

omit [DecidableEq G] [Fintype G] [Fintype K] in
private lemma split_size (U V : Finset G) (f : G →+ K) (hf : Function.Injective f)
    {j : K} (hj : ∀ y, f y ≠ j) : (splitLayer U V f j).card = U.card+V.card := by
  have h : Disjoint (U.image f) (V.image (fun x => j-f x)) := by
    apply disjoint_left.mpr
    intro x hx hh
    obtain ⟨a,_,rfl⟩ := mem_image.mp hx
    obtain ⟨b,_,hb⟩ := mem_image.mp hh
    exact hj (a+b) (by rw [map_add,← hb]; abel)
  rw [splitLayer,card_union_of_disjoint h,card_image_of_injective _ hf,
    card_image_of_injective _ (fun a b h => hf (sub_right_inj.mp h))]

omit [DecidableEq G] in
private lemma split_exists (W : Finset K) (f : G →+ K) (hf : Function.Injective f)
    {j : K} (hj : ∀ x, f x ≠ j) (hK : Fintype.card K=2*Fintype.card G) :
    ∃ U V : Finset G, W=splitLayer U V f j ∧ W.card=U.card+V.card := by
  let U := univ.filter (fun x => f x∈W)
  let V := univ.filter (fun x => j-f x∈W)
  have all : splitLayer univ univ f j=univ := by
    apply (Finset.card_eq_iff_eq_univ _).mp
    rw [split_size _ _ _ hf hj,card_univ,hK,two_mul]
  have eqn : W=splitLayer U V f j := by
    ext x
    constructor
    · intro hx
      have hh : x∈splitLayer univ univ f j := all ▸ mem_univ _
      rcases mem_union.mp hh with hh | hh <;> obtain ⟨y,_,rfl⟩ := mem_image.mp hh
      · exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hx⟩))
      · exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hx⟩))
    · intro hx
      rcases mem_union.mp hx with hx | hx <;> obtain ⟨y,hy,rfl⟩ := mem_image.mp hx <;> exact (mem_filter.mp hy).2
  exact ⟨U,V,eqn,eqn ▸ split_size _ _ _ hf hj⟩

omit [Fintype K] in
private lemma mixed_misses (B U V : Finset G) (f : G →+ K) (j : K) :
    let A := layers B f j
    let W := splitLayer U V f j
    ((W+A) \ (A+A)).card ≤ (B-B)ᶜ.card + ((U+B) \ (B+B)).card + ((V+B) \ (B+B)).card := by
  let A := layers B f j
  let W := splitLayer U V f j
  let H := (B-B)ᶜ.image (fun z => j+f z)
  let L := ((U+B) \ (B+B)).image f
  let R := ((V+B) \ (B+B)).image (fun z => j+j-f z)
  have yes (a : G) (ha : a∈B) : f a∈A := mem_union_left _ (mem_image_of_mem _ ha)
  have no (a : G) (ha : a∈B) : j-f a∈A := mem_union_right _ (mem_image_of_mem _ ha)
  have left (z : G) (hz : z∈B+B) : f z∈A+A := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hz
    rw [map_add]; exact add_mem_add (yes a ha) (yes b hb)
  have right (z : G) (hz : z∈B+B) : j+j-f z∈A+A := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hz
    rw [map_add,show j+j-(f a+f b)=(j-f a)+(j-f b) by abel]
    exact add_mem_add (no a ha) (no b hb)
  have odd (z : G) (hz : z∈B-B) : j+f z∈A+A := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_sub.mp hz
    rw [map_sub,show j+(f a-f b)=f a+(j-f b) by abel]
    exact add_mem_add (yes a ha) (no b hb)
  have sub : (W+A) \ (A+A) ⊆ H∪L∪R := by
    intro z hz
    obtain ⟨ins,miss⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp ins
    rcases mem_union.mp hx with hx | hx <;> obtain ⟨u,hu,rfl⟩ := mem_image.mp hx <;>
      rcases mem_union.mp hy with hy | hy <;> obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
    · rw [← map_add] at miss ⊢
      exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr
        ⟨add_mem_add hu hb,mt (left _) miss⟩)))
    · have eqn : f u+(j-f b)=j+f (u-b) := by rw [map_sub]; abel
      rw [eqn] at miss ⊢
      exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_compl.mpr (mt (odd _) miss))))
    · have eqn : j-f u+f b=j+f (b-u) := by rw [map_sub]; abel
      rw [eqn] at miss ⊢
      exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ (mem_compl.mpr (mt (odd _) miss))))
    · have eqn : (j-f u)+(j-f b)=j+j-f (u+b) := by rw [map_add]; abel
      rw [eqn] at miss ⊢
      exact mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨add_mem_add hu hb,mt (right _) miss⟩))
  have hsum := (card_le_card sub).trans (card_union_le _ _)
  have hHL := card_union_le H L
  have hh : H.card ≤ (B-B)ᶜ.card := card_image_le
  have hl : L.card ≤ ((U+B) \ (B+B)).card := card_image_le
  have hr : R.card ≤ ((V+B) \ (B+B)).card := card_image_le
  change ((W+A) \ (A+A)).card ≤ _
  omega

/-- In an index-two extension, adding w elements covers at most the remaining
odd holes, the same-parity fresh mixed sums, and the new unordered pairs. -/
theorem repair_cost (B : Finset G) (hB : IsSidon (B : Set G)) (f : G →+ K) (hf : Function.Injective f)
    {j : K} (hj : ∀ x, f x ≠ j) (hK : Fintype.card K=2*Fintype.card G)
    (T : Finset K) (hb : T+T=univ) :
    let A := layers B f j
    let w := (T \ A).card
    let h := (B-B)ᶜ.card
    ∃ e : ℕ, 2*(A+A)ᶜ.card ≤ 2*h+B.card*w+2*e+w^2+w ∧
      e^2 ≤ h*(w*B.card+w^2) := by
  let A := layers B f j
  let W := T \ A
  obtain ⟨U,V,heq,hw⟩ := split_exists W f hf hj hK
  have mixed := mixed_misses B U V f j
  change (((splitLayer U V f j)+A) \ (A+A)).card ≤ _ at mixed
  rw [← heq] at mixed
  have sub : (A+A)ᶜ ⊆ ((W+A) \ (A+A)) ∪ (W+W) := by
    intro z hz
    have hin : z∈T+T := hb ▸ mem_univ _
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hin
    have nh := mem_compl.mp hz
    by_cases hh : a∈A <;> by_cases hh' : b∈A
    · exact (nh (add_mem_add hh hh')).elim
    · apply mem_union_left _ (mem_sdiff.mpr ⟨?_,nh⟩)
      exact (add_comm b a) ▸ Finset.add_mem_add (show b∈W from Finset.mem_sdiff.mpr ⟨hb,hh'⟩) hh
    · exact mem_union_left _ (mem_sdiff.mpr ⟨add_mem_add (mem_sdiff.mpr ⟨ha,hh⟩) hh',nh⟩)
    · exact mem_union_right _ (add_mem_add (mem_sdiff.mpr ⟨ha,hh⟩) (mem_sdiff.mpr ⟨hb,hh'⟩))
  have hs := (card_le_card sub).trans (card_union_le _ _)
  obtain ⟨eu,hu,hus⟩ := fresh_mixed_bound U B hB
  obtain ⟨ev,hv,hvs⟩ := fresh_mixed_bound V B hB
  have wnew := sum_upper W
  have huW : U.card ≤ W.card := by omega
  have hvW : V.card ≤ W.card := by omega
  refine ⟨max eu ev,?_,?_⟩
  · change 2*(A+A)ᶜ.card ≤ 2*(B-B)ᶜ.card + B.card*W.card+2*max eu ev+W.card^2+W.card
    have hprod : B.card*W.card=U.card*B.card+V.card*B.card := by rw [hw]; ring
    omega
  · change (max eu ev)^2 ≤ (B-B)ᶜ.card*(W.card*B.card+W.card^2)
    rcases le_total eu ev with he | he
    · rw [max_eq_right he]; exact hvs.trans (by gcongr)
    · rw [max_eq_left he]; exact hus.trans (by gcongr)

end Layers

private lemma added_lower (k w h H e z : ℕ → ℝ)
    (hk : Tendsto k atTop (𝓝 1)) (hh : Tendsto h atTop (𝓝 0))
    (hH : Tendsto H atTop (𝓝 (1/4))) (hz : Tendsto z atTop (𝓝 0))
    (pos : ∀ i, 0≤k i ∧ 0≤w i ∧ 0≤h i ∧ 0≤z i)
    (cost : ∀ i, 2*H i ≤ 2*h i+k i*w i+2*e i+(w i)^2+w i*z i)
    (err : ∀ i, (e i)^2 ≤ h i*(w i*k i+(w i)^2))
    {d : ℝ} (hd : 0≤d) (hd' : d < (Real.sqrt 3-1)/2) :
    ∀ᶠ i in atTop, d < w i := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hd₂ : d+d^2 < 1/2 := by
    nlinarith only [hs,mul_pos (sub_pos.mpr hd') (show 0 < (Real.sqrt 3-1)/2+d+1 by linarith [Real.sqrt_nonneg 3])]
  have hdlim := tendsto_const_nhds (f := atTop (α := ℕ)) (x := d)
  have h₁ := (hh.mul ((hdlim.mul hk).add (hdlim.pow 2))).sqrt
  have h₂ := (((((tendsto_const_nhds (x := (2:ℝ))).mul hh).add (hk.mul hdlim)).add
    ((tendsto_const_nhds (x := (2:ℝ))).mul h₁)).add (hdlim.pow 2)).add (hdlim.mul hz)
  have h₃ := (tendsto_const_nhds (x := (2:ℝ))).mul hH
  norm_num at h₂ h₃
  filter_upwards [h₂.eventually_lt h₃ hd₂] with i hi
  by_contra! hw
  obtain ⟨hk₀,hw₀,hh₀,hz₀⟩ := pos i
  have hsq := pow_le_pow_left₀ hw₀ hw 2
  have hroot : e i ≤ Real.sqrt (h i*(d*k i+d^2)) := by
    apply Real.le_sqrt_of_sq_le
    exact (err i).trans (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hw hk₀) hsq) hh₀)
  change 2*h i+k i*d+2*Real.sqrt (h i*(d*k i+d^2))+d^2+d*z i < 2*H i at hi
  linarith only [hi,cost i,hsq,hroot,mul_le_mul_of_nonneg_left hw hk₀,mul_le_mul_of_nonneg_right hw hz₀]

section Families

variable {S P : ℕ → Type*} [∀ i, AddCommGroup (S i)] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    [∀ i, AddCommGroup (P i)] [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

/-- A quarter of the half-order missing from the doubled seed forces a
normalized size of at least (3+√3)/(2√2) for every containing two-basis. -/
theorem dense_extension_lower (B : (i : ℕ) → Finset (S i)) (hB : ∀ i, IsSidon (B i : Set (S i)))
    (hne : ∀ i, (B i).Nonempty) (f : (i : ℕ) → S i →+ P i) (hf : ∀ i, Function.Injective (f i))
    (j : (i : ℕ) → P i) (hj : ∀ i x, f i x ≠ j i) (hK : ∀ i, Fintype.card (P i)=2*Fintype.card (S i))
    (hm : Tendsto (fun i => Fintype.card (S i)) atTop atTop)
    (hk : Tendsto (fun i => ((B i).card : ℝ)/Real.sqrt (Fintype.card (S i))) atTop (𝓝 1))
    (hH : Tendsto (fun i => (((layers (B i) (f i) (j i)+layers (B i) (f i) (j i))ᶜ.card : ℝ) /
        Fintype.card (S i))) atTop (𝓝 (1/4)))
    (T : (i : ℕ) → Finset (P i)) (hsub : ∀ i, layers (B i) (f i) (j i) ⊆ T i)
    (hb : ∀ i, T i+T i=univ) {c : ℝ} (hc : c < (3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, c < (↑(T i).card : ℝ)/Real.sqrt (Fintype.card (P i)) := by
  let m (i : ℕ) : ℝ := Fintype.card (S i)
  let s (i : ℕ) := Real.sqrt (m i)
  let k (i : ℕ) : ℝ := (B i).card
  let A i := layers (B i) (f i) (j i)
  let w (i : ℕ) : ℝ := (T i \ A i).card
  let H (i : ℕ) : ℝ := (A i+A i)ᶜ.card
  let h (i : ℕ) : ℝ := (B i-B i)ᶜ.card
  have hm₀ (i : ℕ) : 0<m i := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hs (i : ℕ) : 0<s i := Real.sqrt_pos.mpr (hm₀ i)
  have hsq (i : ℕ) : (s i)^2=m i := Real.sq_sqrt (hm₀ i).le
  have hmt : Tendsto m atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hst : Tendsto s atTop atTop := Real.tendsto_sqrt_atTop.comp hmt
  have hz := (tendsto_const_nhds (x := (1:ℝ))).div_atTop hst
  have h₁ : Tendsto (fun i => (k i)^2/m i) atTop (𝓝 1) := by
    have hh := hk.pow 2
    rw [one_pow] at hh
    apply hh.congr
    intro i
    change (k i/s i)^2=_
    rw [div_pow,hsq]
  have h₂ : Tendsto (fun i => k i/m i) atTop (𝓝 0) := by
    apply (hk.div_atTop hst).congr
    intro i
    change k i/s i/s i=_
    rw [div_div,←sq,hsq]
  have hh : Tendsto (fun i => h i/m i) atTop (𝓝 0) := by
    have hl := (((tendsto_const_nhds (x := (1:ℝ))).sub h₁).add h₂).sub ((tendsto_const_nhds (x := (1:ℝ))).div_atTop hmt)
    norm_num at hl
    apply hl.congr
    intro i
    have hdiff := sidon_difference_size (hB i) (hne i)
    have hcard := card_compl_add_card (B i-B i)
    have hc' : h i + (↑(B i-B i).card : ℝ)=m i := by dsimp [h,m]; exact_mod_cast hcard
    change 1-(k i)^2/m i+k i/m i-(m i)⁻¹=h i/m i
    field_simp [(hm₀ i).ne']
    change _ = (k i)^2-k i+1 at hdiff
    linarith
  choose E hcost herr using fun i => repair_cost (B i) (hB i) (f i) (hf i) (hj i) (hK i) (T i) (hb i)
  let e (i : ℕ) : ℝ := E i
  have hc₀ (i : ℕ) : 2*H i ≤ 2*h i+k i*w i+2*e i+(w i)^2+w i := by
    dsimp [H,h,k,w,e,A]
    exact_mod_cast hcost i
  have he₀ (i : ℕ) : (e i)^2 ≤ h i*(w i*k i+(w i)^2) := by
    dsimp [e,h,w,k,A]
    exact_mod_cast herr i
  have cost (i : ℕ) : 2*(H i/m i) ≤ 2*(h i/m i)+(k i/s i)*(w i/s i)+2*(e i/m i)+(w i/s i)^2+(w i/s i)*(1/s i) := by
    have hdiv := div_le_div_of_nonneg_right (hc₀ i) (hm₀ i).le
    calc _ = 2*H i/m i := by ring
         _ ≤ _ := hdiv
         _ = _ := by rw [← hsq i]; ring
  have err (i : ℕ) : (e i/m i)^2 ≤ (h i/m i)*((w i/s i)*(k i/s i)+(w i/s i)^2) := by
    rw [div_pow]
    apply (div_le_div_of_nonneg_right (he₀ i) (sq_nonneg _)).trans_eq
    rw [← hsq i]; ring
  let α := (Real.sqrt 3-1)/2
  let d := max 0 ((c*Real.sqrt 2-2+α)/2)
  have hs2 : 0<Real.sqrt 2 := by positivity
  have hα : 0<α := by dsimp [α]; nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg 3]
  have hc' : c*Real.sqrt 2-2 < α := by
    dsimp [α]; have := (lt_div_iff₀ (by positivity : 0<2*Real.sqrt 2)).mp hc; linarith
  have hd : d<α := max_lt hα (by linarith)
  have hw := added_lower (fun i => k i/s i) (fun i => w i/s i) (fun i => h i/m i)
    (fun i => H i/m i) (fun i => e i/m i) (fun i => 1/s i) hk hh hH hz
    (fun i => by dsimp [k,w,h,A,m,s]; exact ⟨by positivity,by positivity,by positivity,by positivity⟩)
    cost err (le_max_left _ _) hd
  have hc'' : c*Real.sqrt 2 < 2+d := by have ht := le_max_right (0:ℝ) ((c*Real.sqrt 2-2+α)/2); dsimp [d]; linarith
  have hl := ((tendsto_const_nhds (x := (2:ℝ))).mul hk).add (tendsto_const_nhds (x := d))
  rw [mul_one] at hl
  filter_upwards [hw,hl.eventually_const_lt hc''] with i hi hi'
  have hAc : (A i).card=(B i).card+(B i).card := split_size _ _ _ (hf i) (hj i)
  have hTc : (T i \ A i).card+(A i).card=(T i).card := card_sdiff_add_card_eq_card (hsub i)
  have hT' : ((T i).card : ℝ)=2*k i+w i := by
    rw [hAc] at hTc
    dsimp [k,w]; exact_mod_cast (show (T i).card=2*(B i).card+(T i \ A i).card by omega)
  have hN : Real.sqrt (Fintype.card (P i))=Real.sqrt 2*s i := by
    rw [hK,Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num)]
  rw [hN,hT',div_mul_eq_div_div_swap,lt_div_iff₀ hs2,add_div,mul_div_assoc]
  change c*Real.sqrt 2 < 2*(k i/s i)+d at hi'
  linarith

/-- Quarter overlap suffices for the same lower constant. For cyclic dense
Sidon seeds the preceding variance theorem supplies this overlap in probability. -/
theorem overlap_extension_lower (B : (i : ℕ) → Finset (S i)) (hB : ∀ i, IsSidon (B i : Set (S i)))
    (hne : ∀ i, (B i).Nonempty) (f : (i : ℕ) → S i →+ P i) (hf : ∀ i, Function.Injective (f i))
    (j : (i : ℕ) → P i) (hj : ∀ i x, f i x ≠ j i) (hK : ∀ i, Fintype.card (P i)=2*Fintype.card (S i))
    (m : (i : ℕ) → S i) (hc : ∀ i, f i (m i)=j i+j i)
    (ht : Tendsto (fun i => Fintype.card (S i)) atTop atTop)
    (hk : Tendsto (fun i => ((B i).card : ℝ)/Real.sqrt (Fintype.card (S i))) atTop (𝓝 1))
    (ho : Tendsto (fun i => (overlap (B i) (m i) : ℝ)/Fintype.card (S i)) atTop (𝓝 (1/4)))
    (T : (i : ℕ) → Finset (P i)) (hsub : ∀ i, layers (B i) (f i) (j i) ⊆ T i)
    (hb : ∀ i, T i+T i=univ) {c : ℝ} (hlt : c < (3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, c < ((T i).card : ℝ)/Real.sqrt (Fintype.card (P i)) := by
  apply dense_extension_lower B hB hne f hf j hj hK ht hk _ T hsub hb hlt
  let n (i : ℕ) : ℝ := Fintype.card (S i)
  have hn (i : ℕ) : 0<n i := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hnt : Tendsto n atTop atTop := tendsto_natCast_atTop_atTop.comp ht
  have hsq := hk.pow 2
  rw [one_pow] at hsq
  have hlim := (((tendsto_const_nhds (x := (2:ℝ))).sub ((tendsto_const_nhds (x := (2:ℝ))).mul hsq)).sub
    ((tendsto_const_nhds (x := (1:ℝ))).div_atTop hnt)).add ho
  norm_num at hlim
  apply hlim.congr
  intro i
  let A := layers (B i) (f i) (j i)
  have hs := layer_sumset_size (hB i) (hne i) (f i) (hf i) (hj i) (hc i)
  change ((A+A).card : ℝ)=2*((B i).card : ℝ)^2+1-overlap (B i) (m i) at hs
  have hm := card_compl_add_card (A+A)
  rw [hK] at hm
  have hc' : ((A+A)ᶜ.card : ℝ)+(A+A).card=2*n i := by dsimp [n]; exact_mod_cast hm
  change 2-2*(((B i).card : ℝ)/Real.sqrt (n i))^2-(n i)⁻¹+
    (overlap (B i) (m i) : ℝ)/n i= ((A+A)ᶜ.card : ℝ)/n i
  rw [div_pow,Real.sq_sqrt (hn i).le]
  field_simp [(hn i).ne']
  linarith

end Families

/-- Every ordinary cyclic basis containing the two reflected Ruzsa layers
has eventual normalized size above each c < (3+√3)/(2√2). -/
theorem prime_extension_bound (p : ℕ → ℕ) [hp : ∀ i, Fact (p i).Prime]
    (t : ∀ i, ZMod (order (p i))) (ht : Tendsto p atTop atTop)
    (T : (i : ℕ) → Finset (ZMod (2*(order (p i)).val)))
    (hsub : ∀ i, primeLayers (p i) (t i) ⊆ T i) (hb : ∀ i, T i+T i=univ)
    {c : ℝ} (hc : c < (3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, c < ((T i).card : ℝ)/Real.sqrt (2*(order (p i)).val : ℕ) := by
  let B i := graph (ZMod (p i))
  let A i := primeLayers (p i) (t i)
  let k (i : ℕ) : ℝ := (p i-1 : ℕ)
  let m (i : ℕ) : ℝ := (order (p i)).val
  have hsid i : IsSidon (B i : Set (Plane (ZMod (p i)))) := Green33SidonProfile.graph_sidon (ZMod (p i))
  have hsz (i : ℕ) : (B i).card=(p i)-1 := by
    change (univ.image _).card=_
    rw [card_image_of_injective _ (fun a b h => Units.ext (congrArg Prod.snd h)),card_univ,ZMod.card_units]
  have hne i : (B i).Nonempty := card_pos.mp (by rw [hsz]; have := (hp i).out.one_lt; omega)
  have hcard (i : ℕ) : Fintype.card (Plane (ZMod (p i)))=(order (p i)).val := by
    simp only [Plane,order,Fintype.card_prod,Fintype.card_additive,ZMod.card_units,ZMod.card]
    rfl
  have hm (i : ℕ) : m i=k i*(k i+1) := by
    dsimp [m,k,order]; push_cast [Nat.cast_sub (hp i).out.one_le]; ring
  have hk₀ (i : ℕ) : 0<k i := by dsimp [k]; exact_mod_cast (show 0<p i-1 by have := (hp i).out.one_lt; omega)
  have hpos (i : ℕ) : 0<m i := by dsimp [m]; exact_mod_cast (order (p i)).pos
  have hkt : Tendsto k atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [ht.eventually_ge_atTop (j+1)] with i hi
    omega
  have hnt : Tendsto (fun i => Fintype.card (Plane (ZMod (p i)))) atTop atTop := by
    apply tendsto_atTop_mono _ ht
    intro i
    rw [hcard]
    change p i ≤ (p i-1)*p i
    exact Nat.le_mul_of_pos_left _ (by have := (hp i).out.one_lt; omega)
  have hsize : Tendsto (fun i => ((B i).card : ℝ)/Real.sqrt (Fintype.card (Plane (ZMod (p i))))) atTop (𝓝 1) := by
    have hkt' : Tendsto (fun i => k i+1) atTop atTop := hkt.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
    have hratio := (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℕ)) ).sub
      ((tendsto_const_nhds (x := (1:ℝ))).div_atTop hkt')
    rw [sub_zero] at hratio
    have hs : Tendsto (fun i => (k i)^2/m i) atTop (𝓝 1) := by
      apply hratio.congr
      intro i
      rw [hm]; field_simp [(hk₀ i).ne',show k i+1≠0 by linarith [hk₀ i]]; ring
    have h := hs.sqrt
    rw [Real.sqrt_one] at h
    apply h.congr
    intro i
    rw [hsz,hcard,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (hk₀ i).le]
  choose f j z hf hj _ he using fun i => primeLayers_structure (p i) (t i)
  have hkcard (i : ℕ) : Fintype.card (ZMod (2*(order (p i)).val))=2*Fintype.card (Plane (ZMod (p i))) := by rw [ZMod.card,hcard]
  have hh : Tendsto (fun i => (((layers (B i) (f i) (j i)+layers (B i) (f i) (j i))ᶜ.card : ℝ) /
        Fintype.card (Plane (ZMod (p i))))) atTop (𝓝 (1/4)) := by
    have h := (prime_hole_fraction p t ht).mul_const 2
    norm_num at h
    apply h.congr
    intro i
    change ((2*m i-((A i+A i).card : ℝ))/(2*m i))*2=_
    rw [← he,hcard]
    have hm' := card_compl_add_card (A i+A i)
    rw [ZMod.card] at hm'
    have hcm : (((A i+A i)ᶜ.card : ℝ)+(A i+A i).card)=2*m i := by dsimp [m]; exact_mod_cast hm'
    change _=((A i+A i)ᶜ.card : ℝ)/m i
    field_simp [(hpos i).ne']
    linarith
  have H := dense_extension_lower B hsid hne f hf j hj hkcard hnt hsize hh T
    (fun i => he i ▸ hsub i) hb hc
  simpa only [ZMod.card] using H

#print axioms fresh_mixed_bound
#print axioms repair_cost
#print axioms dense_extension_lower
#print axioms overlap_extension_lower
#print axioms prime_extension_bound

end Green33SidonLayerRepairs
