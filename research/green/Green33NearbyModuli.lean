import Green33RotatedIntervals
import Green33RankSimplex

/-! How the integer sumset of a cyclic seed changes under reduction at a larger modulus. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33NearbyModuli

/-- Distinct integer sums lost on reduction modulo `n`. -/
def foldLoss (C : Finset ℕ) (n : ℕ) : ℕ := C.card-(C.image (·%n)).card

/-- If every integer lies below twice the modulus, each loss corresponds
to one pair at distance exactly the modulus. -/
theorem foldLoss_eq (C : Finset ℕ) (n : ℕ) (bound : ∀ x∈C, x<2*n) :
    foldLoss C n=(C.filter fun x => x+n∈C).card := by
  let L := C.filter (·<n)
  let H := C.filter (fun x => ¬x<n)
  let U := H.image (·-n)
  have memU (x) : x∈U ↔ x<n ∧ x+n∈C := by
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      obtain ⟨mem,hi⟩ := mem_filter.mp hy
      have := bound y mem
      exact ⟨by omega,by simpa [Nat.sub_add_cancel (by omega : n≤y)] using mem⟩
    · rintro ⟨_,hc⟩
      exact mem_image.mpr ⟨x+n,mem_filter.mpr ⟨hc,by omega⟩,by omega⟩
  have uc : U.card=H.card := by
    apply card_image_iff.mpr
    intro a ha b hb eq
    have := (mem_filter.mp ha).2
    have := (mem_filter.mp hb).2
    change a-n=b-n at eq
    omega
  have both : C.image (·%n)=L∪U := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      by_cases lo : a<n
      · exact mem_union_left _ (by rw [Nat.mod_eq_of_lt lo];exact mem_filter.mpr ⟨ha,lo⟩)
      · have small := bound a ha
        have fit : a-n<n := by omega
        rw [Nat.mod_eq_sub_mod (by omega : n≤a),Nat.mod_eq_of_lt fit]
        exact mem_union_right _ (mem_image.mpr ⟨a,mem_filter.mpr ⟨ha,lo⟩,rfl⟩)
    · intro hx
      rcases mem_union.mp hx with low|high
      · obtain ⟨mem,lt⟩ := mem_filter.mp low
        exact mem_image.mpr ⟨x,mem,Nat.mod_eq_of_lt lt⟩
      · obtain ⟨lt,mem⟩ := (memU x).mp high
        exact mem_image.mpr ⟨x+n,mem,by simp [Nat.mod_eq_of_lt lt]⟩
  have duplicate : L∩U=C.filter (fun x => x+n∈C) := by
    ext x
    simp only [mem_inter,L,mem_filter,memU]
    constructor
    · rintro ⟨⟨a,_⟩,_,b⟩; exact ⟨a,b⟩
    · rintro ⟨a,b⟩
      have := bound (x+n) b
      exact ⟨⟨a,by omega⟩,by omega,b⟩
  have split : L.card+H.card=C.card := card_filter_add_card_filter_not ..
  have e := card_union_add_card_inter L U
  rw [duplicate,← both,uc] at e
  unfold foldLoss
  omega

/-- Summing losses over an interval of moduli equals the number of
ordered pairs of distinct integer values with a gap in the interval. -/
theorem band_losses (C : Finset ℕ) (a b : ℕ) (bound : ∀ x∈C, x<2*a) :
    ∑ n ∈ Ico a b, foldLoss C n=
      ((C×ˢC).filter fun z => z.1+a≤z.2 ∧ z.2<z.1+b).card := by
  have term (n) (hn : n∈Ico a b) : foldLoss C n=(C.filter fun x => x+n∈C).card :=
    foldLoss_eq _ _ fun x hx => (bound x hx).trans_le (Nat.mul_le_mul_left _ (mem_Ico.mp hn).1)
  rw [sum_congr rfl term]
  let S := ((Ico a b)×ˢC).filter fun z => z.2+z.1∈C
  have count : ∑ n ∈ Ico a b, (C.filter fun x => x+n∈C).card=S.card := by
    simp only [card_eq_sum_ones,S,sum_filter,sum_product]
  rw [count]
  apply card_nbij' (fun z => (z.2,z.2+z.1)) (fun z => (z.2-z.1,z.1))
  · rintro ⟨n,x⟩ hz
    obtain ⟨⟨hn,hx⟩,hs⟩ := (by simpa only [mem_coe,S,mem_filter,mem_product] using hz :
      (n∈Ico a b ∧ x∈C) ∧ x+n∈C)
    exact mem_filter.mpr ⟨mk_mem_product hx hs,by simpa using mem_Ico.mp hn⟩
  · rintro ⟨x,y⟩ hz
    obtain ⟨⟨hx,hy⟩,lo,hi⟩ := (by simpa only [mem_coe,mem_filter,mem_product] using hz :
      (x∈C ∧ y∈C) ∧ x+a≤y ∧ y<x+b)
    exact mem_filter.mpr ⟨mk_mem_product (mem_Ico.mpr ⟨by omega,by omega⟩) hx,
      by simpa [show x+(y-x)=y by omega] using hy⟩
  · rintro ⟨n,x⟩ _; simp
  · rintro ⟨x,y⟩ hz
    have lo := (mem_filter.mp hz).2.1
    simp only [Prod.mk.injEq,true_and]
    change x+(y-x)=y
    change x+a≤y at lo
    omega


/-- The number lost by the integer fold is exactly the drop in the size
of the actual cyclic sumset of the same labels. -/
theorem cyclic_balance (B : Finset ℕ) (n : ℕ+) :
    let A := B.image (fun x : ℕ => (x:ZMod n))
    foldLoss (B+B) n.val+(A+A).card=(B+B).card := by
  let A := B.image (fun x : ℕ => (x:ZMod n))
  have eq : (A+A).image ZMod.val=(B+B).image (·%n.val) := by
    ext z
    constructor
    · intro hz
      obtain ⟨_,hs,rfl⟩ := mem_image.mp hz
      obtain ⟨_,hx,_,hy,rfl⟩ := mem_add.mp hs
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨a+b,Finset.mem_add.mpr ⟨a,ha,b,hb,rfl⟩,by rw [← Nat.cast_add,ZMod.val_natCast]⟩
    · intro hz
      obtain ⟨_,hs,rfl⟩ := mem_image.mp hz
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hs
      refine mem_image.mpr ⟨(a:ZMod n)+(b:ZMod n),mem_add.mpr
        ⟨_,mem_image_of_mem _ ha,_,mem_image_of_mem _ hb,rfl⟩,?_⟩
      rw [← Nat.cast_add,ZMod.val_natCast]
  have card := congrArg Finset.card eq
  rw [card_image_of_injective _ (ZMod.val_injective _)] at card
  change (B+B).card-((B+B).image (·%n.val)).card+(A+A).card=(B+B).card
  rw [card,Nat.sub_add_cancel card_image_le]

/-- Endpoint pairs coming from two selected blocks of integer sums force
a loss somewhere in the prescribed band of larger moduli. -/
theorem loss_witness (C L H : Finset ℕ) (a b : ℕ) (ab : a<b)
    (bound : ∀ x∈C, x<2*a) (lo : L⊆C) (hi : H⊆C)
    (gap : ∀ x∈L, ∀ y∈H, x+a≤y ∧ y<x+b) :
    ∃ n∈Ico a b, L.card*H.card≤(b-a)*foldLoss C n := by
  have sub : L×ˢH⊆(C×ˢC).filter (fun z => z.1+a≤z.2 ∧ z.2<z.1+b) := by
    rintro ⟨x,y⟩ hm
    obtain ⟨hx,hy⟩ := mem_product.mp hm
    exact mem_filter.mpr ⟨mk_mem_product (lo hx) (hi hy),gap x hx y hy⟩
  have total := card_le_card sub
  rw [card_product,← band_losses C a b bound] at total
  obtain ⟨n,hn,maxi⟩ := exists_max_image (Ico a b) (foldLoss C) (nonempty_Ico.mpr ab)
  refine ⟨n,hn,total.trans ?_⟩
  simpa [nsmul_eq_mul] using sum_le_sum (fun m (hm : m∈Ico a b) => maxi m hm)


open Green33RankSimplex

variable {M : ℕ+}

/-- The unreduced integer sumset, using the least representatives. -/
def sums (A : Finset (ZMod M)) : Finset ℕ := labels A+labels A

private def off (A : Finset (ZMod M)) : Finset ℕ :=
  sums A \ (labels A).image (fun x => x+x)

private def pairCode (A : Finset (ZMod M)) (i j : Fin A.card) : ℕ×Bool :=
  (labelAt A i+labelAt A j,decide (labelAt A i<labelAt A j))

private theorem pair_hit (A : Finset (ZMod M)) {x : ℕ} (hx : x∈off A) (b : Bool) :
    ∃ i j, pairCode A i j=(x,b) := by
  obtain ⟨h,hd⟩ := mem_sdiff.mp hx
  obtain ⟨a,ha,c,hc,rfl⟩ := mem_add.mp h
  have ne : a≠c := fun eq => hd (eq ▸ mem_image_of_mem _ ha)
  rw [← image_orderEmbOfFin_univ (labels A) (labels_card A)] at ha hc
  obtain ⟨i,_,rfl⟩ := mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := mem_image.mp hc
  change labelAt A i≠labelAt A j at ne
  change ∃ r t, pairCode A r t=(labelAt A i+labelAt A j,b)
  rcases lt_or_gt_of_ne ne with lt|lt <;> cases b
  · exact ⟨j,i,by simp [pairCode,lt.asymm,add_comm]⟩
  · exact ⟨i,j,by simp [pairCode,lt]⟩
  · exact ⟨i,j,by simp [pairCode,lt.asymm]⟩
  · exact ⟨j,i,by simp [pairCode,lt,add_comm]⟩

private def lowerSum (A : Finset (ZMod M)) (z : Fin 4 → Fin A.card) :=
  labelAt A (z 0)+labelAt A (z 1)

private def upperSum (A : Finset (ZMod M)) (z : Fin 4 → Fin A.card) :=
  labelAt A (z 2).rev+labelAt A (z 3).rev

private theorem quad_hit (A : Finset (ZMod M)) (p : ℕ → ℕ → Prop) [DecidableRel p] :
    4*(((off A)×ˢ(off A)).filter (fun z => p z.1 z.2)).card≤
      (univ.filter (fun z : Fin 4 → Fin A.card => p (lowerSum A z) (upperSum A z))).card := by
  let f (z : Fin 4 → Fin A.card) : (ℕ×ℕ)×(Bool×Bool) :=
    ((lowerSum A z,upperSum A z),((pairCode A (z 0) (z 1)).2,(pairCode A (z 2).rev (z 3).rev).2))
  let W := univ.filter (fun z : Fin 4 → Fin A.card => p (lowerSum A z) (upperSum A z))
  let D := ((off A)×ˢ(off A)).filter (fun z => p z.1 z.2)
  have sub : D×ˢ(univ : Finset (Bool×Bool))⊆W.image f := by
    rintro ⟨⟨a,c⟩,b,d⟩ h
    obtain ⟨hm,hp⟩ := mem_filter.mp (mem_product.mp h).1
    obtain ⟨ha,hc⟩ := mem_product.mp hm
    obtain ⟨i,j,e⟩ := pair_hit A ha b
    obtain ⟨k,l,t⟩ := pair_hit A hc d
    let z : Fin 4 → Fin A.card := ![i,j,k.rev,l.rev]
    have es := congrArg Prod.fst e
    have ts := congrArg Prod.fst t
    have eb := congrArg Prod.snd e
    have tb := congrArg Prod.snd t
    change labelAt A i+labelAt A j=a at es
    change labelAt A k+labelAt A l=c at ts
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,by simpa [lowerSum,upperSum,z,es,ts] using hp⟩,
      by simp [f,z,lowerSum,upperSum,es,ts,eb,tb]⟩
  have cap := (card_le_card sub).trans card_image_le
  simpa [W,D,Nat.mul_comm] using cap

/-- Distinct integer sum pairs above the gap threshold. -/
def gapPairs (C : Finset ℕ) (g : ℕ) : Finset (ℕ×ℕ) :=
  (C×ˢC).filter fun z => z.1+g≤z.2

private theorem tuple_comparison (A : Finset (ZMod M)) (g : ℕ) :
    let c := (sums A).card
    let d := (off A).card
    let u := (gapPairs (sums A) g).card
    let v := (gapTuples A g).card
    4*u+4*d^2≤v+4*c^2 ∧ v+4*d^2≤4*u+A.card^4 := by
  let p (a b : ℕ) := a+g≤b
  let C := sums A×ˢsums A
  let D := off A×ˢoff A
  let Q := (univ : Finset (Fin 4 → Fin A.card))
  have sub : D⊆C := product_subset_product sdiff_subset sdiff_subset
  have hit := quad_hit A p
  have miss := quad_hit A (fun a b => ¬p a b)
  have cs := card_filter_add_card_filter_not (s:=C) (fun z => p z.1 z.2)
  have ds := card_filter_add_card_filter_not (s:=D) (fun z => p z.1 z.2)
  have qs := card_filter_add_card_filter_not (s:=Q) (fun z => p (lowerSum A z) (upperSum A z))
  have lo := card_le_card (filter_subset_filter (fun z => p z.1 z.2) sub)
  have hi := card_le_card (filter_subset_filter (fun z => ¬p z.1 z.2) sub)
  change 4*(D.filter _).card≤(Q.filter _).card at hit miss
  have cc : C.card=(sums A).card^2 := by simp [C,sq]
  have dc : D.card=(off A).card^2 := by simp [D,sq]
  have qc : Q.card=A.card^4 := by simp [Q,Fintype.card_pi]
  change 4*(C.filter (fun z => p z.1 z.2)).card+4*(off A).card^2≤(Q.filter (fun z => p (lowerSum A z) (upperSum A z))).card+4*(sums A).card^2 ∧
    (Q.filter (fun z => p (lowerSum A z) (upperSum A z))).card+4*(off A).card^2≤4*(C.filter (fun z => p z.1 z.2)).card+A.card^4
  omega


private theorem sizes (A : Finset (ZMod M)) :
    (A+A).card≤(sums A).card ∧ (sums A).card≤(off A).card+A.card ∧
      2*(off A).card≤A.card^2 := by
  have back : (labels A).image (fun x : ℕ => (x:ZMod M))=A := by
    simp [labels,image_image]
  have bal := cyclic_balance (labels A) M
  dsimp only at bal
  rw [back] at bal
  refine ⟨by dsimp [sums]; omega,?_,?_⟩
  · have bound := card_le_card_sdiff_add_card (s:=sums A) (t:=(labels A).image (fun x => x+x))
    have small : ((labels A).image (fun x => x+x)).card≤A.card := card_image_le.trans_eq (labels_card A)
    change (sums A).card≤((sums A) \ _).card+A.card
    omega
  · let f (p : Fin A.card×Fin A.card) := pairCode A p.1 p.2
    have sub : off A×ˢ(univ : Finset Bool)⊆univ.image f := by
      rintro ⟨x,b⟩ h
      obtain ⟨i,j,e⟩ := pair_hit A (mem_product.mp h).1 b
      exact mem_image.mpr ⟨(i,j),mem_univ _,e⟩
    simpa [sq,Nat.mul_comm] using (card_le_card sub).trans card_image_le

private theorem sizes_limit {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun i => ((sums (A i)).card:ℝ)/(N i:ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun i => ((off (A i)).card:ℝ)/(N i:ℝ)) atTop (𝓝 1) := by
  have k : Tendsto (fun i => ((A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 0) := by
    have lim := size.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
    simpa only [Function.comp_apply,div_div,← sq,Real.sq_sqrt (Nat.cast_nonneg _)] using lim
  have half : Tendsto (fun i => ((A i).card:ℝ)^2/(N i:ℝ)/2) atTop (𝓝 1) := by
    simpa only [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt (Nat.cast_nonneg _),
      div_self (by norm_num : (2:ℝ)≠0)] using (size.pow 2).div_const 2
  have hp i : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have ds : Tendsto (fun i => ((off (A i)).card:ℝ)/(N i:ℝ)) atTop (𝓝 1) := by
    have lo := cover.sub k
    rw [sub_zero] at lo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le lo half
    · intro i
      dsimp only
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ (hp i).le
      have h : ((A i+A i).card:ℝ)≤(off (A i)).card+(A i).card := by
        exact_mod_cast (sizes (A i)).1.trans (sizes (A i)).2.1
      linarith
    · intro i
      have h : 2*((off (A i)).card:ℝ)≤((A i).card:ℝ)^2 := by exact_mod_cast (sizes (A i)).2.2
      field_simp [hp i]
      linarith
  refine ⟨?_,ds⟩
  have hi := ds.add k
  rw [add_zero] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le cover hi
  · intro i; exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (sizes (A i)).1) (hp i).le
  · intro i
    dsimp only
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (hp i).le
    exact_mod_cast (sizes (A i)).2.1

/-- For an asymptotically optimal almost-cover, distinct integer sum
pairs with gap at least `s N` have limiting mass `(2-s)^4/24`. -/
theorem gapPairs_limit {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (g : ℕ → ℕ) (large : ∀ᶠ i in atTop, (N i).val≤g i) {s : ℝ} (lt : s<2)
    (ratio : Tendsto (fun i => (g i:ℝ)/(N i:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun i => ((gapPairs (sums (A i)) (g i)).card:ℝ)/(N i:ℝ)^2) atTop (𝓝 ((2-s)^4/24)) := by
  have sqs := sizes_limit A big size cover
  have quad := gapTuples_limit A big size cover g large lt ratio
  have k : Tendsto (fun i => ((A i).card:ℝ)^2/(N i:ℝ)) atTop (𝓝 2) := by
    simpa only [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sq_sqrt (Nat.cast_nonneg _)] using size.pow 2
  have lo := ((quad.add ((sqs.2.pow 2).const_mul 4)).sub (k.pow 2)).div_const 4
  have hi := ((quad.add ((sqs.1.pow 2).const_mul 4)).sub ((sqs.2.pow 2).const_mul 4)).div_const 4
  rw [show ((2-s)^4/6+4*1^2-2^2)/4=(2-s)^4/24 by ring] at lo
  rw [show ((2-s)^4/6+4*1^2-4*1^2)/4=(2-s)^4/24 by ring] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lo hi
  · intro i
    have hp : (0:ℝ)<N i := by exact_mod_cast (N i).pos
    have h := (tuple_comparison (A i) (g i)).2
    have h' := (Nat.cast_le (α:=ℝ)).mpr h
    push_cast at h'
    dsimp only
    rw [div_pow,div_pow]
    field_simp [hp]
    linarith
  · intro i
    have hp : (0:ℝ)<N i := by exact_mod_cast (N i).pos
    have h := (tuple_comparison (A i) (g i)).1
    have h' := (Nat.cast_le (α:=ℝ)).mpr h
    push_cast at h'
    dsimp only
    rw [div_pow,div_pow]
    field_simp [hp]
    linarith


private theorem sums_lt (A : Finset (ZMod M)) {x : ℕ} (hx : x∈sums A) : x<2*M.val := by
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
  obtain ⟨u,_,rfl⟩ := mem_image.mp ha
  obtain ⟨v,_,rfl⟩ := mem_image.mp hb
  have hu := ZMod.val_lt u
  have hv := ZMod.val_lt v
  omega

private theorem tail_difference (C : Finset ℕ) (a b : ℕ) (ab : a≤b)
    (bound : ∀ x∈C, x<2*a) :
    (∑ m ∈ Ico a b, foldLoss C m)+(gapPairs C b).card=(gapPairs C a).card := by
  have split : ((C×ˢC).filter fun z => z.1+a≤z.2 ∧ z.2<z.1+b)=gapPairs C a \ gapPairs C b := by
    ext z; simp [gapPairs]; tauto
  have sub : gapPairs C b⊆gapPairs C a := by
    intro z hz
    obtain ⟨hm,h⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hm,by change z.1+b≤z.2 at h; omega⟩
  rw [band_losses _ _ _ bound,split,card_sdiff_add_card_eq_card sub]

/-- Total loss of distinct integer sums in a band of larger moduli,
normalized by the square of the original order. The endpoints may move. -/
theorem band_limit {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (a b : ℕ → ℕ) (band : ∀ᶠ i in atTop, (N i).val≤a i ∧ a i≤b i)
    {s t : ℝ} (st : s≤t) (lt : t<2)
    (lo : Tendsto (fun i => (a i:ℝ)/(N i:ℝ)) atTop (𝓝 s))
    (hi : Tendsto (fun i => (b i:ℝ)/(N i:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun i => ((∑ m ∈ Ico (a i) (b i), foldLoss (sums (A i)) m:ℕ):ℝ)/(N i:ℝ)^2) atTop
      (𝓝 (((2-s)^4-(2-t)^4)/24)) := by
  have low := gapPairs_limit A big size cover a (band.mono fun _ h => h.1) (st.trans_lt lt) lo
  have high := gapPairs_limit A big size cover b (band.mono fun _ h => h.1.trans h.2) lt hi
  rw [sub_div]
  apply (low.sub high).congr'
  filter_upwards [band] with i h
  rw [← sub_div]
  congr 1
  have eq := tail_difference (sums (A i)) (a i) (b i) h.2 (fun _ hx => (sums_lt _ hx).trans_le
    (Nat.mul_le_mul_left _ h.1))
  exact sub_eq_iff_eq_add.mpr (by exact_mod_cast eq.symm)

/-- Reinterpret the original least representatives at a positive modulus. -/
def recast (A : Finset (ZMod M)) (m : ℕ+) : Finset (ZMod m) :=
  (labels A).image (fun x : ℕ => (x:ZMod m))

private theorem small_band (δ : ℝ) (dpos : 0<δ) (dsmall : δ<1) {N : ℕ → ℕ+}
    (A : ∀ i, Finset (ZMod (N i))) (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1)) :
    let a i := (N i).val+1
    let b i := ⌊(1+δ)*(N i:ℝ)⌋₊+1
    Tendsto (fun i => ((∑ m ∈ Ico (a i) (b i), foldLoss (sums (A i)) m:ℕ):ℝ)/
      ((b i:ℝ)-(a i:ℝ))/(N i:ℝ)) atTop (𝓝 ((1-(1-δ)^4)/(24*δ))) := by
  let a i := (N i).val+1
  let b i := ⌊(1+δ)*(N i:ℝ)⌋₊+1
  have mp i : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have inv : Tendsto (fun i => 1/(N i:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp big)
  have al : Tendsto (fun i => (a i:ℝ)/(N i:ℝ)) atTop (𝓝 1) := by
    simpa [a,add_div,(mp _).ne'] using (tendsto_const_nhds (x:=(1:ℝ))).add inv
  have fit i : 0≤(1+δ)*(N i:ℝ) := mul_nonneg (by linarith) (mp i).le
  have le i : (N i:ℝ)≤(1+δ)*(N i:ℝ) := by nlinarith [mul_nonneg dpos.le (mp i).le]
  have bl : Tendsto (fun i => (b i:ℝ)/(N i:ℝ)) atTop (𝓝 (1+δ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun i => (1+δ)+1/(N i:ℝ)) atTop (𝓝 (1+δ)) by simpa using tendsto_const_nhds.add inv)
    · intro i
      rw [le_div_iff₀ (mp i)]
      simpa [b] using (Nat.lt_floor_add_one ((1+δ)*(N i:ℝ))).le
    · intro i
      dsimp only
      rw [div_le_iff₀ (mp i),add_mul,div_mul_cancel₀ _ (mp i).ne']
      simpa [b] using Nat.floor_le (fit i)
  have band := band_limit A big size cover a b (Eventually.of_forall (fun i => ⟨Nat.le_succ _,
    Nat.succ_le_succ (Nat.le_floor (le i))⟩)) (by linarith : (1:ℝ)≤1+δ) (by linarith) al bl
  have diff := bl.sub al
  rw [show (1+δ)-1=δ by ring] at diff
  convert band.div diff dpos.ne' using 1
  · funext i
    simp only [Pi.div_apply]
    rw [← sub_div]
    change _/((b i:ℝ)-(a i:ℝ))/(N i:ℝ)=_/((N i:ℝ)^2)/(((b i:ℝ)-(a i:ℝ))/(N i:ℝ))
    rw [div_div_eq_mul_div]
    field_simp [(mp i).ne']
    ring
  · ring


/-- Every critical cyclic almost-cover has a strictly larger, arbitrarily
nearby modulus where its original least representatives cover at most
`5/6 + ε` of the new group. The seed is held fixed. -/
theorem nearby_sixth {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ i in atTop, ∃ m : ℕ+, (N i).val < m.val ∧ (m:ℝ)≤(1+ε)*(N i:ℝ) ∧
      ((recast (A i) m+recast (A i) m).card:ℝ)/(m:ℝ)≤5/6+ε := by
  let d := min ε (1/2:ℝ)
  have dp : 0<d := lt_min ep (by norm_num)
  have de : d≤ε := min_le_left _ _
  have dh : d≤1/2 := min_le_right _ _
  let a i := (N i).val+1
  let b i := ⌊(1+d)*(N i:ℝ)⌋₊+1
  let T i : ℕ := ∑ m ∈ Ico (a i) (b i), foldLoss (sums (A i)) m
  let avg i : ℝ := (T i:ℝ)/((b i:ℝ)-(a i:ℝ))/(N i:ℝ)
  let v := (1-(1-d)^4)/(24*d)
  have vl : Tendsto avg atTop (𝓝 v) := small_band d dp (by linarith) A big size cover
  have poly : v=1/6-d/4+d^2/6-d^3/24 := by dsimp [v]; field_simp; ring
  have pp : 0≤d^2*(4-d) := mul_nonneg (sq_nonneg _) (by linarith)
  have vp : 0<v := by rw [poly]; nlinarith
  have wanted : 1-v<5/6+ε := by rw [poly]; nlinarith
  have close := ((sizes_limit A big size cover).1.sub vl).eventually_lt_const wanted
  filter_upwards [vl.eventually_const_lt vp,close] with i nonempty close
  have ab : a i<b i := by
    by_contra! bad
    have nil : Ico (a i) (b i)=∅ := Ico_eq_empty_of_le bad
    simp [avg,T,nil] at nonempty
  obtain ⟨m,hm,mx⟩ := exists_max_image (Ico (a i) (b i)) (foldLoss (sums (A i))) (nonempty_Ico.mpr ab)
  obtain ⟨lo,hi⟩ := mem_Ico.mp hm
  have more : (N i).val < m := lo
  let n : ℕ+ := ⟨m,(N i).pos.trans more⟩
  have small : m≤⌊(1+d)*(N i:ℝ)⌋₊ := Nat.le_of_lt_succ hi
  have mp : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have np : (N i:ℝ)≤n := by exact_mod_cast more.le
  have nfit : (m:ℝ)≤(1+ε)*(N i:ℝ) :=
    ((Nat.cast_le.mpr small).trans (Nat.floor_le (mul_nonneg (by linarith) mp.le))).trans
      (mul_le_mul_of_nonneg_right (by linarith) mp.le)
  refine ⟨n,more,nfit,?_⟩
  have mass : T i≤(b i-a i)*foldLoss (sums (A i)) m := by
    simpa [T,nsmul_eq_mul] using sum_le_sum (fun j (hj : j∈Ico (a i) (b i)) => mx j hj)
  have width : (0:ℝ)<(b i:ℝ)-(a i:ℝ) := sub_pos.mpr (Nat.cast_lt.mpr ab)
  have av : avg i≤(foldLoss (sums (A i)) m:ℝ)/(N i:ℝ) := by
    apply div_le_div_of_nonneg_right _ mp.le
    apply (div_le_iff₀ width).mpr
    rw [← Nat.cast_sub ab.le,mul_comm,← Nat.cast_mul]
    exact_mod_cast mass
  have eq := cyclic_balance (labels (A i)) n
  change foldLoss (sums (A i)) m+(recast (A i) n+recast (A i) n).card=(sums (A i)).card at eq
  have re := congrArg (Nat.cast (R:=ℝ)) eq
  push_cast at re
  apply (div_le_div_of_nonneg_left (Nat.cast_nonneg _) mp np).trans
  have diff : ((recast (A i) n+recast (A i) n).card:ℝ)/(N i:ℝ)=
      ((sums (A i)).card:ℝ)/(N i:ℝ)-(foldLoss (sums (A i)) m:ℝ)/(N i:ℝ) := by
    rw [← sub_div]; congr 1; linarith
  rw [diff]
  exact (sub_le_sub_left av _).trans close.le

#print axioms foldLoss_eq
#print axioms band_losses
#print axioms cyclic_balance
#print axioms loss_witness
#print axioms gapPairs_limit
#print axioms band_limit
#print axioms nearby_sixth
end Green33NearbyModuli
