import Green33NearbyModuli
import Mathlib.Data.Sym.Card

/-! Bounds for loss and repair when a critical cyclic seed changes modulus. -/

open Finset Filter Green33RankSimplex Green33NearbyModuli
open scoped Pointwise Topology

namespace Green33FoldedTails

/-- The two nonnegative ranks have total at most t. -/
def triangle (t : ℕ) : Finset (ℕ×ℕ) :=
  ((range (t+1))×ˢ(range (t+1))).filter fun z => z.1+z.2≤t

private theorem mem_triangle {i j t : ℕ} : (i,j)∈triangle t ↔ i+j≤t := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h;exact mem_filter.mpr ⟨mk_mem_product (mem_range.mpr (by omega)) (mem_range.mpr (by omega)),h⟩

theorem triangle_count (t : ℕ) : 2*(triangle t).card=(t+1)*(t+2) := by
  have c : (triangle t).card=((range (t+1)).sigma fun i => range (i+1)).card := by
    apply card_nbij' (fun (p : ℕ×ℕ) => (⟨p.1+p.2,p.1⟩ : (i : ℕ) × ℕ))
      (fun p => (p.2,p.1-p.2))
    · rintro ⟨i,j⟩ hp
      have h := mem_triangle.mp hp
      exact mem_sigma.mpr ⟨mem_range.mpr (by dsimp;omega),mem_range.mpr (by dsimp;omega)⟩
    · rintro ⟨b,a⟩ hp
      obtain ⟨h,k⟩ := mem_sigma.mp hp
      have hb := mem_range.mp h;have ha := mem_range.mp k
      apply mem_triangle.mpr;dsimp at *;omega
    · rintro ⟨i,j⟩ _;simp
    · rintro ⟨b,a⟩ hp
      have l := mem_range.mp (mem_sigma.mp hp).2
      dsimp at l ⊢;rw [Nat.add_sub_of_le (by omega)]
  rw [c,card_sigma]
  simp only [card_range,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
  have h := sum_range_id_mul_two (t+1)
  simp at h
  nlinarith

private theorem tail_count (B T : Finset ℕ) (sub : T⊆B+B) (r : ℕ → ℕ)
    (inj : Set.InjOn r B) (t : ℕ)
    (cap : ∀ x∈B, ∀ y∈B, x+y∈T → r x+r y≤t) :
    2*T.card≤(triangle t).card+2*B.card := by
  let P := (B×ˢB).filter fun z => z.1+z.2∈T
  have size : P.card≤(triangle t).card := by
    apply card_le_card_of_injOn (fun z => (r z.1,r z.2))
    · rintro ⟨x,y⟩ h
      obtain ⟨hp,ht⟩ := mem_filter.mp h
      obtain ⟨hx,hy⟩ := mem_product.mp hp
      exact mem_triangle.mpr (cap x hx y hy ht)
    · rintro ⟨x,y⟩ h ⟨z,w⟩ k e
      obtain ⟨hx,hy⟩ := mem_product.mp (mem_filter.mp h).1
      obtain ⟨hz,hw⟩ := mem_product.mp (mem_filter.mp k).1
      exact Prod.ext (inj hx hz (congrArg Prod.fst e)) (inj hy hw (congrArg Prod.snd e))
  let D := B.image fun x => x+x
  let f (z : ℕ×ℕ) := (z.1+z.2,decide (z.1<z.2))
  have hit : (T \ D)×ˢ(univ:Finset Bool) ⊆ P.image f := by
    rintro ⟨z,b⟩ h
    obtain ⟨ht,nd⟩ := mem_sdiff.mp (mem_product.mp h).1
    obtain ⟨x,hx,y,hy,e⟩ := mem_add.mp (sub ht)
    change x+y=z at e
    subst z
    have ne : x≠y := by rintro rfl;exact nd (mem_image_of_mem _ hx)
    have up : (x,y)∈P := mem_filter.mpr ⟨mk_mem_product hx hy,ht⟩
    have dn : (y,x)∈P := mem_filter.mpr ⟨mk_mem_product hy hx,by simpa only [add_comm y x] using ht⟩
    rcases lt_or_gt_of_ne ne with l|l
    · cases b
      · exact mem_image.mpr ⟨_,dn,by simp [f,l.asymm,add_comm]⟩
      · exact mem_image.mpr ⟨_,up,by simp [f,l]⟩
    · cases b
      · exact mem_image.mpr ⟨_,up,by simp [f,l.asymm]⟩
      · exact mem_image.mpr ⟨_,dn,by simp [f,l,add_comm]⟩
  have c := (card_le_card hit).trans card_image_le
  simp only [card_product,card_univ,Fintype.card_bool] at c
  have d : D.card≤B.card := card_image_le
  have part := card_le_card_sdiff_add_card (s:=T) (t:=D)
  omega


/-- Largest rank sum needed in the two tails once the new modulus is at least d. -/
noncomputable def tailRadius {N : ℕ+} (A : Finset (ZMod N)) (d : ℕ) : ℕ :=
  ⌊((A.card:ℝ)-(d:ℝ)*((A.card:ℝ)/N)/2)+2*rankError A⌋₊

/-- Uniform collision bound for every modulus m ≥ d ≥ N. -/
theorem fold_tail_bound {N : ℕ+} (A : Finset (ZMod N)) (d m : ℕ) (large : N.val≤d) (dm : d ≤ m) :
    2*foldLoss (sums A) m≤(tailRadius A d+1)*(tailRadius A d+2)+4*A.card := by
  classical
  let B := labels A
  let C := sums A
  let U := C.filter (fun z => 2*z+d≤2*N.val)
  let V := C.filter (fun z => 2*N.val+d<2*z)
  let T := C.filter (fun x => x+m∈C)
  have all : ∀ x∈C, x<2*m := by
    intro x hx
    obtain ⟨r,hr,s,hs,rs⟩ := mem_add.mp hx
    obtain ⟨a,_,ea⟩ := mem_image.mp hr
    obtain ⟨b,_,eb⟩ := mem_image.mp hs
    have l := ZMod.val_lt a;have k := ZMod.val_lt b;omega
  have cut : T.card≤U.card+V.card := by
    have one : T.filter (fun x => 2*x+d≤2*N.val)⊆U := by
      intro x hx
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp hx).2⟩
    have two : (T.filter (fun x => ¬2*x+d≤2*N.val)).card≤V.card := by
      apply card_le_card_of_injOn (fun x => x+m)
      · intro x hx
        obtain ⟨ht,k⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨(mem_filter.mp ht).2,by change 2*N.val+d<2*(x+m);omega⟩
      · exact fun _ _ _ _ eq => Nat.add_right_cancel eq
    have h := card_filter_add_card_filter_not (s:=T) (fun x => 2*x+d≤2*N.val)
    exact h ▸ Nat.add_le_add (card_le_card one) two
  let e := B.orderIsoOfFin (labels_card A)
  let r (x : ℕ) : ℕ := if hx : x∈B then (e.symm ⟨x,hx⟩).val else 0
  have inj : Set.InjOn r B := by
    intro x hx y hy eq
    change x∈B at hx
    change y∈B at hy
    simp only [r,dif_pos hx,dif_pos hy] at eq
    exact congrArg Subtype.val (e.symm.injective (Fin.ext eq))
  have small {x : ℕ} (hx : x∈B) : r x<A.card := by simp only [r,dif_pos hx];exact Fin.isLt _
  have err {x : ℕ} (hx : x∈B) : |(r x:ℝ)-x*((A.card:ℝ)/N)|≤rankError A := by
    have v : B.orderEmbOfFin (labels_card A) (e.symm ⟨x,hx⟩)=x :=
      congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
    simpa only [r,dif_pos hx,v,B] using rank_bound A (e.symm ⟨x,hx⟩)
  let c : ℝ := A.card/(N:ℝ)
  have nn : 0≤c := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have nk : (N:ℝ)*c=A.card := by dsimp [c];field_simp
  have low := tail_count B U (filter_subset ..) r inj (tailRadius A d) (by
    intro x hx y hy pair
    apply Nat.le_floor
    have z : 2*((x:ℝ)+y)+d≤2*(N:ℝ) := by exact_mod_cast (mem_filter.mp pair).2
    have l := (abs_le.mp (err hx)).2;have k := (abs_le.mp (err hy)).2
    push_cast
    change (r x:ℝ)+r y≤A.card-d*c/2+2*rankError A
    change (r x:ℝ)-x*c≤_ at l
    change (r y:ℝ)-y*c≤_ at k
    nlinarith [mul_le_mul_of_nonneg_right z nn])
  let s x := A.card-1-r x
  have sinj : Set.InjOn s B := by
    intro x hx y hy eq
    apply inj hx hy
    dsimp [s] at eq
    have h := small hx;have k := small hy;omega
  have high := tail_count B V (filter_subset ..) s sinj (tailRadius A d) (by
    intro x hx y hy pair
    apply Nat.le_floor
    have z : 2*(N:ℝ)+d≤2*((x:ℝ)+y) := by exact_mod_cast (mem_filter.mp pair).2.le
    have l := (abs_le.mp (err hx)).1;have k := (abs_le.mp (err hy)).1
    have comp (x : ℕ) (hx : x∈B) : (s x:ℝ)+(r x:ℝ)≤A.card := by
      exact_mod_cast (show s x+r x≤A.card by have h := small hx;dsimp [s];omega)
    push_cast
    change (s x:ℝ)+s y≤A.card-d*c/2+2*rankError A
    change _≤(r x:ℝ)-x*c at l
    change _≤(r y:ℝ)-y*c at k
    nlinarith [mul_le_mul_of_nonneg_right z nn,comp x hx,comp y hy])
  have sz : B.card=A.card := labels_card A
  have loss : foldLoss (sums A) m=T.card := foldLoss_eq C m all
  rw [loss]
  nlinarith [triangle_count (tailRadius A d)]


private theorem radius_limit {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (d : ℕ → ℕ) (endpt : ∀ᶠ i in atTop, d i≤2*(N i).val)
    {s : ℝ} (rate : Tendsto (fun i => (d i:ℝ)/(N i)) atTop (𝓝 s)) :
    Tendsto (fun i => (tailRadius (A i) (d i):ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2*(2-s)/2)) := by
  let f (i : ℕ) := ((A i).card:ℝ)-(d i:ℝ)*((A i).card/(N i:ℝ))/2+2*rankError (A i)
  have err := rankError_vanish A big size cover
  have pred := (size.sub ((rate.mul size).div_const 2)).add (err.const_mul 2)
  have lim : Tendsto (fun i => f i/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2*(2-s)/2)) := by
    convert pred using 1
    · ext i;dsimp [f];ring
    · congr 1; ring
  have tiny : Tendsto (fun i => 1/Real.sqrt (N i)) atTop (𝓝 (0:ℝ)) := tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
  have lo := lim.sub tiny
  rw [sub_zero] at lo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo lim
  · filter_upwards with i
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact le_of_lt (by linarith [Nat.lt_floor_add_one (f i)] : f i-1 < (⌊f i⌋₊:ℝ))
  · filter_upwards [endpt] with i hi
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Nat.floor_le
    have a : (d i:ℝ)≤2*(N i:ℝ) := by exact_mod_cast hi
    have b := mul_le_mul_of_nonneg_right a (div_nonneg (Nat.cast_nonneg (α:=ℝ) (A i).card) (Nat.cast_nonneg (N i).val))
    have pos : (N i:ℝ)≠0 := by exact_mod_cast (N i).pos.ne'
    have c : (2*(N i:ℝ))*((A i).card/(N i:ℝ))=2*(A i).card := by field_simp
    have e : 0≤rankError (A i) := abs_nonneg _
    linarith

/-- Uniform loss bound (2−s)²/4 for all m above a moving threshold
d with d/N tending to s between one and two. -/
theorem uniform_tail_loss {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (d : ℕ → ℕ) (band : ∀ᶠ i in atTop, (N i).val≤d i ∧ d i≤2*(N i).val)
    {s : ℝ} (rate : Tendsto (fun i => (d i:ℝ)/(N i)) atTop (𝓝 s))
    {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ i in atTop, ∀ m≥d i, (foldLoss (sums (A i)) m:ℝ)/(N i)≤(2-s)^2/4+ε := by
  let r i := tailRadius (A i) (d i)
  have rad := radius_limit A big size cover d (band.mono fun _ h => h.2) rate
  have tiny (k : ℝ) : Tendsto (fun i => k/Real.sqrt (N i)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
  have u := rad.add (tiny 1)
  have v := rad.add (tiny 2)
  have w := size.mul (tiny 4)
  have lim := (((u.mul v).add w).div_const 2)
  have target : ((Real.sqrt 2*(2-s)/2+0)*(Real.sqrt 2*(2-s)/2+0)+Real.sqrt 2*0)/2=(2-s)^2/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),
      show (Real.sqrt 2*(2-s))^2=2*(2-s)^2 by rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]]
  rw [target] at lim
  filter_upwards [band,lim.eventually_lt_const (lt_add_of_pos_right _ ep)] with i hi si
  intro m hm
  have np : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have raw := fold_tail_bound (A i) (d i) m hi.1 hm
  have b : 2*(foldLoss (sums (A i)) m:ℝ)≤((r i:ℝ)+1)*(r i+2)+4*(A i).card := by exact_mod_cast raw
  apply le_trans _ si.le
  change _ ≤ (((r i:ℝ)/_+1/_)*((r i:ℝ)/_+2/_)+((A i).card/_)*(4/_))/2
  rw [← add_div,← add_div,div_mul_div_comm,div_mul_div_comm,Real.mul_self_sqrt np.le,← add_div]
  rw [div_div,le_div_iff₀ (mul_pos np (by norm_num)),← mul_assoc,div_mul_cancel₀ _ np.ne']
  linarith


/-- Moduli in [a,b) at which reduction identifies at least γN of
the distinct ordinary integer sums. -/
noncomputable def lossOrders {N : ℕ+} (A : Finset (ZMod N)) (a b : ℕ) (γ : ℝ) : Finset ℕ :=
  (Ico a b).filter fun m => γ≤(foldLoss (sums A) m:ℝ)/N

private theorem count_above (W : Finset ℕ) (f : ℕ → ℝ) {g u : ℝ} (cap : ∀ m∈W, f m≤u) :
    ∑ m ∈ W, f m ≤ g*W.card+(u-g)*((W.filter fun m => g≤f m).card:ℝ) := by
  classical
  calc
    _ ≤ ∑ m ∈ W, (g+if g≤f m then u-g else 0) := by
      apply sum_le_sum;intro m hm
      split_ifs with h
      · linarith [cap m hm]
      · linarith [lt_of_not_ge h]
    _ = _ := by simp [sum_add_distrib,sum_ite,Finset.sum_const,nsmul_eq_mul,mul_comm];ring

/-- A lower bound on the fraction of moduli with prescribed loss, on
any fixed macroscopic interval strictly between normalized orders 1 and 2,
including intervals starting at 1. -/
theorem band_prevalence {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (a b : ℕ → ℕ) (band : ∀ᶠ i in atTop, (N i).val≤a i ∧ a i≤b i)
    {s t : ℝ} (st : s<t) (lt : t<2)
    (lo : Tendsto (fun i => (a i:ℝ)/(N i)) atTop (𝓝 s))
    (hi : Tendsto (fun i => (b i:ℝ)/(N i)) atTop (𝓝 t))
    {γ p : ℝ} (γu : γ≤(2-s)^2/4) (p1 : p≤1)
    (gap : γ+((2-s)^2/4-γ)*p < ((2-s)^4-(2-t)^4)/(24*(t-s))) :
    ∀ᶠ i in atTop, p*((Ico (a i) (b i)).card:ℝ)<(lossOrders (A i) (a i) (b i) γ).card := by
  let u := (2-s)^2/4
  let v := ((2-s)^4-(2-t)^4)/(24*(t-s))
  let e := (v-(γ+(u-γ)*p))/2
  have ep : 0<e := by change 0<(v-(γ+(u-γ)*p))/2;change γ+(u-γ)*p<v at gap;linarith
  have bound : (γ+(u+e-γ)*p)*(t-s)<((2-s)^4-(2-t)^4)/24 := by
    have h : γ+(u+e-γ)*p<v := by
      dsimp [e];change γ+(u-γ)*p<v at gap
      nlinarith [mul_le_mul_of_nonneg_left p1 ep.le]
    calc
      _ < v*(t-s) := mul_lt_mul_of_pos_right h (sub_pos.mpr st)
      _ = _ := by dsimp [v];field_simp [sub_ne_zero.mpr st.ne']
  let W i := Ico (a i) (b i)
  have width : Tendsto (fun i => ((W i).card:ℝ)/(N i)) atTop (𝓝 (t-s)) := by
    apply (hi.sub lo).congr'
    filter_upwards [band] with i h
    simp [W,Nat.card_Ico,Nat.cast_sub h.2,sub_div]
  have cap := uniform_tail_loss A big size cover a (band.and (lo.eventually_lt_const (st.trans lt)) |>.mono
    (fun i ⟨h,lim⟩ => ⟨h.1,by
      have q : (0:ℝ)<N i := by exact_mod_cast (N i).pos
      exact_mod_cast ((div_lt_iff₀ q).mp lim).le⟩)) lo ep
  have mean := band_limit A big size cover a b band st.le lt lo hi
  have ev := (width.const_mul (γ+(u+e-γ)*p)).eventually_lt mean bound
  filter_upwards [cap,ev] with i boundLoss high
  by_contra! few
  let n : ℝ := N i
  have pos : 0<n := by dsimp [n];exact_mod_cast (N i).pos
  let F (m : ℕ) : ℝ := (foldLoss (sums (A i)) m:ℝ)/n
  have count := count_above (W i) F (g:=γ) (u:=u+e) (fun m hm => boundLoss m (mem_Ico.mp hm).1)
  change _≤γ*(W i).card+(u+e-γ)*(lossOrders (A i) (a i) (b i) γ).card at count
  have few' := mul_le_mul_of_nonneg_left few (show 0≤u+e-γ by change γ≤u at γu;linarith)
  have mass : (∑ m ∈ W i, F m)≤(γ+(u+e-γ)*p)*(W i).card := by
    change _≤(u+e-γ)*(p*(W i).card) at few';nlinarith
  simp only [F,← Finset.sum_div] at mass
  have upper := div_le_div_of_nonneg_right mass pos.le
  change (γ+(u+e-γ)*p)*((W i).card/n)<((∑ m ∈ W i, foldLoss (sums (A i)) m:ℕ):ℝ)/n^2 at high
  push_cast at high
  rw [div_div,← sq] at upper
  linarith [show (γ+(u+e-γ)*p)*(W i).card/n=(γ+(u+e-γ)*p)*((W i).card/n) by ring]


private theorem pair_cap {G : Type*} [AddCommMonoid G] [DecidableEq G] (B : Finset G) :
    2*(B+B).card≤B.card*(B.card+1) := by
  let f : Sym2 G → G := Sym2.lift ⟨(·+·),add_comm⟩
  have sub : B+B ⊆ B.sym2.image f := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    exact mem_image.mpr ⟨s(x,y),mk_mem_sym2_iff.mpr ⟨hx,hy⟩,rfl⟩
  have h := (card_le_card sub).trans card_image_le
  rw [card_sym2,Nat.choose_two_right] at h
  simp only [Nat.add_sub_cancel] at h
  simpa only [mul_comm] using (Nat.le_div_iff_mul_le (by decide : 0<2)).mp h

private theorem sums_limit {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun i => ((sums (A i)).card:ℝ)/(N i)) atTop (𝓝 1) := by
  have tiny : Tendsto (fun i => 1/Real.sqrt (N i)) atTop (𝓝 (0:ℝ)) := tendsto_const_nhds.div_atTop
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
  have upper := (size.mul (size.add tiny)).div_const 2
  rw [add_zero,← sq,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),div_self (by norm_num)] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le cover upper
  · intro i
    have same : (labels (A i)).image (fun x : ℕ => (x:ZMod (N i)))=A i := by
      simp [labels,image_image,Function.comp_def]
    have balance := cyclic_balance (labels (A i)) (N i)
    dsimp only at balance
    rw [same] at balance
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (by change _≤(labels (A i)+labels (A i)).card;omega)) (Nat.cast_nonneg _)
  · intro i
    have cap := pair_cap (labels (A i))
    rw [labels_card] at cap
    have b : 2*((sums (A i)).card:ℝ)≤(A i).card*((A i).card+1) := by exact_mod_cast cap
    have pos : (0:ℝ)<N i := by exact_mod_cast (N i).pos
    dsimp only
    rw [← add_div,div_mul_div_comm,Real.mul_self_sqrt pos.le,div_div,
      le_div_iff₀ (mul_pos pos (by norm_num)),← mul_assoc,div_mul_cancel₀ _ pos.ne']
    linarith

/-- The actual cyclic sumset formed by reusing the least labels occupies
asymptotically at least 1−s/4 of any modulus m with m/N → s in [1,2]. -/
theorem recast_floor {N M : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (band : ∀ᶠ i in atTop, (N i).val≤(M i).val ∧ (M i).val≤2*(N i).val)
    {s : ℝ} (sp : 0<s) (rate : Tendsto (fun i => (M i:ℝ)/(N i)) atTop (𝓝 s))
    {v : ℝ} (lt : v<1-s/4) : ∀ᶠ i in atTop,
    v < ((recast (A i) (M i)+recast (A i) (M i)).card:ℝ)/(M i) := by
  let e := (1-(2-s)^2/4-v*s)/2
  have ep : 0<e := by dsimp [e];nlinarith [mul_lt_mul_of_pos_right lt sp]
  have margin : v*s+((2-s)^2/4+e)<1 := by dsimp [e];nlinarith [mul_lt_mul_of_pos_right lt sp]
  have test := ((rate.const_mul v).add (tendsto_const_nhds (x:=(2-s)^2/4+e))).eventually_lt
    (sums_limit A big size cover) margin
  have cap := uniform_tail_loss A big size cover (fun i => (M i).val) band rate ep
  filter_upwards [test,cap] with i hi ci
  have b := ci _ le_rfl
  have bal := cyclic_balance (labels (A i)) (M i)
  change foldLoss (sums (A i)) _+(recast (A i) (M i)+recast (A i) (M i)).card=(sums (A i)).card at bal
  have np : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have mp : (0:ℝ)<M i := by exact_mod_cast (M i).pos
  rw [lt_div_iff₀ mp]
  apply (div_lt_div_iff_of_pos_right np).mp
  rw [mul_div_assoc]
  change v*((M i:ℝ)/(N i))+_<_ at hi
  rw [← bal,Nat.cast_add,add_div] at hi
  linarith


/-- The next ⌊δN⌋ orders strictly above N. -/
noncomputable def window (n : ℕ) (δ : ℝ) : Finset ℕ := Ico (n+1) (n+1+⌊δ*n⌋₊)

/-- Orders in the window missing at least the fraction η of their residues. -/
noncomputable def incomplete {N : ℕ+} (A : Finset (ZMod N)) (δ η : ℝ) : Finset ℕ :=
  (window N.val δ).filter fun m => (((sums A).image (·%m)).card:ℝ)≤(1-η)*m

theorem mem_incomplete {N : ℕ+} (A : Finset (ZMod N)) (δ η : ℝ) (m : ℕ+) :
    m.val∈incomplete A δ η ↔ m.val∈window N.val δ ∧
    ((recast A m+recast A m).card:ℝ)/m≤1-η := by
  have bal := cyclic_balance (labels A) m
  change foldLoss (sums A) m.val+(recast A m+recast A m).card=(sums A).card at bal
  have le : ((sums A).image (·%m.val)).card≤(sums A).card := card_image_le
  simp only [foldLoss] at bal
  have eq : (recast A m+recast A m).card=((sums A).image (·%m.val)).card := by omega
  simp only [incomplete,mem_filter,eq,div_le_iff₀ (show (0:ℝ)< m by exact_mod_cast m.pos)]

/-- For every positive tolerance ε, at least a 2/3−ε fraction of the
next ⌊δN⌋ moduli miss a fixed positive fraction of their residues.
The width δ may be any fixed positive value up to min(ε,1/3)/4. -/
theorem nearby_two_thirds {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    {ε δ : ℝ} (ep : 0<ε) (dp : 0<δ) (width : δ≤ min ε (1/3)/4) : ∀ᶠ i in atTop,
    (2/3-ε)*((window (N i).val δ).card:ℝ)<(incomplete (A i) δ (min ε (1/3)/32)).card := by
  let h := min ε (1/3:ℝ)
  have hp : 0<h := lt_min ep (by norm_num)
  have h1 : h≤1/3 := min_le_right ..
  have he : h≤ε := min_le_left ..
  have dh : δ≤h/4 := width
  let a i := (N i).val+1
  let b i := (N i).val+1+⌊δ*(N i:ℝ)⌋₊
  have np (i) : (0:ℝ)<N i := by exact_mod_cast (N i).pos
  have tiny : Tendsto (fun i => 1/(N i:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp big)
  have lo : Tendsto (fun i => (a i:ℝ)/(N i)) atTop (𝓝 1) := by
    simpa [a,add_div,(np _).ne'] using (tendsto_const_nhds (x:=(1:ℝ))).add tiny
  have span : Tendsto (fun i => (⌊δ*(N i:ℝ)⌋₊:ℝ)/(N i)) atTop (𝓝 δ) := by
    have lower := (tendsto_const_nhds (x:=δ)).sub tiny
    rw [sub_zero] at lower
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le lower tendsto_const_nhds
    · intro i;rw [le_div_iff₀ (np i),sub_mul,div_mul_cancel₀ _ (np i).ne']
      linarith [Nat.lt_floor_add_one (δ*(N i:ℝ))]
    · intro i;exact (div_le_iff₀ (np i)).mpr (Nat.floor_le (mul_nonneg dp.le (np i).le))
  have hi : Tendsto (fun i => (b i:ℝ)/(N i)) atTop (𝓝 (1+δ)) := by simpa [a,b,add_div] using lo.add span
  have gap : h/16+((2-1)^2/4-h/16)*(2/3-h) <
      ((2-1)^4-(2-(1+δ))^4)/(24*(1+δ-1)) := by
    apply (lt_div_iff₀ (by linarith : 0<24*(1+δ-1))).mpr
    have ha : h/16+((2-1)^2/4-h/16)*(2/3-h)<1/6-δ/4 := by
      nlinarith [mul_le_mul_of_nonneg_left h1 hp.le]
    have hb := mul_lt_mul_of_pos_right ha (show 0<24*(1+δ-1) by linarith)
    nlinarith [mul_nonneg (pow_nonneg dp.le 3) (show 0≤4-δ by linarith)]
  have freq := band_prevalence A big size cover a b (Eventually.of_forall (fun i => ⟨Nat.le_succ _,Nat.le_add_right ..⟩))
    (by linarith : (1:ℝ)<1+δ) (by linarith) lo hi (by nlinarith : h/16≤(2-1)^2/4)
    (by linarith : 2/3-h≤1) gap
  have clip := (sums_limit A big size cover).eventually_lt_const (show (1:ℝ)<1+h/32 by linarith)
  filter_upwards [freq,clip] with i many sz
  have sub : lossOrders (A i) (a i) (b i) (h/16)⊆incomplete (A i) δ (h/32) := by
    intro m hm
    obtain ⟨hm,drop⟩ := mem_filter.mp hm
    refine mem_filter.mpr ⟨hm,?_⟩
    change h/16≤(foldLoss (sums (A i)) m:ℝ)/(N i) at drop
    have fl := (le_div_iff₀ (np i)).mp drop
    have su := (div_lt_iff₀ (np i)).mp sz
    have eq := Nat.sub_add_cancel (card_image_le (s:=sums (A i)) (f:=(·%m)))
    have total : (foldLoss (sums (A i)) m:ℝ)+((sums (A i)).image (·%m)).card=(sums (A i)).card := by exact_mod_cast eq
    have order : (N i:ℝ)≤ m := by exact_mod_cast (Nat.le_succ _).trans (mem_Ico.mp hm).1
    nlinarith [mul_le_mul_of_nonneg_left order (show 0≤1-h/32 by linarith)]
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left he _) (Nat.cast_nonneg _)).trans_lt
    (many.trans_le (Nat.cast_le.mpr (card_le_card sub)))


/-- Only unordered pairs using a changed label can cover a residue that
was previously missing. This finite bound permits repeated summands. -/
theorem repair_capacity {G : Type*} [AddCommMonoid G] [DecidableEq G] (C B : Finset G) :
    (B∩C).card*((B∩C).card+1)+2*(B+B).card ≤ B.card*(B.card+1)+2*(C+C).card := by
  let R := B∩C
  let f : Sym2 G → G := Sym2.lift ⟨(·+·),add_comm⟩
  have hit : (B+B) \ (C+C) ⊆ (B.sym2 \ R.sym2).image f := by
    intro z hz
    obtain ⟨hs,miss⟩ := mem_sdiff.mp hz
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hs
    refine mem_image.mpr ⟨s(x,y),mem_sdiff.mpr ⟨mk_mem_sym2_iff.mpr ⟨hx,hy⟩,?_⟩,rfl⟩
    intro both
    obtain ⟨u,v⟩ := mk_mem_sym2_iff.mp both
    exact miss (mem_add.mpr ⟨x,(mem_inter.mp u).2,y,(mem_inter.mp v).2,rfl⟩)
  have cap := (card_le_card hit).trans card_image_le
  have pairs := card_sdiff_add_card_eq_card (sym2_mono (show R⊆B from inter_subset_left))
  have part := card_le_card_sdiff_add_card (s:=B+B) (t:=C+C)
  have twice (X : Finset G) : 2*X.sym2.card=X.card*(X.card+1) := by
    rw [card_sym2,mul_comm 2]
    simpa only [Nat.choose_one_right,Nat.add_sub_cancel,Nat.reduceAdd,mul_comm] using Nat.choose_succ_right_eq (X.card+1) 1
  change R.card*(R.card+1)+_≤_
  rw [← twice R,← twice B]
  omega

/-- Arbitrarily near the original order, every near-critical full repair
at a witness modulus retains less than a prescribed fraction r of its
labels from the old seed, for every sqrt(5/6) < r ≤ 1. -/
theorem nearby_repair {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    {r : ℝ} (lower : Real.sqrt (5/6)<r) (one : r≤1) :
    ∃ τ : ℝ, 0<τ ∧ ∀ ε : ℝ, 0<ε → ∀ᶠ i in atTop, ∃ m : ℕ+,
      (N i).val< m.val ∧ (m:ℝ)≤(1+ε)*(N i:ℝ) ∧ ∀ B : Finset (ZMod m),
      B+B=univ → (B.card:ℝ)*(B.card+1)≤(2+τ)*m →
      ((B∩recast (A i) m).card:ℝ)<r*B.card := by
  let τ := (2*r^2-5/3)/4
  have rp := (Real.sqrt_nonneg _).trans_lt lower
  have tp : 0<τ := by
    dsimp [τ];nlinarith [mul_self_lt_mul_self (Real.sqrt_nonneg _) lower,Real.sq_sqrt (by norm_num : (0:ℝ)≤5/6)]
  have gap : (2+τ)*(1-r^2)<1/3-2*τ := by
    dsimp [τ] at *;nlinarith [mul_nonneg tp.le (sq_nonneg r)]
  refine ⟨τ,tp,fun ε ep => ?_⟩
  filter_upwards [nearby_sixth A big size cover (lt_min ep tp)] with i witness
  obtain ⟨m,inc,bnd,cov⟩ := witness
  refine ⟨m,inc,bnd.trans (mul_le_mul_of_nonneg_right (by linarith [min_le_left ε τ]) (Nat.cast_nonneg _)),?_⟩
  intro B full budget
  by_contra! keep
  let C := recast (A i) m
  let b : ℝ := B.card
  let k : ℝ := (B∩C).card
  have capacity := repair_capacity C B
  rw [full,card_univ,ZMod.card] at capacity
  have fin : k*(k+1)+2*(m:ℝ)≤b*(b+1)+2*(C+C).card := by
    dsimp only [b,k];exact_mod_cast capacity
  have bn : 0≤b := Nat.cast_nonneg _
  have kn : 0≤k := Nat.cast_nonneg _
  change r*b≤k at keep
  change b*(b+1)≤_ at budget
  have kept : r^2*b*(b+1)≤k*(k+1) := by
    have small : r^2≤r := by nlinarith [mul_nonneg rp.le (sub_nonneg.mpr one)]
    nlinarith [mul_self_le_mul_self (mul_nonneg rp.le bn) keep,mul_le_mul_of_nonneg_right small bn]
  have pos : (0:ℝ)< m := by exact_mod_cast m.pos
  have miss : ((C+C).card:ℝ)≤(5/6+τ)*m := ((div_le_iff₀ pos).mp cov).trans
    (mul_le_mul_of_nonneg_right (by linarith [min_le_right ε τ]) pos.le)
  have mult := mul_le_mul_of_nonneg_right budget (show 0≤1-r^2 by nlinarith [mul_nonneg rp.le (sub_nonneg.mpr one)])
  nlinarith [mul_lt_mul_of_pos_right gap pos]

#print axioms triangle_count
#print axioms fold_tail_bound
#print axioms uniform_tail_loss
#print axioms band_prevalence
#print axioms recast_floor
#print axioms mem_incomplete
#print axioms nearby_two_thirds
#print axioms repair_capacity
#print axioms nearby_repair
end Green33FoldedTails
