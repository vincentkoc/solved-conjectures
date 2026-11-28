import Green33ArcDistribution
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

/-! Sorted cyclic labels and the four-coordinate integer simplex. -/

open Finset Filter Green33ArcDistribution
open scoped Pointwise Topology

namespace Green33RankSimplex

variable {M : ℕ+}

/-- The least nonnegative representatives. -/
def labels (A : Finset (ZMod M)) : Finset ℕ := A.image ZMod.val

theorem labels_card (A : Finset (ZMod M)) : (labels A).card=A.card :=
  card_image_of_injective _ (ZMod.val_injective _)

private noncomputable def prefixError (A : Finset (ZMod M)) (w : ℕ) : ℝ :=
  |((A∩arc 0 w).card:ℝ)-(w:ℝ)*((A.card:ℝ)/M)|

private noncomputable def worst (A : Finset (ZMod M)) : ℕ :=
  (exists_max_image (range (M.val+1)) (prefixError A) (nonempty_range_iff.mpr (Nat.succ_ne_zero _))).choose

private theorem worst_spec (A : Finset (ZMod M)) :
    worst A≤M.val ∧ ∀ w≤M.val, prefixError A w≤prefixError A (worst A) := by
  obtain ⟨hw,hm⟩ := (exists_max_image (range (M.val+1)) (prefixError A) (nonempty_range_iff.mpr (Nat.succ_ne_zero _))).choose_spec
  exact ⟨Nat.le_of_lt_succ (mem_range.mp hw),fun w h => hm w (mem_range.mpr (Nat.lt_succ_of_le h))⟩

/-- The largest absolute error of the prefix counts, in units of labels. -/
noncomputable def rankError (A : Finset (ZMod M)) : ℝ := prefixError A (worst A)

private theorem prefix_card (A : Finset (ZMod M)) {w : ℕ} (fit : w≤M.val) :
    (A∩arc 0 w).card=((labels A).filter (·<w)).card := by
  have eq : (A∩arc 0 w).image ZMod.val=(labels A).filter (·<w) := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,hm,rfl⟩ := mem_image.mp hv
      obtain ⟨ha,hb⟩ := mem_inter.mp hm
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
      refine mem_filter.mpr ⟨mem_image_of_mem _ ha,?_⟩
      simpa [ZMod.val_natCast,Nat.mod_eq_of_lt ((mem_range.mp hj).trans_le fit)] using mem_range.mp hj
    · intro hv
      obtain ⟨ha,lt⟩ := mem_filter.mp hv
      change v∈A.image ZMod.val at ha
      obtain ⟨a,hA,rfl⟩ := mem_image.mp ha
      exact mem_image.mpr ⟨a,mem_inter.mpr ⟨hA,mem_image.mpr ⟨a.val,mem_range.mpr lt,by simp⟩⟩,rfl⟩
  rw [← eq,card_image_of_injective _ (ZMod.val_injective _)]

private theorem rank_card (B : Finset ℕ) {k : ℕ} (eq : B.card=k) (j : Fin k) :
    (B.filter (·<B.orderEmbOfFin eq j)).card=j.val := by
  let e := B.orderEmbOfFin eq
  have obj : (Iio j).image e=B.filter (·<e j) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨orderEmbOfFin_mem ..,e.strictMono (mem_Iio.mp hi)⟩
    · intro hx
      obtain ⟨hb,lt⟩ := mem_filter.mp hx
      rw [← image_orderEmbOfFin_univ B eq] at hb
      obtain ⟨i,_,rfl⟩ := mem_image.mp hb
      exact mem_image.mpr ⟨i,mem_Iio.mpr (e.lt_iff_lt.mp lt),rfl⟩
  change (B.filter (·<e j)).card=_
  rw [← obj,card_image_of_injective _ e.injective,Fin.card_Iio]

/-- The rank of every label differs from its uniformly spaced prediction
by at most the worst prefix discrepancy. -/
theorem rank_bound (A : Finset (ZMod M)) (j : Fin A.card) :
    let v := (labels A).orderEmbOfFin (labels_card A) j
    |(j:ℝ)-(v:ℝ)*((A.card:ℝ)/M)|≤rankError A := by
  let v := (labels A).orderEmbOfFin (labels_card A) j
  have hv : v∈labels A := orderEmbOfFin_mem ..
  obtain ⟨a,_,he⟩ := mem_image.mp hv
  have fit : v≤M.val := he ▸ (ZMod.val_lt a).le
  have bound := (worst_spec A).2 v fit
  rw [prefixError,prefix_card A fit,rank_card (labels A) (labels_card A) j] at bound
  exact bound

/-- The maximum prefix discrepancy is negligible at the size scale of
a critical almost-cover. -/
theorem rankError_vanish {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1)) :
    Tendsto (fun i => rankError (A i)/Real.sqrt (N i)) atTop (𝓝 0) := by
  have arc := arc_distribution A big size cover (fun _ => 0) (fun i => worst (A i))
    (fun i => (worst_spec _).1)
  simpa only [rankError,prefixError,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),abs_zero] using arc.abs


/-- Four ranks whose sum is at most the given integer. -/
def simplex (k t : ℕ) : Finset (Fin 4 → Fin k) :=
  univ.filter fun z => ∑ j, (z j).val≤t

private def pack {k t : ℕ} (x : simplex k t) :
    {v : Fin 5 → ℕ // ∑ j, v j=t} :=
  ⟨Fin.cons (t-∑ j, (x.val j).val) (fun j => (x.val j).val), by
    rw [Fin.sum_univ_succ]
    simpa using Nat.sub_add_cancel (mem_filter.mp x.prop).2⟩

private theorem pack_injective (k t : ℕ) : Function.Injective (@pack k t) := by
  intro x y h
  apply Subtype.ext
  funext j
  exact Fin.ext (congrArg (fun z => z.val j.succ) h)

private theorem bars (t : ℕ) : Fintype.card (Sym (Fin 5) t)=(t+4).choose 4 := by
  rw [Sym.card_sym_eq_choose,Fintype.card_fin,show 5+t-1=t+4 by omega,Nat.choose_symm_add]

/-- Stars and bars bounds the count at every threshold, with equality
while the simplex fits in the rank cube. -/
theorem simplex_count (k t : ℕ) :
    (simplex k t).card≤(t+4).choose 4 ∧ (t<k → (simplex k t).card=(t+4).choose 4) := by
  classical
  let e := Sym.equivNatSumOfFintype (Fin 5) t
  let f : simplex k t → Sym (Fin 5) t := e.symm ∘ pack
  have inj : Function.Injective f := e.symm.injective.comp (pack_injective ..)
  rw [← bars,← Fintype.card_coe (simplex k t)]
  refine ⟨Fintype.card_le_of_injective f inj,fun fit => Fintype.card_congr (Equiv.ofBijective f ⟨inj,?_⟩)⟩
  intro s
  let v := e s
  have total := v.prop
  rw [Fin.sum_univ_succ] at total
  have lt (j : Fin 4) : v.val j.succ<k := by
    have sub : v.val j.succ≤∑ i : Fin 4, v.val i.succ := single_le_sum (f:=fun i : Fin 4 => v.val i.succ)
      (fun _ _ => Nat.zero_le _) (mem_univ j)
    omega
  let z (j : Fin 4) : Fin k := ⟨v.val j.succ,lt j⟩
  have hz : z∈simplex k t := mem_filter.mpr ⟨mem_univ _,by change (∑ j : Fin 4,v.val j.succ)≤t; omega⟩
  refine ⟨⟨z,hz⟩,e.injective ?_⟩
  change e (e.symm _)=v
  rw [e.apply_symm_apply]
  apply Subtype.ext
  funext j
  refine Fin.cases ?_ (fun _ => rfl) j
  change t-(∑ i : Fin 4,v.val i.succ)=v.val 0
  omega


/-- The least representative at position `j` in increasing order. -/
def labelAt (A : Finset (ZMod M)) (j : Fin A.card) : ℕ :=
  (labels A).orderEmbOfFin (labels_card A) j

/-- Ordered quadruples of labels whose second sum exceeds the first by
at least `g`. The two upper labels are indexed in reverse order. -/
def gapTuples (A : Finset (ZMod M)) (g : ℕ) : Finset (Fin 4 → Fin A.card) :=
  univ.filter fun z => labelAt A (z 0)+labelAt A (z 1)+g≤labelAt A (z 2).rev+labelAt A (z 3).rev

private noncomputable def cutoff (A : Finset (ZMod M)) (g : ℕ) : ℝ :=
  2*A.card-2-g*((A.card:ℝ)/M)

private theorem rankError_nonneg (A : Finset (ZMod M)) : 0≤rankError A := abs_nonneg _

private theorem tuple_bounds (A : Finset (ZMod M)) (g : ℕ) (z : Fin 4 → Fin A.card) :
    let t := cutoff A g
    let d := 4*rankError A
    ((∑ j, ((z j).val:ℝ))≤t-d → z∈gapTuples A g) ∧
    (z∈gapTuples A g → (∑ j, ((z j).val:ℝ))≤t+d) := by
  let c : ℝ := (A.card:ℝ)/M
  have kp : 0<A.card := Nat.zero_lt_of_lt (z 0).isLt
  have cp : 0<c := div_pos (by exact_mod_cast kp) (by exact_mod_cast M.pos)
  have b (j : Fin A.card) := abs_le.mp (rank_bound A j)
  have rev (j : Fin A.card) : ((j.rev.val:ℕ):ℝ)=A.card-1-j.val := by
    have eq : j.rev.val+1+j.val=A.card := by rw [Fin.val_rev]; omega
    linarith [show (j.rev.val:ℝ)+1+j.val=A.card by exact_mod_cast eq]
  have a₀ := b (z 0)
  have a₁ := b (z 1)
  have a₂ := b (z 2).rev
  have a₃ := b (z 3).rev
  change -rankError A≤_-(labelAt A _ : ℝ)*c ∧ _-(labelAt A _ : ℝ)*c≤rankError A at a₀ a₁ a₂ a₃
  simp only [rev] at a₂ a₃
  dsimp only [cutoff]
  rw [Fin.sum_univ_four]
  change (_ ≤ 2*(A.card:ℝ)-2-g*c-_ → _) ∧ (_ → _ ≤ 2*(A.card:ℝ)-2-g*c+_)
  constructor
  · intro h
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    apply (Nat.cast_le (α:=ℝ)).mp
    push_cast
    apply (mul_le_mul_iff_of_pos_right cp).mp
    linarith
  · intro h
    have cmp := (mem_filter.mp h).2
    have realCmp : (labelAt A (z 0):ℝ)+labelAt A (z 1)+g≤labelAt A (z 2).rev+labelAt A (z 3).rev := by exact_mod_cast cmp
    linarith [mul_le_mul_of_nonneg_right realCmp cp.le]

/-- The sorted-rank simplex bounds the four-label count above and below.
Both thresholds are measured in units of ranks. -/
theorem gap_bounds (A : Finset (ZMod M)) (g : ℕ) (large : M.val≤g)
    (room : 0≤cutoff A g-4*rankError A) :
    (⌊cutoff A g-4*rankError A⌋₊+4).choose 4≤(gapTuples A g).card ∧
      (gapTuples A g).card≤(⌊cutoff A g+4*rankError A⌋₊+4).choose 4 := by
  let L := ⌊cutoff A g-4*rankError A⌋₊
  let U := ⌊cutoff A g+4*rankError A⌋₊
  have low : simplex A.card L⊆gapTuples A g := by
    intro z hz
    apply (tuple_bounds A g z).1
    exact (show (∑ j, ((z j).val:ℝ))≤L by exact_mod_cast (mem_filter.mp hz).2).trans (Nat.floor_le room)
  have high : gapTuples A g⊆simplex A.card U := by
    intro z hz
    refine mem_filter.mpr ⟨mem_univ _,Nat.le_floor ?_⟩
    simpa only [Nat.cast_sum] using (tuple_bounds A g z).2 hz
  have m : (0:ℝ)<M := by exact_mod_cast M.pos
  have ge := mul_le_mul_of_nonneg_right (show (M:ℝ)≤g by exact_mod_cast large)
    (div_nonneg (Nat.cast_nonneg A.card) m.le)
  rw [show (M:ℝ)*(A.card/(M:ℝ))=A.card by field_simp] at ge
  have small : L<A.card := by
    have le := Nat.floor_le room
    change (L:ℝ)≤2*A.card-2-g*((A.card:ℝ)/M)-4*rankError A at le
    exact_mod_cast (show (L:ℝ)<A.card by linarith [rankError_nonneg A])
  exact ⟨((simplex_count _ _).2 small).symm.le.trans (card_le_card low),
    (card_le_card high).trans (simplex_count _ _).1⟩


private theorem floor_scaled {f h : ℕ → ℝ} {a : ℝ} (positive : 0<a)
    (hp : ∀ i, 0<h i) (large : Tendsto h atTop atTop)
    (lim : Tendsto (fun i => f i/h i) atTop (𝓝 a)) :
    Tendsto (fun i => (⌊f i⌋₊:ℝ)/h i) atTop (𝓝 a) := by
  have small : Tendsto (fun i => 1/h i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop large
  have lower := lim.sub small
  rw [sub_zero] at lower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower lim
  · filter_upwards with i
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (hp i).le
    linarith [Nat.lt_floor_add_one (f i)]
  · filter_upwards [lim.eventually_const_lt positive] with i hi
    exact div_le_div_of_nonneg_right (Nat.floor_le ((div_pos_iff_of_pos_right (hp i)).mp hi |>.le)) (hp i).le

private theorem choose4_poly (t : ℕ) :
    (((t+4).choose 4:ℕ):ℝ)=(t+1)*(t+2)*(t+3)*(t+4)/24 := by
  have eq := Nat.ascFactorial_eq_factorial_mul_choose t 4
  norm_num [Nat.ascFactorial_succ,Nat.factorial] at eq
  have re := congrArg (Nat.cast (R:=ℝ)) eq
  push_cast at re
  linarith

private theorem choose4_scaled {t : ℕ → ℕ} {h : ℕ → ℝ} {a : ℝ}
    (large : Tendsto h atTop atTop)
    (lim : Tendsto (fun i => (t i:ℝ)/h i) atTop (𝓝 a)) :
    Tendsto (fun i => (((t i+4).choose 4:ℕ):ℝ)/(h i)^4) atTop (𝓝 (a^4/24)) := by
  have shift (j : ℕ) : Tendsto (fun i => ((t i:ℝ)+j)/h i) atTop (𝓝 a) := by
    have small : Tendsto (fun i => (j:ℝ)/h i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop large
    simpa only [add_div,add_zero] using lim.add small
  have four := ((((shift 1).mul (shift 2)).mul (shift 3)).mul (shift 4)).div_const 24
  convert four using 1
  · funext i
    rw [choose4_poly]
    push_cast
    ring
  · ring

/-- For gaps converging to a fraction `s` of the original order, the
ordered four-label tail has the limiting four-simplex volume. -/
theorem gapTuples_limit {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(N i:ℝ)) atTop (𝓝 1))
    (g : ℕ → ℕ) (large : ∀ᶠ i in atTop, (N i).val≤g i) {s : ℝ} (lt : s<2)
    (ratio : Tendsto (fun i => (g i:ℝ)/(N i:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun i => ((gapTuples (A i) (g i)).card:ℝ)/(N i:ℝ)^2) atTop (𝓝 ((2-s)^4/6)) := by
  let h (i : ℕ) := Real.sqrt (N i)
  let T i := cutoff (A i) (g i)
  let d i := 4*rankError (A i)
  let v := (2-s)*Real.sqrt 2
  have pos : 0<v := mul_pos (sub_pos.mpr lt) (by positivity)
  have hp i : 0<h i := Real.sqrt_pos.mpr (by exact_mod_cast (N i).pos)
  have ht : Tendsto h atTop atTop := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
  have two : Tendsto (fun i => 2/h i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have tl : Tendsto (fun i => T i/h i) atTop (𝓝 v) := by
    have lim := ((size.const_mul 2).sub two).sub (ratio.mul size)
    convert lim using 1
    · funext i; dsimp [T,h,cutoff]; ring
    · dsimp [v]; ring
  have dl : Tendsto (fun i => d i/h i) atTop (𝓝 0) := by
    simpa only [d,h,mul_div_assoc,mul_zero] using (rankError_vanish A big size cover).const_mul 4
  have L : Tendsto (fun i => (T i-d i)/h i) atTop (𝓝 v) := by simpa only [sub_div,sub_zero] using tl.sub dl
  have U : Tendsto (fun i => (T i+d i)/h i) atTop (𝓝 v) := by simpa only [add_div,add_zero] using tl.add dl
  have below := choose4_scaled ht (floor_scaled pos hp ht L)
  have above := choose4_scaled ht (floor_scaled pos hp ht U)
  have limits : Tendsto (fun i => ((gapTuples (A i) (g i)).card:ℝ)/(h i)^4) atTop (𝓝 (v^4/24)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' below above
    · filter_upwards [large,L.eventually_const_lt pos] with i hi room
      exact div_le_div_of_nonneg_right (by exact_mod_cast (gap_bounds (A i) (g i) hi
        ((div_pos_iff_of_pos_right (hp i)).mp room).le).1)
        (by positivity)
    · filter_upwards [large,L.eventually_const_lt pos] with i hi room
      exact div_le_div_of_nonneg_right (by exact_mod_cast (gap_bounds (A i) (g i) hi
        ((div_pos_iff_of_pos_right (hp i)).mp room).le).2)
        (by positivity)
  convert limits using 1
  · funext i
    rw [show (h i)^4=((N i:ℝ))^2 by rw [show (h i)^4=((h i)^2)^2 by ring,Real.sq_sqrt (Nat.cast_nonneg _)]]
  · dsimp [v]
    rw [mul_pow,show (Real.sqrt 2)^4=((Real.sqrt 2)^2)^2 by ring,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    ring

#print axioms labels_card
#print axioms rank_bound
#print axioms rankError_vanish
#print axioms simplex_count
#print axioms gap_bounds
#print axioms gapTuples_limit
end Green33RankSimplex
