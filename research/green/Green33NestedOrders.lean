import Green33ArcDistribution
import Green33FixedPrefixes
import Mathlib.Data.Nat.Nth

/-! Comparisons between two critical cyclic truncations. -/

open Finset Filter Green33ArcDistribution
open scoped Topology Pointwise

namespace Green33NestedOrders

/-- Least nonnegative integer representatives of a cyclic seed. -/
def labels {N : ℕ+} (A : Finset (ZMod N)) : Finset ℕ := A.image ZMod.val

private theorem labels_card {N : ℕ+} (A : Finset (ZMod N)) :
    (labels A).card=A.card := card_image_of_injective _ (ZMod.val_injective N)

private theorem labels_below {M : ℕ+} (B : Finset (ZMod M)) (w : ℕ) (fit : w≤M.val) :
    (labels B).filter (·<w) = labels (B∩arc 0 w) := by
  ext z
  simp only [labels,mem_filter,mem_image,mem_inter,arc,zero_add]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,lt⟩
    exact ⟨x,⟨hx,⟨x.val,mem_range.mpr lt,ZMod.natCast_zmod_val _⟩⟩,rfl⟩
  · rintro ⟨x,⟨hx,j,hj,rfl⟩,rfl⟩
    refine ⟨⟨_,hx,rfl⟩,?_⟩
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt ((mem_range.mp hj).trans_le fit)] using mem_range.mp hj

/-- Counting the smaller labels retained at the larger order only requires
the occupancy of the larger seed in the initial arc. -/
theorem retained_bound {N M : ℕ+} (A : Finset (ZMod N)) (B : Finset (ZMod M)) (fit : N≤M) :
    A.card ≤ (labels A \ labels B).card + (B∩arc 0 N.val).card := by
  have sub : labels A ∩ labels B ⊆ (labels B).filter (·<N.val) := by
    intro z hz
    obtain ⟨a,_,rfl⟩ := mem_image.mp (mem_inter.mp hz).1
    exact mem_filter.mpr ⟨(mem_inter.mp hz).2,ZMod.val_lt _⟩
  have cap := card_le_card sub
  rw [labels_below (M:=M) B N.val (show N.val≤M.val from fit),labels_card] at cap
  have eq := card_sdiff_add_card_inter (labels A) (labels B)
  rw [labels_card] at eq
  omega


/-- Square root of the relative order. -/
noncomputable def scale (n m : ℕ+) : ℝ := Real.sqrt n / Real.sqrt m

private theorem scale_spec {n m : ℕ+} (fit : n≤m) :
    0≤scale n m ∧ scale n m≤1 ∧ (scale n m)^2=(n:ℝ)/m := by
  have pos := Real.sqrt_pos.mpr (show (0:ℝ)<m by exact_mod_cast m.pos)
  refine ⟨div_nonneg (Real.sqrt_nonneg _) pos.le,(div_le_one pos).mpr (Real.sqrt_le_sqrt ?_),?_⟩
  · exact_mod_cast (show n.val≤m.val from fit)
  · rw [scale,div_pow,Real.sq_sqrt (Nat.cast_nonneg _),Real.sq_sqrt (Nat.cast_nonneg _)]

private theorem two_counts {n m : ℕ+} (A : Finset (ZMod n)) (B : Finset (ZMod m)) (fit : n≤m) :
    ((A.card:ℝ)/Real.sqrt n)*scale n m-((B.card:ℝ)/Real.sqrt m)*(scale n m)^2
      ≤ ((labels A \ labels B).card:ℝ)/Real.sqrt m+
         (((B∩arc 0 n.val).card:ℝ)-n*(B.card/(m:ℝ)))/Real.sqrt m := by
  have np := Real.sqrt_pos.mpr (show (0:ℝ)<n by exact_mod_cast n.pos)
  have mp := Real.sqrt_pos.mpr (show (0:ℝ)<m by exact_mod_cast m.pos)
  have h : (A.card:ℝ) ≤ (labels A \ labels B).card + (B∩arc 0 n.val).card := by exact_mod_cast retained_bound A B fit
  rw [(scale_spec fit).2.2,scale]
  field_simp [np.ne',mp.ne',show (m:ℝ)≠0 by exact_mod_cast m.pos.ne']
  nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α:=ℝ) m.val)]

/-- At every relative scale, a larger almost-full critical seed must drop
some least labels of a smaller critical-size seed. Only the larger seed
needs an additive coverage hypothesis. -/
theorem edit_bound {N M : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i))) (B : ∀ i, Finset (ZMod (M i)))
    (fit : ∀ i, N i≤M i) (big : Tendsto (fun i => (M i).val) atTop atTop)
    (smallSize : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (size : Tendsto (fun i => ((B i).card:ℝ)/Real.sqrt (M i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((B i+B i).card:ℝ)/(M i:ℝ)) atTop (𝓝 1))
    {ε : ℝ} (ep : 0<ε) : ∀ᶠ i in atTop,
    Real.sqrt 2 * scale (N i) (M i) * (1-scale (N i) (M i)) ≤
      ((labels (A i) \ labels (B i)).card:ℝ)/Real.sqrt (M i)+ε := by
  have arcLim := arc_distribution B big size cover (fun _ => 0) (fun i => (N i).val) fit
  have a := smallSize.eventually_const_lt (show Real.sqrt 2-ε/3<Real.sqrt 2 by linarith)
  have b := size.eventually_lt_const (show Real.sqrt 2<Real.sqrt 2+ε/3 by linarith)
  have d := arcLim.eventually_lt_const (show 0<ε/3 by linarith)
  filter_upwards [a,b,d] with i ai bi di
  obtain ⟨nonneg,cap,_⟩ := scale_spec (fit i)
  have sqcap : (scale (N i) (M i))^2≤1 := by nlinarith [mul_nonneg nonneg (sub_nonneg.mpr cap)]
  have l := mul_le_mul_of_nonneg_right ai.le nonneg
  have h := mul_le_mul_of_nonneg_right bi.le (sq_nonneg (scale (N i) (M i)))
  have fin := two_counts (A i) (B i) (fit i)
  nlinarith [mul_le_mul_of_nonneg_left cap ep.le,mul_le_mul_of_nonneg_left sqcap ep.le]


private theorem half_large : Tendsto (fun i : ℕ => i/2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop (2*k)] with i hi
  omega

private theorem index_bound (Q : ℕ → ℕ+) (inc : StrictMono (fun i => (Q i).val)) (i : ℕ) :
    ((i:ℝ)/Q i)^2 ≤ 8*scale (Q (i/2)) (Q i)*(1-scale (Q (i/2)) (Q i)) := by
  let n := Q (i/2)
  let m := Q i
  let u := scale n m
  have fit : n≤m := inc.monotone (Nat.div_le_self ..)
  obtain ⟨u0,u1,u2⟩ := scale_spec fit
  have np : 0<(n:ℝ) := by exact_mod_cast n.pos
  have mp : 0<(m:ℝ) := by exact_mod_cast m.pos
  have incr := inc.add_le_nat (i-i/2) (i/2)
  have start := inc.add_le_nat (i/2) 0
  simp only [Nat.add_zero] at start
  have first : i≤2*n.val := by
    dsimp [n]; have q := (Q 0).pos; omega
  have last : i+2*n.val≤2*m.val := by
    dsimp [n,m]; rw [Nat.sub_add_cancel (Nat.div_le_self ..)] at incr; omega
  have a : (i:ℝ)/m≤2*u^2 := by
    dsimp [u]; rw [u2]; apply (div_le_iff₀ mp).mpr
    have h : (i:ℝ) ≤ 2*n := by exact_mod_cast first
    field_simp [mp.ne']; exact h
  have b : (i:ℝ)/m≤2*(1-u^2) := by
    dsimp [u]; rw [u2]; apply (div_le_iff₀ mp).mpr
    have h : (i:ℝ)+2*n≤2*m := by exact_mod_cast last
    field_simp [mp.ne']; linarith
  have b0 := div_nonneg (Nat.cast_nonneg (α:=ℝ) i) mp.le
  have product := mul_le_mul a b b0 (mul_nonneg (by norm_num) (sq_nonneg _))
  have unit : u*(1-u)≥0 := mul_nonneg u0 (sub_nonneg.mpr u1)
  have factor : u^2+u≤2 := by nlinarith [unit]
  have bound := mul_le_mul_of_nonneg_right factor unit
  change ((i:ℝ)/m)^2≤8*u*(1-u)
  nlinarith

/-- Vanishing losses between the half-index seed and the current seed
force the number of selected orders per unit length to tend to zero. -/
theorem rank_density {Q : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (Q i)))
    (inc : StrictMono (fun i => (Q i).val))
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (Q i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(Q i:ℝ)) atTop (𝓝 1))
    (retain : Tendsto (fun i => ((labels (A (i/2)) \ labels (A i)).card:ℝ)/Real.sqrt (Q i)) atTop (𝓝 0)) :
    Tendsto (fun i : ℕ => (i:ℝ)/(Q i)) atTop (𝓝 0) := by
  let u i := scale (Q (i/2)) (Q i)
  have fit (i : ℕ) : Q (i/2)≤Q i := inc.monotone (Nat.div_le_self ..)
  have t : Tendsto (fun i => Real.sqrt 2*u i*(1-u i)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha; apply Eventually.of_forall; intro i
      obtain ⟨h,j,_⟩ := scale_spec (fit i)
      exact ha.trans_le (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) h) (sub_nonneg.mpr j))
    · intro b hb
      have ep : 0<b/2 := by linarith
      have low := edit_bound (fun i => A (i/2)) A fit inc.tendsto_atTop (size.comp half_large) size cover ep
      filter_upwards [low,retain.eventually_lt_const ep] with i hi li
      dsimp [u]; linarith
  have s := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)
  have dom := ((t.div_const (Real.sqrt 2)).const_mul 8)
  have eq : Tendsto (fun i => 8*u i*(1-u i)) atTop (𝓝 0) := by
    convert dom using 1
    · ext i; field_simp [s.ne']
    · simp
  have sq := squeeze_zero (fun i : ℕ => sq_nonneg ((i:ℝ)/(Q i))) (index_bound Q inc) eq
  simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    using Real.continuous_sqrt.continuousAt.tendsto.comp sq


open Green33RegularTruncations Green33FixedPrefixes

private theorem density_of_rank {Q : ℕ → ℕ+} (inc : StrictMono (fun i => (Q i).val))
    (sparse : Tendsto (fun i : ℕ => (i:ℝ)/(Q i)) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => (countBelow (Set.range (fun i => (Q i).val)) x:ℝ)/x) atTop (𝓝 0) := by
  classical
  let j x := Nat.findGreatest (fun k => (Q k).val<x) x
  have far : Tendsto j atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop (max k ((Q k).val+1))] with x hx
    exact Nat.le_findGreatest ((le_max_left ..).trans hx) (by omega : (Q k).val<x)
  have dom := (sparse.comp far).const_mul 2
  rw [mul_zero] at dom
  apply squeeze_zero' (Eventually.of_forall fun x => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ dom
  filter_upwards [eventually_gt_atTop (Q 0).val,far.eventually (eventually_ge_atTop 1)] with x hx one
  have below : (Q (j x)).val<x := Nat.findGreatest_spec (P:=fun k => (Q k).val<x) (Nat.zero_le x) hx
  have sub : truncation (Set.range (fun i => (Q i).val)) x ⊆ (range (j x+1)).image (fun i => (Q i).val) := by
    intro z hz
    obtain ⟨xz,i,rfl⟩ : z<x ∧ z∈Set.range (fun i => (Q i).val) := by simpa [truncation] using hz
    exact mem_image.mpr ⟨i,mem_range.mpr (Nat.lt_succ_of_le (Nat.le_findGreatest ((inc.id_le _).trans xz.le) xz)),rfl⟩
  have card := (card_le_card sub).trans (card_image_le.trans_eq (card_range _))
  have qp : (0:ℝ)<Q (j x) := by exact_mod_cast (Q (j x)).pos
  have xx : (Q (j x):ℝ)≤x := by exact_mod_cast below.le
  have cap : (countBelow (Set.range (fun i => (Q i).val)) x:ℝ)≤2*(j x) := by
    change ((truncation _ _).card:ℝ)≤_
    exact_mod_cast (show (truncation _ x).card≤2*j x by omega)
  calc
    _ ≤ (2*(j x:ℝ))/(Q (j x)) := (div_le_div_of_nonneg_right cap (Nat.cast_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) qp xx)
    _ = _ := by dsimp [Function.comp_def]; ring

private theorem trunc_labels (S : Set ℕ) (q : ℕ+) : labels (cyclicTruncation S q)=truncation S q.val := by
  classical
  ext z
  simp only [labels,cyclicTruncation,mem_image]
  constructor
  · rintro ⟨a,⟨x,hx,rfl⟩,rfl⟩
    have fit := mem_range.mp (mem_filter.mp hx).1
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt fit] using hx
  · intro h
    have fit := mem_range.mp (mem_filter.mp h).1
    exact ⟨_,⟨z,h,rfl⟩,by rw [ZMod.val_natCast,Nat.mod_eq_of_lt fit]⟩

/-- For one fixed integer set, any increasing sequence of critical-size
prefixes with asymptotically full cyclic sumsets has natural density zero. -/
theorem prefix_orders_density (S : Set ℕ) {Q : ℕ → ℕ+} (inc : StrictMono (fun i => (Q i).val))
    (size : Tendsto (fun i => coefficient S (Q i).val) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => coverage S (Q i)) atTop (𝓝 1)) :
    Tendsto (fun x : ℕ => (countBelow (Set.range (fun i => (Q i).val)) x:ℝ)/x) atTop (𝓝 0) := by
  classical
  apply density_of_rank inc
  refine rank_density (fun i => cyclicTruncation S (Q i)) inc ?_ cover ?_
  · simpa only [coefficient,countBelow,← trunc_labels,labels_card] using size
  · have sub (i : ℕ) : truncation S (Q (i/2)).val ⊆ truncation S (Q i).val := by
      intro x hx
      exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp (mem_filter.mp hx).1).trans_le
        (inc.monotone (Nat.div_le_self ..))),(mem_filter.mp hx).2⟩
    simpa only [trunc_labels,sdiff_eq_empty_iff_subset.mpr (sub _),card_empty,Nat.cast_zero,zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))


/-- Number of least labels that must be inserted or removed to obtain the
prefix of the specified integer set. -/
noncomputable def edits (S : Set ℕ) {q : ℕ+} (A : Finset (ZMod q)) : ℕ :=
  (labels A \ truncation S q.val).card + (truncation S q.val \ labels A).card

private theorem edits_cover_loss (S : Set ℕ) {n m : ℕ+} (A : Finset (ZMod n)) (B : Finset (ZMod m))
    (fit : n≤m) : (labels A \ labels B).card≤edits S A+edits S B := by
  classical
  have sub : labels A \ labels B ⊆ (labels A \ truncation S n.val) ∪ (truncation S m.val \ labels B) := by
    intro x hx
    obtain ⟨ha,hb⟩ := mem_sdiff.mp hx
    by_cases h : x∈truncation S n.val
    · have hi := mem_filter.mp h
      exact mem_union_right _ (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp hi.1).trans_le fit),hi.2⟩,hb⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨ha,h⟩)
  have h := (card_le_card sub).trans (card_union_le _ _)
  unfold edits
  omega

/-- Even allowing sublinear-in-size label edits to a fixed set's prefixes,
the selected orders of critical-size almost-covers have natural density zero. -/
theorem edited_prefix_orders_density (S : Set ℕ) {Q : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (Q i)))
    (inc : StrictMono (fun i => (Q i).val))
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (Q i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((A i+A i).card:ℝ)/(Q i:ℝ)) atTop (𝓝 1))
    (close : Tendsto (fun i => (edits S (A i):ℝ)/Real.sqrt (Q i)) atTop (𝓝 0)) :
    Tendsto (fun x : ℕ => (countBelow (Set.range (fun i => (Q i).val)) x:ℝ)/x) atTop (𝓝 0) := by
  apply density_of_rank inc
  apply rank_density A inc size cover
  have lim := (close.comp half_large).add close
  rw [add_zero] at lim
  apply squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) _ lim
  intro i
  have fit : Q (i/2)≤Q i := inc.monotone (Nat.div_le_self ..)
  have pos := Real.sqrt_pos.mpr (show (0:ℝ)<Q (i/2) by exact_mod_cast (Q (i/2)).pos)
  have le : Real.sqrt (Q (i/2):ℝ)≤Real.sqrt (Q i:ℝ) := Real.sqrt_le_sqrt (Nat.cast_le.mpr fit)
  have h := div_le_div_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (edits_cover_loss S (A (i/2)) (A i) fit)) (Real.sqrt_nonneg (Q i:ℝ))
  rw [Nat.cast_add,add_div] at h
  apply h.trans
  change _ ≤ (edits S (A (i/2)):ℝ)/Real.sqrt (Q (i/2)) + _
  exact add_le_add (div_le_div_of_nonneg_left (Nat.cast_nonneg _) pos le) le_rfl


/-- For convergent positive relative order r, at least
(√2(1−√r)−o(1))√n of the smaller seed's labels are missing. -/
theorem proportional_loss {N M : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i))) (B : ∀ i, Finset (ZMod (M i)))
    (fit : ∀ i, N i≤M i) (big : Tendsto (fun i => (M i).val) atTop atTop)
    (smallSize : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)))
    (size : Tendsto (fun i => ((B i).card:ℝ)/Real.sqrt (M i)) atTop (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => ((B i+B i).card:ℝ)/(M i:ℝ)) atTop (𝓝 1))
    {r : ℝ} (rp : 0<r) (ratio : Tendsto (fun i => (N i:ℝ)/(M i)) atTop (𝓝 r))
    {c : ℝ} (lt : c<Real.sqrt 2*(1-Real.sqrt r)) : ∀ᶠ i in atTop,
    c < ((labels (A i) \ labels (B i)).card:ℝ)/Real.sqrt (N i) := by
  let u i := scale (N i) (M i)
  have us : Tendsto u atTop (𝓝 (Real.sqrt r)) := by
    simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _),u,scale] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ratio
  let p := Real.sqrt 2*Real.sqrt r*(1-Real.sqrt r)-c*Real.sqrt r
  have pp : 0<p := by dsimp [p]; nlinarith [mul_lt_mul_of_pos_right lt (Real.sqrt_pos.mpr rp)]
  have ep : 0<p/2 := by linarith
  have calcLim : Tendsto (fun i => Real.sqrt 2*u i*(1-u i)-c*u i) atTop (𝓝 p) := (((us.const_mul (Real.sqrt 2)).mul (tendsto_const_nhds.sub us)).sub (us.const_mul c))
  have thresh := calcLim.eventually_const_lt (show p/2<p by linarith)
  have low := edit_bound A B fit big smallSize size cover ep
  filter_upwards [thresh,low] with i hi b
  have h : c*u i < ((labels (A i) \ labels (B i)).card:ℝ)/Real.sqrt (M i) := by
    change p/2<Real.sqrt 2*u i*(1-u i)-c*u i at hi
    change Real.sqrt 2*u i*(1-u i)≤_ at b
    linarith
  have npos := Real.sqrt_pos.mpr (show (0:ℝ)<N i by exact_mod_cast (N i).pos)
  have mpos := Real.sqrt_pos.mpr (show (0:ℝ)<M i by exact_mod_cast (M i).pos)
  apply (lt_div_iff₀ npos).mpr
  dsimp [u,scale] at h
  field_simp [mpos.ne'] at h
  exact h


/-- All positive orders at which the least labels of S form an ordinary cyclic two-basis. -/
def exactOrders (S : Set ℕ) : Set ℕ := {n | ∃ q : ℕ+, q.val=n ∧
  cyclicTruncation S q+cyclicTruncation S q=univ}

/-- A global upper counting coefficient of √2 forces the entire set of exact
ordinary cyclic basis orders to have natural density zero. -/
theorem all_exact_orders_density (S : Set ℕ) (upper : UpperCoefficient S (Real.sqrt 2)) :
    Tendsto (fun x : ℕ => (countBelow (exactOrders S) x:ℝ)/x) atTop (𝓝 0) := by
  classical
  by_cases finite : (exactOrders S).Finite
  · have lim : Tendsto (fun x : ℕ => (finite.toFinset.card:ℝ)/x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply squeeze_zero (fun x => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ lim
    intro x
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro z hz
    exact finite.mem_toFinset.mpr (mem_filter.mp hz).2
  let k := Nat.nth (·∈exactOrders S)
  have hi : (Set.ofPred (·∈exactOrders S)).Infinite := finite
  have inc : StrictMono k := Nat.nth_strictMono hi
  have mem (i : ℕ) : k i∈exactOrders S := Nat.nth_mem_of_infinite hi i
  let Q i := (mem i).choose
  have v (i) : (Q i).val=k i := (mem i).choose_spec.1
  have incQ : StrictMono (fun i => (Q i).val) := by simpa only [v] using inc
  have basis i : cyclicTruncation S (Q i)+cyclicTruncation S (Q i)=univ := (mem i).choose_spec.2
  have full : Tendsto (fun i => coverage S (Q i)) atTop (𝓝 1) := by
    have value (i : ℕ) : coverage S (Q i)=1 := by
      rw [coverage,basis,card_univ,ZMod.card,div_self (by exact_mod_cast (Q i).pos.ne')]
    simp_rw [value]
    exact tendsto_const_nhds
  have err : Tendsto (fun i => 2/Real.sqrt (Q i)) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp incQ.tendsto_atTop))
  have floor (i) : Real.sqrt 2-2/Real.sqrt (Q i)≤coefficient S (Q i).val := by
    let A := cyclicTruncation S (Q i)
    have h := Green33ReflectionRigidity.order_bound A (basis i)
    rw [ZMod.card] at h
    have card : countBelow S (Q i).val=A.card := by rw [countBelow,← trunc_labels,labels_card]
    have qpos := Real.sqrt_pos.mpr (show (0:ℝ)<Q i by exact_mod_cast (Q i).pos)
    have rc : 2*(Q i:ℝ)≤(A.card:ℝ)^2+2 := by exact_mod_cast h
    have sq : Real.sqrt (2*(Q i:ℝ))≤A.card+2 := Real.sqrt_le_iff.mpr
      ⟨by positivity,by nlinarith [Nat.cast_nonneg (α:=ℝ) A.card]⟩
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at sq
    rw [coefficient,card,sub_le_iff_le_add,← add_div,le_div_iff₀ qpos]
    linarith
  have sz : Tendsto (fun i => coefficient S (Q i).val) atTop (𝓝 (Real.sqrt 2)) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      filter_upwards [err.eventually_lt_const (sub_pos.mpr hb)] with i h
      linarith [floor i]
    · intro b hb
      filter_upwards [incQ.tendsto_atTop.eventually (upper _ (sub_pos.mpr hb))] with i h
      dsimp [coefficient]; linarith
  have eq : Set.range (fun i => (Q i).val)=exactOrders S := by
    simp only [v]; exact Nat.range_nth_of_infinite hi
  exact eq ▸ prefix_orders_density S incQ sz full

#print axioms retained_bound
#print axioms edit_bound
#print axioms rank_density
#print axioms prefix_orders_density
#print axioms edited_prefix_orders_density
#print axioms proportional_loss
#print axioms all_exact_orders_density
end Green33NestedOrders
