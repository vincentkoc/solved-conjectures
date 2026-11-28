import Green33NestedOrders
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.Real.Pi.Bounds

/-! Missing integer sums and coverage by cyclic prefixes. -/

open Finset Filter Green33RegularTruncations Green33NestedOrders Green33FixedPrefixes
open scoped Topology Pointwise

namespace Green33OrdinaryHoles

/-- Nonnegative integers without a representation by two elements of S. -/
def holes (S : Set ℕ) : Set ℕ := (S+S)ᶜ

/-- If both possible ordinary lifts of a residue are missing, the prefix
cannot represent it modulo q. -/
theorem missing_residue (S : Set ℕ) {a : ℕ} {q : ℕ+} (small : a<q.val)
    (ha : a∈holes S) (hb : a+q.val∈holes S) :
    (a:ZMod q)∉cyclicTruncation S q+cyclicTruncation S q := by
  classical
  rintro h
  obtain ⟨_,hx,_,hy,eq⟩ := Finset.mem_add.mp h
  obtain ⟨x,hxx,rfl⟩ := mem_image.mp hx
  obtain ⟨y,hyy,rfl⟩ := mem_image.mp hy
  have xv := mem_range.mp (mem_filter.mp hxx).1
  have yv := mem_range.mp (mem_filter.mp hyy).1
  have rep : x+y ∈ S+S := Set.add_mem_add (mem_filter.mp hxx).2 (mem_filter.mp hyy).2
  rw [← Nat.cast_add] at eq
  have modEq := congrArg ZMod.val eq
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt small] at modEq
  by_cases l : x+y<q.val
  · rw [Nat.mod_eq_of_lt l] at modEq
    exact ha (modEq ▸ rep)
  · rw [Nat.mod_eq_sub_mod (by omega : q.val≤x+y),Nat.mod_eq_of_lt (by omega)] at modEq
    exact hb ((show x+y=a+q.val by omega) ▸ rep)


/-- Residues whose two possible integer lifts both lie in the hole set. -/
noncomputable def doubleHoles (S : Set ℕ) (q : ℕ) : Finset ℕ := by
  classical exact (range q).filter fun a => a∈holes S ∧ a+q∈holes S

theorem double_hole_bound (S : Set ℕ) (q : ℕ+) :
    ((doubleHoles S q.val).card:ℝ)/q ≤ 1-coverage S q := by
  classical
  let A := cyclicTruncation S q
  let D := doubleHoles S q.val
  have cap : D.card≤(univ \ (A+A)).card := by
    apply card_le_card_of_injOn (fun x : ℕ => (x:ZMod q))
    · intro x hx
      obtain ⟨rng,ha,hb⟩ := mem_filter.mp hx
      exact mem_sdiff.mpr ⟨mem_univ _,missing_residue S (mem_range.mp rng) ha hb⟩
    · intro x hx y hy e
      have v := congrArg ZMod.val e
      rwa [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hx).1),
        Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hy).1)] at v
  have counts : D.card+(A+A).card≤q.val := by
    have c := card_sdiff_add_card_eq_card (subset_univ (A+A))
    rw [card_univ,ZMod.card] at c; omega
  have rc : (D.card:ℝ)+(A+A).card≤q := by exact_mod_cast counts
  rw [coverage,le_sub_iff_add_le,← add_div,div_le_one (by exact_mod_cast q.pos)]
  exact rc

/-- Sum of the missing fractions forced by pairs of integer holes,
charged at the reciprocal of the upper hole rather than the modulus. -/
theorem weighted_holes (S : Set ℕ) (X : ℕ) :
    ∑ b ∈ truncation (holes S) X, (countBelow (holes S) ((b+1)/2):ℝ)/b ≤
      ∑ q ∈ range X, ((doubleHoles S q).card:ℝ)/q := by
  classical
  let U := (truncation (holes S) X).sigma fun b => truncation (holes S) ((b+1)/2)
  let V := (range X).sigma (doubleHoles S)
  let f (p : (i : ℕ) × ℕ) : (i : ℕ) × ℕ := ⟨p.1-p.2,p.2⟩
  have info {p : (i : ℕ) × ℕ} (hp : p∈U) :
      p.1<X ∧ p.1∈holes S ∧ 2*p.2<p.1 ∧ p.2∈holes S := by
    obtain ⟨hb,ha⟩ := mem_sigma.mp hp
    have lt := mem_range.mp (mem_filter.mp ha).1
    exact ⟨mem_range.mp (mem_filter.mp hb).1,(mem_filter.mp hb).2,by omega,(mem_filter.mp ha).2⟩
  have sub : U.image f⊆V := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hv
    obtain ⟨x,hb,lt,ha⟩ := info hp
    apply mem_sigma.mpr
    refine ⟨mem_range.mpr ((Nat.sub_le ..).trans_lt x),mem_filter.mpr ⟨mem_range.mpr (by dsimp [f];omega),ha,?_⟩⟩
    simpa only [f,Nat.add_sub_of_le (by omega : p.2≤p.1)] using hb
  have inj : Set.InjOn f U := by
    rintro ⟨b,a⟩ h ⟨d,c⟩ k e
    have l := (info h).2.2.1
    have t := (info k).2.2.1
    have e1 := congrArg Sigma.fst e
    have e2 := congrArg (fun p : (i : ℕ) × ℕ => p.2) e
    dsimp [f] at e1 e2 l t
    congr 1; omega
  calc
    _ = ∑ p ∈ U, 1/(p.1:ℝ) := by simp [U,Finset.sum_sigma,countBelow,nsmul_eq_mul,div_eq_mul_inv]
    _ ≤ ∑ p ∈ U, 1/((f p).1:ℝ) := by
      apply sum_le_sum
      intro p hp
      have h := (info hp).2.2.1
      apply one_div_le_one_div_of_le
      · exact_mod_cast (show 0<p.1-p.2 by omega)
      · exact_mod_cast Nat.sub_le p.1 p.2
    _ = ∑ p ∈ U.image f, 1/(p.1:ℝ) := by rw [sum_image inj]
    _ ≤ ∑ p ∈ V, 1/(p.1:ℝ) := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
    _ = _ := by simp [V,Finset.sum_sigma,nsmul_eq_mul,div_eq_mul_inv]


/-- Fraction of residues missed at a positive order, extended by zero at zero. -/
noncomputable def loss (S : Set ℕ) : ℕ → ℝ
  | 0 => 0
  | q+1 => 1-coverage S (Nat.succPNat q)

/-- Average missed fraction at orders one through X. -/
noncomputable def meanLoss (S : Set ℕ) (X : ℕ) : ℝ := (∑ q ∈ range (X+1), loss S q)/X

/-- Fraction of integers below X that belong to T. -/
noncomputable def fraction (T : Set ℕ) (X : ℕ) : ℝ := (countBelow T X:ℝ)/X

private theorem missing_le (S : Set ℕ) (q : ℕ) :
    ((doubleHoles S q).card:ℝ)/q≤loss S q := by
  cases q with
  | zero => simp [loss]
  | succ q => exact double_hole_bound S (Nat.succPNat q)

private theorem loss_bounds (S : Set ℕ) (q : ℕ) : 0≤loss S q ∧ loss S q≤1 := by
  refine ⟨(div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans (missing_le S q),?_⟩
  cases q with
  | zero => simp [loss]
  | succ q =>
    change 1-(_ / _)≤1
    exact sub_le_self _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem mean_bounds (S : Set ℕ) (X : ℕ) : 0≤meanLoss S X ∧ meanLoss S X≤1 := by
  constructor
  · exact div_nonneg (sum_nonneg fun q _ => (loss_bounds S q).1) (Nat.cast_nonneg _)
  · rcases X with _|n
    · simp [meanLoss]
    · apply (div_le_one (show (0:ℝ)<(n+1:ℕ) by positivity)).mpr
      rw [sum_range_succ']
      simp only [loss,add_zero]
      exact (sum_le_sum (fun i (_ : i∈range (n+1)) => (loss_bounds S (i+1)).2)).trans_eq (by simp)

private theorem fraction_bounds (T : Set ℕ) (X : ℕ) : 0≤fraction T X ∧ fraction T X≤1 := by
  classical
  refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),?_⟩
  rcases X with _|n
  · simp [fraction]
  · apply (div_le_one (show (0:ℝ)<(n+1:ℕ) by positivity)).mpr
    exact_mod_cast (show countBelow T (n+1)≤n+1 from card_filter_le .. |>.trans_eq (card_range _))

private theorem threshold (S : Set ℕ) {a : ℝ} (ap : 0≤a) {K : ℕ}
    (density : ∀ b≥K, a*b≤(countBelow (holes S) b:ℝ)) (X : ℕ) :
    (a/2)*((countBelow (holes S) X:ℝ)-(2*K+1)) ≤ ∑ q ∈ range (X+1), loss S q := by
  classical
  let T := truncation (holes S) X
  let R := T.filter (fun b => 2*K+1≤b)
  let f (b : ℕ) : ℝ := (countBelow (holes S) ((b+1)/2):ℝ)/b
  have term {b : ℕ} (hb : b∈R) : a/2≤f b := by
    have fit := (mem_filter.mp hb).2
    have h := density ((b+1)/2) (by omega)
    have dbl : (b:ℝ)≤2*(((b+1)/2:ℕ):ℝ) := by exact_mod_cast (show b≤2*((b+1)/2) by omega)
    apply (le_div_iff₀ (show (0:ℝ)<b by exact_mod_cast (show 0<b by omega))).mpr
    nlinarith [mul_le_mul_of_nonneg_left dbl ap]
  have small : (T.filter fun b => ¬2*K+1≤b).card≤2*K+1 := by
    apply (card_le_card (t:=range (2*K+1)) ?_).trans_eq (card_range _)
    exact fun x hx => mem_range.mpr (lt_of_not_ge (mem_filter.mp hx).2)
  have partition := card_filter_add_card_filter_not (s:=T) (fun b => 2*K+1≤b)
  have h : countBelow (holes S) X≤R.card+(2*K+1) := by change T.card≤_;dsimp [R];omega
  have realh : (countBelow (holes S) X:ℝ)≤R.card+(2*K+1) := by exact_mod_cast h
  calc
    _ ≤ a/2*R.card := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = ∑ _ ∈ R, a/2 := by simp [mul_comm]
    _ ≤ ∑ b ∈ R, f b := sum_le_sum fun _ hb => term hb
    _ ≤ ∑ b ∈ T, f b := sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun _ _ _ => by dsimp [f]; positivity
    _ ≤ _ := (weighted_holes S X).trans ((sum_le_sum (fun q _ => missing_le S q)).trans
      (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.le_succ X)) fun q _ _ => (loss_bounds S q).1))


/-- Lower ordinary hole density h forces at least h²/2 missed cyclic
residues on average, with each order weighted equally. -/
theorem mean_loss_lower (S : Set ℕ) :
    (liminf (fraction (holes S)) atTop)^2/2 ≤ liminf (meanLoss S) atTop := by
  let h := liminf (fraction (holes S)) atTop
  let m := liminf (meanLoss S) atTop
  have top := isBoundedUnder_of_eventually_le (Eventually.of_forall fun x => (mean_bounds S x).2 :
    ∀ᶠ x in atTop, meanLoss S x≤1)
  have bounded := isBoundedUnder_of_eventually_ge (Eventually.of_forall fun x => (fraction_bounds (holes S) x).1 :
    ∀ᶠ x in atTop, 0≤fraction (holes S) x)
  have mn : 0≤m := le_liminf_of_le top.isCoboundedUnder_ge (Eventually.of_forall fun x => (mean_bounds S x).1)
  have hn : 0≤h := le_liminf_of_le (isBoundedUnder_of_eventually_le (Eventually.of_forall fun x =>
    (fraction_bounds (holes S) x).2 : ∀ᶠ x in atTop, fraction (holes S) x≤1)).isCoboundedUnder_ge
    (Eventually.of_forall fun x => (fraction_bounds (holes S) x).1)
  have bound {a : ℝ} (ap : 0≤a) (lt : a<h) : a^2/2≤m := by
    obtain ⟨K,hK⟩ := eventually_atTop.mp ((eventually_lt_of_lt_liminf lt bounded).and (eventually_gt_atTop 0))
    have density : ∀ b≥K, a*b≤(countBelow (holes S) b:ℝ) := by
      intro b hb
      obtain ⟨sz,pos⟩ := hK b hb
      exact ((lt_div_iff₀ (show (0:ℝ)<b by exact_mod_cast pos)).mp sz).le
    let C := (a/2)*(2*K+1)
    have tiny : Tendsto (fun X : ℕ => C/X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have lim : Tendsto (fun X : ℕ => a^2/2-C/X) atTop (𝓝 (a^2/2)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x:=a^2/2)).sub tiny
    have ev : ∀ᶠ X : ℕ in atTop, a^2/2-C/X ≤ meanLoss S X := by
      filter_upwards [eventually_ge_atTop K,eventually_gt_atTop 0] with X hx xp
      have d := mul_le_mul_of_nonneg_left (density X hx) (show 0≤a/2 by positivity)
      have b := threshold S ap density X
      have pos : (0:ℝ)<X := by exact_mod_cast xp
      rw [meanLoss,le_div_iff₀ pos,sub_mul,div_mul_cancel₀ _ pos.ne']
      dsimp [C]; nlinarith
    simpa only [lim.liminf_eq] using liminf_le_liminf ev lim.isBoundedUnder_ge top.isCoboundedUnder_ge
  change h^2/2≤m
  by_contra! wrong
  have root : Real.sqrt (2*m)<h := (Real.sqrt_lt' (by nlinarith : 0<h)).mpr (by nlinarith)
  obtain ⟨a,lo,hi⟩ := exists_between root
  have ap := (Real.sqrt_nonneg _).trans lo.le
  have b := bound ap hi
  nlinarith [Real.sq_sqrt (show 0≤2*m by positivity),mul_self_lt_mul_self (Real.sqrt_nonneg _) lo]


/-- Rank pairs of unwrapped ordinary sums sit in a quarter disk. The
diagonal correction accounts for repeated summands. -/
theorem ordinary_disk (S : Set ℕ) (X t : ℕ)
    (fit : ∀ x∈S, ∀ y∈S, x+y<X → (countBelow S x)^2+(countBelow S y)^2≤t) :
    2*countBelow (S+S) X ≤ (squareDisk t).card+2*countBelow S X := by
  classical
  let D := (truncation S X).image fun x => x+x
  let T := truncation (S+S) X \ D
  let g := Nat.nth (·∈S)
  let f (p : ℕ×ℕ) := (g p.1+g p.2,decide (g p.1<g p.2))
  have inv {x} (hx : x∈S) : g (countBelow S x)=x := by
    simpa only [g,countBelow,truncation,Nat.count_eq_card_filter_range] using (Nat.nth_count (p:=(·∈S)) hx)
  have hit : T×ˢ(univ:Finset Bool) ⊆ (squareDisk t).image f := by
    rintro ⟨s,b⟩ hs
    obtain ⟨hm,nd⟩ := mem_sdiff.mp (mem_product.mp hs).1
    obtain ⟨rng,add⟩ := mem_filter.mp hm
    obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_add.mp add
    have lt := mem_range.mp rng
    have ne : x≠y := by
      rintro rfl
      exact nd (mem_image_of_mem _ (mem_filter.mpr ⟨mem_range.mpr (by omega),hx⟩))
    have up := mem_squareDisk.mpr (fit x hx y hy lt)
    have dn := mem_squareDisk.mpr (fit y hy x hx (by omega))
    rcases lt_or_gt_of_ne ne with l|l
    · cases b
      · exact mem_image.mpr ⟨_,dn,by simp [f,inv hy,inv hx,l.asymm,add_comm]⟩
      · exact mem_image.mpr ⟨_,up,by simp [f,inv hx,inv hy,l]⟩
    · cases b
      · exact mem_image.mpr ⟨_,up,by simp [f,inv hx,inv hy,l.asymm]⟩
      · exact mem_image.mpr ⟨_,dn,by simp [f,inv hy,inv hx,l,add_comm]⟩
  have cap := (card_le_card hit).trans card_image_le
  simp only [card_product,card_univ,Fintype.card_bool] at cap
  have d : D.card≤countBelow S X := card_image_le
  have c := card_le_card_sdiff_add_card (s:=truncation (S+S) X) (t:=D)
  change countBelow (S+S) X≤T.card+D.card at c
  omega

private theorem disk_majorant (S : Set ℕ) {c a : ℝ} (lt : c<a)
    (upper : UpperCoefficient S c) : ∃ K : ℕ, ∀ X,
    2*countBelow (S+S) X ≤ (squareDisk (⌊a^2*X+2*(K:ℝ)^2⌋₊)).card+2*countBelow S X := by
  classical
  obtain ⟨K,h⟩ := eventually_atTop.mp ((upper (a-c) (sub_pos.mpr lt)).and (eventually_gt_atTop 0))
  have rank (x : ℕ) : (countBelow S x:ℝ)^2≤a^2*x+(K:ℝ)^2 := by
    by_cases hx : K≤x
    · obtain ⟨sz,xp⟩ := h x hx
      have rpos := Real.sqrt_pos.mpr (show (0:ℝ)<x by exact_mod_cast xp)
      have le := (div_lt_iff₀ rpos).mp sz
      have sq := mul_self_le_mul_self (Nat.cast_nonneg (α:=ℝ) (countBelow S x))
        (show (countBelow S x:ℝ)≤a*Real.sqrt x by linarith)
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) x),sq_nonneg (K:ℝ),
        show (a*Real.sqrt (x:ℝ))^2=a^2*x by rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]]
    · have cap : countBelow S x≤x := (card_filter_le ..).trans_eq (card_range _)
      have le : (countBelow S x:ℝ)≤K := by exact_mod_cast cap.trans (le_of_not_ge hx)
      nlinarith [mul_self_le_mul_self (Nat.cast_nonneg (α:=ℝ) (countBelow S x)) le,
        mul_nonneg (sq_nonneg a) (Nat.cast_nonneg (α:=ℝ) x)]
  refine ⟨K,fun X => ordinary_disk S X _ (fun x _ y _ hxy => ?_)⟩
  apply Nat.le_floor
  push_cast
  have v : (x:ℝ)+y≤X := by exact_mod_cast hxy.le
  nlinarith [rank x,rank y,mul_le_mul_of_nonneg_left v (sq_nonneg a)]


private theorem upper_nonneg (S : Set ℕ) {c : ℝ} (upper : UpperCoefficient S c) : 0≤c := by
  by_contra! neg
  obtain ⟨x,h⟩ := (upper (-c) (neg_pos.mpr neg)).exists
  linarith [div_nonneg (Nat.cast_nonneg (α:=ℝ) (countBelow S x)) (Real.sqrt_nonneg (x:ℝ))]

private theorem thin_fraction (S : Set ℕ) {c : ℝ} (upper : UpperCoefficient S c) :
    Tendsto (fraction S) atTop (𝓝 0) := by
  have tiny : Tendsto (fun X : ℕ => (c+1)/Real.sqrt X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall fun X => (fraction_bounds S X).1) _ tiny
  filter_upwards [upper 1 zero_lt_one,eventually_gt_atTop 0] with X h xp
  have pos := Real.sqrt_pos.mpr (show (0:ℝ)<X by exact_mod_cast xp)
  have b := div_le_div_of_nonneg_right h.le pos.le
  rwa [div_div,← sq,Real.sq_sqrt (Nat.cast_nonneg _)] at b

/-- The upper counting coefficient c bounds the upper natural density
of the ordinary sumset by π c²/8. -/
theorem sumset_density (S : Set ℕ) {c : ℝ} (upper : UpperCoefficient S c) :
    limsup (fraction (S+S)) atTop≤Real.pi*c^2/8 := by
  have base := isBoundedUnder_of_eventually_ge (Eventually.of_forall fun X => (fraction_bounds (S+S) X).1 :
    ∀ᶠ X in atTop, 0≤fraction (S+S) X)
  have cap {a : ℝ} (gt : c<a) : limsup (fraction (S+S)) atTop≤Real.pi*a^2/8 := by
    obtain ⟨K,hK⟩ := disk_majorant S gt upper
    let t (X : ℕ) := ⌊a^2*X+2*(K:ℝ)^2⌋₊
    have tiny (d : ℝ) : Tendsto (fun X : ℕ => d/X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have auxiliary (d : ℝ) : Tendsto (fun X : ℕ => a^2+d/X) atTop (𝓝 (a^2)) := by
      simpa using (tendsto_const_nhds (x:=a^2)).add (tiny d)
    have radius : Tendsto (fun X : ℕ => (t X:ℝ)/X) atTop (𝓝 (a^2)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (auxiliary (2*(K:ℝ)^2-1)) (auxiliary (2*(K:ℝ)^2))
      · filter_upwards [eventually_gt_atTop 0] with X xp
        have pos : (0:ℝ)<X := by exact_mod_cast xp
        rw [le_div_iff₀ pos,add_mul,div_mul_cancel₀ _ pos.ne']
        dsimp [t]; linarith [Nat.lt_floor_add_one (a^2*X+2*(K:ℝ)^2)]
      · filter_upwards [eventually_gt_atTop 0] with X xp
        have pos : (0:ℝ)<X := by exact_mod_cast xp
        rw [div_le_iff₀ pos,add_mul,div_mul_cancel₀ _ pos.ne']
        exact Nat.floor_le (by positivity)
    have disk := squareDisk_limit (N:=id) tendsto_id radius
    have lim := (disk.div_const 2).add (thin_fraction S upper)
    rw [add_zero,show Real.pi*a^2/4/2=Real.pi*a^2/8 by ring] at lim
    have le : ∀ᶠ X : ℕ in atTop, fraction (S+S) X≤
        ((squareDisk (t X)).card:ℝ)/X/2+fraction S X := by
      filter_upwards [eventually_gt_atTop 0] with X xp
      have raw : 2*countBelow (S+S) X≤(squareDisk (t X)).card+2*countBelow S X := hK X
      have h : 2*(countBelow (S+S) X:ℝ)≤(squareDisk (t X)).card+2*countBelow S X := by exact_mod_cast raw
      dsimp [fraction]
      field_simp [show (X:ℝ)≠0 by exact_mod_cast xp.ne']
      linarith
    exact (limsup_le_limsup le base.isCoboundedUnder_le lim.isBoundedUnder_le).trans_eq lim.limsup_eq
  let a (n : ℕ) := c+1/((n:ℝ)+1)
  have tend : Tendsto a atTop (𝓝 c) := by
    simpa only [add_zero] using (tendsto_const_nhds (x:=c)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (((tend.pow 2).const_mul Real.pi).div_const 8)
    (fun n => cap (show c<a n by exact lt_add_of_pos_right _ (by positivity)))


private theorem complement_count (S : Set ℕ) (X : ℕ) :
    countBelow (S+S) X+countBelow (holes S) X=X := by
  classical
  simpa [countBelow,truncation,holes] using card_filter_add_card_filter_not (s:=range X) (fun x => x∈S+S)

private theorem lower_holes (S : Set ℕ) :
    liminf (fraction (holes S)) atTop=1-limsup (fraction (S+S)) atTop := by
  have bounded := isBoundedUnder_of_eventually_le (Eventually.of_forall fun X => (fraction_bounds (S+S) X).2 :
    ∀ᶠ X in atTop, fraction (S+S) X≤1)
  have below := isBoundedUnder_of_eventually_ge (Eventually.of_forall fun X => (fraction_bounds (S+S) X).1 :
    ∀ᶠ X in atTop, 0≤fraction (S+S) X)
  have ev : ∀ᶠ X : ℕ in atTop, fraction (holes S) X=1-fraction (S+S) X := by
    filter_upwards [eventually_gt_atTop 0] with X xp
    have part : (countBelow (S+S) X:ℝ)+countBelow (holes S) X=X := by exact_mod_cast complement_count S X
    dsimp [fraction]; field_simp [show (X:ℝ)≠0 by exact_mod_cast xp.ne']; linarith
  exact (Filter.liminf_congr ev).trans (liminf_const_sub atTop _ 1 bounded below.isCoboundedUnder_le)

/-- Counting envelope alone forces a positive average deficit for all
coefficients below the Stöhr threshold. -/
theorem coefficient_loss (S : Set ℕ) {c : ℝ} (upper : UpperCoefficient S c) :
    (max 0 (1-Real.pi*c^2/8))^2/2≤liminf (meanLoss S) atTop := by
  have h := mean_loss_lower S
  rw [lower_holes] at h
  have b := sumset_density S upper
  have u := limsup_le_of_le (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun X =>
    (fraction_bounds (S+S) X).1 : ∀ᶠ X in atTop, 0≤fraction (S+S) X)).isCoboundedUnder_le
    (Eventually.of_forall fun X => (fraction_bounds (S+S) X).2)
  have le : max 0 (1-Real.pi*c^2/8)≤1-limsup (fraction (S+S)) atTop := max_le (by linarith) (by linarith)
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (le_max_left ..) le _) (by norm_num)).trans h

/-- A single ordinary hole gives an injection from all sufficiently
large ordinary holes below X into the unsuccessful cyclic orders below X. -/
theorem exact_count (S : Set ℕ) : ∃ K : ℕ, ∀ X,
    countBelow (exactOrders S) X ≤ countBelow (S+S) X+K := by
  classical
  by_cases ex : (holes S).Nonempty
  · obtain ⟨a,ha⟩ := ex
    refine ⟨2*a+1,fun X => ?_⟩
    let E := truncation (exactOrders S) X
    let T := truncation (holes S) X
    let R := T.filter fun b => 2*a+1≤b
    have cap : R.card≤(range X \ E).card := by
      apply card_le_card_of_injOn (fun b => b-a)
      · intro b hb
        obtain ⟨ht,l⟩ := mem_filter.mp hb
        obtain ⟨hx,hh⟩ := mem_filter.mp ht
        refine mem_sdiff.mpr ⟨mem_range.mpr ((Nat.sub_le ..).trans_lt (mem_range.mp hx)),?_⟩
        intro hg
        obtain ⟨q,e,full⟩ := (mem_filter.mp hg).2
        change q.val=b-a at e
        have hit : (a:ZMod q)∈cyclicTruncation S q+cyclicTruncation S q := full ▸ mem_univ _
        exact missing_residue S (by omega : a<q.val) ha ((show a+q.val=b by omega) ▸ hh) hit
      · intro x hx y hy eq
        have a1 := (mem_filter.mp hx).2
        have a2 := (mem_filter.mp hy).2
        dsimp at eq; omega
    have left : (T.filter fun b => ¬2*a+1≤b).card≤2*a+1 := by
      apply (card_le_card (t:=range (2*a+1)) ?_).trans_eq (card_range _)
      exact fun x hx => mem_range.mpr (lt_of_not_ge (mem_filter.mp hx).2)
    have p := card_filter_add_card_filter_not (s:=T) (fun b => 2*a+1≤b)
    have e := card_sdiff_add_card_eq_card (show E⊆range X from filter_subset ..)
    rw [card_range] at e
    have cm := complement_count S X
    change _+T.card=X at cm
    change E.card≤_
    change R.card+_=T.card at p
    omega
  · refine ⟨0,fun X => ?_⟩
    have emp : truncation (holes S) X=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun z hz => ex ⟨z,(mem_filter.mp hz).2⟩
    have c := complement_count S X
    simp only [countBelow,emp,card_empty,add_zero] at c
    change (truncation _ _).card≤(truncation _ _).card+0
    rw [c,add_zero]
    exact (card_filter_le ..).trans_eq (card_range _)

/-- The upper density of exact cyclic prefix orders never exceeds the
upper density of the ordinary integer sumset. -/
theorem exact_density (S : Set ℕ) :
    limsup (fraction (exactOrders S)) atTop≤limsup (fraction (S+S)) atTop := by
  obtain ⟨K,hK⟩ := exact_count S
  have top := isBoundedUnder_of_eventually_le (Eventually.of_forall fun X => (fraction_bounds (S+S) X).2 :
    ∀ᶠ X in atTop, fraction (S+S) X≤1)
  have bottom := isBoundedUnder_of_eventually_ge (Eventually.of_forall fun X => (fraction_bounds (exactOrders S) X).1 :
    ∀ᶠ X in atTop, 0≤fraction (exactOrders S) X)
  have zero : Tendsto (fun X : ℕ => (K:ℝ)/X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  by_contra! gap
  obtain ⟨v,lo,hi⟩ := exists_between gap
  obtain ⟨w,low,wv⟩ := exists_between lo
  apply hi.not_ge (limsup_le_of_le bottom.isCoboundedUnder_le ?_)
  filter_upwards [eventually_lt_of_limsup_lt low top,zero.eventually_lt_const (sub_pos.mpr wv)] with X h z
  have le : fraction (exactOrders S) X ≤ fraction (S+S) X+(K:ℝ)/X := by
    rw [fraction,fraction,← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hK X) (Nat.cast_nonneg _)
  linarith


/-- A sequence of averaging cutoffs with vanishing mean loss forces
the classical Stöhr lower coefficient, without regular growth of S. -/
theorem mean_full_threshold (S : Set ℕ) {c : ℝ} (upper : UpperCoefficient S c)
    (full : liminf (meanLoss S) atTop=0) : Real.sqrt (8/Real.pi)≤c := by
  have h := coefficient_loss S upper
  rw [full] at h
  have z : max 0 (1-Real.pi*c^2/8)=0 := by
    nlinarith [sq_nonneg (max 0 (1-Real.pi*c^2/8))]
  apply Real.sqrt_le_iff.mpr ⟨upper_nonneg S upper,?_⟩
  apply (div_le_iff₀ Real.pi_pos).mpr
  linarith [le_max_right 0 (1-Real.pi*c^2/8),mul_comm (c^2) Real.pi]

/-- Every fixed set attaining the best finite-basis coefficient has a
uniform positive mean deficit and misses a positive proportion of orders. -/
theorem optimal_deficits (S : Set ℕ) (upper : UpperCoefficient S optimalCoefficient) :
    limsup (fraction (exactOrders S)) atTop≤81*Real.pi/260 ∧
    (1-81*Real.pi/260)^2/2≤liminf (meanLoss S) atTop ∧ 81*Real.pi/260<1 := by
  have low := optimal_bounds.1
  have high := optimal_bounds.2
  have cap := pow_le_pow_left₀ ((Real.sqrt_nonneg 2).trans low) high 2
  rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤130)] at cap
  have u : Real.pi*optimalCoefficient^2/8≤81*Real.pi/260 := by
    nlinarith [mul_le_mul_of_nonneg_left cap Real.pi_pos.le]
  have gap : 81*Real.pi/260<1 := by linarith [Real.pi_lt_d2]
  refine ⟨(exact_density S).trans ((sumset_density S upper).trans u),?_,gap⟩
  have le : 1-81*Real.pi/260≤max 0 (1-Real.pi*optimalCoefficient^2/8) :=
    (by linarith : 1-81*Real.pi/260≤1-Real.pi*optimalCoefficient^2/8).trans (le_max_right ..)
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) le 2) (by norm_num)).trans (coefficient_loss S upper)

#print axioms missing_residue
#print axioms double_hole_bound
#print axioms weighted_holes
#print axioms mean_loss_lower
#print axioms ordinary_disk
#print axioms sumset_density
#print axioms coefficient_loss
#print axioms exact_count
#print axioms exact_density
#print axioms mean_full_threshold
#print axioms optimal_deficits
end Green33OrdinaryHoles
