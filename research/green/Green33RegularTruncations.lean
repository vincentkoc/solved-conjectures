import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Counting pairs of ranks in a quarter disk for regularly growing cyclic truncations. -/

open Finset Filter MeasureTheory intervalIntegral
open scoped Topology Pointwise

namespace Green33RegularTruncations

/-- The height of the upper semicircle above a nonnegative coordinate. -/
noncomputable def rowHeight (r x : ℝ) := Real.sqrt (r^2-x^2)

private theorem quarter_unit : (∫ x in (0:ℝ)..1, rowHeight 1 x)=Real.pi/4 := by
  have c : Continuous (rowHeight 1) := by unfold rowHeight; fun_prop
  have split := integral_add_adjacent_intervals (μ:=volume) (c.intervalIntegrable (-1:ℝ) 0) (c.intervalIntegrable 0 1)
  have sym := integral_comp_neg (rowHeight 1) (a:=0) (b:=1)
  have even (x : ℝ) : rowHeight 1 (-x)=rowHeight 1 x := by simp [rowHeight]
  simp only [even,neg_zero] at sym
  have area : (∫ x in (-1:ℝ)..1, rowHeight 1 x)=Real.pi/2 := by simpa [rowHeight] using integral_sqrt_one_sub_sq
  linarith

/-- Area of a quarter disk, expressed as the integral of its row lengths. -/
theorem quarter_area (r : ℝ) (hr : 0≤r) :
    (∫ x in (0:ℝ)..r, rowHeight r x)=Real.pi*r^2/4 := by
  rcases hr.eq_or_lt with rfl|hp
  · simp
  have factor (x : ℝ) : rowHeight r (x*r)=r*rowHeight 1 x := by
    unfold rowHeight
    rw [show r^2-(x*r)^2=r^2*(1^2-x^2) by ring,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hp.le]
  have eq := integral_comp_mul_right (rowHeight r) (a:=0) (b:=1) hp.ne'
  simp only [factor,zero_mul,one_mul,smul_eq_mul,intervalIntegral.integral_const_mul,quarter_unit] at eq
  field_simp at eq
  linarith


/-- Lattice points of the closed first-quadrant disk of integer radius `n`. -/
def disk (n : ℕ) : Finset (ℕ×ℕ) :=
  ((range (n+1))×ˢ(range (n+1))).filter fun z => z.1^2+z.2^2≤n^2

theorem mem_disk {i j n : ℕ} : (i,j)∈disk n ↔ i^2+j^2≤n^2 := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    have hi : i≤n := by nlinarith
    have hj : j≤n := by nlinarith
    exact mem_filter.mpr ⟨mk_mem_product (mem_range.mpr (by omega)) (mem_range.mpr (by omega)),h⟩

private theorem rows (n : ℕ) :
    (disk n).card=∑ i ∈ range (n+1), (⌊rowHeight n i⌋₊+1) := by
  have count (i : ℕ) (hi : i∈range (n+1)) :
      ((range (n+1)).filter (fun j => i^2+j^2≤n^2)).card=⌊rowHeight n i⌋₊+1 := by
    have le : i≤n := by simpa using mem_range.mp hi
    have pos : 0≤(n:ℝ)^2-(i:ℝ)^2 := by nlinarith [show (i:ℝ)≤n by exact_mod_cast le]
    have eq : (range (n+1)).filter (fun j => i^2+j^2≤n^2)=range (⌊rowHeight n i⌋₊+1) := by
      ext j
      simp only [mem_filter,mem_range,Nat.lt_succ_iff]
      constructor
      · intro h
        apply Nat.le_floor
        apply Real.le_sqrt_of_sq_le
        have e : (i:ℝ)^2+j^2≤(n:ℝ)^2 := by exact_mod_cast h.2
        linarith
      · intro h
        have r : (j:ℝ)≤rowHeight n i := (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.sqrt_nonneg _))
        have rs : (rowHeight n i)^2=(n:ℝ)^2-(i:ℝ)^2 := Real.sq_sqrt pos
        have re : (i:ℝ)^2+(j:ℝ)^2≤(n:ℝ)^2 := by nlinarith [sq_le_sq' (by linarith [Real.sqrt_nonneg ((n:ℝ)^2-i^2)] : -(rowHeight n i)≤(j:ℝ)) r]
        have nat : i^2+j^2≤n^2 := by exact_mod_cast re
        exact ⟨by nlinarith, nat⟩
    rw [eq,card_range]
  unfold disk
  simp only [card_eq_sum_ones,sum_filter,sum_product]
  apply sum_congr rfl
  intro i hi
  simpa only [card_eq_sum_ones,sum_filter] using count i hi


/-- The area approximates the quadrant lattice count with an explicit
linear error, including the two axes and the circular boundary. -/
theorem disk_count (n : ℕ) :
    Real.pi*(n:ℝ)^2/4≤((disk n).card:ℝ) ∧
    ((disk n).card:ℝ)≤Real.pi*(n:ℝ)^2/4+2*n+1 := by
  let f := rowHeight (n:ℝ)
  have anti : AntitoneOn f (Set.Icc 0 (0+(n:ℝ))) := by
    intro x hx y _ le
    apply Real.sqrt_le_sqrt
    nlinarith [sq_le_sq' (by linarith [hx.1] : -y≤x) le]
  have lower := anti.integral_le_sum
  have upper := anti.sum_le_integral
  simp only [zero_add] at lower upper
  rw [show (∫ x in (0:ℝ)..n, f x)=Real.pi*(n:ℝ)^2/4 from quarter_area _ (Nat.cast_nonneg _)] at lower upper
  have start : f 0=(n:ℝ) := by simp [f,rowHeight,Real.sqrt_sq (Nat.cast_nonneg _)]
  have last : f n=0 := by simp [f,rowHeight]
  have sum₀ : ∑ i ∈ range (n+1), f i=∑ i ∈ range n, f i := by rw [sum_range_succ,last,add_zero]
  have sum₁ : ∑ i ∈ range (n+1), f i=(∑ i ∈ range n, f ↑(i+1))+n := by rw [sum_range_succ',Nat.cast_zero,start]
  have eq : ((disk n).card:ℝ)=∑ i ∈ range (n+1), ((⌊f i⌋₊:ℝ)+1) := by rw [rows]; push_cast; rfl
  rw [eq]
  constructor
  · rw [← sum₀] at lower
    exact lower.trans (sum_le_sum (fun i _ => (Nat.lt_floor_add_one (f i)).le))
  · calc
      _ ≤ ∑ i ∈ range (n+1), (f i+1) := sum_le_sum fun i _ => by
        linarith [Nat.floor_le (show 0≤f i from Real.sqrt_nonneg _)]
      _ = (∑ i ∈ range n, f ↑(i+1))+n+((n:ℝ)+1) := by simp [sum_add_distrib,sum₁]
      _ ≤ _ := by linarith


/-- Quadrant disk counts at moving radii on the square-root scale. -/
theorem disk_limit {N r : ℕ → ℕ} (big : Tendsto N atTop atTop) {a : ℝ}
    (lim : Tendsto (fun i => (r i:ℝ)/Real.sqrt (N i)) atTop (𝓝 a)) :
    Tendsto (fun i => ((disk (r i)).card:ℝ)/(N i:ℝ)) atTop (𝓝 (Real.pi*a^2/4)) := by
  have nt : Tendsto (fun i => (N i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have rt := Real.tendsto_sqrt_atTop.comp nt
  have ls : Tendsto (fun i => (r i:ℝ)^2/(N i:ℝ)) atTop (𝓝 (a^2)) := by
    simpa only [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using lim.pow 2
  have rs : Tendsto (fun i => (r i:ℝ)/(N i:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,div_div,← sq,Real.sq_sqrt (Nat.cast_nonneg _)] using lim.div_atTop rt
  have inv : Tendsto (fun i => 1/(N i:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop nt
  have lower := (ls.const_mul Real.pi).div_const 4
  have upper := (lower.add (rs.const_mul 2)).add inv
  simp only [mul_zero,add_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lower upper
  · intro i
    have h := div_le_div_of_nonneg_right (disk_count (r i)).1 (Nat.cast_nonneg (α:=ℝ) (N i))
    dsimp only
    convert h using 1
    ring
  · intro i
    have h := div_le_div_of_nonneg_right (disk_count (r i)).2 (Nat.cast_nonneg (α:=ℝ) (N i))
    dsimp only
    convert h using 1
    ring


/-- Quarter disk indexed by squared radius. -/
def squareDisk (t : ℕ) : Finset (ℕ×ℕ) :=
  (disk (t.sqrt+1)).filter fun z => z.1^2+z.2^2≤t

theorem mem_squareDisk {i j t : ℕ} : (i,j)∈squareDisk t ↔ i^2+j^2≤t := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨mem_disk.mpr (h.trans (Nat.lt_succ_sqrt' _).le),h⟩

/-- A squared-radius threshold asymptotic to `a N` encloses
`(π a/4 + o(1)) N` nonnegative lattice points. -/
theorem squareDisk_limit {N t : ℕ → ℕ} (big : Tendsto N atTop atTop) {a : ℝ}
    (lim : Tendsto (fun i => (t i:ℝ)/(N i:ℝ)) atTop (𝓝 a)) :
    Tendsto (fun i => ((squareDisk (t i)).card:ℝ)/(N i:ℝ)) atTop (𝓝 (Real.pi*a/4)) := by
  let r i := (t i).sqrt
  have rt := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
  have small : Tendsto (fun i => 1/Real.sqrt (N i)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop rt
  have cont := Real.continuous_sqrt.continuousAt.tendsto.comp lim
  have sq : Tendsto (fun i => Real.sqrt (t i)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt a)) := by
    simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _)] using cont
  have floorlim : Tendsto (fun i => (r i:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt a)) := by
    have lower := sq.sub small
    rw [sub_zero] at lower
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le lower sq
    · intro i
      dsimp only
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have ceil := Nat.lt_floor_add_one (Real.sqrt (t i))
      rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at ceil
      dsimp [r]
      linarith
    · intro i
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      simpa only [r,← Real.nat_floor_real_sqrt_eq_nat_sqrt] using Nat.floor_le (Real.sqrt_nonneg (t i))
  have plus : Tendsto (fun i => ((r i+1:ℕ):ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt a)) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_div,add_zero] using floorlim.add small
  have l := disk_limit big floorlim
  have u := disk_limit big plus
  have pos : 0≤a := le_of_tendsto_of_tendsto' tendsto_const_nhds lim (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [Real.sq_sqrt pos] at l u
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le l u
  · intro i
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Nat.cast_le.mpr (card_le_card ?_)
    rintro ⟨x,y⟩ h
    exact mem_squareDisk.mpr ((mem_disk.mp h).trans (Nat.sqrt_le' _))
  · intro i
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_le_card (filter_subset ..))) (Nat.cast_nonneg _)


/-- Integer sums reduced modulo the selected order. -/
def residues (B : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (B+B).image (·%N)

/-- Ordered representations whose residue is in the last `w` places. -/
def edgePairs (B : Finset ℕ) (N w : ℕ) : Finset (ℕ×ℕ) :=
  (B×ˢB).filter fun z => (z.1+z.2)%N∈Ico (N-w) N

/-- Missing residues and diagonal sums account for the loss from
two ordered witnesses per residue in the last window. -/
theorem edge_coverage (B : Finset ℕ) (N w : ℕ) (pos : 0<N) (fit : w≤N) :
    2*w≤(edgePairs B N w).card+2*B.card+2*(N-(residues B N).card) := by
  let W := Ico (N-w) N
  let R := residues B N
  let diag := B.image (fun x => (x+x)%N)
  let D := (W∩R) \ diag
  have wc : W.card=w := by dsimp [W]; rw [Nat.card_Ico]; omega
  have sub : R⊆range N := by
    intro x hx
    obtain ⟨_,_,rfl⟩ := mem_image.mp hx
    exact mem_range.mpr (Nat.mod_lt _ pos)
  have misses : (W \ R).card≤N-R.card := by
    rw [← card_range N,← card_sdiff_of_subset sub]
    apply card_le_card
    intro x hx
    obtain ⟨hw,hr⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨mem_range.mpr (mem_Ico.mp hw).2,hr⟩
  have wc' := card_sdiff_add_card_inter W R
  have dc := card_le_card_sdiff_add_card (s:=W∩R) (t:=diag)
  have di : diag.card≤B.card := card_image_le
  let f (z : ℕ×ℕ) := ((z.1+z.2)%N,decide (z.1<z.2))
  have hit : D×ˢ(univ : Finset Bool)⊆(edgePairs B N w).image f := by
    rintro ⟨x,b⟩ h
    obtain ⟨hm,nd⟩ := mem_sdiff.mp (mem_product.mp h).1
    obtain ⟨hw,hr⟩ := mem_inter.mp hm
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hr
    obtain ⟨a,ha,c,hc,rfl⟩ := mem_add.mp hs
    have ne : a≠c := fun eq => nd (eq ▸ mem_image_of_mem _ ha)
    have up : (a,c)∈edgePairs B N w := mem_filter.mpr ⟨mk_mem_product ha hc,hw⟩
    have down : (c,a)∈edgePairs B N w := mem_filter.mpr ⟨mk_mem_product hc ha,by change (c+a)%N∈W; simpa only [add_comm c a] using hw⟩
    rcases lt_or_gt_of_ne ne with lt|lt <;> cases b
    · exact mem_image.mpr ⟨(c,a),down,by simp [f,lt.asymm,add_comm]⟩
    · exact mem_image.mpr ⟨(a,c),up,by simp [f,lt]⟩
    · exact mem_image.mpr ⟨(a,c),up,by simp [f,lt.asymm]⟩
    · exact mem_image.mpr ⟨(c,a),down,by simp [f,lt,add_comm]⟩
  have cap := (card_le_card hit).trans card_image_le
  simp only [card_product,card_univ,Fintype.card_bool] at cap
  change (W∩R).card≤D.card+diag.card at dc
  change 2*w≤_+_+2*(N-R.card)
  omega


/-- The elements strictly below the cutoff. -/
noncomputable def truncation (S : Set ℕ) (N : ℕ) : Finset ℕ := by
  classical exact (range N).filter (·∈S)

private theorem mem_trunc {S : Set ℕ} {x N : ℕ} :
    x∈truncation S N ↔ x<N ∧ x∈S := by classical simp [truncation]

/-- The number of elements of the fixed set strictly below an integer. -/
noncomputable def countBelow (S : Set ℕ) (N : ℕ) : ℕ := (truncation S N).card

private theorem rank_inj (S : Set ℕ) : Set.InjOn (countBelow S) S := by
  have strict {a b : ℕ} (ha : a∈S) (lt : a<b) : countBelow S a<countBelow S b := by
    apply card_lt_card
    apply ssubset_iff_subset_ne.mpr
    refine ⟨fun x hx => mem_trunc.mpr ⟨(mem_trunc.mp hx).1.trans lt,(mem_trunc.mp hx).2⟩,?_⟩
    intro eq
    have h : a∈truncation S a := eq ▸ mem_trunc.mpr ⟨lt,ha⟩
    exact (lt_irrefl a) (mem_trunc.mp h).1
  intro a ha b hb eq
  rcases lt_trichotomy a b with h|h|h
  · exact ((strict ha h).ne eq).elim
  · exact h
  · exact ((strict hb h).ne eq.symm).elim

private theorem top_count (S : Set ℕ) (N w : ℕ) :
    ((truncation S N).filter (N-w≤·)).card+countBelow S (N-w)=countBelow S N := by
  classical
  have eq : (truncation S N).filter (fun x => ¬N-w≤x)=truncation S (N-w) := by
    ext x
    simp only [mem_filter,mem_trunc,not_le]
    constructor
    · rintro ⟨⟨_,hx⟩,lt⟩; exact ⟨lt,hx⟩
    · rintro ⟨lt,hx⟩; exact ⟨⟨lt.trans_le (Nat.sub_le ..),hx⟩,lt⟩
  simpa only [countBelow,← eq] using card_filter_add_card_filter_not
    (s:=truncation S N) (fun x => N-w≤x)

/-- Unwrapped representations in the terminal window fit in a rank
annulus. Wrapped representations use two labels from the terminal window. -/
theorem edge_annulus (S : Set ℕ) (N w L U : ℕ) (order : L≤U)
    (bounds : ∀ x∈truncation S N, ∀ y∈truncation S N, N-w≤x+y → x+y<N →
      L<(countBelow S x)^2+(countBelow S y)^2 ∧ (countBelow S x)^2+(countBelow S y)^2≤U) :
    (edgePairs (truncation S N) N w).card+(squareDisk L).card ≤
      (squareDisk U).card+((truncation S N).filter (N-w≤·)).card^2 := by
  classical
  let E := edgePairs (truncation S N) N w
  let B := (truncation S N).filter (N-w≤·)
  let f (z : ℕ×ℕ) := (countBelow S z.1,countBelow S z.2)
  let low := E.filter (fun z => z.1+z.2<N)
  let high := E.filter (fun z => ¬z.1+z.2<N)
  have data {z : ℕ×ℕ} (h : z∈E) := mem_filter.mp h
  have lower : low.card≤(squareDisk U \ squareDisk L).card := by
    apply card_le_card_of_injOn f
    · rintro ⟨x,y⟩ hm
      obtain ⟨he,lt⟩ := mem_filter.mp hm
      obtain ⟨hB,hw⟩ := data he
      obtain ⟨hx,hy⟩ := mem_product.mp hB
      change x+y<N at lt
      change (x+y)%N∈Ico (N-w) N at hw
      rw [Nat.mod_eq_of_lt lt] at hw
      obtain ⟨lo,hi⟩ := bounds x hx y hy (mem_Ico.mp hw).1 lt
      exact mem_sdiff.mpr ⟨mem_squareDisk.mpr hi,fun h => lo.not_ge (mem_squareDisk.mp h)⟩
    · rintro ⟨x,y⟩ h ⟨a,b⟩ h' eq
      obtain ⟨hx,hy⟩ := mem_product.mp (data (mem_filter.mp h).1).1
      obtain ⟨ha,hb⟩ := mem_product.mp (data (mem_filter.mp h').1).1
      exact Prod.ext (rank_inj S (mem_trunc.mp hx).2 (mem_trunc.mp ha).2 (congrArg Prod.fst eq))
        (rank_inj S (mem_trunc.mp hy).2 (mem_trunc.mp hb).2 (congrArg Prod.snd eq))
  have upper : high⊆B×ˢB := by
    rintro ⟨x,y⟩ hm
    obtain ⟨he,large⟩ := mem_filter.mp hm
    obtain ⟨hB,hw⟩ := data he
    obtain ⟨hx,hy⟩ := mem_product.mp hB
    have bx := (mem_trunc.mp hx).1
    have by' := (mem_trunc.mp hy).1
    change ¬x+y<N at large
    change (x+y)%N∈Ico (N-w) N at hw
    rw [Nat.mod_eq_sub_mod (by omega : N≤x+y),Nat.mod_eq_of_lt (by omega)] at hw
    have lo := (mem_Ico.mp hw).1
    exact mk_mem_product (mem_filter.mpr ⟨hx,by omega⟩) (mem_filter.mpr ⟨hy,by omega⟩)
  have up := card_le_card upper
  rw [card_product,← sq] at up
  have sub : squareDisk L⊆squareDisk U := by
    rintro ⟨i,j⟩ h; exact mem_squareDisk.mpr ((mem_squareDisk.mp h).trans order)
  have ann := card_sdiff_add_card_eq_card sub
  have split : low.card+high.card=E.card := card_filter_add_card_filter_not ..
  change E.card+_≤_+B.card^2
  omega


private noncomputable def peak (f : ℕ → ℝ) (N : ℕ) : ℕ :=
  (exists_max_image (range (N+1)) f (nonempty_range_iff.mpr (Nat.succ_ne_zero _))).choose

private theorem peak_spec (f : ℕ → ℝ) (N : ℕ) :
    peak f N≤N ∧ ∀ j≤N, f j≤f (peak f N) := by
  obtain ⟨hm,hi⟩ := (exists_max_image (range (N+1)) f (nonempty_range_iff.mpr (Nat.succ_ne_zero _))).choose_spec
  exact ⟨Nat.le_of_lt_succ (mem_range.mp hm),fun j h => hi j (mem_range.mpr (Nat.lt_succ_of_le h))⟩

private theorem peak_vanish (f : ℕ → ℝ) (nonneg : ∀ j, 0≤f j)
    (lim : Tendsto (fun j => f j/j) atTop (𝓝 0)) :
    Tendsto (fun n => f (peak f n)/n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  obtain ⟨k,hk⟩ := eventually_atTop.mp (lim.eventually_lt_const ep)
  have early : Tendsto (fun n : ℕ => f (peak f k)/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [early.eventually_lt_const ep,eventually_ge_atTop 1] with n short pos
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (nonneg _) (Nat.cast_nonneg _))]
  by_cases small : peak f n≤k
  · exact ((div_le_div_of_nonneg_right ((peak_spec f k).2 _ small) (Nat.cast_nonneg n))).trans_lt short
  · have p : (0:ℝ)<peak f n := by exact_mod_cast (show 0<peak f n by omega)
    have np : (0:ℝ)<n := by exact_mod_cast pos
    have bound := (div_lt_iff₀ p).mp (hk _ (by omega))
    apply (div_lt_iff₀ np).mpr
    exact bound.trans_le (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (peak_spec f n).1) ep.le)

private noncomputable def rankCost (S : Set ℕ) (c : ℝ) (x : ℕ) :=
  |(countBelow S x:ℝ)^2-c^2*x|

private noncomputable def errorBudget (S : Set ℕ) (c : ℝ) (N : ℕ) :=
  rankCost S c (peak (rankCost S c) N)

private theorem error_vanish (S : Set ℕ) {c : ℝ}
    (regular : Tendsto (fun x : ℕ => (countBelow S x:ℝ)/Real.sqrt x) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => errorBudget S c n/n) atTop (𝓝 0) := by
  apply peak_vanish (rankCost S c) (fun _ => abs_nonneg _)
  have lim : Tendsto (fun x : ℕ => (countBelow S x:ℝ)^2/x) atTop (𝓝 (c^2)) := by
    simpa only [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using regular.pow 2
  have diff := (lim.sub (tendsto_const_nhds (x:=c^2))).abs
  rw [sub_self,abs_zero] at diff
  apply diff.congr'
  filter_upwards [eventually_ge_atTop 1] with i pos
  have nz : (i:ℝ)≠0 := by exact_mod_cast (show i≠0 by omega)
  change |_|=|_|/_
  rw [show (|((countBelow S i:ℝ)^2-c^2*i)|/(i:ℝ))=|((countBelow S i:ℝ)^2-c^2*i)/i| by simp only [abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) i)]]
  congr 1
  field_simp


private theorem floor_ratio {f : ℕ → ℝ} {N : ℕ → ℕ} {a : ℝ}
    (big : Tendsto N atTop atTop) (pos : ∀ i, 0<N i) (aPos : 0<a)
    (lim : Tendsto (fun i => f i/N i) atTop (𝓝 a)) :
    Tendsto (fun i => (⌊f i⌋₊:ℝ)/N i) atTop (𝓝 a) := by
  have inv : Tendsto (fun i => 1/(N i:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp big)
  have lower := lim.sub inv
  rw [sub_zero] at lower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lower lim
  · filter_upwards with i
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one (f i)]) (Nat.cast_nonneg _)
  · filter_upwards [lim.eventually_const_lt aPos] with i hi
    exact div_le_div_of_nonneg_right (Nat.floor_le ((div_pos_iff_of_pos_right (by exact_mod_cast pos i)).mp hi).le)
      (Nat.cast_nonneg _)

private theorem rank_band (S : Set ℕ) {c : ℝ} (N w : ℕ) (room : 0≤c^2*((N-w:ℕ):ℝ)-2*errorBudget S c N-1) :
    let U := ⌊c^2*(N:ℝ)+2*errorBudget S c N⌋₊
    let L := ⌊c^2*((N-w:ℕ):ℝ)-2*errorBudget S c N-1⌋₊
    (edgePairs (truncation S N) N w).card+(squareDisk L).card ≤
      (squareDisk U).card+((truncation S N).filter (N-w≤·)).card^2 := by
  let e := errorBudget S c N
  have ep : 0≤e := abs_nonneg _
  have le : c^2*((N-w:ℕ):ℝ)≤c^2*(N:ℝ) := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.sub_le ..)) (sq_nonneg _)
  apply edge_annulus S N w (order:=Nat.floor_mono (by change c^2*((N-w:ℕ):ℝ)-2*e-1≤c^2*(N:ℝ)+2*e; linarith))
  intro x hx y hy hLo hHi
  have bound (a : ℕ) (ha : a∈truncation S N) :
      -e≤(countBelow S a:ℝ)^2-c^2*a ∧ (countBelow S a:ℝ)^2-c^2*a≤e :=
    abs_le.mp ((peak_spec (rankCost S c) N).2 a (mem_trunc.mp ha).1.le)
  have low := mul_le_mul_of_nonneg_left (show ((N-w:ℕ):ℝ)≤(x:ℝ)+y by exact_mod_cast hLo) (sq_nonneg c)
  have high := mul_le_mul_of_nonneg_left (show (x:ℝ)+y≤N by exact_mod_cast hHi.le) (sq_nonneg c)
  have bx := bound x hx
  have by' := bound y hy
  constructor
  · apply (Nat.cast_lt (α:=ℝ)).mp
    push_cast
    apply lt_of_le_of_lt (Nat.floor_le room)
    change c^2*((N-w:ℕ):ℝ)-2*e-1<_
    linarith
  · apply Nat.le_floor
    push_cast
    change _≤c^2*(N:ℝ)+2*e
    linarith

private theorem hole_bound (B : Finset ℕ) (N : ℕ) (pos : 0<N) : (residues B N).card≤N := by
  apply le_trans _ (card_range N).le
  apply card_le_card
  intro x hx
  obtain ⟨_,_,rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (Nat.mod_lt _ pos)

/-- The ordinary cyclic sumset of the truncation includes diagonal pairs. -/
noncomputable def cyclicTruncation (S : Set ℕ) (N : ℕ+) : Finset (ZMod N) :=
  (truncation S N.val).image (fun x : ℕ => (x : ZMod N))

private theorem residues_eq (S : Set ℕ) (N : ℕ+) :
    (residues (truncation S N.val) N.val).card=(cyclicTruncation S N+cyclicTruncation S N).card := by
  have eq : residues (truncation S N.val) N.val=(cyclicTruncation S N+cyclicTruncation S N).image ZMod.val := by
    ext z
    constructor
    · intro h
      obtain ⟨_,hs,rfl⟩ := mem_image.mp h
      obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hs
      exact mem_image.mpr ⟨(x:ZMod N)+y,mem_add.mpr ⟨_,mem_image_of_mem _ hx,_,mem_image_of_mem _ hy,rfl⟩,
        by rw [← Nat.cast_add,ZMod.val_natCast]⟩
    · intro h
      obtain ⟨_,hs,rfl⟩ := mem_image.mp h
      obtain ⟨_,hx,_,hy,rfl⟩ := mem_add.mp hs
      obtain ⟨x,hxS,rfl⟩ := mem_image.mp hx
      obtain ⟨y,hyS,rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x+y,Finset.mem_add.mpr ⟨x,hxS,y,hyS,rfl⟩,by rw [← Nat.cast_add,ZMod.val_natCast]⟩
  rw [eq,card_image_of_injective _ (ZMod.val_injective _)]


/-- For a regularly growing set, every subsequential coverage limit
satisfies the terminal-window bound for all relative cutoffs `t²`. -/
theorem window_bound (S : Set ℕ) {c : ℝ} (cp : 0<c)
    (regular : Tendsto (fun x : ℕ => (countBelow S x:ℝ)/Real.sqrt x) atTop (𝓝 c))
    (Q : ℕ → ℕ+) (big : Tendsto (fun i => (Q i).val) atTop atTop) {p : ℝ}
    (cover : Tendsto (fun i => ((cyclicTruncation S (Q i)+cyclicTruncation S (Q i)).card:ℝ)/(Q i:ℝ)) atTop (𝓝 p))
    {t : ℝ} (tp : 0<t) (ts : t<1) :
    2*(1-t^2) ≤ Real.pi*c^2*(1-t^2)/4+(c*(1-t))^2+2*(1-p) := by
  let N i := (Q i).val
  let b i := ⌊t^2*(N i:ℝ)⌋₊
  let w i := N i-b i
  let B i := truncation S (N i)
  let k i := countBelow S (N i)
  let e i := errorBudget S c (N i)
  let u (i : ℕ) := c^2*(N i:ℝ)+2*e i
  let l (i : ℕ) := c^2*(b i:ℝ)-2*e i-1
  let top i := ((B i).filter (b i≤·)).card
  let holes i := N i-(residues (B i) (N i)).card
  have npos i : 0<N i := (Q i).pos
  have mp i : (0:ℝ)<N i := by exact_mod_cast npos i
  have nt : Tendsto (fun i => (N i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have inv : Tendsto (fun i => 1/(N i:ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop nt
  have tsq : t^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ts.le) (by linarith : 0≤1+t)]
  have fit i : b i≤N i := Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_right tsq (mp i).le)
  have cut i : N i-w i=b i := by dsimp only [w]; have := fit i; omega
  have bl : Tendsto (fun i => (b i:ℝ)/N i) atTop (𝓝 (t^2)) := by
    apply floor_ratio (N:=N) big npos (sq_pos_of_pos tp)
    simpa only [mul_div_cancel_right₀ _ (mp _).ne'] using (tendsto_const_nhds (x:=t^2) (f:=atTop (α:=ℕ)))
  have wl : Tendsto (fun i => (w i:ℝ)/N i) atTop (𝓝 (1-t^2)) := by
    simpa only [w,Nat.cast_sub (fit _),sub_div,div_self (mp _).ne'] using (tendsto_const_nhds (x:=(1:ℝ))).sub bl
  have bt : Tendsto b atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R:=ℝ)).mp
    simpa only [div_mul_cancel₀ _ (mp _).ne'] using bl.pos_mul_atTop (sq_pos_of_pos tp) nt
  have root : Tendsto (fun i => Real.sqrt (b i)/Real.sqrt (N i)) atTop (𝓝 t) := by
    simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _),Real.sqrt_sq tp.le] using
      Real.continuous_sqrt.continuousAt.tendsto.comp bl
  have early : Tendsto (fun i => (countBelow S (b i):ℝ)/Real.sqrt (N i)) atTop (𝓝 (c*t)) := by
    apply ((regular.comp bt).mul root).congr'
    filter_upwards [bt.eventually (eventually_ge_atTop 1)] with i pos
    have bp : (0:ℝ)<b i := by exact_mod_cast pos
    change _/Real.sqrt (b i)*(Real.sqrt (b i)/_)=_
    field_simp
  have kl : Tendsto (fun i => (k i:ℝ)/Real.sqrt (N i)) atTop (𝓝 c) := regular.comp big
  have topl : Tendsto (fun i => (top i:ℝ)/Real.sqrt (N i)) atTop (𝓝 (c*(1-t))) := by
    rw [show c*(1-t)=c-c*t by ring]
    apply (kl.sub early).congr
    intro i
    have eq := top_count S (N i) (w i)
    rw [cut] at eq
    change top i+countBelow S (b i)=k i at eq
    have re := congrArg (Nat.cast (R:=ℝ)) eq
    rw [← sub_div]
    congr 1
    push_cast at re
    linarith
  have top2 : Tendsto (fun i => (top i:ℝ)^2/N i) atTop (𝓝 ((c*(1-t))^2)) := by
    simpa only [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using topl.pow 2
  have tiny : Tendsto (fun i => (k i:ℝ)/N i) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,div_div,← sq,Real.sq_sqrt (Nat.cast_nonneg _)] using
      kl.div_atTop (Real.tendsto_sqrt_atTop.comp nt)
  have hol : Tendsto (fun i => (holes i:ℝ)/N i) atTop (𝓝 (1-p)) := by
    apply ((tendsto_const_nhds (x:=(1:ℝ))).sub cover).congr
    intro i
    rw [show (holes i:ℝ)=(N i:ℝ)-((residues (B i) (N i)).card:ℝ) by
      exact Nat.cast_sub (hole_bound _ _ (npos i)),sub_div,div_self (mp i).ne',residues_eq S (Q i)]
  have el : Tendsto (fun i => e i/N i) atTop (𝓝 0) := (error_vanish S regular).comp big
  have ul : Tendsto (fun i => u i/N i) atTop (𝓝 (c^2)) := by
    simpa only [u,add_div,mul_div_cancel_right₀ _ (mp _).ne',mul_div_assoc,mul_zero,add_zero] using
      (tendsto_const_nhds (x:=c^2)).add (el.const_mul 2)
  have ll : Tendsto (fun i => l i/N i) atTop (𝓝 (c^2*t^2)) := by
    simpa only [l,sub_div,mul_div_assoc,mul_zero,sub_zero] using
      (((bl.const_mul (c^2)).sub (el.const_mul 2)).sub inv)
  have lower := squareDisk_limit big (floor_ratio big npos (mul_pos (sq_pos_of_pos cp) (sq_pos_of_pos tp)) ll)
  have upper := squareDisk_limit big (floor_ratio big npos (sq_pos_of_pos cp) ul)
  have room : ∀ᶠ i in atTop, 0≤l i := by
    filter_upwards [ll.eventually_const_lt (mul_pos (sq_pos_of_pos cp) (sq_pos_of_pos tp))] with i hi
    exact ((div_pos_iff_of_pos_right (mp i)).mp hi).le
  have lhs := (wl.const_mul 2).add lower
  have rhs := (((upper.add top2).add (tiny.const_mul 2)).add (hol.const_mul 2))
  have bound := le_of_tendsto_of_tendsto lhs rhs (show ∀ᶠ i in atTop, _ by
    filter_upwards [room] with i ri
    have band := rank_band S (N i) (w i) (by rw [cut]; exact ri)
    dsimp only at band
    rw [cut] at band
    have edges := edge_coverage (B i) (N i) (w i) (npos i) (Nat.sub_le ..)
    have all : 2*w i+(squareDisk ⌊l i⌋₊).card≤(squareDisk ⌊u i⌋₊).card+(top i)^2+2*k i+2*holes i := by
      change (edgePairs (B i) (N i) (w i)).card+_≤_+((B i).filter (b i≤·)).card^2 at band
      change 2*w i≤_+2*k i+2*holes i at edges
      change (edgePairs (B i) (N i) (w i)).card+(squareDisk ⌊l i⌋₊).card≤(squareDisk ⌊u i⌋₊).card+_ at band
      change (edgePairs (B i) (N i) (w i)).card+(squareDisk ⌊l i⌋₊).card≤(squareDisk ⌊u i⌋₊).card+(top i)^2 at band
      omega
    have re := (Nat.cast_le (α:=ℝ)).mpr all
    push_cast at re
    have cmp := div_le_div_of_nonneg_right re (mp i).le
    simpa only [add_div,mul_div_assoc] using cmp)
  linarith


/-- Fraction of residues covered by the original least labels of `S`. -/
noncomputable def coverage (S : Set ℕ) (q : ℕ+) : ℝ :=
  ((cyclicTruncation S q+cyclicTruncation S q).card:ℝ)/(q:ℝ)

private theorem area_defect (S : Set ℕ) {c : ℝ} (cp : 0<c)
    (regular : Tendsto (fun x : ℕ => (countBelow S x:ℝ)/Real.sqrt x) atTop (𝓝 c))
    (Q : ℕ → ℕ+) (big : Tendsto (fun i => (Q i).val) atTop atTop) {p : ℝ}
    (cover : Tendsto (fun i => coverage S (Q i)) atTop (𝓝 p))
    (subcritical : Real.pi*c^2<8) :
    let a := 1-Real.pi*c^2/8
    a^2/(a+c^2/2)≤1-p := by
  let a := 1-Real.pi*c^2/8
  let d := a+c^2/2
  have ap : 0<a := by dsimp [a]; linarith
  have cp2 := sq_pos_of_pos cp
  have dp : 0<d := by dsimp [d]; positivity
  let t := (c^2/2)/d
  have tp : 0<t := div_pos (by positivity) dp
  have ts : t<1 := (div_lt_one dp).mpr (by dsimp [d]; linarith)
  have h := window_bound S cp regular Q big cover tp ts
  have cut : a*(1-t^2)-(c^2/2)*(1-t)^2≤1-p := by dsimp only [a]; linarith
  have opt : a*(1-t^2)-(c^2/2)*(1-t)^2=a^2/d := by
    dsimp only [t]
    field_simp [dp.ne']
    dsimp only [d]
    ring
  change a^2/d≤1-p
  rwa [opt] at cut

/-- Optimizing the terminal window bounds the best subsequential
coverage among all positive moduli of a fixed regularly growing set. -/
theorem coverage_limsup (S : Set ℕ) {c : ℝ} (cp : 0<c)
    (regular : Tendsto (fun x : ℕ => (countBelow S x:ℝ)/Real.sqrt x) atTop (𝓝 c))
    (subcritical : Real.pi*c^2<8) :
    let a := 1-Real.pi*c^2/8
    limsup (coverage S) atTop≤1-a^2/(a+c^2/2) := by
  have nonneg (q : ℕ+) : 0≤coverage S q := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have upper (q : ℕ+) : coverage S q≤1 := by
    apply (div_le_one (by exact_mod_cast q.pos : (0:ℝ)<q)).mpr
    have h := Finset.card_le_univ (cyclicTruncation S q+cyclicTruncation S q)
    rw [ZMod.card] at h
    exact_mod_cast h
  obtain ⟨Q,lim,big⟩ := exists_seq_tendsto_limsup (isCoboundedUnder_le_of_le atTop nonneg)
    (isBoundedUnder_of_eventually_le (Eventually.of_forall upper))
  have h := area_defect S cp regular Q (tendsto_PNat_val_atTop_atTop.comp big) lim subcritical
  dsimp only at h ⊢
  linarith

/-- Regular growth at Green's critical size forces a positive proportion
of omissions along every unbounded sequence of orders. -/
theorem critical_coverage (S : Set ℕ)
    (regular : Tendsto (fun x : ℕ => (countBelow S x:ℝ)/Real.sqrt x) atTop (𝓝 (Real.sqrt 2))) :
    limsup (coverage S) atTop≤1-(1-Real.pi/4)^2/(2-Real.pi/4) := by
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have sub : Real.pi*(Real.sqrt 2)^2<8 := by rw [sq]; linarith [Real.pi_lt_d2]
  have h := coverage_limsup S (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)) regular sub
  dsimp only at h
  rw [sq] at h
  convert h using 1
  ring

/-- Stöhr's numerical threshold is necessary even for cyclic near-coverage
along an unbounded subsequence when the single set has regular growth. -/
theorem regular_lower_bound (S : Set ℕ) {c : ℝ}
    (regular : Tendsto (fun x : ℕ => (countBelow S x:ℝ)/Real.sqrt x) atTop (𝓝 c))
    (Q : ℕ → ℕ+) (big : Tendsto (fun i => (Q i).val) atTop atTop)
    (cover : Tendsto (fun i => coverage S (Q i)) atTop (𝓝 1)) :
    Real.sqrt (8/Real.pi)≤c := by
  have nonneg : 0≤c := le_of_tendsto_of_tendsto' tendsto_const_nhds regular
    (fun i => div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  have kl := regular.comp big
  have k : Tendsto (fun i => (countBelow S (Q i).val:ℝ)^2/(Q i:ℝ)) atTop (𝓝 (c^2)) := by
    simpa only [Function.comp_def,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using kl.pow 2
  have unity : 1≤c^2 := by
    apply le_of_tendsto_of_tendsto' cover k
    intro i
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have im : (cyclicTruncation S (Q i)).card≤countBelow S (Q i).val := card_image_le
    have cap := (card_add_le : (cyclicTruncation S (Q i)+cyclicTruncation S (Q i)).card≤_).trans (Nat.mul_le_mul im im)
    rw [← sq] at cap
    exact_mod_cast cap
  have cp : 0<c := lt_of_le_of_ne nonneg (by rintro rfl; norm_num at unity)
  have area : 8≤Real.pi*c^2 := by
    by_contra! small
    have h := area_defect S cp regular Q big cover small
    dsimp only at h
    have pos : 0<1-Real.pi*c^2/8 := by linarith
    have := div_pos (sq_pos_of_pos pos) (add_pos pos (by positivity : 0<c^2/2))
    linarith
  exact (Real.sqrt_le_iff.mpr ⟨nonneg,(div_le_iff₀ Real.pi_pos).mpr (by linarith)⟩)

#print axioms quarter_area
#print axioms mem_disk
#print axioms disk_count
#print axioms disk_limit
#print axioms mem_squareDisk
#print axioms squareDisk_limit
#print axioms edge_coverage
#print axioms edge_annulus
#print axioms window_bound
#print axioms coverage_limsup
#print axioms critical_coverage
#print axioms regular_lower_bound
end Green33RegularTruncations
