import Green33RegularTruncations
import Green33ReflectionRigidity
import Green33QuarticSeed

/-! Green's question through prefixes of one integer set. -/

open Finset Filter Green33RegularTruncations
open scoped Topology Pointwise

namespace Green33FixedPrefixes

/-- Move the cyclic origin to `u` and take the least nonnegative labels. -/
def block {q : ℕ+} (A : Finset (ZMod q)) (u : ℕ) : Finset ℕ :=
  (range q.val).filter fun x => (((u+x:ℕ):ZMod q)∈A)

private theorem count_all {q : ℕ+} (A : Finset (ZMod q)) (u : ℕ) :
    (block A u).card=A.card := by
  let f (x : ℕ) := ((u+x:ℕ):ZMod q)
  let g (z : ZMod q) := (z-(u:ZMod q)).val
  apply card_nbij' f g
  · intro x hx; exact (mem_filter.mp hx).2
  · intro z hz
    exact mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),by simpa [g,Nat.cast_add] using hz⟩
  · intro x hx
    have h := mem_range.mp (mem_filter.mp hx).1
    simp [f,g,Nat.cast_add,ZMod.val_natCast,Nat.mod_eq_of_lt h]
  · intro z _; simp [f,g,Nat.cast_add]

private theorem shifted_basis {q : ℕ+} (A : Finset (ZMod q)) (u : ℕ) (cov : A+A=univ) :
    let B := (block A u).image (fun x : ℕ => (x:ZMod q))
    B+B=univ := by
  apply eq_univ_of_forall
  intro z
  have hit : z+(u:ZMod q)+u∈A+A := cov ▸ mem_univ _
  obtain ⟨a,ha,b,hb,e⟩ := mem_add.mp hit
  have mem (a : ZMod q) (ha : a∈A) : a-u∈(block A u).image (fun x : ℕ => (x:ZMod q)) := by
    refine mem_image.mpr ⟨(a-u).val,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),?_⟩,ZMod.natCast_zmod_val _⟩
    simpa [Nat.cast_add] using ha
  exact mem_add.mpr ⟨_,mem a ha,_,mem b hb,by rw [show a-u+(b-u)=a+b-u-u by abel,e]; abel⟩

/-- A cyclic cut controls every prefix simultaneously. The ordinary
cyclic sumset is preserved up to translation at that cut. -/
theorem balanced_cut {q : ℕ+} (A : Finset (ZMod q)) :
    ∃ u<q.val, ∀ x≤q.val, q.val*((block A u).filter (·<x)).card≤A.card*x := by
  let k : ℤ := A.card
  let n : ℤ := q.val
  let f (i : ℕ) : ℤ := (if (i:ZMod q)∈A then n else 0)-k
  let F (j : ℕ) := ∑ i ∈ range j, f i
  have term (u x : ℕ) : ∑ i ∈ range x, f (u+i) =
      n*(((range x).filter (fun i => (((u+i:ℕ):ZMod q)∈A))).card:ℤ)-k*x := by
    simp [f,sum_sub_distrib,sum_ite,mul_comm]
  have endpt : F q.val=0 := by
    have eq := term 0 q.val
    simp only [zero_add] at eq
    have e := count_all A 0
    simp only [block,zero_add] at e
    simpa only [F,e,n,k,sub_self,mul_comm] using eq
  have periodic (t) : F (q.val+t)=F t := by
    change ∑ i ∈ range (q.val+t), f i=_
    rw [sum_range_add,show (∑ i ∈ range q.val,f i)=0 from endpt,zero_add]
    simp [F,f,Nat.cast_add]
  obtain ⟨u,hu,most⟩ := exists_max_image (range q.val) F (nonempty_range_iff.mpr q.pos.ne')
  refine ⟨u,mem_range.mp hu,fun x hx => ?_⟩
  have le : F (u+x)≤F u := by
    by_cases small : u+x<q.val
    · exact most _ (mem_range.mpr small)
    · have uv := mem_range.mp hu
      rw [show u+x=q.val+(u+x-q.val) by omega,periodic]
      exact most _ (mem_range.mpr (by omega))
  have eq : F (u+x)=F u+(n*(((range x).filter (fun i => (((u+i:ℕ):ZMod q)∈A))).card:ℤ)-k*x) := by
    dsimp only [F]; rw [sum_range_add,term]
  have same : (block A u).filter (·<x)=(range x).filter (fun i => (((u+i:ℕ):ZMod q)∈A)) := by
    ext i; simp only [block,mem_filter,mem_range]; constructor
    · rintro ⟨⟨_,ha⟩,hi⟩; exact ⟨hi,ha⟩
    · rintro ⟨hi,ha⟩; exact ⟨⟨hi.trans_le hx,ha⟩,hi⟩
  rw [same]
  have ar : n*(((range x).filter (fun i => (((u+i:ℕ):ZMod q)∈A))).card:ℤ)≤k*x := by linarith
  dsimp only [n,k] at ar
  exact_mod_cast ar


/-- Each positive tolerance admits unbounded orders with normalized
ordinary basis size below the specified upper coefficient plus the tolerance. -/
def feasible (c : ℝ) : Prop := ∀ ε : ℝ, 0<ε → ∃ᶠ q : ℕ+ in atTop,
  ∃ A : Finset (ZMod q), A+A=univ ∧ (A.card:ℝ)/Real.sqrt q<c+ε

private theorem envelope {q : ℕ+} (A : Finset (ZMod q)) (u : ℕ)
    (pref : ∀ x≤q.val, q.val*((block A u).filter (·<x)).card≤A.card*x) (x : ℕ) :
    (((block A u).filter (·<x)).card:ℝ)≤((A.card:ℝ)/Real.sqrt q)*Real.sqrt x := by
  have qp : (0:ℝ)<q := by exact_mod_cast q.pos
  have root := Real.sqrt_pos.mpr qp
  have k : (0:ℝ)≤A.card := Nat.cast_nonneg _
  rcases le_total x q.val with le|ge
  · have cs : (Real.sqrt (x:ℝ))≤Real.sqrt q := Real.sqrt_le_sqrt (by exact_mod_cast le)
    have h := (Nat.cast_le (α:=ℝ)).mpr (pref x le)
    push_cast at h
    have bound := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cs (Real.sqrt_nonneg x)) k
    rw [← sq,Real.sq_sqrt (Nat.cast_nonneg _)] at bound
    rw [div_mul_eq_mul_div,le_div_iff₀ root]
    apply (mul_le_mul_iff_of_pos_right root).mp
    rw [mul_assoc,← sq,Real.sq_sqrt qp.le]
    nlinarith
  · have cs := Real.sqrt_le_sqrt (show (q:ℝ)≤x by exact_mod_cast ge)
    have le := (card_le_card (filter_subset (·<x) (block A u))).trans_eq (count_all A u)
    calc _ ≤ (A.card:ℝ) := Nat.cast_le.mpr le
         _ = (A.card:ℝ)/Real.sqrt q*Real.sqrt q := (div_mul_cancel₀ _ root.ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left cs (div_nonneg k root.le)

private structure Stage where
  order : ℕ+
  labels : Finset ℕ
  bounded : labels⊆range order.val
  basis : let A := labels.image (fun x : ℕ => (x:ZMod order)); A+A=univ

private theorem far_stage {c : ℝ} (H : feasible c) (K : ℕ) {ε : ℝ} (ep : 0<ε) :
    ∃ s : Stage, K<s.order.val ∧ (∀ z∈s.labels, K≤z) ∧
      ∀ x : ℕ, ((s.labels.filter (·<x)).card:ℝ)≤(c+ε)*Real.sqrt x := by
  let b := ⌈max (c+ε) 1⌉₊+1
  let lower := (b*(K+1))^2+K+1
  obtain ⟨q,hq,A,hA,sz⟩ := frequently_atTop.mp (H ε ep) (Nat.succPNat lower)
  have nq : lower+1≤q.val := hq
  have more : K<q.val := by dsimp [lower] at nq; omega
  have bpos : 0<(b:ℝ) := by dsimp [b]; positivity
  have coeff : c+ε≤(b:ℝ) := by
    have := Nat.le_ceil (max (c+ε) 1)
    dsimp [b]; push_cast; linarith [le_max_left (c+ε) 1]
  have poly : (b*(K+1))^2<q.val := by
    dsimp [lower] at nq
    omega
  have root : (b:ℝ)*(K+1)<Real.sqrt q := by
    apply Real.lt_sqrt_of_sq_lt
    exact_mod_cast poly
  have qp : (0:ℝ)<q := by exact_mod_cast q.pos
  have kp := (div_lt_iff₀ (Real.sqrt_pos.mpr qp)).mp sz
  have tiny : A.card*K<q.val := by
    apply (Nat.cast_lt (α:=ℝ)).mp
    push_cast
    have e := mul_le_mul_of_nonneg_right (kp.le.trans (mul_le_mul_of_nonneg_right coeff (Real.sqrt_nonneg _))) (Nat.cast_nonneg (α:=ℝ) K)
    have bm : (b:ℝ)*K<Real.sqrt q := by nlinarith
    have final := mul_lt_mul_of_pos_right bm (Real.sqrt_pos.mpr qp)
    rw [← sq,Real.sq_sqrt qp.le] at final
    nlinarith
  obtain ⟨u,_,pref⟩ := balanced_cut A
  refine ⟨⟨q,block A u,filter_subset ..,shifted_basis A u hA⟩,more,?_,?_⟩
  · intro z hz
    by_contra! lt
    have nonempty : ((block A u).filter (·<K)).Nonempty := ⟨z,mem_filter.mpr ⟨hz,lt⟩⟩
    have cap := pref K more.le
    have one := Nat.mul_le_mul_left q.val (card_pos.mpr nonempty)
    omega
  · intro x
    exact (envelope A u pref x).trans (mul_le_mul_of_nonneg_right sz.le (Real.sqrt_nonneg _))


private def separation (i q : ℕ) := ((i+2)*(q+1))^2

private theorem separation_gt (i q : ℕ) : q<separation i q := by
  have e := Nat.le_mul_of_pos_left (q+1) (by omega : 0 < i+2)
  have sq : (i+2)*(q+1)≤((i+2)*(q+1))^2 := Nat.le_self_pow (by decide) _
  exact (Nat.lt_of_lt_of_le (Nat.lt_succ_self q) e).trans_le sq

private noncomputable def stages {c : ℝ} (H : feasible c) : ℕ → Stage
  | 0 => (far_stage H 0 (by positivity : 0 < 1/(((0:ℕ):ℝ)+1))).choose
  | i+1 => (far_stage H (separation i (stages H i).order.val)
      (by positivity : 0<1/(((i+1:ℕ):ℝ)+1))).choose

private def cutoff (s : ℕ → Stage) : ℕ → ℕ
  | 0 => 0
  | i+1 => separation i (s i).order.val

private theorem stage_spec {c : ℝ} (H : feasible c) (i : ℕ) :
    let s := stages H
    cutoff s i < (s i).order.val ∧ (∀ z∈(s i).labels, cutoff s i≤z) ∧
      ∀ x : ℕ, (((s i).labels.filter (·<x)).card:ℝ)≤(c+1/((i:ℝ)+1))*Real.sqrt x := by
  cases i with
  | zero => exact (far_stage H 0 (by positivity : 0 < 1/(((0:ℕ):ℝ)+1))).choose_spec
  | succ i => exact (far_stage H (separation i (stages H i).order.val)
      (by positivity : 0<1/(((i+1:ℕ):ℝ)+1))).choose_spec

private def glued (s : ℕ → Stage) : Set ℕ := {x | ∃ i, x∈(s i).labels}

/-- Global eventual upper bound on prefix size, at every sufficiently
large integer cutoff for each positive tolerance. -/
def UpperCoefficient (S : Set ℕ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ x : ℕ in atTop, (countBelow S x:ℝ)/Real.sqrt x<c+ε

private theorem has_basis (s : ℕ → Stage) (i : ℕ) :
    let q := (s i).order
    cyclicTruncation (glued s) q+cyclicTruncation (glued s) q=univ := by
  classical
  let q := (s i).order
  let B := (s i).labels.image (fun z : ℕ => (z:ZMod q))
  have sub : B⊆cyclicTruncation (glued s) q := by
    apply image_subset_image
    intro x hx
    exact mem_filter.mpr ⟨(s i).bounded hx,⟨i,hx⟩⟩
  apply eq_univ_of_forall
  intro z
  have e : z∈B+B := (s i).basis ▸ mem_univ _
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp e
  exact mem_add.mpr ⟨a,sub ha,b,sub hb,rfl⟩

private theorem stage_counts {c : ℝ} (H : feasible c) (i x : ℕ)
    (fit : x≤cutoff (stages H) (i+2)) :
    countBelow (glued (stages H)) x≤(stages H i).order.val+((stages H (i+1)).labels.filter (·<x)).card := by
  classical
  let s := stages H
  have cuts : StrictMono (cutoff s) := strictMono_nat_of_lt_succ fun j =>
    (stage_spec H j).1.trans (separation_gt j _)
  have orders : StrictMono (fun j => (s j).order.val) := strictMono_nat_of_lt_succ fun j =>
    (separation_gt j _).trans (stage_spec H (j+1)).1
  have sub : truncation (glued s) x⊆range (s i).order.val∪((s (i+1)).labels.filter (·<x)) := by
    intro z hz
    obtain ⟨bound,hgl⟩ := mem_filter.mp hz
    obtain ⟨j,hj⟩ := hgl
    have lx := mem_range.mp bound
    by_cases early : j ≤ i
    · exact mem_union_left _ (mem_range.mpr ((mem_range.mp ((s j).bounded hj)).trans_le (orders.monotone early)))
    · have cap := (stage_spec H j).2.1 z hj
      have lt : j < i+2 := by
        by_contra! ge
        exact (not_lt_of_ge ((cuts.monotone ge).trans cap)) (lx.trans_le fit)
      obtain rfl : j=i+1 := by omega
      exact mem_union_right _ (mem_filter.mpr ⟨hj,lx⟩)
  exact (card_le_card sub).trans ((card_union_le ..).trans_eq (by rw [card_range]))

private theorem gap_ratio (i q x : ℕ) (h : separation i q≤x) :
    (q:ℝ)/Real.sqrt x ≤ 1/(((i+1:ℕ):ℝ)+1) := by
  have s : ((i:ℝ)+2)*(q+1)≤Real.sqrt x := Real.le_sqrt_of_sq_le (by exact_mod_cast h)
  have hp : (0:ℝ)<x := by exact_mod_cast (Nat.zero_le q).trans_lt ((separation_gt i q).trans_le h)
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hp) (by positivity)]
  push_cast
  nlinarith


/-- Normalized count of the elements strictly below the cutoff. -/
noncomputable def coefficient (S : Set ℕ) (x : ℕ) : ℝ := (countBelow S x:ℝ)/Real.sqrt x

/-- Unbounded orders where the truncation is an exact ordinary basis. -/
def PrefixBases (S : Set ℕ) : Prop := ∃ᶠ q : ℕ+ in atTop,
  cyclicTruncation S q+cyclicTruncation S q=univ

private theorem cuts_strict {c : ℝ} (H : feasible c) : StrictMono (cutoff (stages H)) :=
  strictMono_nat_of_lt_succ fun j => (stage_spec H j).1.trans (separation_gt j _)

private theorem orders_strict {c : ℝ} (H : feasible c) : StrictMono (fun j => (stages H j).order.val) :=
  strictMono_nat_of_lt_succ fun j => (separation_gt j _).trans (stage_spec H (j+1)).1

private theorem all_prefixes {c : ℝ} (H : feasible c) : UpperCoefficient (glued (stages H)) c := by
  let s := stages H
  have cuts := cuts_strict H
  let j (x : ℕ) := Nat.findGreatest (fun i => cutoff s i≤x) x
  have begins x : cutoff s (j x)≤x := Nat.findGreatest_spec (P:=fun i => cutoff s i≤x) (Nat.zero_le x) (show cutoff s 0≤x from Nat.zero_le x)
  have ends x : x<cutoff s (j x+1) := by
    by_contra! h
    have bound : j x+1≤x := (cuts.id_le (j x+1)).trans h
    have ge : j x+1≤j x := Nat.le_findGreatest bound h
    omega
  have jt : Tendsto j atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [eventually_ge_atTop (cutoff s m)] with x h
    exact Nat.le_findGreatest ((cuts.id_le m).trans h) h
  have piece (i x : ℕ) (beginning : cutoff s (i+1)≤x) (ending : x≤cutoff s (i+2)) :
      coefficient (glued s) x≤c+2*(1/(((i+1:ℕ):ℝ)+1)) := by
    have hp : (0:ℝ)<x := by exact_mod_cast (Nat.zero_le (s i).order.val).trans_lt ((separation_gt i _).trans_le beginning)
    have cap := (Nat.cast_le (α:=ℝ)).mpr (stage_counts H i x ending)
    push_cast at cap
    have gr := gap_ratio i (s i).order.val x beginning
    have env := (stage_spec H (i+1)).2.2 x
    have rr := (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mp gr
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
    change (countBelow (glued (stages H)) x:ℝ)≤_
    change ((stages H i).order.val:ℝ)≤_ at rr
    linarith
  intro ε ep
  have tiny := (tendsto_one_div_add_atTop_nhds_zero_nat.comp jt).const_mul (2:ℝ)
  rw [mul_zero] at tiny
  filter_upwards [tiny.eventually_lt_const ep,jt.eventually (eventually_ge_atTop 1)] with x small positive
  obtain ⟨i,hi⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j x≠0)
  have start := begins x
  have stop := ends x
  change 2*(1/((j x:ℝ)+1))<ε at small
  rw [hi] at start stop small
  exact (piece i x start stop.le).trans_lt (by linarith)

private theorem valley {c : ℝ} (H : feasible c) (i : ℕ) :
    let s := stages H
    coefficient (glued s) (cutoff s (i+1))≤1/(((i+1:ℕ):ℝ)+1) := by
  classical
  let s := stages H
  let x := cutoff s (i+1)
  have sub : truncation (glued s) x ⊆ range (s i).order.val := by
    intro z hz
    obtain ⟨bound,hgl⟩ := mem_filter.mp hz
    obtain ⟨j,hj⟩ := hgl
    have early : j ≤ i := by
      by_contra! h
      have a := (cuts_strict H).monotone h
      have b := (stage_spec H j).2.1 z hj
      exact (not_lt_of_ge (a.trans b)) (mem_range.mp bound)
    exact mem_range.mpr ((mem_range.mp ((s j).bounded hj)).trans_le ((orders_strict H).monotone early))
  have cap := (card_le_card sub).trans_eq (card_range _)
  exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr cap) (Real.sqrt_nonneg _)).trans (gap_ratio i _ _ le_rfl)

/-- Arbitrarily large finite bases can be pasted into one integer set.
The coefficient bound holds at all cutoffs and a subsequence has
normalized count tending to zero. -/
theorem fixed_prefixes {c : ℝ} (H : feasible c) :
    ∃ S : Set ℕ, UpperCoefficient S c ∧ PrefixBases S ∧
      ∃ L : ℕ → ℕ, Tendsto L atTop atTop ∧ Tendsto (fun i => coefficient S (L i)) atTop (𝓝 0) := by
  let s := stages H
  refine ⟨glued s,all_prefixes H,?_,fun i => cutoff s (i+1),?_,?_⟩
  · apply frequently_atTop.mpr
    intro q
    exact ⟨(s q.val).order,(orders_strict H).id_le _,has_basis s _⟩
  · apply tendsto_atTop_mono _ tendsto_id
    exact fun i => (Nat.le_succ i).trans ((cuts_strict H).id_le _)
  · have upper : Tendsto (fun i : ℕ => 1/(((i+1:ℕ):ℝ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    exact squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (valley H) upper


private theorem prefix_feasible {S : Set ℕ} {c : ℝ} (upper : UpperCoefficient S c)
    (basis : PrefixBases S) : feasible c := by
  intro ε ep
  have ev := tendsto_PNat_val_atTop_atTop.eventually (upper ε ep)
  apply (basis.and_eventually ev).mono
  rintro q ⟨base,sz⟩
  exact ⟨cyclicTruncation S q,base,
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_image_le :
      (cyclicTruncation S q).card≤countBelow S q.val)) (Real.sqrt_nonneg _)).trans_lt sz⟩

/-- Finite feasibility at any upper coefficient is exactly feasibility
by the prefixes of one set with the same global upper coefficient. -/
theorem feasible_iff_fixed (c : ℝ) : feasible c ↔
    ∃ S : Set ℕ, UpperCoefficient S c ∧ PrefixBases S := by
  constructor
  · intro h
    obtain ⟨S,up,base,_⟩ := fixed_prefixes h
    exact ⟨S,up,base⟩
  · rintro ⟨S,up,base⟩
    exact prefix_feasible up base

private theorem size_slack {q : ℕ+} (A : Finset (ZMod q)) (h : A+A=univ) :
    Real.sqrt 2-2/Real.sqrt q≤(A.card:ℝ)/Real.sqrt q := by
  have floor := Green33ReflectionRigidity.order_bound A h
  rw [ZMod.card] at floor
  have cap : 2*(q:ℝ)≤(A.card:ℝ)^2+2 := by exact_mod_cast floor
  have sq : Real.sqrt (2*(q:ℝ))≤A.card+2 := Real.sqrt_le_iff.mpr
    ⟨by positivity,by nlinarith [Nat.cast_nonneg (α:=ℝ) A.card]⟩
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at sq
  have root := Real.sqrt_pos.mpr (show (0:ℝ)<q by exact_mod_cast q.pos)
  rw [sub_le_iff_le_add,← add_div,le_div_iff₀ root]
  linarith

private theorem upper_to_green (H : feasible (Real.sqrt 2)) : Green33StrictReduction.OrdinaryLimit := by
  intro ε ep
  have one : Tendsto (fun q : ℕ+ => 2/Real.sqrt q) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop))
  apply ((H ε ep).and_eventually (one.eventually_lt_const ep)).mono
  rintro q ⟨⟨A,ha,sz⟩,sl⟩
  refine ⟨A,ha,abs_lt.mpr ⟨?_,by linarith⟩⟩
  linarith [size_slack A ha]

private theorem coe_nonneg (S : Set ℕ) (x : ℕ) : 0≤coefficient S x :=
  div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

private theorem bounded {S : Set ℕ} {c : ℝ} (upper : UpperCoefficient S c) :
    IsBoundedUnder (·≤·) atTop (coefficient S) :=
  isBoundedUnder_of_eventually_le ((upper 1 zero_lt_one).mono fun _ h => h.le)

private theorem upper_limsup {S : Set ℕ} {c : ℝ} (upper : UpperCoefficient S c) :
    limsup (coefficient S) atTop≤c := by
  apply (limsup_le_iff (isCoboundedUnder_le_of_le atTop (coe_nonneg S)) (bounded upper)).mpr
  intro z hz
  filter_upwards [upper (z-c) (sub_pos.mpr hz)] with x hx
  change (countBelow S x:ℝ)/Real.sqrt x<z
  linarith

private theorem positive_limsup {S : Set ℕ} {c : ℝ} (cp : 0<c) (h : limsup (coefficient S) atTop=c) :
    UpperCoefficient S c := by
  have bdd : IsBoundedUnder (·≤·) atTop (coefficient S) := by
    by_contra bad
    have empty : {a : ℝ | ∀ᶠ n in atTop, coefficient S n≤a}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact bad (isBoundedUnder_of_eventually_le ha)
    rw [limsup_eq,empty,Real.sInf_empty] at h
    linarith
  intro ε ep
  exact eventually_lt_of_limsup_lt (h.trans_lt (lt_add_of_pos_right _ ep)) bdd

private theorem basis_limsup {S : Set ℕ} {c : ℝ} (upper : UpperCoefficient S c) (basis : PrefixBases S) :
    Real.sqrt 2≤limsup (coefficient S) atTop := by
  apply (le_limsup_iff (isCoboundedUnder_le_of_le atTop (coe_nonneg S)) (bounded upper)).mpr
  intro a ha
  have tiny : Tendsto (fun q : ℕ+ => 2/Real.sqrt q) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop))
  have freq := basis.and_eventually (tiny.eventually_lt_const (sub_pos.mpr ha))
  apply frequently_atTop.mpr
  intro n
  obtain ⟨q,hq,base,sl⟩ := frequently_atTop.mp freq (Nat.succPNat n)
  have cap := div_le_div_of_nonneg_right (Nat.cast_le.mpr (card_image_le :
    (cyclicTruncation S q).card≤countBelow S q.val) : ((cyclicTruncation S q).card:ℝ)≤countBelow S q.val)
    (Real.sqrt_nonneg (q:ℝ))
  exact ⟨q.val,(Nat.le_succ n).trans hq,show a<(countBelow S q.val:ℝ)/Real.sqrt q by
    linarith [size_slack _ base]⟩

private theorem zero_liminf {S : Set ℕ} {c : ℝ} (upper : UpperCoefficient S c) (L : ℕ → ℕ)
    (ltop : Tendsto L atTop atTop) (low : Tendsto (fun i => coefficient S (L i)) atTop (𝓝 0)) :
    liminf (coefficient S) atTop=0 := by
  have nonneg := isBoundedUnder_of_eventually_ge (Eventually.of_forall (coe_nonneg S) : ∀ᶠ n in atTop, 0≤coefficient S n)
  have mapped : IsBoundedUnder (·≤·) (map L atTop) (coefficient S) := isBoundedUnder_of_eventually_le
    (((upper 1 zero_lt_one).mono fun _ h => h.le).filter_mono ltop)
  have hi := Filter.Tendsto.liminf_le_liminf_comp (u:=coefficient S) ltop
    mapped.isCoboundedUnder_ge nonneg
  rw [show liminf (coefficient S ∘ L) atTop=0 from low.liminf_eq] at hi
  exact le_antisymm hi (le_liminf_of_le (bounded upper).isCoboundedUnder_ge (Eventually.of_forall (coe_nonneg S)))

/-- Green's literal ordinary-basis question is equivalent to using
one fixed set of integer labels, with global upper counting limit
`√2` and lower counting limit zero. -/
theorem green_iff_one_set : Green33StrictReduction.OrdinaryLimit ↔
    ∃ S : Set ℕ, PrefixBases S ∧ limsup (coefficient S) atTop=Real.sqrt 2 ∧ liminf (coefficient S) atTop=0 := by
  constructor
  · intro h
    have feasible₂ : feasible (Real.sqrt 2) := fun ε ep => (h ε ep).mono
      (fun _ ⟨A,ha,sz⟩ => ⟨A,ha,by linarith [(abs_lt.mp sz).2]⟩)
    obtain ⟨S,up,base,L,ltop,low⟩ := fixed_prefixes feasible₂
    exact ⟨S,base,le_antisymm (upper_limsup up) (basis_limsup up base),zero_liminf up L ltop low⟩
  · rintro ⟨S,base,hi,_⟩
    exact upper_to_green (prefix_feasible (positive_limsup (by positivity) hi) base)


open Green33MaximalOrders

/-- Reciprocal square root of the limiting Graham–Sloane order constant. -/
noncomputable def optimalCoefficient : ℝ := 1/Real.sqrt orderConstant

private theorem budget_ratio : Tendsto (fun k : ℕ => (k:ℝ)/Real.sqrt (maxOrder false k)) atTop (𝓝 optimalCoefficient) := by
  have pos : 0<orderConstant := lt_of_lt_of_le (by norm_num : (0:ℝ)<7/18) orderConstant_bounds.1
  have roots := Real.continuous_sqrt.continuousAt.tendsto.comp (budget_limits false)
  have inv := roots.inv₀ (Real.sqrt_pos.mpr pos).ne'
  simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _),
    inv_div,optimalCoefficient,one_div] using inv

private theorem budget_witness (k : ℕ) (pos : 0<maxOrder false k) :
    ∃ q : ℕ+, q.val=maxOrder false k ∧ ∃ A : Finset (ZMod q), A.card≤k ∧ A+A=univ := by
  classical
  let p (n : ℕ) := n=0 ∨ ∃ q : ℕ+, q.val=n ∧ ∃ A : Finset (ZMod q), A.card≤k ∧ Covers false A
  have h : p (maxOrder false k) := by
    unfold maxOrder
    exact Nat.findGreatest_spec (Nat.zero_le (k^2)) (show p 0 from Or.inl rfl)
  rcases h with zero|⟨q,eq,A,sz,base⟩
  · omega
  · exact ⟨q,eq,A,sz,covers_false_iff.mp base⟩

/-- The upper coefficients achievable at arbitrarily large cyclic
orders form a closed ray with endpoint given by the maximal orders. -/
theorem feasible_iff_optimal_le (c : ℝ) : feasible c ↔ optimalCoefficient≤c := by
  constructor
  · intro h
    by_contra! below
    obtain ⟨v,cv,vo⟩ := exists_between below
    obtain ⟨k,hk⟩ := eventually_atTop.mp (budget_ratio.eventually_const_lt vo)
    obtain ⟨q,large,A,base,sz⟩ := frequently_atTop.mp (h (v-c) (sub_pos.mpr cv)) (Nat.succPNat (k^2))
    have bound : q.val≤A.card^2 := by
      simpa [base,ZMod.card,sq] using (card_add_le : (A+A).card≤A.card*A.card)
    have kq : k^2+1≤q.val := large
    have enough : k≤A.card := by
      by_contra! small
      have le := Nat.pow_le_pow_left small.le 2
      omega
    have hi := hk A.card enough
    have lo := div_le_div_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) A.card)
      (Real.sqrt_pos.mpr (show (0:ℝ)<q by exact_mod_cast q.pos))
      (Real.sqrt_le_sqrt (Nat.cast_le.mpr (le_maxOrder le_rfl (covers_false_iff.mpr base))))
    linarith
  · intro le ε ep
    obtain ⟨k,hk⟩ := eventually_atTop.mp (budget_ratio.eventually_lt_const (show optimalCoefficient<c+ε by linarith))
    apply frequently_atTop.mpr
    intro r
    let K := max k r.val
    have hU : (univ:Finset (ZMod r))+univ=univ := by
      apply eq_univ_of_forall
      intro x
      exact mem_add.mpr ⟨0,mem_univ _,x,mem_univ _,zero_add _⟩
    have kr : r.val≤maxOrder false K := le_maxOrder
      (show (univ:Finset (ZMod r)).card≤K by simp [K,ZMod.card]) (covers_false_iff.mpr hU)
    obtain ⟨q,eq,A,bnd,hA⟩ := budget_witness K (r.pos.trans_le kr)
    have sz := hk K (le_max_left ..)
    rw [← eq] at sz
    exact ⟨q,show r.val≤q.val by simpa [eq] using kr,A,hA,
      (div_le_div_of_nonneg_right (Nat.cast_le.mpr bnd) (Real.sqrt_nonneg _)).trans_lt sz⟩

/-- A single set attains the optimal upper coefficient of unrestricted
finite cyclic bases, with exact prefix bases and lower counting limit zero. -/
theorem optimal_fixed_set :
    ∃ S : Set ℕ, PrefixBases S ∧ UpperCoefficient S optimalCoefficient ∧
      limsup (coefficient S) atTop=optimalCoefficient ∧ liminf (coefficient S) atTop=0 := by
  obtain ⟨S,up,base,L,ltop,lo⟩ := fixed_prefixes ((feasible_iff_optimal_le _).mpr le_rfl)
  have actual : UpperCoefficient S (limsup (coefficient S) atTop) := fun _ ep =>
    eventually_lt_of_limsup_lt (lt_add_of_pos_right _ ep) (bounded up)
  exact ⟨S,base,up,le_antisymm (upper_limsup up) ((feasible_iff_optimal_le _).mp (prefix_feasible actual base)),
    zero_liminf up L ltop lo⟩

/-- The attained coefficient lies between the counting lower bound and
the coefficient of the eighteen-label strict cover at order 130. -/
theorem optimal_bounds : Real.sqrt 2≤optimalCoefficient ∧ optimalCoefficient≤18/Real.sqrt 130 := by
  obtain ⟨S,base,up,hi,_⟩ := optimal_fixed_set
  refine ⟨hi ▸ basis_limsup up base,(feasible_iff_optimal_le _).mp ?_⟩
  intro ε ep
  exact (Green33QuarticSeed.frequently_cyclic_basis ε ep).mono fun _ ⟨A,hA,sz⟩ =>
    ⟨A,hA,by linarith [(abs_lt.mp sz).2]⟩

#print axioms balanced_cut
#print axioms fixed_prefixes
#print axioms feasible_iff_fixed
#print axioms green_iff_one_set
#print axioms feasible_iff_optimal_le
#print axioms optimal_fixed_set
#print axioms optimal_bounds
end Green33FixedPrefixes
