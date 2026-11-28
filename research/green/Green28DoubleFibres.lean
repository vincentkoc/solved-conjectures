import Green28DeficientFibre
import Green28NormOutcomes

/-! Normalized atom weights in Green 28 when a sum has at most two representations. -/

namespace Green28DoubleFibres

open Polynomial Finset Green28 Green28UniformSums Green28AlgebraicWidth
  Green28UnpairedSites Green28DeficientFibre Green28PolynomialReduction
open scoped ENNReal Polynomial

/-- Occupied rows in the fibre of the integer sum `z`. Each row determines one column. -/
def fibreRows (P Q : PMF ℤ) (z : ℤ) : Set ℤ := {i | i ∈ P.support ∧ z-i ∈ Q.support}

/-- All sums involving column `d` have at most two representations. -/
def DoubleAt (P Q : PMF ℤ) (d : ℤ) : Prop :=
  ∀ i ∈ P.support, (fibreRows P Q (i+d)).ncard ≤ 2

private theorem endpoint_data {P : PMF ℤ} (ep : EndpointWeights P) {a : ℤ}
    (top : IsGreatest P.support a) {i : ℤ} (hi : i ∈ P.support) :
    0 < weight P a i ∧ weight P a i ≤ 1 ∧ IsIntegral ℤ (weight P a i) := by
  obtain ⟨e,em,le,ws⟩ := ep
  obtain rfl := top.unique (show IsGreatest P.support e from ⟨em,le⟩)
  exact ⟨div_pos (ENNReal.toReal_pos ((P.mem_support_iff _).mp hi) (P.apply_ne_top _))
    (ENNReal.toReal_pos ((P.mem_support_iff _).mp top.1) (P.apply_ne_top _)),(ws i).2.1,(ws i).2.2.1⟩

private theorem endpoint_one {P : PMF ℤ} {a : ℤ} (top : IsGreatest P.support a) : weight P a a = 1 :=
  div_self (ENNReal.toReal_pos ((P.mem_support_iff _).mp top.1) (P.apply_ne_top _)).ne'

/-- At a double fibre, a cell below normalized mass one has a distinct
complementary cell. Both coordinates change, and the weights add to one. -/
theorem complementary_cell {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {a b : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b)
    {i d : ℤ} (pi : i ∈ P.support) (qd : d ∈ Q.support)
    (small : weight P a i*weight Q b d < 1) (two : (fibreRows P Q (i+d)).ncard ≤ 2) :
    ∃ j ∈ P.support, ∃ e ∈ Q.support, j ≠ i ∧ e ≠ d ∧ i+d = j+e ∧
      weight P a i*weight Q b d+weight P a j*weight Q b e = 1 := by
  classical
  obtain ⟨pf,_⟩ := finite_of_uniform_sum flat
  let F := pf.toFinset.filter fun j => i+d-j ∈ Q.support
  have spec {j : ℤ} : j ∈ F ↔ j ∈ P.support ∧ i+d-j ∈ Q.support := by simp [F]
  have eqF : (F:Set ℤ) = fibreRows P Q (i+d) := by ext j; exact spec
  rw [←eqF,Set.ncard_coe_finset] at two
  have im : i ∈ F := spec.mpr ⟨pi,by simpa using qd⟩
  let v (j : ℤ) := weight P a j*weight Q b (i+d-j)
  have scale : (P a).toReal*(Q b).toReal ≠ 0 := mul_ne_zero
    (ENNReal.toReal_pos ((P.mem_support_iff _).mp pa.1) (P.apply_ne_top _)).ne'
    (ENNReal.toReal_pos ((Q.mem_support_iff _).mp qb.1) (Q.apply_ne_top _)).ne'
  have orig := sum_at_occupied flat pf pa qb (show ∃ j ∈ P.support, i+d-j ∈ Q.support from
    ⟨i,pi,by simpa using qd⟩)
  have full : (∑ j ∈ pf.toFinset,v j) = 1 := by
    simp only [v,weight,div_mul_div_comm,←sum_div,orig,div_self scale]
  have restrict : (∑ j ∈ F,v j) = ∑ j ∈ pf.toFinset,v j := by
    apply sum_subset (filter_subset _ _)
    intro j jm off
    have miss := fun (h : i+d-j ∈ Q.support) => off (spec.mpr ⟨pf.mem_toFinset.mp jm,h⟩)
    simp [v,weight,(Q.apply_eq_zero_iff _).mpr miss]
  have eq := restrict.trans full
  rw [←add_sum_erase _ _ im] at eq
  have own : v i = weight P a i*weight Q b d := by simp [v]
  rw [own] at eq
  have live : (F.erase i).Nonempty := by
    by_contra! empty
    rw [empty,sum_empty,add_zero] at eq
    exact small.ne eq
  obtain ⟨j,hj⟩ := live
  have sz := card_erase_add_one im
  have unique := card_le_one.mp (show (F.erase i).card ≤ 1 by omega)
  have sing : F.erase i = {j} := eq_singleton_iff_unique_mem.mpr ⟨hj,fun k hk => unique _ hk _ hj⟩
  rw [sing,sum_singleton] at eq
  obtain ⟨ji,jm⟩ := mem_erase.mp hj
  exact ⟨j,(spec.mp jm).1,i+d-j,(spec.mp jm).2,ji,by omega,by omega,eq⟩

/-- Every normalized row weight belongs to any real subring containing all normalized column weights. -/
theorem weight_mem_ring {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {a b : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b) (R : Subring ℝ)
    (inc : ∀ d ∈ Q.support, weight Q b d ∈ R) {i : ℤ} (hi : i ∈ P.support) : weight P a i ∈ R := by
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨f,l,s,m,fm,_,_⟩ := chart P pf
  obtain ⟨g,k,t,n,gm,_,_⟩ := chart Q qf
  have bin := ((m.mul n).uniform_iff (fm.mul gm)).mp flat
  have gmemb (j : ℕ) : g.coeff j ∈ R := by
    rw [←model_weight n gm qb j]
    by_cases site : k+(j:ℤ) ∈ Q.support
    · exact inc _ site
    · rw [weight,(Q.apply_eq_zero_iff _).mpr site,ENNReal.toReal_zero,zero_div]; exact R.zero_mem
  have lo : l ≤ i := by by_contra! lt; exact (P.mem_support_iff _).mp hi (m.below _ lt)
  have val := model_weight m fm pa (i-l).toNat
  rw [show l+↑(i-l).toNat = i by omega] at val
  rw [val]
  exact coeff_mem_of_monic_factor gm (by simpa only [mul_comm g f] using bin) R gmemb _

/-- For every deficient column whose fibres have size at most two, another
deficient column occurs across a double representation of normalized mass one.
The two contributing rows need not have different mass values. -/
theorem deficient_partner {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {a b d : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b)
    (qd : d ∈ Q.support) (dl : weight Q b d < 1) (two : DoubleAt P Q d) :
    ∃ i ∈ P.support, ∃ j ∈ P.support, ∃ e ∈ Q.support, e ≠ d ∧ weight Q b e < 1 ∧
      i+d = j+e ∧ weight P a i*weight Q b d+weight P a j*weight Q b e = 1 := by
  classical
  obtain ⟨pf,_⟩ := finite_of_uniform_sum flat
  obtain ⟨pe,qe⟩ := endpoint_weights flat
  let W := pf.toFinset.image (weight P a)
  have wm {t : ℝ} : t ∈ W ↔ ∃ i ∈ P.support, weight P a i = t := by simp [W]
  have one : (1:ℝ) ∈ W := wm.mpr ⟨a,pa.1,endpoint_one pa⟩
  let u := weight Q b d
  have up : 0 < u := (endpoint_data qe qb qd).1
  by_contra no
  have step : ∀ w ∈ W, 1-u*w ∈ W.erase 1 := by
    intro w hw
    obtain ⟨i,pi,rfl⟩ := wm.mp hw
    obtain ⟨p,le,_⟩ := endpoint_data pe pa pi
    have small := (mul_le_mul_of_nonneg_right le up.le).trans_lt (by simpa only [one_mul] using dl : 1*u < 1)
    obtain ⟨j,pj,e,ej,_,ed,sum,eq⟩ := complementary_cell flat pa qb pi qd small (two i pi)
    have high : weight Q b e = 1 := by
      by_contra ne
      exact no ⟨i,pi,j,pj,e,ej,ed,lt_of_le_of_ne (endpoint_data qe qb ej).2.1 ne,sum,eq⟩
    rw [high,mul_one] at eq
    apply mem_erase.mpr
    constructor
    · exact ne_of_lt (sub_lt_self _ (mul_pos up p))
    · exact wm.mpr ⟨j,pj,by dsimp [u]; linarith only [eq]⟩
  let next (v : ℝ) := 1-u*v
  have inj : Function.Injective next := by
    intro v t eq; apply mul_left_cancel₀ up.ne'; dsimp [next] at eq; linarith
  have sub : W.image next ⊆ W.erase 1 := by
    intro z hz; obtain ⟨w,hw,rfl⟩ := mem_image.mp hz; exact step _ hw
  have card := card_le_card sub
  rw [card_image_of_injective _ inj] at card
  have less := card_erase_lt_of_mem one
  omega

/-- The normalized coefficient order of one marginal. -/
noncomputable def weightOrder (Q : PMF ℤ) (b : ℤ) : Subalgebra ℤ ℝ :=
  Algebra.adjoin ℤ ((weight Q b) '' Q.support)

/-- The two deficient column weights generate the unit ideal in the order of
the normalized column weights. The coefficients witness the actual double fibre. -/
theorem unit_ideal_pair {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {a b d : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b)
    (qd : d ∈ Q.support) (dl : weight Q b d < 1) (two : DoubleAt P Q d) :
    ∃ e ∈ Q.support, e ≠ d ∧ weight Q b e < 1 ∧
      ∃ s ∈ weightOrder Q b, ∃ t ∈ weightOrder Q b, s*weight Q b d+t*weight Q b e = 1 := by
  obtain ⟨i,pi,j,pj,e,qe,ed,el,_,eq⟩ := deficient_partner flat pa qb qd dl two
  have inc (r : ℤ) (hr : r ∈ Q.support) : weight Q b r ∈ (weightOrder Q b).toSubring :=
    Algebra.subset_adjoin (Set.mem_image_of_mem _ hr)
  exact ⟨e,qe,ed,el,_,weight_mem_ring flat pa qb _ inc pi,_,weight_mem_ring flat pa qb _ inc pj,eq⟩

/-- If there is only one deficient atom, bounding the multiplicities
through that column alone suffices, with an arbitrary opposite law. -/
theorem uniform_of_one_deficit_double {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (one : OneDeficit Q) (two : ∀ d ∈ Q.support, (∃ j, Q d < Q j) → DoubleAt P Q d) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  by_contra bad
  obtain ⟨w⟩ := boundary_of_one_deficit flat one bad
  have bp := ENNReal.toReal_pos ((Q.mem_support_iff _).mp w.topQ.1) (Q.apply_ne_top _)
  have low : weight Q w.b w.d < 1 := (div_lt_one bp).mpr w.deficient
  have hit := two w.d w.lowQ ⟨w.b,(ENNReal.toReal_lt_toReal (Q.apply_ne_top _) (Q.apply_ne_top _)).mp w.deficient⟩
  obtain ⟨_,_,_,_,e,qe,ed,el,_,_⟩ := deficient_partner flat w.topP w.topQ w.lowQ low hit
  rw [weight,w.other _ qe ed,div_self bp.ne'] at el
  exact lt_irrefl _ el

/-- With two column weights, either the scaled row weight or its complement
occurs as a row weight. Otherwise the largest row in one reflection class
and the largest deficient column could only pair inside that same class. -/
theorem two_level_transition {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {a b : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b) {u : ℝ}
    (actual : ∃ d ∈ Q.support, weight Q b d = u) (up : 0 < u) (ul : u < 1)
    (levels : ∀ d ∈ Q.support, weight Q b d = 1 ∨ weight Q b d = u)
    (double : ∀ d ∈ Q.support, weight Q b d = u → DoubleAt P Q d)
    {i : ℤ} (ip : i ∈ P.support) : ∃ j ∈ P.support,
      weight P a j = u*weight P a i ∨ weight P a j = 1-u*weight P a i := by
  classical
  by_contra none
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  let w := weight P a i
  let T := pf.toFinset.filter fun j => weight P a j = w ∨ u*weight P a j = 1-u*w
  let L := qf.toFinset.filter fun d => weight Q b d = u
  have tr {j : ℤ} : j ∈ T ↔ j ∈ P.support ∧ (weight P a j = w ∨ u*weight P a j = 1-u*w) := by simp [T]
  have lc {d : ℤ} : d ∈ L ↔ d ∈ Q.support ∧ weight Q b d = u := by simp [L]
  have tn : T.Nonempty := ⟨i,tr.mpr ⟨ip,Or.inl rfl⟩⟩
  obtain ⟨f,qf',fv⟩ := actual
  have ln : L.Nonempty := ⟨f,lc.mpr ⟨qf',fv⟩⟩
  let h := T.max' tn
  let d := L.max' ln
  obtain ⟨ph,cl⟩ := tr.mp (T.max'_mem tn)
  obtain ⟨qd,du⟩ := lc.mp (L.max'_mem ln)
  have le := (endpoint_data (endpoint_weights flat).1 pa ph).2.1
  have lt : weight P a h*weight Q b d < 1 := by
    rw [du]; exact (mul_le_mul_of_nonneg_right le up.le).trans_lt (by simpa only [one_mul] using ul)
  obtain ⟨j,pj,e,qe,ne,_,sum,eq⟩ := complementary_cell flat pa qb ph qd lt (double _ qd du _ ph)
  rw [du] at eq
  rcases levels e qe with high|low
  · rw [high,mul_one] at eq
    apply none ⟨j,pj,?_⟩
    change weight P a j = u*w ∨ weight P a j = 1-u*w
    rcases cl with cl|cl
    · right; rw [cl] at eq; linarith only [eq]
    · left; linarith only [cl,eq]
  · rw [low] at eq
    have jm : j ∈ T := by
      apply tr.mpr ⟨pj,?_⟩
      rcases cl with h'|h'
      · right; rw [h'] at eq; linarith only [eq]
      · left; apply mul_left_cancel₀ up.ne'; linarith only [h',eq]
    have jp := T.le_max' j jm
    have ep := L.le_max' e (lc.mpr ⟨qe,low⟩)
    change j ≤ h at jp; change e ≤ d at ep
    omega

private theorem collision {W : Finset ℝ} {u : ℝ} (up : 0 < u) (ul : u < 1) (one : 1 ∈ W)
    (bounds : ∀ w ∈ W, 0 < w ∧ w ≤ 1) (step : ∀ w ∈ W, u*w ∈ W ∨ 1-u*w ∈ W) :
    ∃ s ∈ W, ∃ t ∈ W, s ≠ t ∧ u*(s+t) = 1 := by
  classical
  let f (w : ℝ) := if u*w ∈ W then u*w else 1-u*w
  have sub : W.image f ⊆ W.erase 1 := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    obtain ⟨wp,wl⟩ := bounds w hw
    have pos := mul_pos up wp
    have lt : u*w < 1 := (mul_le_mul_of_nonneg_left wl up.le).trans_lt (by simpa using ul)
    by_cases h : u*w ∈ W
    · simpa [f,h] using (mem_erase.mpr ⟨lt.ne,h⟩ : u*w ∈ W.erase 1)
    · have mem := (step w hw).resolve_left h
      simpa [f,h] using (mem_erase.mpr ⟨(sub_lt_self _ pos).ne,mem⟩ : 1-u*w ∈ W.erase 1)
  by_contra none
  have inj : Set.InjOn f (W : Set ℝ) := by
    intro s hs t ht eq
    by_contra ne
    by_cases a : u*s ∈ W <;> by_cases b : u*t ∈ W <;> simp [f,a,b] at eq
    · exact ne (by simpa [up.ne'] using eq)
    · exact none ⟨s,hs,t,ht,ne,by nlinarith only [eq]⟩
    · exact none ⟨s,hs,t,ht,ne,by nlinarith only [eq]⟩
    · exact ne (eq.resolve_right up.ne')
  have card := card_le_card sub
  rw [card_image_of_injOn inj] at card
  exact (card_erase_lt_of_mem one).not_ge card

private noncomputable def walk (W : Finset ℝ) (u : ℝ) (p : ℚ[X]) : ℕ → ℚ[X] := by
  classical
  exact Nat.rec p (fun _ h => if u*aeval u h ∈ W then X*h else 1-X*h)

/-- For a finite set of states closed under a choice between the maps
`x ↦ u*x` and `x ↦ 1-u*x`, every conjugate obeys the escape inequality
at every state reached by a rational polynomial in `u`. -/
theorem conjugate_escape {W : Finset ℝ} {u : ℝ} (step : ∀ w ∈ W, u*w ∈ W ∨ 1-u*w ∈ W)
    {p : ℚ[X]} (start : aeval u p ∈ W) {z : ℂ} (root : aeval z (minpoly ℚ u) = 0) :
    (‖z‖-1)*‖aeval z p‖ ≤ 1 := by
  classical
  let h := walk W u p
  have next (n : ℕ) : h (n+1) = if u*aeval u (h n) ∈ W then X*h n else 1-X*h n := rfl
  have closed (n : ℕ) : aeval u (h n) ∈ W := by
    induction n with
    | zero => exact start
    | succ n ih =>
      rw [next]
      split_ifs with yes
      · simpa using yes
      · simpa using (step _ ih).resolve_left yes
  let s (n : ℕ) := ‖aeval z (h n)‖
  have bound (n : ℕ) : ‖z‖*s n ≤ 1+s (n+1) := by
    dsimp only [s]
    rw [next]
    split_ifs
    · simp
    · simp only [map_sub,map_mul,aeval_X,map_one,←norm_mul]
      calc
        ‖z*aeval z (h n)‖ = ‖1-(1-z*aeval z (h n))‖ := by rw [sub_sub_cancel]
        _ ≤ _ := by simpa using norm_sub_le (1:ℂ) (1-z*aeval z (h n))
  by_contra! fail
  change 1 < (‖z‖-1)*s 0 at fail
  have zp : 0 ≤ ‖z‖-1 := by
    by_contra! neg
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg neg.le (norm_nonneg _))) (by linarith)
  have grow (n : ℕ) (le : s 0 ≤ s n) : s n < s (n+1) := by
    have t := mul_le_mul_of_nonneg_left le zp
    nlinarith only [t,fail,bound n]
  have low (n : ℕ) : s 0 ≤ s n := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (grow n ih).le
  have strict : StrictMono s := strictMono_nat_of_lt_succ fun n => grow n (low n)
  let f (i : Fin (W.card+1)) : W := ⟨_,closed i⟩
  obtain ⟨i,j,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have equal : aeval u (h i) = aeval u (h j) := congrArg Subtype.val eq
  have dv := minpoly.dvd ℚ u (p := h i-h j) (by simp [equal])
  obtain ⟨g,hg⟩ := dv
  have corr := congrArg (aeval z) hg
  simp only [map_sub,map_mul,root,zero_mul,sub_eq_zero] at corr
  exact ne (Fin.ext (strict.injective (congrArg norm corr)))

/-- Necessary conditions on a deficient weight and all its algebraic conjugates.
The row masses are unrestricted, as are multiplicities at sums without a low column. -/
theorem two_level_constraints {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {a b : ℤ} (pa : IsGreatest P.support a) (qb : IsGreatest Q.support b) {u : ℝ}
    (actual : ∃ d ∈ Q.support, weight Q b d = u) (ul : u < 1)
    (levels : ∀ d ∈ Q.support, weight Q b d = 1 ∨ weight Q b d = u)
    (double : ∀ d ∈ Q.support, weight Q b d = u → DoubleAt P Q d) :
    1/2 < u ∧ (minpoly ℤ u).coeff 0 ∣ 1 ∧
      ∀ z : ℂ, aeval z (minpoly ℚ u) = 0 → ‖z‖ ≤ 2 ∧ (‖z‖-1)*‖1-z‖ ≤ 1 := by
  classical
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum flat
  obtain ⟨pe,qe⟩ := endpoint_weights flat
  obtain ⟨d₀,qd₀,vd₀⟩ := actual
  obtain ⟨up,_,int⟩ := endpoint_data qe qb qd₀
  rw [vd₀] at up int
  let W := pf.toFinset.image (weight P a)
  have wm {w : ℝ} : w ∈ W ↔ ∃ i ∈ P.support, weight P a i = w := by simp [W]
  have one := wm.mpr ⟨a,pa.1,endpoint_one pa⟩
  have bounds (w : ℝ) (hw : w ∈ W) : 0 < w ∧ w ≤ 1 := by
    obtain ⟨i,hi,rfl⟩ := wm.mp hw
    have h := endpoint_data pe pa hi
    exact ⟨h.1,h.2.1⟩
  have step (w : ℝ) (hw : w ∈ W) : u*w ∈ W ∨ 1-u*w ∈ W := by
    obtain ⟨i,hi,rfl⟩ := wm.mp hw
    obtain ⟨j,hj,eq|eq⟩ := two_level_transition flat pa qb ⟨d₀,qd₀,vd₀⟩ up ul levels double hi
    · exact Or.inl (wm.mpr ⟨j,hj,eq⟩)
    · exact Or.inr (wm.mpr ⟨j,hj,eq⟩)
  obtain ⟨s,hs,t,ht,st,unit⟩ := collision up ul one bounds step
  have sl := (bounds s hs).2
  have tl := (bounds t ht).2
  have lt : s+t < 2 := by rcases lt_or_gt_of_ne st with lt|gt <;> linarith
  have half := mul_lt_mul_of_pos_left lt up
  let R := Algebra.adjoin ℤ ({u}:Set ℝ)
  have inc (j : ℤ) (hj : j ∈ Q.support) : weight Q b j ∈ R.toSubring := by
    rcases levels j hj with eq|eq
    · rw [eq]; exact R.one_mem
    · rw [eq]; exact Algebra.subset_adjoin (Set.mem_singleton u)
  have mem (w : ℝ) (hw : w ∈ W) : w ∈ R := by
    obtain ⟨i,hi,rfl⟩ := wm.mp hw
    exact weight_mem_ring flat pa qb R.toSubring inc hi
  have dv := Green28NormOutcomes.specialize_linear (q := 0) (N := -1) int
    (R.add_mem (mem s hs) (mem t ht)) (by push_cast; linarith only [unit])
  refine ⟨by linarith only [unit,half],by simpa [coeff_zero_eq_eval_zero] using dv,?_⟩
  let L := qf.toFinset.filter fun j => weight Q b j = u
  have lm {j : ℤ} : j ∈ L ↔ j ∈ Q.support ∧ weight Q b j = u := by simp [L]
  have live : L.Nonempty := ⟨d₀,lm.mpr ⟨qd₀,vd₀⟩⟩
  let d := L.max' live
  obtain ⟨qd,vd⟩ := lm.mp (L.max'_mem live)
  have top := endpoint_one pa
  have low : weight P a a*weight Q b d < 1 := by rwa [top,one_mul,vd]
  obtain ⟨j,pj,e,he,ne,_,eq,mass⟩ := complementary_cell flat pa qb pa.1 qd low (double d qd vd a pa.1)
  have le := pa.2 pj
  have high := (levels e he).resolve_right (fun low => by
    have ed : e ≤ d := L.le_max' e (lm.mpr ⟨he,low⟩)
    omega)
  rw [top,one_mul,vd,high,mul_one] at mass
  have comp := wm.mpr ⟨j,pj,show weight P a j = 1-u by linarith only [mass]⟩
  intro z root
  have h := conjugate_escape (p := 1) step (by simpa using one) root
  have k := conjugate_escape (p := 1-X) step (by simpa using comp) root
  simp only [map_one,norm_one,mul_one] at h
  exact ⟨by linarith only [h],by simpa using k⟩

private theorem degree_three {u : ℝ} (int : IsIntegral ℤ u) (half : 1/2 < u) (ul : u < 1)
    (unit : (minpoly ℤ u).coeff 0 ∣ 1)
    (escape : ∀ z : ℂ, aeval z (minpoly ℚ u) = 0 → (‖z‖-1)*‖1-z‖ ≤ 1) :
    3 ≤ (minpoly ℚ u).natDegree := by
  classical
  let m := minpoly ℤ u
  have frac := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ int
  rw [frac,natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ))]
  change 3 ≤ m.natDegree
  have two : 2 ≤ m.natDegree := (minpoly.two_le_natDegree_iff int).mpr (by
    rintro ⟨n,hn⟩
    change (n:ℝ) = u at hn
    have h₁ : (0:ℤ) < n := by exact_mod_cast (by linarith only [hn,half] : (0:ℝ) < n)
    have h₂ : n<(1:ℤ) := by exact_mod_cast (by linarith only [hn,ul] : (n:ℝ) < 1)
    omega)
  by_contra! small
  have deg : m.natDegree = 2 := by omega
  have mon : m.coeff 2 = 1 := deg ▸ (minpoly.monic int).coeff_natDegree
  let t := -m.coeff 1
  let c := m.coeff 0
  have poly : m = C c-C t*X+X^2 := by
    conv_lhs => rw [m.as_sum_range_C_mul_X_pow,deg]
    simp [sum_range_succ,c,t,mon]
  have zero := minpoly.aeval ℤ u
  change aeval u m = 0 at zero
  rw [poly] at zero
  simp only [map_add,map_sub,map_mul,map_pow,aeval_X,eq_intCast,map_intCast] at zero
  let v := (t:ℝ)-u
  have prod : u*v = (c:ℝ) := by dsimp [v]; nlinarith only [zero]
  have root : aeval (v:ℂ) (minpoly ℚ u) = 0 := by
    rw [frac]
    change aeval (v:ℂ) (m.map (algebraMap ℤ ℚ)) = 0
    rw [aeval_map_algebraMap,poly]
    simp only [map_add,map_sub,map_mul,map_pow,aeval_X,eq_intCast,map_intCast]
    exact_mod_cast (by dsimp [v]; nlinarith only [zero] : (c:ℝ)-(t:ℝ)*v+v^2 = 0)
  obtain ⟨g,hg⟩ := unit
  change 1 = c*g at hg
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hg.symm with pos|neg
  · rw [pos,Int.cast_one] at prod
    have vgt : 1 < v := by
      by_contra! le
      have := mul_le_mul_of_nonneg_left le (show 0 ≤ u by linarith); nlinarith only [this,prod,ul]
    have vlt : v < 2 := by
      by_contra! le
      have := mul_le_mul_of_nonneg_left le (show 0 ≤ u by linarith); nlinarith only [this,prod,half]
    have h₁ : (2:ℤ) < t := by
      have := mul_pos (sub_pos.mpr ul) (sub_pos.mpr vgt)
      exact_mod_cast (by dsimp [v] at *; nlinarith only [this,prod] : (2:ℝ) < t)
    have h₂ : t<(3:ℤ) := by exact_mod_cast (by dsimp [v] at vlt; linarith only [ul,vlt] : (t:ℝ) < 3)
    omega
  · rw [neg,Int.cast_neg,Int.cast_one] at prod
    have vlt : v < -1 := by
      by_contra! le
      have := mul_le_mul_of_nonneg_left le (show 0 ≤ u by linarith); nlinarith only [this,prod,ul]
    have bound := escape _ root
    rw [←Complex.ofReal_one,←Complex.ofReal_sub] at bound
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_neg (show v < 0 by linarith),
      abs_of_pos (show 0 < 1-v by linarith)] at bound
    have vlo : -3/2 < v := by nlinarith only [bound,sq_nonneg (v+3/2)]
    have h₁ : (-1:ℤ) < t := by exact_mod_cast (by dsimp [v] at vlo; linarith only [half,vlo] : (-1:ℝ) < t)
    have h₂ : t<(0:ℤ) := by exact_mod_cast (by dsimp [v] at vlt; linarith only [ul,vlt] : (t:ℝ) < 0)
    omega

/-- Any counterexample with two positive mass levels and the local representation
bound supplies an actual lighter atom with the integral and conjugate constraints. -/
theorem counterexample_weight {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q))
    (levels : Green28TwoMassLevels.AtMostTwo Q)
    (localBound : ∀ b, IsGreatest Q.support b → ∀ d ∈ Q.support, Q d < Q b → DoubleAt P Q d) :
    ∃ b, IsGreatest Q.support b ∧ ∃ d ∈ Q.support, Q d < Q b ∧
      let u := weight Q b d
      IsIntegral ℤ u ∧ 1/2 < u ∧ u < 1 ∧ (minpoly ℤ u).coeff 0 ∣ 1 ∧
        ∀ z : ℂ, aeval z (minpoly ℚ u) = 0 → ‖z‖ ≤ 2 ∧ (‖z‖-1)*‖1-z‖ ≤ 1 := by
  obtain ⟨al⟩ := (alignment_alternative flat).resolve_left bad
  let b := al.right.hi
  let d := al.rightLow.lo
  have qb : IsGreatest Q.support b := al.right.greatest
  have ld : d ∈ lowerSites Q al.right.lo := al.rightLow.least.1
  have top := (maximal_rectangle flat al.left al.right).2.1
  have ne : (Q d).toReal ≠ (Q b).toReal := fun eq => ld.2 (eq.trans top)
  have bp := ENNReal.toReal_pos ((Q.mem_support_iff _).mp qb.1) (Q.apply_ne_top _)
  let u := weight Q b d
  obtain ⟨_,le,int⟩ := endpoint_data (endpoint_weights flat).2 qb ld.1
  have ul : u < 1 := le.lt_of_ne (fun eq => ne ((div_eq_one_iff_eq bp.ne').mp eq))
  have low (e : ℤ) (eq : weight Q b e = u) : Q e < Q b :=
    (ENNReal.toReal_lt_toReal (Q.apply_ne_top _) (Q.apply_ne_top _)).mp
      ((div_lt_one bp).mp (show weight Q b e < 1 from eq ▸ ul))
  obtain ⟨A,B,palette⟩ := levels
  have dich (e : ℤ) (he : e ∈ Q.support) : weight Q b e = 1 ∨ weight Q b e = u := by
    have a := palette e he
    have h := palette b qb.1
    have l := palette d ld.1
    have eq : (Q e).toReal = (Q b).toReal ∨ (Q e).toReal = (Q d).toReal := by grind
    rcases eq with eq|eq
    · left; simp [weight,eq,bp.ne']
    · right; simp [u,weight,eq]
  obtain ⟨half,unit,escape⟩ := two_level_constraints flat al.left.greatest qb ⟨d,ld.1,rfl⟩ ul dich
    (fun e he eq => localBound b qb e he (low e eq))
  exact ⟨b,qb,d,ld.1,low d rfl,int,half,ul,unit,escape⟩

/-- Green 28 holds when one marginal has at most two positive masses, its low
mass divided by its top-site mass has degree at most two, and every sum through
a low site has at most two representations. -/
theorem uniform_of_two_level_quadratic {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (levels : Green28TwoMassLevels.AtMostTwo Q)
    (localBound : ∀ b, IsGreatest Q.support b → ∀ d ∈ Q.support, Q d < Q b →
      (minpoly ℚ (weight Q b d)).natDegree ≤ 2 ∧ DoubleAt P Q d) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  by_contra bad
  obtain ⟨b,qb,d,qd,low,int,half,ul,unit,escape⟩ := counterexample_weight flat bad levels
    (fun b qb d qd low => (localBound b qb d qd low).2)
  have large := degree_three int half ul unit (fun z hz => (escape z hz).2)
  have small := (localBound b qb d qd low).1
  omega

#print axioms complementary_cell
#print axioms deficient_partner
#print axioms weight_mem_ring
#print axioms unit_ideal_pair
#print axioms uniform_of_one_deficit_double
#print axioms two_level_transition
#print axioms conjugate_escape
#print axioms two_level_constraints
#print axioms counterexample_weight
#print axioms uniform_of_two_level_quadratic
end Green28DoubleFibres
