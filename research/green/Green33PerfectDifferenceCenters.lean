import Green33SidonLayerRepairs

/-! Exact correlations and exceptional reflection centers of perfect difference sets. -/

open Finset Green33TailEnergy Green33ReflectedLayers
open scoped Pointwise BigOperators

namespace Green33PerfectDifferenceCenters

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Each nonzero group element occurs once as an ordered difference. -/
def Perfect (D : Finset G) : Prop := ∀ t ≠ 0, diffReps D t = 1

private theorem difference_weights (D : Finset G) (hD : Perfect D) (w : G → ℝ) :
    ∑ a ∈ D, ∑ b ∈ D, w (a-b) = ((D.card:ℝ)-1)*w 0 + ∑ t, w t := by
  classical
  have zero : diffReps D 0 = D.card := by
    change ((D ×ˢ D).filter fun p => p.1-p.2=0).card = D.card
    rw [show ((D ×ˢ D).filter fun p => p.1-p.2=0) = D.diag by
      ext p; simp [Finset.mem_diag]; grind]
    simp
  have fiber : ∑ t, (diffReps D t : ℝ)*w t = ∑ a ∈ D, ∑ b ∈ D, w (a-b) := by
    simp only [diffReps,card_eq_sum_ones,Nat.cast_sum,sum_mul,sum_filter]
    rw [sum_comm]
    simp [sum_product]
  have point (t : G) : (diffReps D t : ℝ)*w t =
      (if t=0 then ((D.card:ℝ)-1)*w 0 else 0)+w t := by
    by_cases ht : t=0
    · subst t;rw [if_pos rfl,zero];ring
    · rw [if_neg ht,hD t ht];simp
  rw [← fiber]
  simp only [point,sum_add_distrib,sum_ite_eq',mem_univ,if_true]

/-- The parameter identity includes the group of order one. -/
theorem parameters (D : Finset G) (hD : Perfect D) :
    (D.card:ℝ)^2 = Fintype.card G + D.card - 1 := by
  have h := difference_weights D hD (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one,card_univ] at h
  nlinarith

#print axioms parameters

/-- The difference-set identity applied to two test functions. -/
theorem translate_inner (D : Finset G) (hD : Perfect D) (f g : G → ℝ) :
    ∑ x, (∑ a ∈ D, f (x-a))*(∑ b ∈ D, g (x-b)) =
      ((D.card:ℝ)-1)*(∑ x, f x*g x)+(∑ x, f x)*(∑ x, g x) := by
  let C (t : G) := ∑ x, f x*g (x+t)
  have move (h : G → ℝ) (t : G) : ∑ x, h (x+t) = ∑ x, h x :=
    Equiv.sum_comp (Equiv.addRight t) h
  have shifted (a b : G) : ∑ x, f (x-a)*g (x-b) = C (a-b) := by
    calc
      _ = ∑ x, (fun y => f y*g (y+(a-b))) (x-a) := by
        apply sum_congr rfl
        intro x _
        dsimp
        rw [show x-a+(a-b)=x-b by abel]
      _ = _ := by
        simpa only [C,sub_eq_add_neg] using
          (move (fun y => f y*g (y+(a-b))) (-a))
  have total : ∑ t, C t = (∑ x, f x)*(∑ x, g x) := by
    unfold C
    rw [sum_comm,sum_mul]
    apply sum_congr rfl
    intro x _
    rw [← mul_sum]
    congr 1
    exact Equiv.sum_comp (Equiv.addLeft x) g
  have expand : ∑ x, (∑ a ∈ D, f (x-a))*(∑ b ∈ D, g (x-b)) =
      ∑ a ∈ D, ∑ b ∈ D, C (a-b) := by
    have product (x : G) : (∑ a ∈ D, f (x-a))*(∑ b ∈ D, g (x-b)) =
        ∑ a ∈ D, ∑ b ∈ D, f (x-a)*g (x-b) := by
      rw [sum_mul]
      exact sum_congr rfl fun a _ => Finset.mul_sum ..
    simp only [product]
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    rw [sum_comm]
    exact sum_congr rfl fun b _ => shifted a b
  rw [expand,difference_weights D hD,total]
  simp [C]

#print axioms translate_inner

/-- The centered number of ordered paths of length r to x. -/
noncomputable def residual (D : Finset G) (r : ℕ) (x : G) : ℝ :=
  paths D r x-(D.card:ℝ)^r/Fintype.card G

private theorem residual_step (D : Finset G) (r : ℕ) (x : G) :
    residual D (r+1) x = ∑ a ∈ D, residual D r (x-a) := by
  simp only [residual,paths,walk,sum_sub_distrib,sum_const,nsmul_eq_mul,pow_succ]
  ring

private theorem residual_sum (D : Finset G) (r : ℕ) : ∑ x, residual D r x = 0 := by
  have move (f : G → ℝ) (a : G) : ∑ x, f (x-a) = ∑ x, f x := by
    simpa only [sub_eq_add_neg] using
      (show ∑ x, f (x+(-a)) = ∑ x, f x from Equiv.sum_comp (Equiv.addRight (-a)) f)
  induction r with
  | zero =>
    have m : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [residual,paths,sum_sub_distrib,m]
  | succ r ih =>
    simp only [residual_step]
    rw [sum_comm]
    simp only [move,ih,sum_const_zero]

/-- Autocorrelation at every displacement, including zero, for every path length. -/
theorem path_covariance (D : Finset G) (hD : Perfect D) (r : ℕ) (t : G) :
    ∑ x, residual D r x * residual D r (x+t) =
      ((D.card:ℝ)-1)^r*((if t=0 then 1 else 0)-1/(Fintype.card G:ℝ)) := by
  have move (f : G → ℝ) (a : G) : ∑ x, f (x+a) = ∑ x, f x :=
    Equiv.sum_comp (Equiv.addRight a) f
  induction r with
  | zero =>
    let d (x : G) : ℝ := if x=0 then 1 else 0
    let m : ℝ := Fintype.card G
    have mp : m ≠ 0 := by dsimp [m];exact_mod_cast Fintype.card_ne_zero
    have one : ∑ x, d x=1 := by simp [d]
    have pair : ∑ x, d x * d (x+t) = d t := by
      have pt (x : G) : d x*d (x+t) = if x=0 then d t else 0 := by
        by_cases h : x=0 <;> simp [d,h]
      simp only [pt,sum_ite_eq',mem_univ,if_true]
    have point (x : G) : residual D 0 x * residual D 0 (x+t) =
        d x*d (x+t)-d x/m-d (x+t)/m+1/m^2 := by
      simp only [residual,paths,d,m,pow_zero]
      ring
    simp only [point,sum_add_distrib,sum_sub_distrib,← sum_div,pair,move,one,
      sum_const,nsmul_eq_mul,card_univ,pow_zero,one_mul]
    change d t-1/m-1/m+m*1/m^2=d t-1/m
    field_simp
    ring
  | succ r ih =>
    let f := residual D r
    have form (x : G) : residual D (r+1) (x+t) = ∑ a ∈ D, f ((x-a)+t) := by
      rw [residual_step]
      exact sum_congr rfl fun a _ => congrArg f (by abel)
    have prod := translate_inner D hD f (fun y => f (y+t))
    have zero : ∑ x, f x=0 := residual_sum D r
    rw [zero,zero_mul,add_zero] at prod
    calc
      _ = ∑ x, (∑ a ∈ D, f (x-a))*(∑ a ∈ D, f ((x-a)+t)) :=
        sum_congr rfl fun x _ => congrArg₂ (·*·) (residual_step D r x) (form x)
      _ = _ := by rw [prod]; dsimp [f];rw [ih,pow_succ];ring

#print axioms path_covariance

omit [Fintype G] in
/-- Distinct summands in a perfect difference set are determined as an unordered pair. -/
theorem Perfect.sidon {D : Finset G} (hD : Perfect D) : IsSidon (D : Set G) := by
  intro a ha b hb c hc d hd h
  by_cases eq : a=b
  · subst b;exact Or.inl ⟨rfl,add_left_cancel h⟩
  · let P := (D×ˢD).filter fun p => p.1-p.2=a-b
    have one : P.card≤1 := (hD _ (sub_ne_zero.mpr eq)).le
    have ab : (a,b)∈P := mem_filter.mpr ⟨mk_mem_product ha hb,rfl⟩
    have dc : (d,c)∈P := mem_filter.mpr ⟨mk_mem_product hd hc,
      (sub_eq_sub_iff_add_eq_add.mpr (show a+c=d+b by simpa only [add_comm d b] using h)).symm⟩
    have same := card_le_one.mp one (a,b) ab (d,c) dc
    exact Or.inr ⟨congrArg Prod.fst same,(congrArg Prod.snd same).symm⟩

/-- A family of centers with a common shortfall spends its squared shortfall
against one exact four-step variance. -/
theorem shortfall_budget {D : Finset G} (hD : Perfect D) (T : Finset G)
    {b : ℝ} (hb : 0 ≤ b)
    (poor : ∀ c ∈ T, 4*(overlap D c:ℝ)+b ≤ (D.card:ℝ)^4/Fintype.card G) :
    (T.card:ℝ)*b^2 ≤ ((D.card:ℝ)-1)^4*(1-1/(Fintype.card G:ℝ)) := by
  have variance := path_covariance D hD 4 0
  simp only [add_zero,if_pos] at variance
  have each (c : G) (hc : c∈T) : b^2 ≤ residual D 4 c ^2 := by
    have cover := (two_walk_overlap hD.sidon c).1
    change paths D 4 c≤4*(overlap D c:ℝ) at cover
    have p := poor c hc
    have dist : b ≤ -residual D 4 c := by unfold residual;linarith
    simpa only [neg_sq] using (pow_le_pow_left₀ hb dist 2)
  calc
    _ = ∑ _c ∈ T, b^2 := by simp
    _ ≤ ∑ c ∈ T, residual D 4 c^2 := sum_le_sum each
    _ ≤ ∑ c, residual D 4 c^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ T) (fun c _ _ => sq_nonneg _)
    _ = _ := by simpa only [sq] using variance

#print axioms Perfect.sidon
#print axioms shortfall_budget

/-- Every set of centers with the same r-step count shares one variance budget. -/
theorem equal_count_budget (D : Finset G) (hD : Perfect D) (r : ℕ) (c : G)
    (T : Finset G) (same : ∀ t ∈ T, paths D r t=paths D r c) :
    (T.card:ℝ)*(residual D r c)^2 ≤
      ((D.card:ℝ)-1)^r*(1-1/(Fintype.card G:ℝ)) := by
  have variance := path_covariance D hD r 0
  simp only [add_zero,if_pos] at variance
  calc
    _ = ∑ _t ∈ T, residual D r c^2 := by simp
    _ = ∑ t ∈ T, residual D r t^2 := by
      apply sum_congr rfl
      intro t ht
      rw [residual,residual,same t ht]
    _ ≤ ∑ t, residual D r t^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ T) fun t _ _ => sq_nonneg _
    _ = _ := by simpa only [sq] using variance

#print axioms equal_count_budget

/-- The size coefficient of a perfect seed differs from one by at most
the reciprocal square root of the group order. -/
theorem size_band {D : Finset G} (hD : Perfect D) :
    Real.sqrt (Fintype.card G)-1 ≤ D.card ∧
    (D.card:ℝ) ≤ Real.sqrt (Fintype.card G)+1 := by
  let k : ℝ := D.card
  let v : ℝ := Fintype.card G
  have eq : k^2=v+k-1 := parameters D hD
  have kp : 0≤k := Nat.cast_nonneg _
  have lower : Real.sqrt v≤k+1 := by
    calc
      _ ≤ Real.sqrt ((k+1)^2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = _ := Real.sqrt_sq (by positivity)
  have upper : k-1≤Real.sqrt v := by
    calc
      _ ≤ |k-1| := le_abs_self _
      _ = Real.sqrt ((k-1)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  change Real.sqrt v-1 ≤ k ∧ k ≤ Real.sqrt v+1
  constructor <;> linarith

open Filter
open scoped Topology

section Limits

variable {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

theorem perfect_size_limit (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop) :
    Tendsto (fun i => ((D i).card:ℝ)/Real.sqrt (Fintype.card (V i))) atTop (𝓝 1) := by
  let s i := Real.sqrt (Fintype.card (V i))
  have tiny : Tendsto (fun i => 1/s i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
  have low := (tendsto_const_nhds (x:=(1:ℝ))).sub tiny
  have high := (tendsto_const_nhds (x:=(1:ℝ))).add tiny
  rw [sub_zero] at low
  rw [add_zero] at high
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
  · filter_upwards with i
    have pos : 0<s i := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    have h := div_le_div_of_nonneg_right (size_band (hD i)).1 pos.le
    change (s i-1)/s i ≤ ((D i).card:ℝ)/s i at h
    simpa only [sub_div,div_self pos.ne'] using h
  · filter_upwards with i
    have pos : 0<s i := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
    have h := div_le_div_of_nonneg_right (size_band (hD i)).2 pos.le
    change ((D i).card:ℝ)/s i ≤ (s i+1)/s i at h
    simpa only [add_div,div_self pos.ne'] using h

end Limits

#print axioms size_band
#print axioms perfect_size_limit

private noncomputable def mean4 (D : Finset G) : ℝ :=
  (D.card:ℝ)^4/(Fintype.card G:ℝ)^2

private noncomputable def budget4 (D : Finset G) : ℝ :=
  ((D.card:ℝ)-1)^4/(Fintype.card G:ℝ)^2

private noncomputable def diag4 (D : Finset G) : ℝ := 4*D.card/(Fintype.card G:ℝ)

private noncomputable def dev4 (D : Finset G) (c : G) : ℝ := residual D 4 c/Fintype.card G

private theorem overlap_interval {D : Finset G} (hD : Perfect D) (c : G) :
    mean4 D+dev4 D c ≤ 4*(overlap D c:ℝ)/Fintype.card G ∧
    4*(overlap D c:ℝ)/Fintype.card G ≤ mean4 D+dev4 D c+diag4 D := by
  have mp : 0 < (Fintype.card G:ℝ) := by exact_mod_cast Fintype.card_pos
  have h := two_walk_overlap hD.sidon c
  change paths D 4 c ≤ 4*(overlap D c:ℝ) ∧ 4*(overlap D c:ℝ) ≤ paths D 4 c+4*D.card at h
  have sum : mean4 D+dev4 D c = paths D 4 c/Fintype.card G := by
    unfold mean4 dev4 residual
    ring
  rw [sum]
  exact ⟨div_le_div_of_nonneg_right h.1 mp.le,
    (div_le_div_of_nonneg_right h.2 mp.le).trans_eq (add_div ..)⟩

private theorem budget_subset {D : Finset G} (hD : Perfect D) (T : Finset G) :
    ∑ c ∈ T, dev4 D c^2 ≤ budget4 D := by
  have m : 0 < (Fintype.card G:ℝ) := by exact_mod_cast Fintype.card_pos
  have h := path_covariance D hD 4 0
  simp only [add_zero,if_pos] at h
  have sub : ∑ c ∈ T, residual D 4 c^2 ≤ ∑ c, residual D 4 c^2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ T) fun c _ _ => sq_nonneg _
  simp only [← sq] at h
  calc
    _ = (∑ c ∈ T, residual D 4 c^2)/(Fintype.card G:ℝ)^2 := by
      simp only [dev4,div_pow,sum_div]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [h] at sub
      have hn : 0 ≤ ((D.card:ℝ)-1)^4 := by positivity
      exact sub.trans (by nlinarith [mul_nonneg hn (by positivity : 0≤1/(Fintype.card G:ℝ))])

section Normalized

variable {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

private theorem normal_limits (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop) :
    Tendsto (fun i => mean4 (D i)) atTop (𝓝 1) ∧
    Tendsto (fun i => budget4 (D i)) atTop (𝓝 1) ∧
    Tendsto (fun i => diag4 (D i)) atTop (𝓝 0) := by
  let v i : ℝ := Fintype.card (V i)
  let s i := Real.sqrt (v i)
  have vp i : 0<v i := by dsimp [v];exact_mod_cast Fintype.card_pos
  have sq i : s i^2=v i := Real.sq_sqrt (vp i).le
  have four i : s i^4=v i^2 := by calc
    _ = (s i^2)^2 := by ring
    _ = _ := by rw [sq]
  have sz := perfect_size_limit D hD big
  have tiny : Tendsto (fun i => 1/s i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
  have k4 := sz.pow 4
  have b4 := (sz.sub tiny).pow 4
  have dia := (sz.mul tiny).const_mul 4
  norm_num at k4 b4 dia
  simp only [← one_div] at b4 dia
  refine ⟨k4.congr (fun i => ?_),b4.congr (fun i => ?_),dia.congr (fun i => ?_)⟩
  · change (((D i).card:ℝ)/s i)^4 = (D i).card^4/v i^2
    rw [div_pow,four]
  · change (((D i).card:ℝ)/s i-1/s i)^4 = ((D i).card-1)^4/v i^2
    rw [← sub_div,div_pow,four]
  · change 4*(((D i).card:ℝ)/s i*(1/s i))=4*(D i).card/v i
    rw [← sq]
    ring

end Normalized

section Centers

variable {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop) (c : ∀ i, V i)
    (poor : Tendsto (fun i => (overlap (D i) (c i):ℝ)/Fintype.card (V i)) atTop (𝓝 0))

include hD big poor

private theorem center_deficit :
    Tendsto (fun i => dev4 (D i) (c i)) atTop (𝓝 (-1)) := by
  obtain ⟨mean,_,err⟩ := normal_limits D hD big
  have hi := (poor.const_mul 4).sub mean
  have lo := hi.sub err
  norm_num at hi lo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
  · filter_upwards with i
    have h := (overlap_interval (hD i) (c i)).2
    linarith only [h,show 4*((overlap (D i) (c i):ℝ)/Fintype.card (V i)) =
      4*(overlap (D i) (c i):ℝ)/Fintype.card (V i) by ring]
  · filter_upwards with i
    have h := (overlap_interval (hD i) (c i)).1
    linarith only [h,show 4*((overlap (D i) (c i):ℝ)/Fintype.card (V i)) =
      4*(overlap (D i) (c i):ℝ)/Fintype.card (V i) by ring]

private theorem other_deviations {ε : ℝ} (pos : 0<ε) :
    ∀ᶠ i in atTop, ∀ t ≠ c i, |dev4 (D i) t| < ε := by
  have l := center_deficit D hD big c poor
  have v := (normal_limits D hD big).2.1.sub (l.pow 2)
  norm_num at v
  have test := v.eventually_lt_const (sq_pos_of_pos pos)
  filter_upwards [test] with i hi
  intro t ne
  have cap := budget_subset (hD i) {t,c i}
  simp only [sum_pair ne] at cap
  have h : dev4 (D i) t^2 < ε^2 := by linarith
  exact (sq_lt_sq.mp h).trans_eq (abs_of_pos pos)

/-- If one reflection overlap is sublinear, every other center has overlap
asymptotic to one quarter of the group, uniformly in the other center. -/
theorem other_centers {ε : ℝ} (pos : 0<ε) :
    ∀ᶠ i in atTop, ∀ t ≠ c i,
    |(overlap (D i) t:ℝ)/Fintype.card (V i)-1/4| < ε := by
  obtain ⟨mean,_,diag⟩ := normal_limits D hD big
  have lo := mean.eventually_const_lt (show 1-ε<1 by linarith)
  have hi := mean.eventually_lt_const (show 1<1+ε by linarith)
  filter_upwards [lo,hi,diag.eventually_lt_const pos,other_deviations D hD big c poor pos] with i l u e z
  intro t ne
  obtain ⟨p,q⟩ := overlap_interval (hD i) t
  obtain ⟨neg,lt⟩ := abs_lt.mp (z t ne)
  rw [abs_lt]
  have scale : 4*((overlap (D i) t:ℝ)/Fintype.card (V i)) =
      4*(overlap (D i) t:ℝ)/Fintype.card (V i) := by ring
  constructor <;> linarith

/-- A center with sublinear overlap is eventually fixed by every affine
symmetry of the seed, under its induced action on four-term sums. -/
theorem center_fixed :
    ∀ᶠ i in atTop, ∀ (e : V i ≃+ V i) (s : V i),
      (D i).image (fun x => e x+s)=D i → e (c i)+4 • s=c i := by
  have cut := (center_deficit D hD big c poor).eventually_lt_const
    (show (-1:ℝ)< -(1/2) by norm_num)
  filter_upwards [cut,other_deviations D hD big c poor (show (0:ℝ)<1/2 by norm_num)] with i lo hi
  intro e s eq
  by_contra moved
  have h := paths_affine (D i) e s 4 (c i)
  rw [eq] at h
  have same : dev4 (D i) (e (c i)+4 • s)=dev4 (D i) (c i) := by
    simp only [dev4,residual,h]
  have bound := (abs_lt.mp (hi _ moved)).1
  rw [same] at bound
  linarith

end Centers

#print axioms other_centers
#print axioms center_fixed

section Quantitative

variable {V : ℕ → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

/-- Below the stated overlap density there is eventually at most one center,
uniformly over all choices of centers in the successive groups. -/
private theorem at_most_one_path (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop)
    {a : ℝ} (small : a < (1-1/Real.sqrt 2)/4) :
    ∀ᶠ i in atTop, (univ.filter (fun c => paths (D i) 4 c/Fintype.card (V i) ≤ 4*a)).card ≤ 1 := by
  obtain ⟨mean,budget,_⟩ := normal_limits D hD big
  have rt : 0 < Real.sqrt 2 := by positivity
  have ir : 0 < 1/Real.sqrt 2 := by positivity
  have sq : 2*(1/Real.sqrt 2)^2 = 1 := by rw [div_pow,Real.sq_sqrt (by norm_num)];norm_num
  have gap : 1/Real.sqrt 2 < 1-4*a := by linarith
  have twice : 1 < 2*(1-4*a)^2 := by
    nlinarith [pow_lt_pow_left₀ gap ir.le (by decide : 2 ≠ 0)]
  have low := mean.eventually_const_lt (show 4*a < 1 by linarith)
  have lim := (((mean.sub_const (4*a)).pow 2).const_mul 2)
  filter_upwards [low,budget.eventually_lt lim twice] with i plenty cap
  apply card_le_one.mpr
  intro c hc t ht
  by_contra ne
  have term (x : V i) (hx : paths (D i) 4 x/Fintype.card (V i) ≤ 4*a) :
      (mean4 (D i)-4*a)^2 ≤ dev4 (D i) x^2 := by
    have h : mean4 (D i)+dev4 (D i) x=paths (D i) 4 x/Fintype.card (V i) := by
      unfold mean4 dev4 residual
      ring
    have le : mean4 (D i)-4*a ≤ -dev4 (D i) x := by linarith
    simpa only [neg_sq] using pow_le_pow_left₀ (sub_nonneg.mpr plenty.le) le 2
  have bounds := budget_subset (hD i) {c,t}
  simp only [sum_pair ne] at bounds
  have one := term c (mem_filter.mp hc).2
  have two := term t (mem_filter.mp ht).2
  linarith

private theorem paths_low {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {D : Finset G} (hD : Perfect D) (c : G) {a : ℝ} (low : (overlap D c:ℝ)/Fintype.card G≤a) :
    paths D 4 c/Fintype.card G ≤ 4*a := by
  have h := (two_walk_overlap hD.sidon c).1
  change paths D 4 c ≤ 4*(overlap D c:ℝ) at h
  calc
    _ ≤ 4*(overlap D c:ℝ)/Fintype.card G := div_le_div_of_nonneg_right h (by positivity)
    _ = 4*((overlap D c:ℝ)/Fintype.card G) := by ring
    _ ≤ _ := by linarith

/-- At most one reflected intersection can fall below this density. -/
theorem at_most_one (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop)
    {a : ℝ} (small : a < (1-1/Real.sqrt 2)/4) :
    ∀ᶠ i in atTop, (univ.filter (fun c => (overlap (D i) c:ℝ)/Fintype.card (V i) ≤ a)).card ≤ 1 := by
  filter_upwards [at_most_one_path D hD big small] with i bound
  apply (card_le_card _).trans bound
  exact fun c hc => mem_filter.mpr ⟨mem_univ _,paths_low (hD i) c (mem_filter.mp hc).2⟩

/-- Every center moved by any affine seed symmetry has an explicit overlap floor. -/
theorem moved_center_floor (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop)
    {a : ℝ} (small : a < (1-1/Real.sqrt 2)/4) :
    ∀ᶠ i in atTop, ∀ (c : V i) (e : V i ≃+ V i) (s : V i),
      (D i).image (fun x => e x+s)=D i → e c+4 • s≠c →
      a<(overlap (D i) c:ℝ)/Fintype.card (V i) := by
  filter_upwards [at_most_one_path D hD big small] with i bound
  intro c e s symm move
  by_contra! low
  have poor := paths_low (hD i) c low
  have other := paths_affine (D i) e s 4 c
  rw [symm] at other
  exact move (card_le_one.mp bound _ (mem_filter.mpr ⟨mem_univ _,other ▸ poor⟩) _
    (mem_filter.mpr ⟨mem_univ _,poor⟩))

/-- Centers in growing sets of equal four-term multiplicity have asymptotic
overlap one quarter. An affine multiplier orbit supplies such a set. -/
theorem growing_level (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop) (c : ∀ i, V i)
    (T : ∀ i, Finset (V i)) (large : Tendsto (fun i => (T i).card) atTop atTop)
    (same : ∀ i x, x∈T i → paths (D i) 4 x=paths (D i) 4 (c i)) :
    Tendsto (fun i => (overlap (D i) (c i):ℝ)/Fintype.card (V i)) atTop (𝓝 (1/4)) := by
  obtain ⟨mean,budget,diag⟩ := normal_limits D hD big
  have cap (i : ℕ) : ((T i).card:ℝ)*dev4 (D i) (c i)^2 ≤ budget4 (D i) := by
    calc
      _ = ∑ _x ∈ T i, dev4 (D i) (c i)^2 := by simp
      _ = ∑ x ∈ T i, dev4 (D i) x^2 := by
        apply sum_congr rfl
        intro x hx
        simp only [dev4,residual,same i x hx]
      _ ≤ _ := budget_subset (hD i) _
  have ct : Tendsto (fun i => ((T i).card:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp large
  have van := budget.div_atTop ct
  have sq : Tendsto (fun i => dev4 (D i) (c i)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _ van
    filter_upwards [ct.eventually_gt_atTop 0] with i hi
    apply (le_div_iff₀ hi).mpr
    simpa only [mul_comm] using cap i
  have root := sq.sqrt
  simp only [Real.sqrt_sq_eq_abs,Real.sqrt_zero] at root
  have dev : Tendsto (fun i => dev4 (D i) (c i)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using root)
  have lo := (mean.add dev).div_const 4
  have hi := ((mean.add dev).add diag).div_const 4
  norm_num at lo hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi
  · filter_upwards with i
    have h := (overlap_interval (hD i) (c i)).1
    linarith only [h,show 4*((overlap (D i) (c i):ℝ)/Fintype.card (V i)) =
      4*(overlap (D i) (c i):ℝ)/Fintype.card (V i) by ring]
  · filter_upwards with i
    have h := (overlap_interval (hD i) (c i)).2
    linarith only [h,show 4*((overlap (D i) (c i):ℝ)/Fintype.card (V i)) =
      4*(overlap (D i) (c i):ℝ)/Fintype.card (V i) by ring]

end Quantitative

#print axioms at_most_one
#print axioms moved_center_floor
#print axioms growing_level

section Layers

variable {V W : ℕ → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]

/-- For a perfect seed in an index-two embedding, asymptotically full
coverage of its reflected layers is equivalent to sublinear overlap. -/
theorem layers_iff (D : ∀ i, Finset (V i)) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => Fintype.card (V i)) atTop atTop)
    (f : ∀ i, V i →+ W i) (inj : ∀ i, Function.Injective (f i))
    (j : ∀ i, W i) (odd : ∀ i x, f i x ≠ j i)
    (double : ∀ i, Fintype.card (W i)=2*Fintype.card (V i))
    (c : ∀ i, V i) (lifted : ∀ i, f i (c i)=j i+j i) :
    Tendsto (fun i => let B := layers (D i) (f i) (j i)
      ((B+B).card:ℝ)/Fintype.card (W i)) atTop (𝓝 1) ↔
    Tendsto (fun i => (overlap (D i) (c i):ℝ)/Fintype.card (V i)) atTop (𝓝 0) := by
  let v (i : ℕ) : ℝ := Fintype.card (V i)
  let a i := 2*(((D i).card:ℝ)/Real.sqrt (v i))^2+1/v i
  let o i := (overlap (D i) (c i):ℝ)/v i
  let B i := layers (D i) (f i) (j i)
  let cov i := ((B i+B i).card:ℝ)/Fintype.card (W i)
  have vp i : 0<v i := by dsimp [v];exact_mod_cast Fintype.card_pos
  have tiny : Tendsto (fun i => 1/v i) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp big)
  have la : Tendsto a atTop (𝓝 2) := by
    have h := (((perfect_size_limit D hD big).pow 2).const_mul 2).add tiny
    simpa only [one_pow,mul_one,add_zero] using h
  have bal : ∀ᶠ i in atTop, 2*cov i+o i=a i := by
    filter_upwards [big.eventually_gt_atTop 1] with i hi
    have nonempty : (D i).Nonempty := by
      by_contra e
      have zero := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp e)
      have h := parameters (D i) (hD i)
      rw [zero] at h
      have gt : 1 < (Fintype.card (V i):ℝ) := by exact_mod_cast hi
      norm_num at h
      linarith
    have h := layer_sumset_size (hD i).sidon nonempty (f i) (inj i) (odd i) (lifted i)
    change ((B i+B i).card:ℝ) = 2*((D i).card:ℝ)^2+1-overlap (D i) (c i) at h
    dsimp only [a,cov,o]
    rw [h,double,Nat.cast_mul,Nat.cast_ofNat,div_pow,Real.sq_sqrt (vp i).le]
    change 2*((2*((D i).card:ℝ)^2+1-overlap (D i) (c i))/(2*v i))+
      (overlap (D i) (c i):ℝ)/v i=2*(((D i).card:ℝ)^2/v i)+1/v i
    field_simp [(vp i).ne']
    ring
  change Tendsto cov atTop (𝓝 1) ↔ Tendsto o atTop (𝓝 0)
  constructor
  · intro hc
    have lim := la.sub (hc.const_mul 2)
    norm_num at lim
    exact lim.congr' (bal.mono fun i h => by linarith)
  · intro ho
    have lim := (la.sub ho).div_const 2
    norm_num at lim
    exact lim.congr' (bal.mono fun i h => by linarith)

end Layers

/-- For odd cyclic orders and doubling-invariant perfect seeds, zero is the
only center that can persist in a family of sublinear overlaps. -/
theorem doubling_center {v : ℕ → ℕ+} (D : ∀ i, Finset (ZMod (v i))) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => (v i).val) atTop atTop) (odd : ∀ i, Odd (v i).val)
    (stable : ∀ i, (D i).image (fun x => x+x)=D i) (c : ∀ i, ZMod (v i))
    (poor : Tendsto (fun i => (overlap (D i) (c i):ℝ)/(v i)) atTop (𝓝 0)) :
    ∀ᶠ i in atTop, c i=0 := by
  have large : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by
    simpa only [ZMod.card] using big
  have cover : Tendsto (fun i => (overlap (D i) (c i):ℝ)/Fintype.card (ZMod (v i))) atTop (𝓝 0) := by
    simpa only [ZMod.card] using poor
  filter_upwards [center_fixed D hD large c cover] with i fixed
  let u := ZMod.unitOfCoprime 2 (odd i).coprime_two_left
  let e := AddAut.mulRight u
  have eval (x : ZMod (v i)) : e x=x+x := by simp [e,u,mul_two]
  have symm : (D i).image (fun x => e x+0)=D i := by simpa only [add_zero,eval] using stable i
  have eq := fixed e 0 symm
  simp only [nsmul_zero,add_zero,eval] at eq
  exact add_eq_right.mp eq

#print axioms layers_iff
#print axioms doubling_center

/-- The two copies of D in the cyclic group of order 2m, reflected across
the odd residue 1+2t. Their overlap center in the smaller group is 1+2t. -/
def doubled {m : ℕ+} (D : Finset (ZMod m)) (t : ZMod m) : Finset (ZMod (2*m.val)) :=
  layers D (doubleHom m) (1+doubleHom m t)

/-- Exact number of missing residues after forming the cyclic reflected seed,
expressed without truncated subtraction. -/
theorem doubled_count {m : ℕ+} {D : Finset (ZMod m)} (hD : Perfect D)
    (ne : D.Nonempty) (t : ZMod m) :
    (doubled D t+doubled D t).card+overlap D (1+t+t)+1=2*m.val+2*D.card := by
  obtain ⟨inj,odd,axis⟩ := double_coordinates m t
  have h := layer_sumset_size hD.sidon ne (doubleHom m) inj odd axis
  change ((doubled D t+doubled D t).card:ℝ)=2*(D.card:ℝ)^2+1-overlap D (1+t+t) at h
  have k := parameters D hD
  rw [ZMod.card] at k
  exact_mod_cast (show ((doubled D t+doubled D t).card:ℝ)+overlap D (1+t+t)+1=2*(m:ℝ)+2*D.card by linarith)

/-- Every nonzero center in an odd-order doubling-invariant perfect family
loses at least (1−1/√2)/8 of the doubled cyclic group in the limit inferior. -/
theorem nonzero_center_loss {v : ℕ → ℕ+} (D : ∀ i, Finset (ZMod (v i))) (hD : ∀ i, Perfect (D i))
    (big : Tendsto (fun i => (v i).val) atTop atTop) (odd : ∀ i, Odd (v i).val)
    (stable : ∀ i, (D i).image (fun x => x+x)=D i)
    {b : ℝ} (small : b<(1-1/Real.sqrt 2)/8) :
    ∀ᶠ i in atTop, ∀ t : ZMod (v i), 1+t+t ≠ 0 →
      ((doubled (D i) t+doubled (D i) t).card:ℝ)/(2*(v i:ℝ)) < 1-b := by
  let a := (2*b+(1-1/Real.sqrt 2)/4)/2
  have left : 2*b<a := by dsimp [a];linarith
  have right : a<(1-1/Real.sqrt 2)/4 := by dsimp [a];linarith
  have large : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by simpa only [ZMod.card] using big
  have err := (normal_limits D hD large).2.2.eventually_lt_const (sub_pos.mpr left)
  filter_upwards [moved_center_floor D hD large right,err,big.eventually_gt_atTop 1] with i floor tiny vi
  intro t nz
  let c : ZMod (v i) := 1+t+t
  let u := ZMod.unitOfCoprime 2 (odd i).coprime_two_left
  let e := AddAut.mulRight u
  have eval (x : ZMod (v i)) : e x=x+x := by simp [e,u,mul_two]
  have symm : (D i).image (fun x => e x+0)=D i := by simpa only [add_zero,eval] using stable i
  have moved : e c+4 • (0:ZMod (v i))≠c := by
    intro h
    apply nz
    change c=0
    apply add_eq_right.mp
    simpa only [nsmul_zero,add_zero,eval] using h
  have low := floor c e 0 symm moved
  rw [ZMod.card] at low
  have vp : (0:ℝ)<v i := by exact_mod_cast (v i).pos
  have ol := (lt_div_iff₀ vp).mp low
  dsimp only [diag4] at tiny
  rw [ZMod.card] at tiny
  have sl := (div_lt_iff₀ vp).mp tiny
  have ne : (D i).Nonempty := by
    by_contra h
    have k := parameters (D i) (hD i)
    rw [ZMod.card,card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)] at k
    have g : (1:ℝ)<v i := by exact_mod_cast vi
    norm_num at k
    linarith
  have bal : ((doubled (D i) t+doubled (D i) t).card:ℝ)+overlap (D i) c+1=2*(v i:ℝ)+2*(D i).card := by
    exact_mod_cast doubled_count (hD i) ne t
  apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*(v i:ℝ))).mpr
  nlinarith only [bal,ol,sl,Nat.cast_nonneg (α:=ℝ) (D i).card]

/-- Any full basis containing the reflected seed at a center with a growing
four-path level set must pay the dense Sidon repair bound. -/
theorem growing_level_repair {v : ℕ → ℕ+} (D : ∀ i, Finset (ZMod (v i))) (hD : ∀ i, Perfect (D i))
    (ne : ∀ i, (D i).Nonempty) (big : Tendsto (fun i => (v i).val) atTop atTop)
    (t : ∀ i, ZMod (v i)) (T : ∀ i, Finset (ZMod (v i)))
    (large : Tendsto (fun i => (T i).card) atTop atTop)
    (same : ∀ i x, x∈T i → paths (D i) 4 x=paths (D i) 4 (1+t i+t i))
    (B : ∀ i, Finset (ZMod (2*(v i).val))) (sub : ∀ i, doubled (D i) (t i) ⊆ B i)
    (full : ∀ i, B i+B i=univ) {s : ℝ} (below : s < (3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, s<((B i).card:ℝ)/Real.sqrt (2*(v i:ℝ)) := by
  have largeV : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by simpa only [ZMod.card] using big
  have h := Green33SidonLayerRepairs.overlap_extension_lower D (fun i => (hD i).sidon) ne
    (fun i => doubleHom (v i)) (fun i => (double_coordinates _ (t i)).1)
    (fun i => 1+doubleHom _ (t i)) (fun i => (double_coordinates _ (t i)).2.1)
    (by intro i;simp only [ZMod.card])
    (fun i => 1+t i+t i) (fun i => (double_coordinates _ (t i)).2.2)
    largeV (perfect_size_limit D hD largeV) (growing_level D hD largeV _ T large same)
    B sub full below
  simpa only [ZMod.card,Nat.cast_mul,Nat.cast_ofNat] using h

#print axioms doubled_count
#print axioms nonzero_center_loss
#print axioms growing_level_repair

end Green33PerfectDifferenceCenters
