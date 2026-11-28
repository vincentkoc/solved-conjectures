import Green33SingerKloosterman
import Green33PerfectDifferenceCenters

/-! Conditional bounds for cyclic Singer sumsets from the classical rank-four
hyper-Kloosterman estimate, in arbitrary characteristic. -/

open Finset Green33SingerKloosterman Green33ReflectedLayers Green33PerfectDifferenceCenters
open Green33SingerProjectiveOverlap (Plane scalars scalar_card)
open scoped Pointwise BigOperators

namespace Green33SingerAllCharacteristics

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
variable [DecidableEq F] [DecidableEq K]

noncomputable local instance : Fintype (Plane F K) := Fintype.ofFinite _

abbrev order (F : Type*) [Fintype F] := (Fintype.card F)^2+Fintype.card F+1

omit [DecidableEq F] [DecidableEq K] in
private theorem order_eq (h : Fintype.card K=(Fintype.card F)^3) :
    Nat.card (Plane F K)=order F := by
  classical
  let q := Fintype.card F
  have pos : 1<q := Fintype.one_lt_card
  have e := (scalars F K).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_units,Nat.card_eq_fintype_card,h,scalar_card] at e
  change q^3-1=Nat.card (Plane F K)*(q-1) at e
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0<q-1)
  rw [← e]
  have p := Nat.sub_add_cancel (show 1≤q by omega)
  change q^3-1=(q^2+q+1)*(q-1)
  apply Nat.sub_eq_of_eq_add
  nlinarith only [congrArg (fun x => (q^2+q+1)*x) p]

private noncomputable def cyclic (h : Fintype.card K=(Fintype.card F)^3) :
    ZMod (order F) ≃+ Additive (Plane F K) := by
  letI : IsCyclic (Plane F K) := isCyclic_of_surjective (QuotientGroup.mk' (scalars F K))
    (QuotientGroup.mk'_surjective _)
  exact (ZMod.ringEquivCongr (order_eq h).symm).toAddEquiv.trans
    (zmodAddCyclicAddEquiv (G:=Additive (Plane F K)) inferInstance)

private noncomputable def point (h : Fintype.card K=(Fintype.card F)^3) :
    ZMod (order F) ≃ Plane F K := (cyclic h).toEquiv.trans Additive.toMul

/-- Labels in the actual cyclic group of the points of the given hyperplane. -/
noncomputable def labels (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) :
    Finset (ZMod (order F)) := (hyperplane L).map (point h).symm.toEmbedding

private theorem label_mem (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) (x : ZMod (order F)) :
    x∈labels h L ↔ point h x∈hyperplane L := by
  rw [labels,mem_map_equiv,Equiv.symm_symm]

theorem perfect_labels (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) (onto : Function.Surjective L) :
    Perfect (labels h L) := by
  classical
  intro c hc
  let e := point h
  have mul (x y) : e (x+y)=e x*e y := by simp [e,point]
  have zero : e 0=1 := by simp [e,point]
  have cn : e c≠1 := fun j => hc (e.injective (j.trans zero.symm))
  have unique := card_eq_one_iff_existsUnique.mp ((cubic_parameters L onto h).2 (e c) cn)
  obtain ⟨z,hz,uq⟩ := unique
  obtain ⟨hz₁,hz₂⟩ := mem_filter.mp hz
  let y := e.symm z
  have val : e y=z := e.apply_symm_apply _
  have hy := (label_mem h L y).mpr (val ▸ hz₁)
  have hcy := (label_mem h L (c+y)).mpr (by change e (c+y)∈_;rwa [mul,val])
  apply card_eq_one_iff_existsUnique.mpr
  refine ⟨(c+y,y),mem_filter.mpr ⟨mem_product.mpr ⟨hcy,hy⟩,add_sub_cancel_right ..⟩,?_⟩
  rintro ⟨a,b⟩ hab
  obtain ⟨pair,eq⟩ := mem_filter.mp hab
  obtain ⟨ha,hb⟩ := mem_product.mp pair
  change a-b=c at eq
  have ab := sub_eq_iff_eq_add.mp eq
  have bz : e b=z := uq _ (mem_filter.mpr ⟨(label_mem ..).mp hb,by rw [← mul,← ab];exact (label_mem ..).mp ha⟩)
  have yb : b=y := e.injective (bz.trans val.symm)
  exact Prod.ext (ab.trans (congrArg (c+·) yb)) yb

/-- Convolution powers of the hyperplane indicator are the ordinary ordered
counts of positive-length sums in cyclic coordinates, including repetitions. -/
private theorem cyclic_paths [DecidableEq (Plane F K)] (h : Fintype.card K=(Fintype.card F)^3)
    (L : K→ₗ[F] F) (r : ℕ) (c : ZMod (order F)) :
    iter (Green33SingerKloosterman.mark (hyperplane L)) r (point h c) =
      (paths (labels h L) (r+1) c:ℂ) := by
  classical
  induction r generalizing c with
  | zero =>
    simp only [iter,Green33SingerKloosterman.mark,paths,walk,sub_eq_zero,sum_ite_eq,label_mem]
    split_ifs <;> simp
  | succ r ih =>
    change conv _ _ _=(walk (labels h L) (paths (labels h L) (r+1)) c:ℂ)
    unfold conv walk
    simp only [Green33SingerKloosterman.mark,ite_mul,one_mul,zero_mul,← sum_filter,
      filter_mem_eq_inter,univ_inter,labels,sum_map,Complex.ofReal_sum,Equiv.coe_toEmbedding]
    apply sum_congr rfl
    intro x _
    have div : point h (c-(point h).symm x) = point h c/x := by
      change (cyclic h (c-(point h).symm x)).toMul=_
      rw [map_sub,toMul_sub]
      change point h c/(point h ((point h).symm x))=_
      rw [Equiv.apply_symm_apply]
    rw [← div,ih]
    rfl

/-- The classical Deligne size bound, stated for the unnormalized rank-four
sum on the extension field. The argument of `kloosterman` is rank minus one. -/
def RankFourBound (L : K→ₗ[F] F) (ψ : AddChar F ℂ) : Prop :=
  ∀ x : Kˣ, ‖kloosterman L ψ 3 x‖≤4*(Fintype.card K:ℝ)*Real.sqrt (Fintype.card K)

/-- The centered ordered four-sum count, with a uniform error of order q^(3/2)
assuming the pointwise rank-four hyper-Kloosterman bound. -/
theorem four_count (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F)
    (onto : Function.Surjective L) (ψ : AddChar F ℂ) (nt : ψ≠0) (bound : RankFourBound L ψ)
    (c : ZMod (order F)) :
    |paths (labels h L) 4 c-((Fintype.card F:ℝ)+1)^4/(order F:ℝ)| ≤
      4*(Fintype.card F:ℝ)*Real.sqrt (Fintype.card F)+1 := by
  classical
  let q : ℝ := Fintype.card F
  let v : ℝ := order F
  let p := paths (labels h L) 4 c
  have qp : 1≤q := by dsimp [q];exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α:=F))
  have vn : 1≤v := by dsimp [v,order];exact_mod_cast (by omega : 1≤(Fintype.card F)^2+Fintype.card F+1)
  have src := rank_error L onto ψ nt 3 _ bound (point h c)
  rw [cyclic_paths] at src
  have card := (cubic_parameters L onto h).1
  have ambient : Fintype.card (Plane F K)=order F := Nat.card_eq_fintype_card.symm.trans (order_eq h)
  rw [card,ambient,h] at src
  norm_num only [Nat.reduceAdd,Nat.cast_pow,Nat.cast_add,Nat.cast_one] at src
  have sourceBound : ‖(p:ℂ)-((Fintype.card F:ℂ)+1)^4/(order F:ℂ)‖ ≤
    ((q-1)*(4*q^3*Real.sqrt (q^3))+1/v)/q^4 := by
    simpa only [p,q,v,Nat.cast_add,Nat.cast_pow,Nat.cast_one] using src
  have cast : ((p-(q+1)^4/v:ℝ):ℂ)=(p:ℂ)-((Fintype.card F:ℂ)+1)^4/(order F:ℂ) := by
    dsimp only [q,v]
    push_cast
    rfl
  rw [← cast,Complex.norm_real,Real.norm_eq_abs] at sourceBound
  change |p-(q+1)^4/v|≤4*q*Real.sqrt q+1
  refine sourceBound.trans ?_
  have pos : 0<q := by linarith
  have sq : Real.sqrt (q^3)=q*Real.sqrt q := by
    rw [show q^3=q^2*q by ring,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq pos.le]
  rw [sq]
  apply (div_le_iff₀ (pow_pos pos 4)).mpr
  have small : 1/v≤1 := (div_le_iff₀ (by linarith : 0<v)).mpr (by linarith)
  have qfour : 1≤q^4 := one_le_pow₀ qp
  have grow := mul_le_mul_of_nonneg_right (show q-1≤q by linarith) (show 0≤4*q^3*(q*Real.sqrt q) by positivity)
  nlinarith only [grow,small,qfour]

/-- Error for the literal cyclic intersection of the sumset and its reflection.
The four diagonal corrections are included for all characteristics and centers. -/
theorem overlap_bound (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (ψ : AddChar F ℂ) (nt : ψ≠0) (bound : RankFourBound L ψ) (c : ZMod (order F)) :
    |4*(overlap (labels h L) c:ℝ)-(order F:ℝ)| ≤
      (Fintype.card F:ℝ)*(4*Real.sqrt (Fintype.card F)+10) := by
  classical
  let q : ℝ := Fintype.card F
  let v : ℝ := order F
  let I : ℝ := overlap (labels h L) c
  let p := paths (labels h L) 4 c
  have qp : 2≤q := by dsimp [q];exact_mod_cast (Fintype.one_lt_card (α:=F) : 2≤Fintype.card F)
  have vq : v=q^2+q+1 := by simp [v,q]
  have vp : 0<v := by nlinarith only [vq,qp,sq_nonneg q]
  have center : v≤(q+1)^4/v ∧ (q+1)^4/v≤v+3*q := by
    constructor
    · apply (le_div_iff₀ vp).mpr
      rw [vq];nlinarith only [sq_nonneg q,show 0≤q^3 by positivity,qp]
    · apply (div_le_iff₀ vp).mpr
      rw [vq];nlinarith only [sq_nonneg q,show 0≤q^3 by positivity,qp]
  have count := abs_le.mp (four_count h L onto ψ nt bound c)
  change -(4*q*Real.sqrt q+1) ≤ p-(q+1)^4/v ∧ p-(q+1)^4/v≤4*q*Real.sqrt q+1 at count
  have d := two_walk_overlap (perfect_labels h L onto).sidon c
  have card : (labels h L).card=Fintype.card F+1 := by
    rw [labels,card_map,(cubic_parameters L onto h).1]
  change p≤4*I ∧ 4*I≤p+4*((labels h L).card:ℝ) at d
  rw [card,Nat.cast_add,Nat.cast_one] at d
  change p≤4*I ∧ 4*I≤p+4*(q+1) at d
  change |4*I-v|≤q*(4*Real.sqrt q+10)
  rw [abs_le]
  constructor <;> nlinarith only [qp,center.1,center.2,count.1,count.2,d.1,d.2]

#print axioms perfect_labels
#print axioms four_count
#print axioms overlap_bound

private theorem label_card (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) (onto : Function.Surjective L) :
    (labels h L).card=Fintype.card F+1 := by
  classical rw [labels,card_map,(cubic_parameters L onto h).1]

abbrev positiveOrder (F : Type*) [Fintype F] : ℕ+ := ⟨order F,by unfold order;omega⟩

/-- The reflected even/odd construction, now for every finite characteristic. -/
noncomputable def reflected (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) (t : ZMod (order F)) :=
  doubled (m:=positiveOrder F) (labels h L) t

/-- Uniform finite error in the doubled ordinary sumset. -/
theorem doubled_bound (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (ψ : AddChar F ℂ) (nt : ψ≠0) (bound : RankFourBound L ψ) (t : ZMod (order F)) :
    |4*((reflected h L t+reflected h L t).card:ℝ)-7*(order F:ℝ)|≤
      (Fintype.card F:ℝ)*(4*Real.sqrt (Fintype.card F)+20) := by
  let c := 1+t+t
  have nz : (labels h L).Nonempty := by rw [← card_pos,label_card h L onto];omega
  have dc := doubled_count (m:=positiveOrder F) (perfect_labels h L onto) nz t
  have realCount := congrArg (Nat.cast (R:=ℝ)) dc
  have size := congrArg (Nat.cast (R:=ℝ)) (label_card h L onto)
  push_cast at size
  push_cast at realCount
  change ((reflected h L t+reflected h L t).card:ℝ)+(overlap (labels h L) c:ℝ)+1=
    2*(order F:ℝ)+2*((labels h L).card:ℝ) at realCount
  have p := abs_le.mp (overlap_bound h L onto ψ nt bound c)
  have q2 : (2:ℝ)≤Fintype.card F := by exact_mod_cast (Fintype.one_lt_card (α:=F) : 2≤Fintype.card F)
  rw [abs_le]
  constructor <;> nlinarith only [realCount,size,p.1,p.2,q2]

open Filter
open scoped Topology

private theorem normalized_limit (q v u : ℕ→ℝ) (b a : ℝ) (ha : 0≤a) (pos : ∀ i,0<q i)
    (hv : ∀ i, q i^2≤v i) (big : Tendsto q atTop atTop)
    (err : ∀ i, |u i-b*v i|≤q i*(4*Real.sqrt (q i)+a)) :
    Tendsto (fun i => u i/v i) atTop (𝓝 b) := by
  have small := ((tendsto_const_nhds (x:=(4:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp big)).add
    ((tendsto_const_nhds (x:=a)).div_atTop big)
  rw [add_zero] at small
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ small
  filter_upwards with i
  have qp := pos i
  have vp := (sq_pos_of_pos qp).trans_le (hv i)
  have rt := Real.sqrt_pos.mpr qp
  let z := 4*Real.sqrt (q i)+a
  have zn : 0≤z := by dsimp [z];positivity
  change ‖u i/v i-b‖≤4/Real.sqrt (q i)+a/q i
  rw [show u i/v i-b=(u i-b*v i)/v i by field_simp,Real.norm_eq_abs,abs_div,abs_of_pos vp]
  calc
    _ ≤ (q i*z)/v i := (div_le_div_iff_of_pos_right vp).mpr (err i)
    _ ≤ (q i*z)/q i^2 := div_le_div_of_nonneg_left (mul_nonneg qp.le zn) (sq_pos_of_pos qp) (hv i)
    _ = 4/Real.sqrt (q i)+a/q i := by
      dsimp [z]
      field_simp [qp.ne',rt.ne']
      nlinarith only [Real.sq_sqrt qp.le]

section Limits
variable {F K : ℕ→Type*} [∀ i, Field (F i)] [∀ i, Field (K i)] [∀ i, Algebra (F i) (K i)]
    [∀ i, Fintype (F i)] [∀ i, Fintype (K i)] [∀ i, DecidableEq (F i)] [∀ i, DecidableEq (K i)]

/-- The all-center quarter-overlap limit with the analytic input exposed. -/
theorem quarter (h : ∀ i, Fintype.card (K i)=(Fintype.card (F i))^3)
    (L : ∀ i, K i→ₗ[F i] F i) (onto : ∀ i, Function.Surjective (L i))
    (ψ : ∀ i, AddChar (F i) ℂ) (nt : ∀ i, ψ i≠0) (bound : ∀ i, RankFourBound (L i) (ψ i))
    (c : ∀ i, ZMod (order (F i))) (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => (overlap (labels (h i) (L i)) (c i):ℝ)/(order (F i):ℝ)) atTop (𝓝 (1/4)) := by
  let q i : ℝ := Fintype.card (F i)
  let v i : ℝ := order (F i)
  let I i : ℝ := overlap (labels (h i) (L i)) (c i)
  have e := normalized_limit q v (fun i => 4*I i) 1 10 (by norm_num)
    (fun _ => by dsimp [q];exact_mod_cast Fintype.card_pos) (fun i => by simp [v,q]; linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (F i))])
    (tendsto_natCast_atTop_atTop.comp big) (fun i => by simpa only [one_mul] using (overlap_bound (h i) (L i) (onto i) (ψ i) (nt i) (bound i) (c i)))
  apply (e.div_const 4).congr
  intro i
  change 4*I i/v i/4=I i/v i
  ring

/-- The all-axis seven-eighths coverage limit with the same analytic input. -/
theorem coverage (h : ∀ i, Fintype.card (K i)=(Fintype.card (F i))^3)
    (L : ∀ i, K i→ₗ[F i] F i) (onto : ∀ i, Function.Surjective (L i))
    (ψ : ∀ i, AddChar (F i) ℂ) (nt : ∀ i, ψ i≠0) (bound : ∀ i, RankFourBound (L i) (ψ i))
    (t : ∀ i, ZMod (order (F i))) (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop) :
    Tendsto (fun i => ((reflected (h i) (L i) (t i)+reflected (h i) (L i) (t i)).card:ℝ)/
      (2*(order (F i):ℝ))) atTop (𝓝 (7/8)) := by
  let q i : ℝ := Fintype.card (F i)
  let v i : ℝ := order (F i)
  let a i : ℝ := (reflected (h i) (L i) (t i)+reflected (h i) (L i) (t i)).card
  have e := normalized_limit q v (fun i => 4*a i) 7 20 (by norm_num)
    (fun _ => by dsimp [q];exact_mod_cast Fintype.card_pos) (fun i => by simp [v,q]; linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (F i))])
    (tendsto_natCast_atTop_atTop.comp big) (fun i => doubled_bound (h i) (L i) (onto i) (ψ i) (nt i) (bound i) (t i))
  apply (e.div_const 8).congr
  intro i
  change 4*a i/v i/8=a i/(2*v i)
  ring

#print axioms doubled_bound
#print axioms quarter
#print axioms coverage

/-- The full-sumset condition forces the repair coefficient above every real
number below (3+√3)/(2√2), under the same explicit rank-four hypothesis. -/
theorem repair_floor (h : ∀ i, Fintype.card (K i)=(Fintype.card (F i))^3)
    (L : ∀ i, K i→ₗ[F i] F i) (onto : ∀ i, Function.Surjective (L i))
    (ψ : ∀ i, AddChar (F i) ℂ) (nt : ∀ i, ψ i≠0) (bound : ∀ i, RankFourBound (L i) (ψ i))
    (t : ∀ i, ZMod (order (F i))) (big : Tendsto (fun i => Fintype.card (F i)) atTop atTop)
    (B : ∀ i, Finset (ZMod (2*order (F i)))) (sub : ∀ i, reflected (h i) (L i) (t i)⊆B i)
    (full : ∀ i,B i+B i=univ) {s : ℝ} (below : s<(3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, s<((B i).card:ℝ)/Real.sqrt (2*(order (F i):ℝ)) := by
  let v i := positiveOrder (F i)
  let D (i : ℕ) : Finset (ZMod (v i)) := labels (h i) (L i)
  let T (i : ℕ) : ZMod (v i) := t i
  have ne i : (D i).Nonempty := by
    change (labels (h i) (L i)).Nonempty
    rw [← card_pos,label_card (h i) (L i) (onto i)];omega
  have hd i : Perfect (D i) := perfect_labels (h i) (L i) (onto i)
  have vg : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by
    simp only [ZMod.card]
    exact tendsto_atTop_mono (fun i => by dsimp [v,positiveOrder,order];omega) big
  have inter : Tendsto (fun i => (overlap (D i) (1+T i+T i):ℝ)/Fintype.card (ZMod (v i))) atTop (𝓝 (1/4)) := by
    simp only [ZMod.card]
    convert quarter h L onto ψ nt bound (fun i => 1+t i+t i) big using 1
    rfl
  have res := Green33SidonLayerRepairs.overlap_extension_lower D (fun i => (hd i).sidon) ne
    (fun i => doubleHom (v i)) (fun i => (double_coordinates (v i) (T i)).1)
    (fun i => 1+doubleHom (v i) (T i)) (fun i => (double_coordinates (v i) (T i)).2.1)
    (by intro i;simp only [ZMod.card]) (fun i => 1+T i+T i)
    (fun i => (double_coordinates (v i) (T i)).2.2) vg (perfect_size_limit D hd vg) inter B sub full below
  simp only [ZMod.card,Nat.cast_mul,Nat.cast_ofNat] at res
  convert res using 1
  rfl

#print axioms repair_floor
end Limits

end Green33SingerAllCharacteristics
