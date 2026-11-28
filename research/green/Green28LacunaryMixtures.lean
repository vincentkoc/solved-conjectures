import Green28InverseStability
import Green28ReflectedPrefix

/-! Uniformity of approximate sums with a growing number of integer outcomes. -/

namespace Green28LacunaryMixtures
open Green28 Green28InverseStability Finset MeasureTheory
open scoped ENNReal

/-- An equal mixture of finitely many integer laws. -/
noncomputable def average {m : ℕ} (hm : 0 < m) (f : Fin m → PMF ℤ) : PMF ℤ :=
  letI : NeZero m := ⟨hm.ne'⟩
  (PMF.uniformOfFintype (Fin m)).bind f

private theorem average_event {m : ℕ} (hm : 0 < m) (f : Fin m → PMF ℤ) (E : Set ℤ) :
    (average hm f).toMeasure.real E = (∑ i, (f i).toMeasure.real E) / m := by
  let _ : NeZero m := ⟨hm.ne'⟩
  rw [average,Measure.real,PMF.toMeasure_bind_apply _ _ E (.of_discrete),tsum_fintype]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ((PMF.uniformOfFintype _).apply_ne_top _) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,PMF.uniformOfFintype_apply,Fintype.card_fin,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Measure.real,←mul_sum,div_eq_mul_inv,mul_comm]

open scoped Classical in
private theorem uniform_event (S : Finset ℤ) (hs : S.Nonempty) (E : Set ℤ) :
    (PMF.uniformOfFinset S hs).toMeasure.real E = ((S.filter (fun x => x ∈ E)).card:ℝ)/S.card := by
  rw [Measure.real,PMF.toMeasure_uniformOfFinset_apply hs E (.of_discrete),ENNReal.toReal_div]
  simp

private theorem uniform_finset (S E : Finset ℤ) (hs : S.Nonempty) :
    (PMF.uniformOfFinset S hs).toMeasure.real (E:Set ℤ) = ((S ∩ E).card:ℝ)/S.card := by
  classical
  rw [uniform_event]
  congr 3
  ext x
  simp

/-- Equal mixtures of uniform laws on geometrically separated sizes are far from every
uniform law, regardless of how their underlying supports overlap. -/
theorem far_from_uniform {n : ℕ} (hn : 0 < n) (A : Fin n → Finset ℤ)
    (ne : ∀ i, (A i).Nonempty)
    (growth : ∀ i j, i < j → n^3*(A i).card ≤ (A j).card)
    (T : Finset ℤ) (ht : T.Nonempty) :
    ∃ E : Finset ℤ, 1-3/(n:ℝ) ≤ (PMF.uniformOfFinset T ht).toMeasure.real (E:Set ℤ) -
      (average hn (fun i => PMF.uniformOfFinset (A i) (ne i))).toMeasure.real (E:Set ℤ) := by
  classical
  let C := Finset.univ.filter fun i => n^2*(A i).card ≤ T.card
  let M := Finset.univ.filter fun i => T.card < n^2*(A i).card ∧ (A i).card < n*T.card
  let F := C.biUnion A
  let E := T \ F
  have middle : M.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    have impossible (i j : Fin n) (hi : i ∈ M) (hj : j ∈ M) (lt : i < j) : False := by
      have a := (mem_filter.mp hi).2.1
      have b := (mem_filter.mp hj).2.2
      have c := Nat.mul_lt_mul_of_pos_left a hn
      rw [←Nat.mul_assoc,show n*n^2=n^3 by ring] at c
      exact (not_lt.mpr (growth _ _ lt)) (b.trans c)
    exact le_antisymm (le_of_not_gt (impossible j i hj hi)) (le_of_not_gt (impossible i j hi hj))
  have small : n*F.card ≤ T.card := by
    have b : n*(n*F.card) ≤ n*T.card := calc
      _ = n^2*F.card := by ring
      _ ≤ n^2*(∑ i ∈ C,(A i).card) := Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ i ∈ C,n^2*(A i).card := mul_sum ..
      _ ≤ ∑ _i ∈ C,T.card := sum_le_sum fun i hi => (mem_filter.mp hi).2
      _ ≤ n*T.card := by simpa using Nat.mul_le_mul_right T.card (show C.card ≤ n by simpa using C.card_le_univ)
    exact Nat.le_of_mul_le_mul_left b hn
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have htR : (0:ℝ)<T.card := by exact_mod_cast ht.card_pos
  have unif : 1-(n:ℝ)⁻¹ ≤ (PMF.uniformOfFinset T ht).toMeasure.real (E:Set ℤ) := by
    rw [uniform_finset,inter_eq_right.mpr (sdiff_subset)]
    have card : T.card ≤ E.card+F.card := by
      have h := card_sdiff_add_card_inter T F
      have le := card_le_card (inter_subset_right (s₁:=T) (s₂:=F))
      dsimp [E];omega
    apply (le_div_iff₀ htR).mpr
    have sc : (n:ℝ)*F.card ≤ T.card := by exact_mod_cast small
    have dc : (T.card:ℝ) ≤ E.card+F.card := by exact_mod_cast card
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left dc hnR.le]
  let mass (i : Fin n) := (PMF.uniformOfFinset (A i) (ne i)).toMeasure.real (E:Set ℤ)
  have per (i : Fin n) : mass i ≤ (n:ℝ)⁻¹ + (if i ∈ M then 1 else 0) := by
    by_cases small_i : i ∈ C
    · have disj : A i ∩ E = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        obtain ⟨ha,he⟩ := mem_inter.mp hz
        exact (mem_sdiff.mp he).2 (mem_biUnion.mpr ⟨i,small_i,ha⟩)
      dsimp [mass]
      rw [uniform_finset,disj,card_empty,Nat.cast_zero,zero_div]
      positivity
    by_cases mid : i ∈ M
    · rw [if_pos mid]
      have mass_le : mass i ≤ 1 := by
        simpa only [probReal_univ] using
          (measureReal_mono (μ:=(PMF.uniformOfFinset (A i) (ne i)).toMeasure) (Set.subset_univ (E:Set ℤ)) (measure_ne_top _ _))
      linarith [inv_nonneg.mpr hnR.le]
    · have large : n*T.card ≤ (A i).card := by
        by_contra! bad
        exact mid (mem_filter.mpr ⟨mem_univ _,lt_of_not_ge (fun h => small_i (mem_filter.mpr ⟨mem_univ _,h⟩)),bad⟩)
      have count := card_le_card (show A i ∩ E ⊆ T from (inter_subset_right).trans (sdiff_subset))
      have pos : (0:ℝ) < (A i).card := by exact_mod_cast (ne i).card_pos
      dsimp [mass]
      rw [if_neg mid,add_zero,uniform_finset,←one_div,div_le_div_iff₀ pos hnR,one_mul]
      exact_mod_cast (Nat.mul_comm .. ▸ (Nat.mul_le_mul_left n count).trans large)
  refine ⟨E,?_⟩
  rw [average_event]
  have calcSum : (∑ i, mass i) ≤ 2 := calc
    _ ≤ ∑ i : Fin n, ((n:ℝ)⁻¹+(if i ∈ M then 1 else 0)) := sum_le_sum fun i _ => per i
    _ = 1 + M.card := by
      rw [sum_add_distrib];simp [hn.ne']
    _ ≤ 2 := by exact_mod_cast (by omega : 1+M.card ≤ 2)
  change 1-3/(n:ℝ) ≤ _ - (∑ i, mass i)/n
  have eb := div_le_div_of_nonneg_right calcSum hnR.le
  have id : 3/(n:ℝ) = (n:ℝ)⁻¹+2/n := by ring
  linarith

/-- A uniform law on a subset of the target loses at most the missing fraction in total variation. -/
private theorem subset_uniform {A S : Finset ℤ} (ha : A.Nonempty) (hs : S.Nonempty) (inc : A ⊆ S) :
    TVLe (1-(A.card:ℝ)/S.card) (PMF.uniformOfFinset A ha) (PMF.uniformOfFinset S hs) := by
  classical
  intro E
  let X := A.filter fun z => z ∈ E
  let Y := S.filter fun z => z ∈ E
  have sub : X ⊆ Y := by
    intro z hz
    obtain ⟨a,e⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨inc a,e⟩
  have posA : (0:ℝ) < A.card := by exact_mod_cast ha.card_pos
  have posS : (0:ℝ) < S.card := by exact_mod_cast hs.card_pos
  have c : (X.card:ℝ) ≤ Y.card := by exact_mod_cast card_le_card sub
  have a : (X.card:ℝ) ≤ A.card := by exact_mod_cast card_le_card (filter_subset ..)
  have b : (A.card:ℝ) ≤ S.card := by exact_mod_cast card_le_card inc
  rw [uniform_event,uniform_event]
  change (X.card:ℝ)/A.card ≤ (Y.card:ℝ)/S.card + (1-(A.card:ℝ)/S.card)
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr b),mul_le_mul_of_nonneg_right c posA.le]

/-- Mixing laws within a fixed total variation tolerance preserves the same tolerance. -/
private theorem bind_close {ι : Type*} (p : PMF ι) (f : ι → PMF ℤ) {Q : PMF ℤ} {δ : ℝ}
    (hd : 0 ≤ δ) (all : ∀ i, TVLe δ (f i) Q) : TVLe δ (p.bind f) Q := by
  intro E
  let c := Q.toMeasure.real E + δ
  have nonneg : 0 ≤ c := add_nonneg ENNReal.toReal_nonneg hd
  have each (i : ι) : (f i).toMeasure E ≤ ENNReal.ofReal c := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal nonneg]
    exact all i E
  have h := ENNReal.tsum_le_tsum fun i => show p i*(f i).toMeasure E ≤ p i*ENNReal.ofReal c by
    gcongr
    exact each i
  rw [ENNReal.tsum_mul_right,p.tsum_coe,one_mul,← PMF.toMeasure_bind_apply _ _ E (.of_discrete)] at h
  change ((p.bind f).toMeasure E).toReal ≤ c
  simpa only [ENNReal.toReal_ofReal nonneg] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

private noncomputable def die (d : ℕ) (hd : 0 < d) : PMF (Fin d) :=
  letI : NeZero d := ⟨hd.ne'⟩
  PMF.uniformOfFintype _

private theorem dice_pair {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun i => (PMF.uniformOfFintype β).map (fun j => (i,j))) =
      PMF.uniformOfFintype (α × β) := by
  classical
  ext ⟨i,j⟩
  simp only [PMF.bind_apply,PMF.map_apply,tsum_fintype,PMF.uniformOfFintype_apply,Fintype.card_prod,
    Nat.cast_mul]
  rw [sum_eq_single i]
  · simp [ENNReal.mul_inv,Fintype.card_ne_zero]
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

private theorem sample2 {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α × β → ℤ) :
    (PMF.uniformOfFintype α).bind (fun i => (PMF.uniformOfFintype β).map (fun j => f (i,j))) =
      (PMF.uniformOfFintype (α × β)).map f := by
  rw [←dice_pair,PMF.map_bind]
  simp only [PMF.map_comp,Function.comp_def]

private theorem uniform_image {α : Type*} [Fintype α] [Nonempty α] (f : α → ℤ)
    (inj : Function.Injective f) : (PMF.uniformOfFintype α).map f =
      PMF.uniformOfFinset (Finset.univ.image f) (univ_nonempty.image _) := by
  classical
  ext z
  rw [PMF.map_apply,tsum_fintype]
  by_cases hz : z ∈ Finset.univ.image f
  · obtain ⟨a,_,rfl⟩ := mem_image.mp hz
    rw [sum_eq_single a,if_pos rfl,PMF.uniformOfFintype_apply,PMF.uniformOfFinset_apply_of_mem _ hz,
      card_image_of_injective _ inj,card_univ]
    · intro b _ hb;exact if_neg (fun e => hb (inj e).symm)
    · simp
  · rw [PMF.uniformOfFinset_apply_of_notMem _ hz]
    apply sum_eq_zero
    intro a _
    apply if_neg
    rintro rfl
    exact hz (mem_image_of_mem f (mem_univ a))

private def digit (t d e : ℕ) (p : Fin d × Fin e) : ℤ := (p.1.val:ℤ) + (t:ℤ)*p.2.val

private def box (t d e : ℕ) : Finset ℤ := Finset.univ.image (digit t d e)

private theorem digit_inj {t d e : ℕ} (ht : 0 < t) (hd : d ≤ t) : Function.Injective (digit t d e) := by
  rintro ⟨a,b⟩ ⟨c,f⟩ eq
  unfold digit at eq
  have key : a.val+t*b.val = c.val+t*f.val := by exact_mod_cast eq
  have da := congrArg (·%t) key
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (a.isLt.trans_le hd),
    Nat.mod_eq_of_lt (c.isLt.trans_le hd)] at da
  have db : b.val = f.val := Nat.eq_of_mul_eq_mul_left ht (by omega)
  exact Prod.ext (Fin.ext da) (Fin.ext db)

private theorem box_card {t d e : ℕ} (ht : 0 < t) (hd : d ≤ t) : (box t d e).card = d*e := by
  rw [box,card_image_of_injective _ (digit_inj ht hd),card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]

private theorem box_ne {t d e : ℕ} (hd : 0 < d) (he : 0 < e) : (box t d e).Nonempty :=
  ⟨_,mem_image_of_mem _ (mem_univ (⟨0,hd⟩,⟨0,he⟩))⟩

private theorem box_sample {t d e : ℕ} (ht : 0 < t) (hd : 0 < d) (he : 0 < e) (fit : d ≤ t) :
    (die d hd).bind (fun i => (die e he).map fun j => digit t d e (i,j)) =
      PMF.uniformOfFinset (box t d e) (box_ne hd he) := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let _ : NeZero e := ⟨he.ne'⟩
  exact (sample2 _).trans (uniform_image _ (digit_inj ht fit))

private theorem box_swap {t d e : ℕ} (ht : 0 < t) (hd : 0 < d) (he : 0 < e) (fit : d ≤ t) :
    (die e he).bind (fun j => (die d hd).map fun i => digit t d e (i,j)) =
      PMF.uniformOfFinset (box t d e) (box_ne hd he) := by
  rw [←box_sample ht hd he fit]
  exact PMF.bind_comm _ _ (fun j i => PMF.pure (digit t d e (i,j)))

/-- The integer interval starting at zero with the stated number of sites. -/
def interval (n : ℕ) : Finset ℤ := Ico 0 n

private theorem interval_card (n : ℕ) : (interval n).card = n := by simp [interval]

private theorem interval_ne {n : ℕ} (h : 0<n) : (interval n).Nonempty := by
  apply card_pos.mp
  rwa [interval_card]

private theorem box_bound {t d e : ℕ} (hd : d ≤ t) : box t d e ⊆ interval (t*e) := by
  intro z hz
  obtain ⟨⟨i,j⟩,_,rfl⟩ := mem_image.mp hz
  have hi := i.isLt.trans_le hd
  have top : i.val+t*j.val < t*e :=
    calc i.val+t*j.val < t+t*j.val := by omega
         _ = t*(j.val+1) := by ring
         _ ≤ t*e := Nat.mul_le_mul_left _ j.isLt
  apply mem_Ico.mpr
  exact ⟨by unfold digit;positivity,by unfold digit;exact_mod_cast top⟩

private theorem full_box {t e : ℕ} (ht : 0 < t) : box t t e = interval (t*e) := by
  apply Subset.antisymm (box_bound le_rfl)
  intro z hz
  obtain ⟨lo,hi⟩ := mem_Ico.mp hz
  let a := z.toNat
  have cast : (a:ℤ) = z := Int.toNat_of_nonneg lo
  have small : a < t*e := by exact_mod_cast (cast.symm ▸ hi : (a:ℤ)<(↑(t*e:ℕ):ℤ))
  let i : Fin t := ⟨a%t,Nat.mod_lt _ ht⟩
  let j : Fin e := ⟨a/t,(Nat.div_lt_iff_lt_mul ht).mpr ((Nat.mul_comm t e) ▸ small)⟩
  refine mem_image.mpr ⟨(i,j),mem_univ _,?_⟩
  rw [←cast]
  unfold digit
  exact_mod_cast Nat.mod_add_div a t

private theorem conv_bind {α β : Type*} (p : PMF α) (q : PMF β) (f : α → PMF ℤ) (g : β → PMF ℤ) :
    indepSum (p.bind f) (q.bind g) = p.bind (fun i => q.bind (fun j => indepSum (f i) (g j))) := by
  simp only [indepSum,Bind.bind,PMF.bind_bind]
  congr 1
  funext i
  exact PMF.bind_comm _ _ _

private theorem conv_map {α β : Type*} (p : PMF α) (q : PMF β) (f : α → ℤ) (g : β → ℤ) :
    indepSum (p.map f) (q.map g) = p.bind (fun i => q.map (fun j => f i+g j)) := by
  simp only [indepSum,Bind.bind,PMF.bind_map,Function.comp_def]
  rfl

private def width (t N : ℕ) := t*N + (t*t-1)

private theorem width_cast {t N : ℕ} (ht : 0<t) : (width t N : ℤ) = (t:ℤ)*N+t*t-1 := by
  have tt := Nat.mul_pos ht ht
  simp only [width,Nat.cast_add,Nat.cast_sub (show 1 ≤ t*t by omega),Nat.cast_mul,Nat.cast_one]
  ring

private theorem width_pos {t N : ℕ} (ht : 0<t) (hN : 0<N) : 0 < width t N :=
  (Nat.mul_pos ht hN).trans_le (Nat.le_add_right _ _)

private theorem width_error {t N k : ℕ} (ht : 0<t) (hN : 0<N) (cover : width t N ≤ k) :
    0 ≤ 1-(t*N:ℕ)/(k:ℝ) := by
  have pos : 0 < (k:ℝ) := by exact_mod_cast (width_pos ht hN).trans_le cover
  apply sub_nonneg.mpr
  apply (div_le_one pos).mpr
  exact_mod_cast (Nat.le_add_right (t*N) (t*t-1)).trans cover

private theorem component_close {t N d e k : ℕ} (ht : 0<t) (hN : 0<N) (hd : 0<d) (he : 0<e)
    (dt : d≤t) (et : e≤t) (cover : width t N ≤ k) :
    TVLe (1-(t*N:ℕ)/(k:ℝ))
      (indepSum (PMF.uniformOfFinset (box t d N) (box_ne hd hN))
        (PMF.uniformOfFinset (box t t e) (box_ne ht he)))
      (PMF.uniformOfFinset (interval k) (interval_ne ((width_pos ht hN).trans_le cover))) := by
  classical
  rw [←box_sample ht hd hN dt,←box_swap ht ht he le_rfl,conv_bind]
  apply bind_close _ _ (width_error ht hN cover)
  intro a
  apply bind_close _ _ (width_error ht hN cover)
  intro b
  let _ : NeZero N := ⟨hN.ne'⟩
  let _ : NeZero t := ⟨ht.ne'⟩
  let f (p : Fin N × Fin t) := digit t d N (a,p.1) + digit t t e (p.2,b)
  have inj : Function.Injective f := by
    intro p q eq
    have key : digit t t N (p.2,p.1) = digit t t N (q.2,q.1) := by
      dsimp [f,digit] at eq ⊢
      linarith
    have same := digit_inj ht le_rfl key
    exact Prod.ext (congrArg Prod.snd same) (congrArg Prod.fst same)
  let K := Finset.univ.image f
  have kn : K.Nonempty := univ_nonempty.image _
  have inside : K ⊆ interval (width t N) := by
    intro z hz
    obtain ⟨p,_,rfl⟩ := mem_image.mp hz
    have left : digit t d N (a,p.1) ∈ box t d N := mem_image_of_mem _ (mem_univ _)
    have right : digit t t e (p.2,b) ∈ box t t e := mem_image_of_mem _ (mem_univ _)
    obtain ⟨p0,p1⟩ := mem_Ico.mp (box_bound dt left)
    obtain ⟨q0,q1⟩ := mem_Ico.mp (box_bound le_rfl right)
    have high : (t*e:ℕ) ≤ t*t := Nat.mul_le_mul_left _ et
    apply mem_Ico.mpr
    dsimp only [f]
    rw [width_cast ht]
    push_cast at p1 q1
    constructor <;> linarith [show (t:ℤ)*e ≤ t*t by exact_mod_cast high]
  have card : K.card = t*N := by simp [K,card_image_of_injective _ inj,Nat.mul_comm]
  rw [conv_map]
  change TVLe _ ((PMF.uniformOfFintype (Fin N)).bind (fun i =>
    (PMF.uniformOfFintype (Fin t)).map (fun j => f (i,j)))) _
  rw [sample2 f,uniform_image f inj]
  have contain : interval (width t N) ⊆ interval k := Ico_subset_Ico_right (by exact_mod_cast cover)
  have bound := subset_uniform kn (interval_ne ((width_pos ht hN).trans_le cover)) (inside.trans contain)
  rwa [card,interval_card] at bound

private theorem average_support {m : ℕ} (hm : 0 < m) (f : Fin m → PMF ℤ) (z : ℤ) :
    z ∈ (average hm f).support ↔ ∃ i, z ∈ (f i).support := by
  let _ : NeZero m := ⟨hm.ne'⟩
  simp only [average,PMF.mem_support_bind_iff,PMF.mem_support_uniformOfFintype,true_and]

private theorem add_interval {P Q : PMF ℤ} {u v : ℕ} (hu : 0<u) (hv : 0<v)
    (p : P.support = (interval u:Set ℤ)) (q : Q.support = (interval v:Set ℤ)) :
    (indepSum P Q).support = (interval (u+v-1):Set ℤ) := by
  ext z
  rw [Green28FiniteSearch.mem_support_indepSum]
  simp only [p,q,coe_Ico,interval,Set.mem_Ico]
  rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
  constructor
  · rintro ⟨a,⟨a0,a1⟩,b,⟨b0,b1⟩,rfl⟩
    constructor <;> omega
  · rintro ⟨z0,z1⟩
    by_cases h : z < u
    · exact ⟨z,⟨z0,h⟩,0,⟨le_rfl,by positivity⟩,by omega⟩
    · exact ⟨(u:ℤ)-1,⟨by omega,by omega⟩,z-(u-1),⟨by omega,by omega⟩,by omega⟩

/-- A lower bound on the total variation distance from every finite uniform law. -/
def Far (r : ℝ) (P : PMF ℤ) : Prop :=
  ∀ (T : Finset ℤ) (ht : T.Nonempty), ∃ E : Finset ℤ,
    r ≤ (PMF.uniformOfFinset T ht).toMeasure.real (E:Set ℤ) - P.toMeasure.real (E:Set ℤ)

private theorem support_of_max {n : ℕ} (hn : 0 < n) (A : Fin n → Finset ℤ) (ne : ∀ i,(A i).Nonempty)
    (S : Finset ℤ) (sub : ∀ i, A i ⊆ S) (full : ∃ i, A i = S) :
    (average hn (fun i => PMF.uniformOfFinset (A i) (ne i))).support = (S:Set ℤ) := by
  ext z
  rw [average_support]
  simp only [PMF.support_uniformOfFinset,mem_coe]
  exact ⟨fun ⟨i,h⟩ => sub i h,fun h => full.elim fun i eq => ⟨i,eq ▸ h⟩⟩

/-- A construction with prescribed layer sizes. Each input and its sum has full interval
support. The numerator of the output error is independent of the smoothing length `N`. -/
theorem interval_construction {n t N : ℕ} (hn : 0 < n) (ht : 0<t) (hN : 0<N)
    (d : Fin n → ℕ) (pos : ∀ i, 0 < d i) (fit : ∀ i, d i ≤ t) (top : ∃ i, d i = t)
    (growth : ∀ i j, i < j → n^3*d i ≤ d j) :
    ∃ P Q : PMF ℤ, P.support = (interval (t*N):Set ℤ) ∧ Q.support = (interval (t*t):Set ℤ) ∧
      (indepSum P Q).support = (interval (width t N):Set ℤ) ∧
      (∀ k (cover : width t N ≤ k), TVLe (1-(t*N:ℕ)/(k:ℝ)) (indepSum P Q)
        (PMF.uniformOfFinset (interval k) (interval_ne ((width_pos ht hN).trans_le cover)))) ∧
      Far (1-3/(n:ℝ)) P ∧ Far (1-3/(n:ℝ)) Q := by
  let A (i : Fin n) := box t (d i) N
  let B (i : Fin n) := box t t (d i)
  have a (i : Fin n) : (A i).Nonempty := box_ne (pos i) hN
  have b (i : Fin n) : (B i).Nonempty := box_ne ht (pos i)
  let P := average hn (fun i => PMF.uniformOfFinset (A i) (a i))
  let Q := average hn (fun i => PMF.uniformOfFinset (B i) (b i))
  obtain ⟨last,eq⟩ := top
  have pl : P.support = (interval (t*N):Set ℤ) := by
    apply support_of_max hn A a _ (fun i => box_bound (fit i))
    exact ⟨last,by simpa [A,eq] using full_box (e:=N) ht⟩
  have qr : Q.support = (interval (t*t):Set ℤ) := by
    apply support_of_max hn B b
    · intro i z hz
      obtain ⟨lo,hi⟩ := mem_Ico.mp (box_bound le_rfl hz)
      exact mem_Ico.mpr ⟨lo,hi.trans_le (by exact_mod_cast Nat.mul_le_mul_left t (fit i))⟩
    · exact ⟨last,by simpa [B,eq] using full_box (e:=t) ht⟩
  refine ⟨P,Q,pl,qr,?_,?_,?_,?_⟩
  · have sum := add_interval (Nat.mul_pos ht hN) (Nat.mul_pos ht ht) pl qr
    have tt := Nat.mul_pos ht ht
    simpa only [width,show t*N+t*t-1 = t*N+(t*t-1) by omega] using sum
  · intro k cover
    let _ : NeZero n := ⟨hn.ne'⟩
    unfold P Q average
    rw [conv_bind]
    apply bind_close _ _ (width_error ht hN cover)
    intro i
    apply bind_close _ _ (width_error ht hN cover)
    intro j
    exact component_close ht hN (pos i) (pos j) (fit i) (fit j) cover
  · apply far_from_uniform hn A a
    intro i j hij
    simp only [A,box_card ht (fit _),←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (growth i j hij)
  · apply far_from_uniform hn B b
    intro i j hij
    simp only [B,box_card ht le_rfl]
    calc n^3*(t*d i) = t*(n^3*d i) := by ring
         _ ≤ t*d j := Nat.mul_le_mul_left _ (growth i j hij)

private noncomputable def extend {k : ℕ} (hk : 0<k) (P R : PMF ℤ) : PMF ℤ :=
  average hk (fun i => if i.val = 0 then R else P)

private theorem extend_close {k : ℕ} (hk : 0<k) (P R : PMF ℤ) : TVLe (1/(k:ℝ)) (extend hk P R) P := by
  classical
  let z : Fin k := ⟨0,hk⟩
  intro E
  have per (i : Fin k) : (if i.val = 0 then R else P).toMeasure.real E ≤
      P.toMeasure.real E + (if i = z then 1 else 0) := by
    by_cases h : i.val = 0
    · rw [if_pos h,if_pos (Fin.ext h)]
      have r : R.toMeasure.real E ≤ 1 := by
        simpa only [probReal_univ] using (measureReal_mono (μ:=R.toMeasure) (Set.subset_univ E) (measure_ne_top _ _))
      linarith [show 0 ≤ P.toMeasure.real E from ENNReal.toReal_nonneg]
    · rw [if_neg h,if_neg (show i ≠ z from fun e => h (congrArg Fin.val e)),add_zero]
  rw [extend,average_event]
  have sum := sum_le_sum (fun i (_ : i ∈ Finset.univ) => per i)
  rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  simp only [sum_ite_eq',mem_univ,if_true] at sum
  apply (div_le_iff₀ (by exact_mod_cast hk)).mpr
  calc _ ≤ _ := sum
       _ = _ := by field_simp

private theorem extend_conv {k : ℕ} (hk : 0<k) (P R Q : PMF ℤ) :
    indepSum (extend hk P R) Q = extend hk (indepSum P Q) (indepSum R Q) := by
  let _ : NeZero k := ⟨hk.ne'⟩
  simp only [extend,average,indepSum,Bind.bind,PMF.bind_bind]
  congr 1
  funext i
  split <;> rfl

private theorem extend_support {k : ℕ} (hk : 0<k) (P R : PMF ℤ) (sub : P.support ⊆ R.support) :
    (extend hk P R).support = R.support := by
  ext z
  rw [extend,average_support]
  constructor
  · rintro ⟨i,h⟩
    split at h
    · exact h
    · exact sub h
  · intro h
    exact ⟨⟨0,hk⟩,by simpa using h⟩

private theorem extend_far {k : ℕ} (hk : 0<k) {P : PMF ℤ} (R : PMF ℤ) {r : ℝ} (f : Far r P) :
    Far (r-1/k) (extend hk P R) := by
  intro T ht
  obtain ⟨E,h⟩ := f T ht
  exact ⟨E,by linarith [extend_close hk P R (E:Set ℤ)]⟩

/-- At every sufficiently large interval length `k`, both marginals are far from every
uniform law while their sum has total variation error at most `C/k` from uniform on its range. -/
theorem every_large_interval {ε : ℝ} (he : 0 < ε) :
    ∃ C K : ℕ, ∀ k ≥ K, ∃ (hk : 0<k) (u v : ℕ) (P Q : PMF ℤ),
      P.support = (interval u:Set ℤ) ∧ Q.support = (interval v:Set ℤ) ∧
      (indepSum P Q).support = (interval k:Set ℤ) ∧
      TVLe ((C:ℝ)/k) (indepSum P Q) (PMF.uniformOfFinset (interval k) (interval_ne hk)) ∧
      Far (1-ε) P ∧ Far (1-ε) Q := by
  obtain ⟨n,large⟩ := exists_nat_gt (4/ε)
  have hnR : 0 < (n:ℝ) := (by positivity : 0 < 4/ε).trans large
  have hn : 0 < n := by exact_mod_cast hnR
  have err : 4/(n:ℝ) < ε := (div_lt_iff₀ hnR).mpr (by linarith [(div_lt_iff₀ he).mp large])
  let d : Fin n → ℕ := fun i => (n^3)^i.val
  let t := (n^3)^(n-1)
  have dp (i : Fin n) : 0 < d i := pow_pos (pow_pos hn _) _
  have ht : 0<t := pow_pos (pow_pos hn _) _
  have fit (i : Fin n) : d i ≤ t := Nat.pow_le_pow_right (pow_pos hn _) (by have := i.isLt;omega)
  have grow (i j : Fin n) (lt : i < j) : n^3*d i ≤ d j := by
    dsimp [d]
    rw [← pow_succ']
    exact Nat.pow_le_pow_right (pow_pos hn _) lt
  have top : ∃ i, d i = t := ⟨⟨n-1,by omega⟩,rfl⟩
  let s := t*t-1
  refine ⟨t*t+t,s+t+n,fun k lower => ?_⟩
  have hk : 0<k := by omega
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  let N := (k-s)/t
  have hN : 0<N := Nat.div_pos (by omega) ht
  let r := (k-s)%t
  have add : k = t*N+s+r := by
    have mod := Nat.mod_add_div (k-s) t
    dsimp only [N,r]
    omega
  have cover : width t N ≤ k := by change t*N+s ≤ k;omega
  have rLt : r < t := Nat.mod_lt _ ht
  obtain ⟨P,Q,hp,hq,_,close,farP,farQ⟩ := interval_construction hn ht hN d dp fit top grow
  let u := k-s
  have pu : t*N ≤ u := by dsimp [u];omega
  have up : 0 < u := (Nat.mul_pos ht hN).trans_le pu
  let R := PMF.uniformOfFinset (interval u) (interval_ne up)
  have hR : R.support = (interval u:Set ℤ) := PMF.support_uniformOfFinset ..
  have sub : P.support ⊆ R.support := by
    rw [hp,hR]
    exact_mod_cast (Ico_subset_Ico_right (α:=ℤ) (a:=0) (show (↑(t*N:ℕ):ℤ) ≤ u by exact_mod_cast pu))
  let P' := extend hk P R
  have eP : P'.support = (interval u:Set ℤ) := (extend_support hk P R sub).trans hR
  refine ⟨hk,u,t*t,P',Q,eP,hq,?_,?_,?_,?_⟩
  · have pair := add_interval up (Nat.mul_pos ht ht) eP hq
    have tt := Nat.mul_pos ht ht
    have sk : s ≤ k := by omega
    have size : u+t*t-1 = k := by dsimp [u,s] at sk ⊢;omega
    rwa [size] at pair
  · have cost : 1/(k:ℝ) + (1-(t*N:ℕ)/(k:ℝ)) ≤ ((t*t+t:ℕ):ℝ)/k := by
      have count : 1+k ≤ t*N+(t*t+t) := by dsimp [s] at add;omega
      have cast : 1+(k:ℝ) ≤ (t*N:ℕ)+(↑(t*t+t:ℕ):ℝ) := by exact_mod_cast count
      field_simp
      linarith
    have mix : TVLe (1/(k:ℝ)) (indepSum P' Q) (indepSum P Q) := by
      rw [show indepSum P' Q = _ from extend_conv hk P R Q]
      exact extend_close hk _ _
    intro E
    linarith [mix E,close k cover E]
  · have step := extend_far hk R farP
    have inv : 1/(k:ℝ) ≤ 1/(n:ℝ) := one_div_le_one_div_of_le hnR (by exact_mod_cast (by omega : n≤k))
    intro T hT
    obtain ⟨E,h⟩ := step T hT
    exact ⟨E,by linarith [show 4/(n:ℝ)=3/n+1/n by ring]⟩
  · intro T hT
    obtain ⟨E,h⟩ := farQ T hT
    exact ⟨E,by linarith [show 4/(n:ℝ)=3/n+1/n by ring,one_div_pos.mpr hnR]⟩

/-- Exact interval factors are fair. This is the interval specialization of the
reflected-prefix theorem used to compare the approximate laws with every exact repair. -/
theorem interval_factors_uniform {k : ℕ} (hk : 0<k) {U V : PMF ℤ}
    (eq : indepSum U V = PMF.uniformOfFinset (interval k) (interval_ne hk)) :
    IsUniformOnSupport U ∧ IsUniformOnSupport V := by
  let ne := interval_ne hk
  have lo : (interval k).min' ne = 0 := by
    exact le_antisymm ((interval k).min'_le _ (mem_Ico.mpr ⟨le_rfl,by positivity⟩))
      (mem_Ico.mp ((interval k).min'_mem ne)).1
  have hi : (interval k).max' ne = (k:ℤ)-1 := by
    have bound := (mem_Ico.mp ((interval k).max'_mem ne)).2
    refine le_antisymm (by omega) ((interval k).le_max' _ ?_)
    apply mem_Ico.mpr
    constructor <;> omega
  apply Green28ReflectedPrefix.uniform_of_reflected_prefix ne eq k
  · intro i h
    rw [lo,hi]
    simp only [interval,mem_Ico]
    omega
  · rw [lo,hi];omega

/-- No output-size-independent total variation tolerance guarantees even one factor within
distance one half of any exact ordered repair. The target is the uniform on the true sum interval. -/
theorem no_size_free_repair {δ : ℝ} (hd : 0<δ) :
    ∃ (k : ℕ) (hk : 0<k) (P Q : PMF ℤ), (indepSum P Q).support = (interval k:Set ℤ) ∧
      TVLe δ (indepSum P Q) (PMF.uniformOfFinset (interval k) (interval_ne hk)) ∧
      ∀ U V : PMF ℤ, indepSum U V = PMF.uniformOfFinset (interval k) (interval_ne hk) →
        ¬ TVLe (1/2) P U ∧ ¬ TVLe (1/2) Q V := by
  obtain ⟨C,K,all⟩ := every_large_interval (ε:=1/4) (by norm_num)
  obtain ⟨L,gt⟩ := exists_nat_gt ((C:ℝ)/δ)
  let k := max K (L+1)
  have upper : L < k := (Nat.lt_succ_self L).trans_le (le_max_right ..)
  obtain ⟨hk,u,v,P,Q,_,_,supp,close,p,q⟩ := all k (le_max_left ..)
  have tol : (C:ℝ)/k ≤ δ := by
    apply (div_le_iff₀ (by exact_mod_cast hk)).mpr
    have u : (L:ℝ) < k := by exact_mod_cast upper
    nlinarith [(div_lt_iff₀ hd).mp gt,mul_lt_mul_of_pos_right u hd]
  have bad {P U : PMF ℤ} (f : Far (1-1/4) P) (fair : IsUniformOnSupport U) : ¬TVLe (1/2) P U := by
    obtain ⟨T,ht,rfl⟩ := fair
    obtain ⟨E,h⟩ := f T ht
    intro near
    linarith [near.symm (E:Set ℤ)]
  refine ⟨k,hk,P,Q,supp,fun E => (close E).trans (by linarith),fun U V eq => ?_⟩
  have fair := interval_factors_uniform hk eq
  exact ⟨bad p fair.1,bad q fair.2⟩

#print axioms far_from_uniform
#print axioms interval_construction
#print axioms every_large_interval
#print axioms interval_factors_uniform
#print axioms no_size_free_repair
end Green28LacunaryMixtures
