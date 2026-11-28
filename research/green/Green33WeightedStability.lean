import FormalConjectures.GreensOpenProblems.«33»
import Green33ApproximateCovers
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Finset.Sym

/-! Stability of weighted independent sum laws at the unordered-pair counting bound. -/

namespace Green33WeightedStability
open Finset
open scoped Pointwise

/-- Two draws need not have the same law. Average event mass and the chance that exactly
one draw belongs to the event control the discrepancy of each individual law. -/
private theorem separate_events {a b x t δ : ℝ} (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (above : t*((a+b)/2-δ) ≤ x) (below : t*(1-(a+b)/2-δ) ≤ 1-x)
    (cross : t*(a+b-2*a*b-δ) ≤ 2*x*(1-x)) :
    let ε := 1-t*(1-δ)
    |(a+b)/2-x| ≤ ε ∧ |a-b|^2 ≤ 6*ε ∧
      |a-x| ≤ ε+Real.sqrt (3*ε/2) ∧ |b-x| ≤ ε+Real.sqrt (3*ε/2) := by
  let y := (a+b)/2
  let ε := 1-t*(1-δ)
  change |y-x| ≤ ε ∧ |a-b|^2 ≤ 6*ε ∧ _ ∧ _
  obtain ⟨a0,a1⟩ := ha
  obtain ⟨b0,b1⟩ := hb
  obtain ⟨x0,x1⟩ := hx
  obtain ⟨_,t1⟩ := ht
  have y0 : 0 ≤ y := by dsimp [y];linarith
  have y1 : y ≤ 1 := by dsimp [y];linarith
  change t*(y-δ) ≤ x at above
  change t*(1-y-δ) ≤ 1-x at below
  have avg : |y-x| ≤ ε := by
    apply abs_le.mpr
    dsimp [ε]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr t1) y0]
    · nlinarith [mul_nonneg (sub_nonneg.mpr t1) (sub_nonneg.mpr y1)]
  have cross1 : a+b-2*a*b ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr a1) (sub_nonneg.mpr b1),mul_nonneg a0 b0]
  have bump : a+b-2*a*b ≤ 2*x*(1-x)+ε := by
    dsimp [ε]
    nlinarith [mul_nonneg (sub_nonneg.mpr t1) (sub_nonneg.mpr cross1)]
  have lip : x*(1-x)-y*(1-y) ≤ ε := by
    calc x*(1-x)-y*(1-y) = (x-y)*(1-x-y) := by ring
         _ ≤ |(x-y)*(1-x-y)| := le_abs_self _
         _ = |x-y| * |1-x-y| := abs_mul _ _
         _ ≤ |x-y| * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith,by linarith⟩) (abs_nonneg _)
         _ = |y-x| := by rw [mul_one,abs_sub_comm]
         _ ≤ ε := avg
  have sq : |a-b|^2 ≤ 6*ε := by
    rw [sq_abs]
    dsimp [y] at lip
    nlinarith
  have root : |a-b|/2 ≤ Real.sqrt (3*ε/2) := Real.le_sqrt_of_sq_le (by nlinarith [sq])
  have lift (c : ℝ) (eq : |c-y| = |a-b|/2) : |c-x| ≤ ε+Real.sqrt (3*ε/2) := by
    calc |c-x| ≤ |c-y| + |y-x| := abs_sub_le _ _ _
         _ ≤ _ := by rw [eq];linarith
  refine ⟨avg,sq,lift a ?_,lift b ?_⟩
  · rw [show a-y=(a-b)/2 by dsimp [y];ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  · rw [show b-y=(b-a)/2 by dsimp [y];ring,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_sub_comm b a]

variable {ι G : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq G]

/-- Probability of a subset of the finite label space. -/
noncomputable def mass (p : PMF ι) (T : Finset ι) : ℝ := ∑ i ∈ T, (p i).toReal

omit [DecidableEq ι] in
private theorem mass_univ (p : PMF ι) : mass p univ = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rwa [tsum_fintype,ENNReal.toReal_sum (fun _ _ => p.apply_ne_top _),ENNReal.toReal_one] at h

private theorem mass_compl (p : PMF ι) (T : Finset ι) : mass p Tᶜ = 1-mass p T := by
  have h := Finset.sum_add_sum_compl T (fun i => (p i).toReal)
  change mass p T+mass p Tᶜ = mass p univ at h
  rw [mass_univ] at h
  linarith

private theorem mass_Icc (p : PMF ι) (T : Finset ι) : mass p T ∈ Set.Icc (0:ℝ) 1 := by
  have hn (V : Finset ι) : 0 ≤ mass p V := sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  exact ⟨hn _,by linarith [hn Tᶜ,mass_compl p T]⟩

/-- Sum the independent draw probabilities over a rectangle and an observation event. -/
private noncomputable def rect (p q : PMF ι) (f : ι → ι → G)
    (U V : Finset ι) (E : Finset G) : ℝ :=
  ∑ i ∈ U, ∑ j ∈ V, if f i j ∈ E then (p i).toReal*(q j).toReal else 0

/-- Probability that the observation of independent labels falls in `E`. -/
noncomputable def observed (p q : PMF ι) (f : ι → ι → G) (E : Finset G) : ℝ :=
  rect p q f univ univ E

omit [Fintype ι] [DecidableEq ι] in
private theorem rect_nonneg (p q : PMF ι) (f : ι → ι → G) (U V : Finset ι) (E : Finset G) :
    0 ≤ rect p q f U V E := by
  unfold rect
  positivity

omit [Fintype ι] [DecidableEq ι] in
private theorem rect_full (p q : PMF ι) (f : ι → ι → G) (U V : Finset ι) (E : Finset G)
    (h : ∀ i ∈ U, ∀ j ∈ V, f i j ∈ E) :
    rect p q f U V E = mass p U*mass q V := by
  unfold rect mass
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  exact sum_congr rfl (fun j hj => if_pos (h i hi j hj))

private theorem blocks (p q : PMF ι) (f : ι → ι → G) (T : Finset ι) (E : Finset G) :
    observed p q f E = rect p q f T T E + rect p q f T Tᶜ E +
      rect p q f Tᶜ T E + rect p q f Tᶜ Tᶜ E := by
  unfold observed rect
  set F := fun (i j : ι) => if f i j ∈ E then (p i).toReal*(q j).toReal else 0
  have split (U : Finset ι) :
      (∑ i ∈ U, ∑ j ∈ T, F i j)+(∑ i ∈ U, ∑ j ∈ Tᶜ, F i j) = ∑ i ∈ U, ∑ j, F i j := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun i _ => sum_add_sum_compl _ _)
  change (∑ i, ∑ j, F i j) = _
  rw [add_assoc (_+_) _ _,split T,split Tᶜ,sum_add_sum_compl]

omit [Fintype ι] [DecidableEq ι] in
private theorem symmetric_card (f : ι → ι → G) (sym : ∀ i j, f i j=f j i) (T : Finset ι) :
    2*(image₂ f T T).card ≤ T.card*(T.card+1) := by
  classical
  let g : Sym2 ι → G := Sym2.lift ⟨f,sym⟩
  have inc : image₂ f T T ⊆ T.sym2.image g := by
    intro z hz
    obtain ⟨i,hi,j,hj,rfl⟩ := mem_image₂.mp hz
    exact mem_image.mpr ⟨Sym2.mk i j, mk_mem_sym2_iff.mpr ⟨hi,hj⟩,rfl⟩
  have h := (card_le_card inc).trans card_image_le
  rw [card_sym2,Nat.choose_two_right,Nat.add_sub_cancel] at h
  rw [Nat.mul_comm T.card]
  omega

/-- An upper bound on every observed event under a diffuse target law. -/
def Diffuse (p q : PMF ι) (f : ι → ι → G) (m δ : ℝ) : Prop :=
  ∀ E : Finset G, observed p q f E ≤ (E.card:ℝ)/m+δ

private theorem event_counts (p q : PMF ι) (f : ι → ι → G) (sym : ∀ i j, f i j=f j i)
    {m δ : ℝ} (hm : 0 < m) (h : Diffuse p q f m δ) (T : Finset ι) :
    let a := mass p T
    let b := mass q T
    let k := (T.card:ℝ)
    let n := (Fintype.card ι:ℝ)
    m*(a+b-2*δ) ≤ k*(n+1) ∧ m*(a+b-2*a*b-δ) ≤ k*(n-k) := by
  classical
  let B := image₂ f T T
  let C := image₂ f T Tᶜ
  let a := mass p T
  let b := mass q T
  have tt (i) (hi : i∈T) (j) (hj : j∈T) : f i j ∈ B := mem_image₂_of_mem hi hj
  have tc (i) (hi : i∈T) (j) (hj : j∈Tᶜ) : f i j ∈ C := mem_image₂_of_mem hi hj
  have ct (i) (hi : i∈Tᶜ) (j) (hj : j∈T) : f i j ∈ C := sym i j ▸ tc j hj i hi
  have both : a*b ≤ observed p q f B := by
    rw [blocks p q f T B,rect_full _ _ _ _ _ _ tt]
    linarith [rect_nonneg p q f T Tᶜ B,rect_nonneg p q f Tᶜ T B,rect_nonneg p q f Tᶜ Tᶜ B]
  have one : a+b-a*b ≤ observed p q f (B∪C) := by
    rw [blocks p q f T (B∪C),
      rect_full _ _ _ _ _ _ (fun i hi j hj => mem_union_left C (tt i hi j hj)),
      rect_full _ _ _ _ _ _ (fun i hi j hj => mem_union_right B (tc i hi j hj)),
      rect_full _ _ _ _ _ _ (fun i hi j hj => mem_union_right B (ct i hi j hj)),mass_compl,mass_compl]
    dsimp [a,b]
    linarith [rect_nonneg p q f Tᶜ Tᶜ (B∪C)]
  have cut : a+b-2*a*b ≤ observed p q f C := by
    rw [blocks p q f T C,rect_full _ _ _ _ _ _ tc,rect_full _ _ _ _ _ _ ct,mass_compl,mass_compl]
    dsimp [a,b]
    linarith [rect_nonneg p q f T T C,rect_nonneg p q f Tᶜ Tᶜ C]
  have divBound {w : ℝ} {E : Finset G} (hw : w ≤ observed p q f E) :
      (w-δ)*m ≤ (E.card:ℝ) := (le_div_iff₀ hm).mp (by linarith [hw.trans (h E)])
  have cntB : 2*(B.card:ℝ) ≤ (T.card:ℝ)*(T.card+1) := by exact_mod_cast symmetric_card f sym T
  have cntC : (C.card:ℝ) ≤ (T.card:ℝ)*Tᶜ.card := by exact_mod_cast card_image₂_le f T Tᶜ
  have cntU : ((B∪C).card:ℝ) ≤ B.card+C.card := by exact_mod_cast card_union_le B C
  have cc : (Tᶜ.card:ℝ) = (Fintype.card ι:ℝ)-T.card := by
    rw [card_compl,Nat.cast_sub (card_le_univ _)]
  rw [cc] at cntC
  change _ ≤ _ ∧ _ ≤ _
  constructor
  · change m*(a+b-2*δ) ≤ _
    nlinarith [divBound both,divBound one]
  · change m*(a+b-2*a*b-δ) ≤ _
    nlinarith [divBound cut]

private theorem scale {m d t u r : ℝ} (hm : 0 < m) (hd : 0 < d) (ht : 0 ≤ t)
    (cap : t*d ≤ m) (bound : m*u ≤ r) (hr : 0 ≤ r) : t*u ≤ r/d := by
  calc t*u ≤ t*(r/m) := mul_le_mul_of_nonneg_left ((le_div_iff₀ hm).mpr (mul_comm u m ▸ bound)) ht
       _ ≤ (m/d)*(r/m) := mul_le_mul_of_nonneg_right ((le_div_iff₀ hd).mpr cap) (div_nonneg hr hm.le)
       _ = _ := by field_simp

/-- If a symmetric observation of two independently weighted labels is nearly uniform at
the unordered-pair counting bound, both input laws are close to uniform on the labels.
The estimate holds simultaneously for every event, including when the two laws differ. -/
theorem weighted_stability [Nonempty ι] (p q : PMF ι) (f : ι → ι → G)
    (sym : ∀ i j, f i j=f j i) {m t δ : ℝ} (hm : 0 < m)
    (ht : t ∈ Set.Icc (0:ℝ) 1)
    (cap : t*(Fintype.card ι:ℝ)*(Fintype.card ι+1) ≤ 2*m)
    (h : Diffuse p q f m δ) (T : Finset ι) :
    let ε := 1-t*(1-δ)
    let x := (T.card:ℝ)/Fintype.card ι
    |(mass p T+mass q T)/2-x| ≤ ε ∧ |mass p T-mass q T|^2 ≤ 6*ε ∧
      |mass p T-x| ≤ ε+Real.sqrt (3*ε/2) ∧ |mass q T-x| ≤ ε+Real.sqrt (3*ε/2) := by
  let n := (Fintype.card ι:ℝ)
  have hn : 0 < n := by dsimp [n];exact_mod_cast Fintype.card_pos (α:=ι)
  have cap₁ : t*(n*(n+1)/2) ≤ m := by change t*n*(n+1) ≤ 2*m at cap;nlinarith
  have cap₂ : t*(n*n/2) ≤ m := by nlinarith [mul_nonneg ht.1 hn.le]
  have avg (V : Finset ι) : t*((mass p V+mass q V)/2-δ) ≤ (V.card:ℝ)/n := by
    have count := (event_counts p q f sym hm h V).1
    have z := scale hm (by positivity : 0<n*(n+1)/2) ht.1 cap₁ count (by positivity)
    have eq : (V.card:ℝ)*(n+1)/(n*(n+1)/2) = 2*((V.card:ℝ)/n) := by
      field_simp
    change _ ≤ (V.card:ℝ)*(n+1)/(n*(n+1)/2) at z
    rw [eq] at z
    linarith
  have sub : (Tᶜ.card:ℝ) = n-T.card := by rw [card_compl,Nat.cast_sub (card_le_univ _)]
  have kn : (T.card:ℝ) ≤ n := by dsimp [n];exact_mod_cast card_le_univ T
  have comp := avg Tᶜ
  rw [mass_compl,mass_compl,sub,sub_div,div_self hn.ne'] at comp
  have cut := (event_counts p q f sym hm h T).2
  have z := scale hm (by positivity : 0<n*n/2) ht.1 cap₂ cut
    (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr kn))
  have eq : (T.card:ℝ)*(n-T.card)/(n*n/2) = 2*((T.card:ℝ)/n)*(1-(T.card:ℝ)/n) := by
    field_simp
  change _ ≤ (T.card:ℝ)*(n-T.card)/(n*n/2) at z
  rw [eq] at z
  exact separate_events (mass_Icc p T) (mass_Icc q T)
    ⟨div_nonneg (Nat.cast_nonneg _) hn.le,(div_le_one hn).mpr kn⟩ ht (avg T) (by linarith) z

/-- Law of a symmetric observation, also defined when the observation function is arbitrary. -/
noncomputable def law (p q : PMF ι) (f : ι → ι → G) : PMF G := p.bind (fun i => q.map (f i))

omit [DecidableEq ι] [DecidableEq G] in
private theorem mass_bind (p : PMF ι) (r : ι → PMF G) (E : Finset G) :
    mass (p.bind r) E = ∑ i, (p i).toReal*mass (r i) E := by
  simp only [mass,PMF.bind_apply,tsum_fintype,ENNReal.toReal_sum
    (fun i _ => ENNReal.mul_ne_top (p.apply_ne_top i) ((r i).apply_ne_top _)),ENNReal.toReal_mul,mul_sum]
  exact sum_comm

omit [Fintype ι] [DecidableEq ι] in
private theorem mass_pure (j : G) (E : Finset G) :
    mass (PMF.pure j) E = if j∈E then 1 else 0 := by
  classical
  unfold mass
  by_cases hj : j∈E
  · rw [if_pos hj,sum_eq_single j]
    · simp
    · intro i _ hi;simp [PMF.pure_apply,hi]
    · exact fun h => (h hj).elim
  · rw [if_neg hj]
    exact sum_eq_zero (fun i hi => by
      have ne : i ≠ j := fun e => hj (e ▸ hi);simp [PMF.pure_apply,ne])

omit [DecidableEq ι] in
theorem observed_eq_mass (p q : PMF ι) (f : ι → ι → G) (E : Finset G) :
    observed p q f E = mass (law p q f) E := by
  unfold law
  rw [mass_bind]
  change _ = ∑ i, (p i).toReal*mass (q.bind (fun j => PMF.pure (f i j))) E
  simp_rw [mass_bind,mass_pure,mul_ite,mul_one,mul_zero,mul_sum,mul_ite,mul_zero]
  rfl

omit [DecidableEq ι] in
private theorem observed_compl [Fintype G] (p q : PMF ι) (f : ι → ι → G) (E : Finset G) :
    observed p q f Eᶜ = 1-observed p q f E := by
  rw [observed_eq_mass,mass_compl,observed_eq_mass]

omit [DecidableEq ι] in
/-- On a finite observation space, diffuseness at its cardinality is the usual two-sided
total variation bound from its uniform distribution. -/
theorem diffuse_iff_tv [Fintype G] [Nonempty G] (p q : PMF ι) (f : ι → ι → G) (δ : ℝ) :
    Diffuse p q f (Fintype.card G) δ ↔
      ∀ E : Finset G, |mass (law p q f) E-(E.card:ℝ)/Fintype.card G| ≤ δ := by
  have hg : (Fintype.card G:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro h E
    have hc := h Eᶜ
    rw [observed_compl,card_compl,Nat.cast_sub (card_le_univ _),sub_div,div_self hg] at hc
    rw [←observed_eq_mass]
    exact abs_le.mpr ⟨by linarith,by linarith [h E]⟩
  · intro h E
    rw [observed_eq_mass]
    linarith [(abs_le.mp (h E)).2]

omit [DecidableEq ι] in
private theorem fair_atom [Nonempty ι] (f : ι → ι → G) (z : G) :
    ((law (PMF.uniformOfFintype ι) (PMF.uniformOfFintype ι) f) z).toReal =
      ((univ.filter (fun ij : ι × ι => f ij.1 ij.2=z)).card:ℝ)/(Fintype.card ι:ℝ)^2 := by
  classical
  let n := (Fintype.card ι:ℝ)
  have h := (observed_eq_mass (PMF.uniformOfFintype ι) (PMF.uniformOfFintype ι) f {z}).symm
  simp only [mass,sum_singleton,observed,rect,mem_singleton,PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv,ENNReal.toReal_natCast] at h
  rw [h]
  rw [card_eq_sum_ones,sum_filter,Nat.cast_sum,Fintype.sum_prod_type]
  simp_rw [sum_div]
  apply sum_congr rfl
  intro i _
  exact sum_congr rfl (fun j _ => by by_cases e : f i j = z <;> simp [e,div_eq_mul_inv,pow_two])

omit [DecidableEq ι] in
/-- Two distinct ordered label pairs above every output suffice for nearly flat fair draws
when the square of the label budget is close to twice the observation-space size. -/
theorem fair_of_two [Nonempty ι] [Fintype G] [Nonempty G] (f : ι → ι → G)
    (twice : ∀ z : G, 2 ≤ (univ.filter (fun ij : ι × ι => f ij.1 ij.2=z)).card) :
    Diffuse (PMF.uniformOfFintype ι) (PMF.uniformOfFintype ι) f (Fintype.card G)
      (1-2*(Fintype.card G:ℝ)/(Fintype.card ι:ℝ)^2) := by
  let n := (Fintype.card ι:ℝ)
  let m := (Fintype.card G:ℝ)
  let p := PMF.uniformOfFintype ι
  have hn : 0 < n := by dsimp [n];exact_mod_cast Fintype.card_pos (α:=ι)
  have hm : 0 < m := by dsimp [m];exact_mod_cast Fintype.card_pos (α:=G)
  have lo (E : Finset G) : (E.card:ℝ)*(2/n^2) ≤ observed p p f E := by
    rw [observed_eq_mass]
    change _ ≤ ∑ z ∈ E, _
    calc _ = ∑ _z ∈ E, (2/n^2) := by simp
         _ ≤ _ := sum_le_sum (fun z _ => by
           rw [show p=PMF.uniformOfFintype ι from rfl,fair_atom]
           exact div_le_div_of_nonneg_right (by exact_mod_cast twice z) (sq_nonneg _))
  have total : observed p p f univ = 1 := by rw [observed_eq_mass,mass_univ]
  have all := lo univ
  rw [total,card_univ] at all
  have rate : 2/n^2 ≤ 1/m := (le_div_iff₀ hm).mpr (by change m*(2/n^2) ≤ 1 at all;linarith)
  intro E
  have comp := lo Eᶜ
  rw [observed_compl,card_compl,Nat.cast_sub (card_le_univ _)] at comp
  change (m-E.card)*(2/n^2) ≤ 1-observed p p f E at comp
  change observed p p f E ≤ (E.card:ℝ)/m + (1-2*m/n^2)
  linarith [mul_le_mul_of_nonneg_left rate (Nat.cast_nonneg E.card),
    show (E.card:ℝ)/m=(E.card:ℝ)*(1/m) by ring,
    show 2*m/n^2=m*(2/n^2) by ring]

open Filter Green33StrictReduction Green33ApproximateCovers
open scoped Topology

/-- The residue observed when two labels from the same cyclic seed are added. -/
def cyclicSum {M : ℕ+} (A : Finset (ZMod M)) (i j : A) : ZMod M := (i:ZMod M)+j

/-- Two independently weighted draws from a common optimal-size budget have a sum
approaching the uniform cyclic law in total variation. -/
def WeightedLimit : Prop :=
  ∃ N : ℕ → ℕ+, Tendsto (fun i => (N i).val) atTop atTop ∧
    ∃ A : (i : ℕ) → Finset (ZMod (N i)),
      ∃ (p q : (i : ℕ) → PMF (A i)) (σ δ : ℕ → ℝ),
        Tendsto σ atTop (𝓝 0) ∧ Tendsto δ atTop (𝓝 0) ∧
        ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ Real.sqrt 2+σ i ∧
          Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)

private theorem twice_of_strict {M : ℕ+} {A : Finset (ZMod M)} (cover : StrictCover A) (z : ZMod M) :
    2 ≤ (univ.filter (fun ij : A×A => cyclicSum A ij.1 ij.2=z)).card := by
  obtain ⟨a,ha,b,hb,ne,eq⟩ := cover z
  let i : A := ⟨a,ha⟩
  let j : A := ⟨b,hb⟩
  apply one_lt_card.mpr
  refine ⟨(i,j),mem_filter.mpr ⟨mem_univ _,eq⟩,(j,i),mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩
  · change b+a=z
    rwa [add_comm]
  · exact fun e => ne (congrArg (fun ij : A×A => (ij.1:ZMod M)) e)

private theorem fair_strict {M : ℕ+} {A : Finset (ZMod M)} [Nonempty A] (cover : StrictCover A) :
    Diffuse (PMF.uniformOfFintype A) (PMF.uniformOfFintype A) (cyclicSum A) (M:ℝ)
      (1-2/((A.card:ℝ)/Real.sqrt M)^2) := by
  have h := fair_of_two (cyclicSum A) (twice_of_strict cover)
  simp only [ZMod.card,Fintype.card_coe] at h
  have eq : 2/((A.card:ℝ)/Real.sqrt M)^2 = 2*(M:ℝ)/(A.card:ℝ)^2 := by
    rw [div_pow,Real.sq_sqrt (by positivity)]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rwa [eq]

private theorem missing_bound {M : ℕ+} (A : Finset (ZMod M)) (p q : PMF A) {δ : ℝ}
    (h : Diffuse p q (cyclicSum A) M δ) : ((A+A)ᶜ.card:ℝ)/M ≤ δ := by
  have hit : observed p q (cyclicSum A) (A+A) = 1 := by
    unfold observed
    rw [rect_full,mass_univ,mass_univ,one_mul]
    exact fun i _ j _ => mem_add.mpr ⟨i,i.property,j,j.property,rfl⟩
  have full := h (A+A)
  rw [hit] at full
  have hM : (M:ℝ) ≠ 0 := by exact_mod_cast M.ne_zero
  rw [card_compl,Nat.cast_sub (card_le_univ _),ZMod.card,sub_div,div_self hM]
  linarith

/-- An upper budget alone forces convergence to the counting constant for weighted draws. -/
theorem size_of_weighted_budget {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i)) {σ δ : ℕ → ℝ}
    (hσ : Tendsto σ atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ Real.sqrt 2+σ i)
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)) := by
  let r (i : ℕ) := ((A i).card:ℝ)/Real.sqrt (N i)
  let l (i : ℕ) := ((A i).card:ℝ)/(N i:ℝ)
  have hm (i) : 0 < (N i:ℝ) := by exact_mod_cast (N i).pos
  have top := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
  have hi : Tendsto (fun i => Real.sqrt 2+σ i) atTop (𝓝 (Real.sqrt 2)) := by
    simpa using (tendsto_const_nhds (x:=Real.sqrt 2)).add hσ
  have low : Tendsto l atTop (𝓝 0) := by
    apply squeeze_zero (fun i => div_nonneg (Nat.cast_nonneg _) (hm i).le) _ (hi.div_atTop top)
    intro i
    calc l i = (((A i).card:ℝ)/Real.sqrt (N i))/Real.sqrt (N i) := by
           rw [div_div,←sq,Real.sq_sqrt (hm i).le]
         _ ≤ _ := div_le_div_of_nonneg_right (budget i) (Real.sqrt_nonneg _)
  have lower (i : ℕ) : Real.sqrt (2*(1-δ i)-l i) ≤ r i := by
    have count := (event_counts (p i) (q i) (cyclicSum (A i)) (fun _ _ => add_comm _ _)
      (hm i) (h i) univ).1
    simp only [mass_univ,card_univ,Fintype.card_coe] at count
    apply Real.sqrt_le_iff.mpr ⟨div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _),?_⟩
    change 2*(1-δ i)-((A i).card:ℝ)/(N i:ℝ) ≤ (((A i).card:ℝ)/Real.sqrt (N i))^2
    rw [div_pow,Real.sq_sqrt (hm i).le,le_div_iff₀ (hm i)]
    have cancel := div_mul_cancel₀ ((A i).card:ℝ) (hm i).ne'
    nlinarith
  have lim := (((tendsto_const_nhds (x:=(2:ℝ))).mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hδ)).sub low).sqrt
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le _ hi lower budget
  simpa using lim

/-- The weighted formulation is equivalent to the literal limiting statement in Green 33. -/
theorem green_iff_weighted : (type_of% Green33.green_33) ↔ WeightedLimit := by
  change OrdinaryLimit ↔ WeightedLimit
  constructor
  · intro green
    have strict := ordinary_iff_strict.mp green
    have W (i : ℕ) : ∃ N : ℕ+, i ≤ N.val ∧ ∃ A : Finset (ZMod N), StrictCover A ∧
        |(A.card:ℝ)/Real.sqrt N-Real.sqrt 2| < 1/((i:ℝ)+1) := by
      obtain ⟨N,hN,A,hA,he⟩ := frequently_atTop.mp (strict (1/((i:ℝ)+1)) (by positivity)) (Nat.succPNat i)
      exact ⟨N,(Nat.le_succ i).trans hN,A,hA,he⟩
    choose N large A cover close using W
    have size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)) := by
      apply (tendsto_iff_dist_tendsto_zero).mpr
      simpa only [Real.dist_eq] using squeeze_zero (fun i => abs_nonneg _)
        (fun i => (close i).le) tendsto_one_div_add_atTop_nhds_zero_nat
    have inhabited (i : ℕ) : Nonempty (A i) := by
      obtain ⟨a,ha,_⟩ := cover i 0
      exact ⟨⟨a,ha⟩⟩
    let p (i : ℕ) : PMF (A i) := @PMF.uniformOfFintype _ _ (inhabited i)
    let δ (i : ℕ) : ℝ := 1-2/(((A i).card:ℝ)/Real.sqrt (N i))^2
    refine ⟨N,tendsto_atTop_mono large tendsto_id,A,p,p,(fun i => ((A i).card:ℝ)/Real.sqrt (N i)-Real.sqrt 2),δ,?_,?_,?_⟩
    · simpa using size.sub (tendsto_const_nhds (x:=Real.sqrt 2))
    · have h := tendsto_const_nhds (x:=(1:ℝ)) |>.sub ((tendsto_const_nhds (x:=(2:ℝ))).div
          (size.pow 2) (by positivity))
      simpa [δ,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] using h
    · intro i
      let _ := inhabited i
      exact ⟨by dsimp;linarith,fair_strict (cover i)⟩
  · rintro ⟨N,big,A,p,q,σ,δ,hσ,hδ,h⟩
    have size := size_of_weighted_budget big A p q hσ hδ (fun i => (h i).1) (fun i => (h i).2)
    apply (green_iff_approximate false).mpr
    refine ⟨N,big,A,size,squeeze_zero (fun i => by positivity) (fun i => ?_) hδ⟩
    exact missing_bound (A i) (p i) (q i) (h i).2

/-- On every asymptotically optimal sequence with vanishing output error, both weighted
draws converge to the uniform law on their common seed in total variation. -/
theorem uniform_weights_of_critical_budget {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i)))
    (p q : (i : ℕ) → PMF (A i)) {σ δ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ Real.sqrt 2+σ i)
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ T : Finset (A i),
      |mass (p i) T-(T.card:ℝ)/(A i).card| < η ∧ |mass (q i) T-(T.card:ℝ)/(A i).card| < η := by
  have size := size_of_weighted_budget big A p q hσ hδ budget h
  let k (i : ℕ) := ((A i).card:ℝ)
  have mpos (i) : 0 < (N i:ℝ) := by exact_mod_cast (N i).pos
  have ne (i) : Nonempty (A i) := (p i).support_nonempty.to_type
  have kpos (i) : 0 < k i := by
    let _ := ne i
    have hn := Fintype.card_pos (α:=A i)
    rw [Fintype.card_coe] at hn
    dsimp [k]
    exact_mod_cast hn
  have low : Tendsto (fun i => k i/(N i:ℝ)) atTop (𝓝 0) := by
    have hr := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
    apply (size.div_atTop hr).congr
    intro i
    change k i/Real.sqrt (N i)/Real.sqrt (N i)=_
    rw [div_div,←sq,Real.sq_sqrt (mpos i).le]
  let u (i : ℕ) := k i*(k i+1)/(N i:ℝ)
  have limit : Tendsto u atTop (𝓝 2) := by
    have lim := (size.pow 2).add low
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),add_zero] at lim
    apply lim.congr
    intro i
    change (k i/Real.sqrt (N i))^2+k i/(N i:ℝ) = u i
    rw [div_pow,Real.sq_sqrt (mpos i).le]
    dsimp [u]
    ring
  let t (i : ℕ) := min 1 (2/u i)
  have tend : Tendsto t atTop (𝓝 1) := by
    have hl := (tendsto_const_nhds (x:=(1:ℝ))).min ((tendsto_const_nhds (x:=(2:ℝ))).div limit (by norm_num))
    simpa [t] using hl
  let e (i : ℕ) := 1-t i*(1-δ i)
  have he : Tendsto e atTop (𝓝 0) := by
    have hl := (tendsto_const_nhds (x:=(1:ℝ))).sub (tend.mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hδ))
    simpa [e] using hl
  have finalBound : Tendsto (fun i => e i+Real.sqrt (3*e i/2)) atTop (𝓝 0) := by
    have hl := he.add (((tendsto_const_nhds (x:=(3:ℝ))).mul he).div_const 2).sqrt
    simpa using hl
  intro η hη
  filter_upwards [finalBound.eventually_lt_const hη] with i small
  have up : 0 < u i := div_pos (mul_pos (kpos i) (by linarith [kpos i])) (mpos i)
  have range : t i ∈ Set.Icc (0:ℝ) 1 := ⟨le_min zero_le_one (div_nonneg (by norm_num) up.le),min_le_left _ _⟩
  have cap : t i*k i*(k i+1) ≤ 2*(N i:ℝ) := by
    have hcap := (le_div_iff₀ up).mp (show t i ≤ 2/u i from min_le_right _ _)
    calc t i*k i*(k i+1) = (t i*u i)*(N i:ℝ) := by dsimp [u];field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_right hcap (mpos i).le
  let _ := ne i
  intro T
  have bound := weighted_stability (p i) (q i) (cyclicSum (A i)) (fun _ _ => add_comm _ _)
    (mpos i) range (by simpa only [Fintype.card_coe] using cap) (h i) T
  simp only [Fintype.card_coe] at bound
  exact ⟨lt_of_le_of_lt bound.2.2.1 small,lt_of_le_of_lt bound.2.2.2 small⟩

#print axioms weighted_stability
#print axioms observed_eq_mass
#print axioms diffuse_iff_tv
#print axioms fair_of_two
#print axioms green_iff_weighted
#print axioms size_of_weighted_budget
#print axioms uniform_weights_of_critical_budget
end Green33WeightedStability
