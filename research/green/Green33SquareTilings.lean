import Green33WeightedPeaks

/-! Rigidity of two probability laws attaining the square-order common support bound. -/

open Finset Green33WeightedStability Green33WeightedPeaks

namespace Green33SquareTilings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A full set of saturated atoms exhausts the mass. -/
private lemma fair_of_card (f : ι → ℝ) (k : ℕ) (nonneg : ∀ i, 0≤f i)
    (total : ∑ i, f i=k) (S : Finset ι) (hs : ∀ i ∈ S, f i=1) (card : S.card=k) :
    ∀ i, f i=if i∈S then 1 else 0 := by
  classical
  have massS : ∑ i ∈ S, f i=k := by
    rw [sum_congr rfl hs];simp [card]
  have rem := sum_sdiff (f:=f) (subset_univ S)
  have zero : ∑ i ∈ univ\S, f i=0 := by linarith
  intro i
  by_cases h : i∈S
  · simpa [h] using hs i h
  · rw [if_neg h]
    apply (sum_eq_zero_iff_of_nonneg (fun j _ => nonneg j)).mp zero
    simp [h]

/-- On a set of 2k−1 labels, two unit-capped weight vectors each of total
mass k cannot together saturate every label unless one is a fair k-set. -/
theorem saturation (k : ℕ) (size : Fintype.card ι+1=2*k) (f g : ι → ℝ)
    (hf : ∀ i, 0≤f i ∧ f i≤1) (hg : ∀ i, 0≤g i ∧ g i≤1)
    (sf : ∑ i, f i=k) (sg : ∑ i, g i=k) (cover : ∀ i, f i=1 ∨ g i=1) :
    ∃ S : Finset ι, S.card=k ∧
      ((∀ i, f i=if i∈S then 1 else 0) ∧ (∀ i ∉ S, g i=1) ∨
       (∀ i, g i=if i∈S then 1 else 0) ∧ (∀ i ∉ S, f i=1)) := by
  classical
  let A := univ.filter fun i => f i=1
  let B := univ.filter fun i => g i=1
  have memA (i) : i∈A ↔ f i=1 := by simp [A]
  have memB (i) : i∈B ↔ g i=1 := by simp [B]
  have cap (w : ι → ℝ) (h : ∀ i, 0≤w i) (t : ∑ i, w i=k) (U : Finset ι)
      (u : ∀ i ∈ U, w i=1) : U.card≤k := by
    have e := sum_le_sum_of_subset_of_nonneg (f:=w) (subset_univ U) (fun i _ _ => h i)
    rw [sum_congr rfl u,t] at e
    simpa using e
  have a := cap f (fun i => (hf i).1) sf A fun i hi => (memA i).mp hi
  have b := cap g (fun i => (hg i).1) sg B fun i hi => (memB i).mp hi
  have u : A∪B=univ := by ext i; simpa only [mem_union,memA,memB,mem_univ,iff_true] using cover i
  have card := card_union_le A B
  rw [u,card_univ] at card
  by_cases eq : A.card=k
  · refine ⟨A,eq,Or.inl ⟨fair_of_card f k (fun i => (hf i).1) sf A (fun i hi => (memA i).mp hi) eq,?_⟩⟩
    exact fun i hi => (cover i).resolve_left (mt (memA i).mpr hi)
  · have eb : B.card=k := by omega
    refine ⟨B,eb,Or.inr ⟨fair_of_card g k (fun i => (hg i).1) sg B (fun i hi => (memB i).mp hi) eb,?_⟩⟩
    exact fun i hi => (cover i).resolve_right (mt (memB i).mpr hi)

omit [DecidableEq ι] in
/-- Equality in the common support count fixes both normalized caps at one
and saturates one cap at each label. -/
private lemma caps_at_equality (k : ℕ) (hk : 0<k) (size : Fintype.card ι+1=2*k)
    (f g : ι → ℝ) (sf : ∑ i, f i=k) (sg : ∑ i, g i=k)
    (diag : ∑ i, f i*g i ≤ 1) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (ab : a*b=1) (capF : ∀ i, f i≤a) (capG : ∀ i, g i≤b) :
    a=1 ∧ b=1 ∧ ∀ i, f i=1 ∨ g i=1 := by
  have nonneg (i) : 0≤(a-f i)*(b-g i) :=
    mul_nonneg (sub_nonneg.mpr (capF i)) (sub_nonneg.mpr (capG i))
  have count := sum_nonneg (s:=univ) (fun i _ => nonneg i)
  have term (i) : (a-f i)*(b-g i)=a*b-b*f i-a*g i+f i*g i := by ring
  have expr : ∑ i, (a-f i)*(b-g i)=(Fintype.card ι:ℝ)-(a+b)*k+∑ i,f i*g i := by
    simp only [term,sum_add_distrib,sum_sub_distrib,← mul_sum,ab,sf,sg,sum_const,card_univ,nsmul_eq_mul,mul_one]
    ring
  have card : (Fintype.card ι:ℝ)+1=2*k := by exact_mod_cast size
  have pos : (0:ℝ)<k := by exact_mod_cast hk
  have small : a+b≤2 := by
    by_contra! big; nlinarith [mul_pos (sub_pos.mpr big) pos]
  have eq : a=b := by
    have h := mul_self_le_mul_self (add_nonneg ha.le hb.le) small
    nlinarith [sq_nonneg (a-b)]
  have a1 : a=1 := by nlinarith [eq]
  have b1 := eq.symm.trans a1
  have zero : ∑ i, (a-f i)*(b-g i)=0 := by nlinarith [a1,b1]
  refine ⟨a1,b1,fun i => ?_⟩
  have z := (sum_eq_zero_iff_of_nonneg (fun j _ => nonneg j)).mp zero i (mem_univ _)
  rcases mul_eq_zero.mp z with z|z
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- The overlap and entrywise bounds force one fair input and fix the
opposite input off its support. All weights are scaled by k. -/
theorem fair_of_caps (k : ℕ) (hk : 0<k) (size : Fintype.card ι+1=2*k)
    (f g : ι → ℝ) (hf : ∀ i, 0≤f i) (hg : ∀ i, 0≤g i)
    (sf : ∑ i, f i=k) (sg : ∑ i, g i=k) (diag : ∑ i, f i*g i ≤ 1)
    {a b : ℝ} (ha : 0<a) (hb : 0<b) (ab : a*b=1)
    (capF : ∀ i, f i≤a) (capG : ∀ i, g i≤b) :
    ∃ S : Finset ι, S.card=k ∧
      ((∀ i, f i=if i∈S then 1 else 0) ∧ (∀ i ∉ S, g i=1) ∨
       (∀ i, g i=if i∈S then 1 else 0) ∧ (∀ i ∉ S, f i=1)) := by
  obtain ⟨rfl,rfl,cover⟩ := caps_at_equality k hk size f g sf sg diag a b ha hb ab capF capG
  exact saturation k size f g (fun i => ⟨hf i,capF i⟩) (fun i => ⟨hg i,capG i⟩) sf sg cover

section Output
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private noncomputable def fiber (l : ι → G) (f g : ι → ℝ) (z : G) : ℝ :=
  ∑ u : ι×ι, if l u.1+l u.2=z then f u.1*g u.2 else 0

omit [DecidableEq ι] [Fintype G] in
private lemma scaled_fiber (l : ι → G) (p q : PMF ι) (k : ℕ) (z : G) :
    fiber l (fun i => k*(p i).toReal) (fun i => k*(q i).toReal) z =
      (k:ℝ)^2*((law p q (fun i j => l i+l j)) z).toReal := by
  have atom := (observed_eq_mass p q (fun i j => l i+l j) {z}).symm
  simp only [mass,sum_singleton] at atom
  rw [atom]
  change _=(k:ℝ)^2*∑ i, ∑ j, if l i+l j∈({z}:Finset G) then (p i).toReal*(q j).toReal else 0
  simp only [fiber,Fintype.sum_prod_type,mem_singleton,mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  split <;> ring

omit [DecidableEq ι] in
private lemma total_scaled (p : PMF ι) (k : ℕ) : ∑ i, (k:ℝ)*(p i).toReal=k := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype,ENNReal.toReal_sum (fun i _ => p.apply_ne_top i),ENNReal.toReal_one] at h
  rw [← mul_sum,h,mul_one]

private lemma normalized_fair (k : ℕ) (hk : 0<k) (groupSize : Fintype.card G=k^2)
    (size : Fintype.card ι+1=2*k) (p q : PMF ι) (l : ι → G)
    (flat : ∀ z, ((law p q (fun i j => l i+l j)) z).toReal=(Fintype.card G:ℝ)⁻¹) :
    ∃ S : Finset ι, S.card=k ∧
      ((∀ i, (k:ℝ)*(p i).toReal=if i∈S then 1 else 0) ∧ (∀ i ∉ S, (k:ℝ)*(q i).toReal=1) ∨
       (∀ i, (k:ℝ)*(q i).toReal=if i∈S then 1 else 0) ∧ (∀ i ∉ S, (k:ℝ)*(p i).toReal=1)) := by
  obtain ⟨a,b,ha,hb,prod,capP,capQ,diag⟩ := exact_atom_caps p q l flat
  have pos : (0:ℝ)<k := by exact_mod_cast hk
  have scale : (k:ℝ)^2*(Fintype.card G:ℝ)⁻¹=1 := by rw [groupSize,Nat.cast_pow,mul_inv_cancel₀ (by positivity)]
  refine fair_of_caps k hk size _ _ (fun i => by positivity) (fun i => by positivity)
    (total_scaled p k) (total_scaled q k) ?_ (mul_pos pos ha) (mul_pos pos hb) ?_
    (fun i => mul_le_mul_of_nonneg_left (capP i) pos.le) (fun i => mul_le_mul_of_nonneg_left (capQ i) pos.le)
  · calc ∑ i, ((k:ℝ)*(p i).toReal)*(k*(q i).toReal) =
          (k:ℝ)^2*∑ i, (p i).toReal*(q i).toReal := by
            rw [mul_sum]; apply sum_congr rfl;intro i _;ring
         _ ≤ _ := (mul_le_mul_of_nonneg_left diag (sq_nonneg (k:ℝ))).trans_eq scale
  · calc ((k:ℝ)*a)*(k*b) = (k:ℝ)^2*(a*b) := by ring
         _ = _ := by rw [prod,scale]

/-- A completion uses the outside labels and one extra label from the tile. -/
def completion (S : Finset ι) (t : ι) := insert t (univ \ S)

/-- The two finite sets represent every group element exactly once. -/
def Tiles (l : ι → G) (S T : Finset ι) := Function.Bijective
  (fun u : S×T => l u.1+l u.2)

omit [DecidableEq ι] [Fintype G] in
private lemma collision (l : ι → G) (f g : ι → ℝ) (hf : ∀ i, 0≤f i) (hg : ∀ i, 0≤g i)
    {u v : ι×ι} (ne : u≠v) (eq : l u.1+l u.2=l v.1+l v.2) :
    f u.1*g u.2+f v.1*g v.2 ≤ fiber l f g (l v.1+l v.2) := by
  classical
  let w (x : ι×ι) := if l x.1+l x.2=l v.1+l v.2 then f x.1*g x.2 else 0
  have h := sum_le_sum_of_subset_of_nonneg (f:=w) (subset_univ ({u,v}:Finset _))
    (fun x _ _ => by dsimp [w];split <;> first | exact mul_nonneg (hf _) (hg _) | exact le_rfl)
  simpa only [sum_insert (notMem_singleton.mpr ne),sum_singleton,w,eq,ite_true,fiber] using h

private lemma tile_of_weights (k : ℕ) (groupSize : Fintype.card G=k^2)
    (size : Fintype.card ι+1=2*k) (l : ι → G) (inj : Function.Injective l)
    (f g : ι → ℝ) (hf : ∀ i, 0≤f i) (hg : ∀ i, 0≤g i)
    (flat : ∀ z, fiber l f g z=1) (S : Finset ι) (card : S.card=k)
    (fair : ∀ i, f i=if i∈S then 1 else 0) (outside : ∀ i ∉ S, g i=1)
    (t : ι) (inside : t∈S) (pos : 0<g t) : Tiles l S (completion S t) := by
  classical
  let T := completion S t
  have sz : T.card=k := by
    have h : t∉univ\S := by simp [inside]
    dsimp [T,completion]
    rw [card_insert_of_notMem h,card_sdiff_of_subset (subset_univ S),card_univ,card]
    omega
  have unit (j : T) (h : (j:ι)≠t) : g j=1 := by
    have mem := j.property
    change (j:ι)∈insert t (univ\S) at mem
    exact outside j (mem_sdiff.mp ((mem_insert.mp mem).resolve_left h)).2
  have positive (j : T) : 0<g j := by
    by_cases e : (j:ι)=t
    · simpa only [e] using pos
    · rw [unit j e];norm_num
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,by simp [Fintype.card_prod,sz,card,groupSize,T,pow_two]⟩
  rintro ⟨i,j⟩ ⟨i',j'⟩ eq
  change l i+l j=l i'+l j' at eq
  by_cases e : (j:ι)=j'
  · have h : (i:ι)=i' := inj (add_right_cancel (e ▸ eq))
    exact Prod.ext (Subtype.ext h) (Subtype.ext e)
  have ne : ((i:ι),(j:ι))≠((i':ι),(j':ι)) := fun h => e (congrArg Prod.snd h)
  have bound := collision l f g hf hg ne eq
  change f i*g j+f i'*g j'≤fiber l f g _ at bound
  rw [flat,fair,fair,if_pos i.property,if_pos i'.property,one_mul,one_mul] at bound
  by_cases et : (j:ι)=t
  · have other : (j':ι)≠t := fun h => e (et.trans h.symm)
    rw [unit j' other] at bound
    linarith [positive j]
  · rw [unit j et] at bound
    linarith [positive j']

omit [DecidableEq ι] [Fintype G] in
private lemma swap_fiber (l : ι → G) (f g : ι → ℝ) (z : G) :
    fiber l f g z=fiber l g f z := by
  apply Fintype.sum_equiv (Equiv.prodComm ι ι)
  intro x; simp [add_comm,mul_comm]

/-- All scaled mass outside the fair tile is one per label. The single unit
inside is a mixture of labels that each give a tiling completion. -/
structure TilingMixture (k : ℕ) (l : ι → G) (S : Finset ι) (f g : ι → ℝ) : Prop where
  card : S.card=k
  fair : ∀ i, f i=if i∈S then 1 else 0
  outside : ∀ i ∉ S, g i=1
  inside : ∑ i ∈ S, g i=1
  tiles : ∀ t ∈ S, 0<g t → Tiles l S (completion S t)

private lemma mixture_of_fair (k : ℕ) (groupSize : Fintype.card G=k^2)
    (size : Fintype.card ι+1=2*k) (l : ι → G) (inj : Function.Injective l)
    (f g : ι → ℝ) (hf : ∀ i, 0≤f i) (hg : ∀ i, 0≤g i) (mass : ∑ i,g i=k)
    (flat : ∀ z, fiber l f g z=1) (S : Finset ι) (card : S.card=k)
    (fair : ∀ i, f i=if i∈S then 1 else 0) (out : ∀ i ∉ S, g i=1) :
    TilingMixture k l S f g := by
  have outside : ∑ i ∈ univ\S,g i = (k:ℝ)-1 := by
    have cnt : (univ\S).card+1=k := by
      rw [card_sdiff_of_subset (subset_univ S),card_univ,card];omega
    have terms : ∀ i ∈ univ\S,g i=1 := fun i hi => out i (mem_sdiff.mp hi).2
    rw [sum_congr rfl terms,sum_const,nsmul_eq_mul,mul_one]
    have cast : ((univ\S).card:ℝ)+1=k := by exact_mod_cast cnt
    linarith
  have rem := sum_sdiff (f:=g) (subset_univ S)
  refine ⟨card,fair,out,by linarith,?_⟩
  exact tile_of_weights k groupSize size l inj f g hf hg flat S card fair out

omit [Fintype G] in
private lemma tiled_fiber (l : ι → G) (S T : Finset ι) (tile : Tiles l S T) (z : G) :
    fiber l (fun i => if i∈S then 1 else 0) (fun i => if i∈T then 1 else 0) z=1 := by
  obtain ⟨⟨i,j⟩,eq⟩ := tile.surjective z
  change l i+l j=z at eq
  rw [fiber,sum_eq_single ((i:ι),(j:ι))]
  · simp [eq,i.property,j.property]
  · rintro ⟨a,b⟩ _ ne
    by_cases ha : a∈S <;> by_cases hb : b∈T <;> simp [ha,hb]
    intro eq'
    have pr := tile.injective (a₁ := ((⟨a,ha⟩:S),(⟨b,hb⟩:T))) (a₂ := (i,j)) (eq'.trans eq.symm)
    exact ne (congrArg (fun x : S×T => ((x.1:ι),(x.2:ι))) pr)
  · simp

omit [Fintype G] [DecidableEq G] in
/-- The second vector is the specified mixture of indicator functions of
tiling complements. The normalized mixture coefficients sum to one. -/
theorem TilingMixture.weights {k : ℕ} {l : ι → G} {S : Finset ι} {f g : ι → ℝ}
    (h : TilingMixture k l S f g) (j : ι) :
    g j=∑ t ∈ S, g t*(if j∈completion S t then 1 else 0) := by
  classical
  by_cases hj : j∈S
  · simp [completion,hj,mul_ite]
  · simpa [completion,hj] using (h.outside j hj).trans h.inside.symm

omit [Fintype G] in
private lemma mixture_fiber {k : ℕ} {l : ι → G} {S : Finset ι} {f g : ι → ℝ}
    (h : TilingMixture k l S f g) (hg : ∀ i, 0≤g i) (z : G) : fiber l f g z=1 := by
  classical
  let W (t j : ι) : ℝ := if j∈completion S t then 1 else 0
  have fd : fiber l f g z=∑ t ∈ S, g t*fiber l f (W t) z := by
    simp only [fiber,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro u _
    rw [h.weights u.2]
    by_cases eq : l u.1+l u.2=z
    · simp only [eq,ite_true,mul_sum,W]
      apply sum_congr rfl;intro i _;ring
    · simp [eq]
  rw [fd,← h.inside]
  apply sum_congr rfl;intro t ht
  by_cases pos : 0<g t
  · have e := tiled_fiber l S (completion S t) (h.tiles t ht pos) z
    rw [show f=(fun i => if i∈S then 1 else 0) from funext h.fair]
    exact (congrArg (g t*·) e).trans (mul_one _)
  · rw [le_antisymm (le_of_not_gt pos) (hg t),zero_mul]

omit [DecidableEq ι] in
private lemma injective_of_flat (k : ℕ) (groupSize : Fintype.card G=k^2)
    (size : Fintype.card ι+1=2*k) (p q : PMF ι) (l : ι → G)
    (flat : ∀ z, ((law p q (fun i j => l i+l j)) z).toReal=(Fintype.card G:ℝ)⁻¹) :
    Function.Injective l := by
  classical
  let J := univ.image l
  let m (i : ι) : J := ⟨l i,mem_image_of_mem _ (mem_univ _)⟩
  have push : law (p.map m) (q.map m) (fun i j : J => (i:G)+j)=law p q (fun i j => l i+l j) := by
    simp only [law,PMF.bind_map,Function.comp_def,PMF.map_comp,m]
  have low := exact_uniform_budget (p.map m) (q.map m) (fun i : J => (i:G)) (fun z => push ▸ flat z)
  rw [groupSize,Nat.cast_pow,Real.sqrt_sq (by positivity),Fintype.card_coe] at low
  have sz : (Fintype.card ι:ℝ)+1=2*k := by exact_mod_cast size
  have rev : Fintype.card ι≤J.card := by exact_mod_cast (show (Fintype.card ι:ℝ)≤J.card by linarith)
  have eq : (univ.image l).card=(univ : Finset ι).card := le_antisymm card_image_le (by simpa only [card_univ] using rev)
  simpa only [coe_univ,Set.injOn_univ] using card_image_iff.mp eq

/-- Classification of all independent real input laws attaining the minimum
common label count at square order in finite abelian groups. -/
theorem flat_iff_tiling_mixture (k : ℕ) (hk : 0<k) (groupSize : Fintype.card G=k^2)
    (size : Fintype.card ι+1=2*k) (p q : PMF ι) (l : ι → G) :
    (∀ z, ((law p q (fun i j => l i+l j)) z).toReal=(Fintype.card G:ℝ)⁻¹) ↔
    ∃ S : Finset ι, TilingMixture k l S (fun i => k*(p i).toReal) (fun i => k*(q i).toReal) ∨
      TilingMixture k l S (fun i => k*(q i).toReal) (fun i => k*(p i).toReal) := by
  let f i := (k:ℝ)*(p i).toReal
  let g i := (k:ℝ)*(q i).toReal
  have hf (i) : 0≤f i := by dsimp [f]; positivity
  have hg (i) : 0≤g i := by dsimp [g]; positivity
  have card : (Fintype.card G:ℝ)=(k:ℝ)^2 := by exact_mod_cast groupSize
  have pos : (0:ℝ)<k := by exact_mod_cast hk
  constructor
  · intro lawEq
    have inj := injective_of_flat k groupSize size p q l lawEq
    obtain ⟨S,sz,alts⟩ := normalized_fair k hk groupSize size p q l lawEq
    have z (x) : fiber l f g x=1 := by
      rw [show fiber l f g x=_ from scaled_fiber l p q k x,lawEq,card,mul_inv_cancel₀ (by positivity)]
    refine ⟨S,?_⟩
    rcases alts with ⟨fair,out⟩|⟨fair,out⟩
    · exact Or.inl (mixture_of_fair k groupSize size l inj f g hf hg (total_scaled q k) z S sz fair out)
    · exact Or.inr (mixture_of_fair k groupSize size l inj g f hg hf (total_scaled p k)
        (fun x => (swap_fiber l g f x).trans (z x)) S sz fair out)
  · rintro ⟨S,h|h⟩ x
    all_goals
      have flat : fiber l f g x=1 := by
        first | exact mixture_fiber h hg x | exact (swap_fiber l f g x).trans (mixture_fiber h hf x)
      rw [show fiber l f g x=_ from scaled_fiber l p q k x] at flat
      rw [card,← one_div,eq_div_iff (by positivity)]
      linarith

/-- The translate of the fair tile contributed by one completion label. -/
def translate (l : ι → G) (S : Finset ι) (t : ι) : Finset G :=
  S.image fun i => l i+l t

omit [Fintype G] in
private lemma translate_subset (l : ι → G) (S : Finset ι) {t u : ι} (ht : t∈S)
    (T : Tiles l S (completion S t)) (U : Tiles l S (completion S u)) :
    translate l S t ⊆ translate l S u := by
  intro z hz
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
  obtain ⟨⟨b,c⟩,e⟩ := U.surjective (l a+l t)
  change l b+l c=l a+l t at e
  by_cases h : (c:ι)=u
  · exact mem_image.mpr ⟨b,b.property,by simpa only [h] using e⟩
  obtain out := (mem_insert.mp c.property).resolve_left h
  let c' : completion S t := ⟨c,mem_insert_of_mem out⟩
  let t' : completion S t := ⟨t,mem_insert_self _ _⟩
  have pr := T.injective (a₁ := (b,c')) (a₂ := ((⟨a,ha⟩:S),t')) e
  have ce : (c:ι)=t := congrArg (fun x : S×completion S t => (x.2:ι)) pr
  exact False.elim ((mem_sdiff.mp out).2 (ce ▸ ht))

/-- Once one completion tiles, replacing its inside label works exactly when
the fair tile has the same translate. Equivalently the replacement labels
belong to one coset of the translation stabilizer. -/
theorem completion_iff_translate (l : ι → G) (S : Finset ι) {t u : ι} (ht : t∈S) (hu : u∈S)
    (T : Tiles l S (completion S t)) :
    Tiles l S (completion S u) ↔ translate l S u=translate l S t := by
  constructor
  · intro U
    exact Subset.antisymm (translate_subset l S hu U T) (translate_subset l S ht T U)
  intro same
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro z
    obtain ⟨⟨a,b⟩,e⟩ := T.surjective z
    change l a+l b=z at e
    by_cases eq : (b:ι)=t
    · have zin : z∈translate l S t := mem_image.mpr ⟨a,a.property,by simpa only [eq] using e⟩
      rw [← same] at zin
      obtain ⟨c,hc,eq'⟩ := mem_image.mp zin
      exact ⟨(⟨c,hc⟩,⟨u,mem_insert_self _ _⟩),eq'⟩
    · have out := (mem_insert.mp b.property).resolve_left eq
      exact ⟨(a,⟨b,mem_insert_of_mem out⟩),e⟩
  · have card := Fintype.card_of_bijective T
    change Fintype.card (S×completion S t)=Fintype.card G at card
    have sz (j : ι) (hj : j∈S) : (completion S j).card=(univ\S).card+1 := by
      exact card_insert_of_notMem (by simpa using hj)
    simpa only [Fintype.card_prod,Fintype.card_coe,sz t ht,sz u hu] using card

/-- A positive inside label always exists, so every extremal weighted seed
contains a balanced direct tiling on the same labels. -/
theorem TilingMixture.exists_completion {k : ℕ} {l : ι → G} {S : Finset ι} {f g : ι → ℝ}
    (h : TilingMixture k l S f g) :
    ∃ t∈S, 0<g t ∧ Tiles l S (completion S t) ∧
      ∀ u∈S, 0<g u → translate l S u=translate l S t := by
  have ex : ∃ t∈S,0<g t := by
    by_contra! none
    have := sum_nonpos none
    linarith [h.inside]
  obtain ⟨t,ht,pos⟩ := ex
  have til := h.tiles t ht pos
  exact ⟨t,ht,pos,til,fun u hu ok => (completion_iff_translate l S ht hu til).mp (h.tiles u hu ok)⟩

/-- For an aperiodic fair tile the other marginal is itself fair on a
single tiling complement. -/
theorem TilingMixture.fair_of_distinct_translates {k : ℕ} {l : ι → G} {S : Finset ι} {f g : ι → ℝ}
    (h : TilingMixture k l S f g) (hg : ∀ i, 0≤g i)
    (aper : Set.InjOn (translate l S) (S : Set ι)) :
    ∃ t∈S, Tiles l S (completion S t) ∧
      ∀ j, g j=if j∈completion S t then 1 else 0 := by
  obtain ⟨t,ht,_,til,same⟩ := h.exists_completion
  have zero (i : ι) (hi : i∈S) (ne : i≠t) : g i=0 := by
    by_contra! nz
    exact ne (aper hi ht (same i hi (lt_of_le_of_ne (hg i) (Ne.symm nz))))
  have one : g t=1 := by
    have total := h.inside
    rwa [sum_eq_single_of_mem t ht zero] at total
  refine ⟨t,ht,til,fun j => ?_⟩
  by_cases e : j=t
  · subst j;simpa [completion] using one
  by_cases hj : j∈S
  · simpa [completion,e,hj] using zero j hj e
  · simpa [completion,e,hj] using h.outside j hj

/-- At minimum common size, real probabilities give no additional label
sets beyond those admitting a direct tiling by two k-sets. -/
theorem exists_flat_iff_tiles (k : ℕ) (hk : 0<k) (groupSize : Fintype.card G=k^2)
    (size : Fintype.card ι+1=2*k) (l : ι → G) :
    (∃ p q : PMF ι, ∀ z, ((law p q (fun i j => l i+l j)) z).toReal=(Fintype.card G:ℝ)⁻¹) ↔
    ∃ S T : Finset ι, S.card=k ∧ T.card=k ∧ Tiles l S T := by
  classical
  constructor
  · rintro ⟨p,q,flat⟩
    obtain ⟨S,h|h⟩ := (flat_iff_tiling_mixture k hk groupSize size p q l).mp flat
    all_goals
      obtain ⟨t,ht,_,tile,_⟩ := h.exists_completion
      have cnt : (completion S t).card=k := by
        rw [completion,card_insert_of_notMem (by simpa using ht),card_sdiff_of_subset (subset_univ S),card_univ,h.card]
        omega
      exact ⟨S,completion S t,h.card,cnt,tile⟩
  · rintro ⟨S,T,cs,ct,tile⟩
    have ns := card_pos.mp (cs ▸ hk)
    have nt := card_pos.mp (ct ▸ hk)
    refine ⟨PMF.uniformOfFinset S ns,PMF.uniformOfFinset T nt,fun z => ?_⟩
    have mass (U : Finset ι) (u : U.Nonempty) (cu : U.card=k) (i : ι) :
        (k:ℝ)*((PMF.uniformOfFinset U u) i).toReal=if i∈U then 1 else 0 := by
      by_cases h : i∈U
      · simp [PMF.uniformOfFinset_apply_of_mem _ h,h,cu,ENNReal.toReal_inv,hk.ne']
      · simp [PMF.uniformOfFinset_apply_of_notMem _ h,h]
    have f := scaled_fiber l (PMF.uniformOfFinset S ns) (PMF.uniformOfFinset T nt) k z
    simp only [mass S ns cs,mass T nt ct,tiled_fiber l S T tile z] at f
    have pos : (0:ℝ)<k := by exact_mod_cast hk
    rw [groupSize,Nat.cast_pow,← one_div,eq_div_iff (by positivity)]
    linarith
end Output

#print axioms saturation
#print axioms fair_of_caps
#print axioms TilingMixture.weights
#print axioms flat_iff_tiling_mixture
#print axioms completion_iff_translate
#print axioms TilingMixture.exists_completion
#print axioms TilingMixture.fair_of_distinct_translates
#print axioms exists_flat_iff_tiles
end Green33SquareTilings
