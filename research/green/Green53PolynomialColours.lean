import Green52CubicTransversals
/-!
# Common popular differences in cubic colour classes

A nonempty fibre of a cubic map on a binary cube meets every translate of a small set.
Apply the cubic horizontal theorem to all corresponding translates simultaneously. Subadditivity
of additive degree then bounds the number of representations of every realized difference.
-/
open Finset
open scoped Pointwise
namespace Green53PolynomialColours
local notation "𝔽" => ZMod 2
variable {U : Type*} [AddCommGroup U]

/-- Additive degree bounded by d, measured by successive mixed forward differences. -/
def Degree : ℕ → (U → 𝔽) → Prop
  | 0,F => ∀ x, F x = F 0
  | n+1,F => ∀ a, Degree n (fwdDiff a F)

private theorem degree_const (d : ℕ) (z : 𝔽) : Degree (U:=U) d (fun _ => z) := by
  induction d generalizing z with
  | zero => intro x; rfl
  | succ d ih => intro a; rw [fwdDiff_const]; exact ih 0

private theorem degree_add {i : ℕ} {f g : U → 𝔽} (hf : Degree i f) (hg : Degree i g) :
    Degree i (f+g) := by
  induction i generalizing f g with
  | zero => intro x; change f x+g x=f 0+g 0; rw [hf x,hg x]
  | succ i ih => intro a; rw [fwdDiff_add]; exact ih (hf a) (hg a)

/-- Translation preserves a Boolean degree bound. -/
theorem shift_degree {i : ℕ} {f : U → 𝔽} (hf : Degree i f) (a : U) :
    Degree i (fun x => f (x+a)) := by
  induction i generalizing f with
  | zero => intro x; exact (hf (x+a)).trans (hf (0+a)).symm
  | succ i ih =>
    intro b
    have eq : fwdDiff b (fun x => f (x+a)) = fun x => fwdDiff b f (x+a) := by
      funext x; simp only [fwdDiff,add_right_comm x b a]
    rw [eq]
    exact ih (hf b)

/-- Taking the other Boolean value preserves the degree bound. -/
theorem degree_complement {d : ℕ} {g : U → 𝔽} (hg : Degree d g) :
    Degree d (fun x => 1+g x) := degree_add (degree_const d 1) hg

private theorem mul_const {d : ℕ} {f : U → 𝔽} (hf : Degree d f) (c : 𝔽) :
    Degree d ((fun _ => c) * f) := by
  rcases (show ∀ z : 𝔽, z=0 ∨ z=1 from by decide) c with rfl|rfl
  · convert degree_const d (0:𝔽) using 1; ext; simp
  · convert hf using 1; ext; simp

/-- The mixed-difference degree of a Boolean product is subadditive. -/
theorem degree_mul {i j : ℕ} {f g : U → 𝔽} (hf : Degree i f) (hg : Degree j g) : Degree (i+j) (f*g) := by
  suffices aux : ∀ n i j, i+j=n → ∀ f g : U → 𝔽, Degree i f → Degree j g → Degree n (f*g) by
    exact aux _ i j rfl f g hf hg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j eq f g hf hg
    cases i with
    | zero =>
      subst n
      rw [zero_add]
      have eqp : f*g=(fun _ => f 0)*g := congrArg (· * g) (funext hf)
      rw [eqp]
      exact mul_const hg (f 0)
    | succ i =>
      cases j with
      | zero =>
        have id : g=fun _ => g 0 := funext hg
        subst n
        rw [id,mul_comm,Nat.add_zero]
        exact mul_const hf (g 0)
      | succ j =>
        subst n
        intro a
        have e : fwdDiff a (f*g) = (fwdDiff a f)*g + (fun x => f (x+a))*(fwdDiff a g) := by
          funext x; simp only [Pi.add_apply,Pi.mul_apply,fwdDiff]; ring
        rw [e]
        apply degree_add
        · change Degree ((i+1)+j) _
          rw [show (i+1)+j=i+(j+1) by omega]
          exact ih _ (by omega) i (j+1) rfl (fwdDiff a f) g (hf a) hg
        · exact ih _ (by omega) (i+1) j rfl (fun x => f (x+a)) (fwdDiff a g) (shift_degree hf a) (hg a)

/-- A nonzero Boolean function of degree at most d has support meeting every
translate of a set of at most 2^d points. -/
theorem support_shifts [DecidableEq U] {d : ℕ} (f : U → 𝔽) (hf : Degree d f) (hit : ∃ x, f x≠0) :
    ∃ S : Finset U, S.card ≤ 2^d ∧ ∀ x, ∃ s∈S, f (x+s)≠0 := by
  classical
  induction d generalizing f with
  | zero =>
    obtain ⟨x,hx⟩ := hit
    exact ⟨{0},by simp,fun y => ⟨0,by simp,by simpa only [add_zero,hf y,hf x] using hx⟩⟩
  | succ d ih =>
    by_cases flat : ∀ x, f x=f 0
    · obtain ⟨x,hx⟩ := hit
      refine ⟨{0},by simpa using (Nat.one_le_pow (d+1) 2 (by decide)),fun y => ⟨0,by simp,?_⟩⟩
      simpa only [add_zero,flat y,flat x] using hx
    push Not at flat
    obtain ⟨a,ha⟩ := flat
    have nz : ∃ x, fwdDiff a f x ≠ 0 := ⟨0,by simpa [fwdDiff,sub_ne_zero] using ha⟩
    obtain ⟨S,card,cover⟩ := ih (fwdDiff a f) (hf a) nz
    let S' := S.map (Equiv.addRight a).toEmbedding
    refine ⟨S∪S',?_,?_⟩
    · have bd := card_union_le S S'
      have same : S'.card=S.card := card_map _
      rw [pow_succ]
      omega
    · intro x
      obtain ⟨s,hs,v⟩ := cover x
      by_cases h : f (x+s)=0
      · refine ⟨s+a,mem_union_right _ (mem_map.mpr ⟨s,hs,rfl⟩),?_⟩
        simpa [fwdDiff,h,add_assoc] using v
      · exact ⟨s,mem_union_left _ hs,h⟩

/-- Vanishing fourth differences give the recursive cubic degree bound. -/
theorem cubic_degree (f : U → 𝔽) (h : Green52CubicPolar.Cubic f) : Degree 3 f := by
  intro a b c x
  simpa only [fwdDiff,zero_add] using sub_eq_zero.mp (h a b c x 0)

private theorem degree_prod {I : Type*} [DecidableEq I] (F : I → U → 𝔽)
    (d : ℕ) (s : Finset I) (h : ∀ i∈s, Degree d (F i)) : Degree (d*s.card) (∏ i∈s, F i) := by
  induction s using Finset.induction_on with
  | empty => rw [prod_empty,card_empty,Nat.mul_zero]; intro x; rfl
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.mul_succ,Nat.add_comm]
    exact degree_mul (h i (mem_insert_self _ _)) (ih fun j hj => h j (mem_insert_of_mem hj))

/-- At most two to the power 3d shifts hit each translate of a specified nonempty fibre. -/
theorem fibre_hits [Module 𝔽 U] [DecidableEq U] {d : ℕ} (f : U → (Fin d → 𝔽))
    (hc : Green52CubicPolar.Cubic f) (y : Fin d → 𝔽) (hit : ∃ x, f x=y) :
    ∃ S : Finset U, S.card ≤ 2^(3*d) ∧ ∀ x, ∃ s∈S, f (x+s)=y := by
  classical
  let F (i : Fin d) (x : U) := (1+y i)+f x i
  let g := ∏ i, F i
  have good (x : U) : g x ≠ 0 ↔ f x=y := by
    change (∏ i:Fin d, F i) x ≠ 0 ↔ _
    rw [Finset.prod_apply,Finset.prod_ne_zero_iff]
    simp only [mem_univ,true_implies]
    have entry (a b : 𝔽) : 1+b+a ≠ 0 ↔ a=b := by decide +revert
    simp only [F,entry,funext_iff]
  have degrees (i : Fin d) : Degree 3 (F i) := by
    have hc' := Green52CubicPolar.scalar_cubic f hc (LinearMap.proj (R:=𝔽) (φ:=fun _:Fin d => 𝔽) i)
    exact degree_add (degree_const 3 (1+y i)) (cubic_degree _ hc')
  have hg : Degree (3*d) g := by simpa [g] using degree_prod F 3 univ (fun i _ => degrees i)
  obtain ⟨x,hx⟩ := hit
  obtain ⟨S,b,all⟩ := support_shifts g hg ⟨x,(good x).mpr hx⟩
  refine ⟨S,b,fun v => ?_⟩
  obtain ⟨s,hs,q⟩ := all v
  exact ⟨s,hs,(good _).mp q⟩

open Green52Complements Green52CubicPolar Green52CubicGraphs

private theorem shifted_pattern_cubic {V : Type*} [AddCommGroup V] (S : Finset U)
    (f : U → V) (hc : Cubic f) : Cubic (fun x (s : S) => f (x+s.val)) := by
  let pattern (g : U → V) (x : U) (s : S) := g (x+s.val)
  have step (g : U → V) (a : U) : fwdDiff a (pattern g) = pattern (fwdDiff a g) := by
    funext x s
    simp only [fwdDiff,pattern,Pi.sub_apply,add_right_comm x a s.val]
  change Cubic (pattern f)
  intro a b c d x
  rw [step,step,step,step]
  funext s
  exact hc a b c d _

/-- A set of shifts meeting designated fibres in every translate yields one common flat. -/
private theorem horizontal_fibres {n d : ℕ} (f : Cube n → (Fin d → 𝔽)) (hc : Cubic f)
    (Y : Set (Fin d → 𝔽)) (S : Finset (Cube n)) {k : ℕ} (card : S.card ≤ k)
    (meet : ∀ y ∈ Y, ∀ x, ∃ s∈S, f (x+s)=y) :
    ∃ W : AffineSubspace 𝔽 (Cube n), (W : Set (Cube n)).Nonempty ∧ (∀ y ∈ Y,
      (W : Set (Cube n)) ⊆ {x | f x=y} + {x | f x=y}) ∧
      n ≤ Module.finrank 𝔽 W.direction + horizontalCost ((2^d)^k) := by
  classical
  let pattern (x : Cube n) (s : S) := f (x+s.val)
  obtain ⟨P,a,dim,dirs⟩ := cubic_horizontal pattern (shifted_pattern_cubic S f hc)
  refine ⟨AffineSubspace.mk' a P,⟨a,AffineSubspace.self_mem_mk' a P⟩,?_,?_⟩
  · intro y hy z hz
    have hp : z-a ∈ P := AffineSubspace.mem_mk'.mp hz
    obtain ⟨x,hx⟩ := dirs ⟨z-a,hp⟩
    change pattern x + pattern (x+(a+(z-a))) = 0 at hx
    rw [add_sub_cancel] at hx
    obtain ⟨s,hs,eq⟩ := meet y hy x
    have same : f (x+s) = f ((x+z)+s) := by
      funext i
      have hi := congrFun (congrFun hx ⟨s,hs⟩) i
      change f (x+s) i + f ((x+z)+s) i = 0 at hi
      exact (show ∀ a b : 𝔽, a+b=0 → a=b by decide) _ _ hi
    refine ⟨x+s,eq,(x+z)+s,same.symm.trans eq,?_⟩
    change x+s+((x+z)+s)=z
    have dbl (v : Cube n) : v+v=0 := by rw [←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul]
    calc
      _ = (x+x)+(s+s)+z := by abel
      _ = z := by rw [dbl,dbl,zero_add,zero_add]
  · rw [AffineSubspace.direction_mk']
    have mono : Monotone horizontalCost := by
      intro b c h; unfold horizontalCost Green52CubicRegularity.cost; dsimp only; gcongr <;> decide
    have cnt : Fintype.card (S → Fin d → 𝔽) ≤ (2^d)^k := by
      simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,ZMod.card]
      exact Nat.pow_le_pow_right (Nat.pow_pos (by decide : 0 < 2)) card
    have dn : Module.finrank 𝔽 (Cube n)=n := by simp [Cube]
    exact (le_of_eq dn.symm).trans (dim.trans (Nat.add_le_add_left (mono cnt) _))

/-- Codimension bound for one specified fibre of d cubic coordinates. -/
def fibreCost (d : ℕ) := horizontalCost ((2^d)^(2^(3*d)))

/-- The sum of a nonempty cubic fibre with itself contains an affine flat. -/
theorem cubic_fibre_flat {n d : ℕ} (f : Cube n → (Fin d → 𝔽)) (hc : Cubic f)
    (y : Fin d → 𝔽) (hit : ∃ x, f x=y) : Flat n (fibreCost d) {x | f x=y} := by
  classical
  obtain ⟨S,card,meet⟩ := fibre_hits f hc y hit
  obtain ⟨W,_,cover,dim⟩ := horizontal_fibres f hc {y} S card (by
    intro z hz; obtain rfl := Set.mem_singleton_iff.mp hz; exact meet)
  exact ⟨W,cover y (Set.mem_singleton _),dim⟩

/-- All occupied fibres share a single affine flat in their twofold sums. -/
theorem cubic_fibres_common_flat {n d : ℕ} (f : Cube n → (Fin d → 𝔽)) (hc : Cubic f) :
    ∃ W : AffineSubspace 𝔽 (Cube n), (W : Set (Cube n)).Nonempty ∧ (∀ y ∈ Set.range f,
      (W : Set (Cube n)) ⊆ {x | f x=y} + {x | f x=y}) ∧
      n ≤ Module.finrank 𝔽 W.direction + horizontalCost ((2^d)^(2^d * 2^(3*d))) := by
  classical
  have pick (y : Fin d → 𝔽) : ∃ S : Finset (Cube n), S.card ≤ 2^(3*d) ∧
      (y ∈ Set.range f → ∀ x, ∃ s∈S, f (x+s)=y) := by
    by_cases hit : y ∈ Set.range f
    · obtain ⟨S,b,h⟩ := fibre_hits f hc y hit
      exact ⟨S,b,fun _ => h⟩
    · exact ⟨∅,by simp,fun hy => (hit hy).elim⟩
  choose T sizes covers using pick
  refine horizontal_fibres f hc (Set.range f) (univ.biUnion T) ?_ ?_
  · calc
      _ ≤ ∑ y : Fin d → 𝔽, (T y).card := card_biUnion_le
      _ ≤ ∑ _y : Fin d → 𝔽, 2^(3*d) := sum_le_sum (fun y _ => sizes y)
      _ = _ := by simp
  · intro y hy x
    obtain ⟨s,hs,eq⟩ := covers y hy x
    exact ⟨s,mem_biUnion.mpr ⟨y,mem_univ y,hs⟩,eq⟩

/-- Regrouping cubic values into colours preserves the conclusion for each occupied class. -/
theorem cubic_colour_flat {n d : ℕ} {I : Type*} (f : Cube n → (Fin d → 𝔽))
    (hc : Cubic f) (colour : (Fin d → 𝔽) → I) (i : I) (hit : ∃ x, colour (f x)=i) :
    Flat n (fibreCost d) {x | colour (f x)=i} := by
  obtain ⟨x,hx⟩ := hit
  obtain ⟨P,sub,dim⟩ := cubic_fibre_flat f hc (f x) ⟨x,rfl⟩
  have incl : {z : Cube n | f z=f x} ⊆ {z | colour (f z)=i} := by
    intro z hz
    exact (congrArg colour hz).trans hx
  exact ⟨P,sub.trans (Set.add_subset_add incl incl),dim⟩

/-- Green 53 for partitions whose colours are functions of a bounded number of cubic coordinates. -/
theorem cubic_partition_green53 (coords : ℕ → ℕ) :
    ∃ c : ℕ → ℕ, ∀ (n k : ℕ) (A : Fin k → Set (Cube n)),
      (⋃ i, A i) = Set.univ → Pairwise (fun i j => Disjoint (A i) (A j)) →
      (∃ (f : Cube n → Fin (coords k) → 𝔽) (colour : (Fin (coords k) → 𝔽) → Fin k),
        Cubic f ∧ ∀ i, A i = {x | colour (f x)=i}) →
      ∃ i, Flat n (c k) (A i) := by
  refine ⟨fun k => fibreCost (coords k),?_⟩
  rintro n k A _ _ ⟨f,colour,hc,rfls⟩
  refine ⟨colour (f 0),?_⟩
  rw [rfls]
  exact cubic_colour_flat f hc colour _ ⟨0,rfl⟩

/-- Counting the hitting translates gives the Reed–Muller lower bound on a nonzero support. -/
theorem support_card [Fintype U] [DecidableEq U] (g : U → 𝔽) {e : ℕ}
    (hg : Degree e g) (hit : ∃ x, g x ≠ 0) :
    Fintype.card U ≤ (univ.filter (fun x => g x ≠ 0)).card * 2^e := by
  classical
  obtain ⟨S,b,meet⟩ := support_shifts g hg hit
  let A := univ.filter (fun x => g x ≠ 0)
  let diff (p : U × U) := p.1-p.2
  have cover : univ ⊆ (A ×ˢ S).image diff := by
    intro x _
    obtain ⟨s,hs,good⟩ := meet x
    exact mem_image.mpr ⟨(x+s,s),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,good⟩,hs⟩,
      by simp [diff]⟩
  calc
    Fintype.card U = (univ : Finset U).card := card_univ.symm
    _ ≤ _ := card_le_card cover
    _ ≤ _ := card_image_le
    _ = A.card * S.card := card_product A S
    _ ≤ _ := Nat.mul_le_mul_left _ b

/-- Any represented fibre pair at a fixed displacement has density at least 2^(-5d). -/
theorem fibre_pair_count {n d : ℕ} (f : Cube n → (Fin d → 𝔽)) (hc : Cubic f)
    (u v : Fin d → 𝔽) (z : Cube n) (hit : ∃ x, f x=u ∧ f (x+z)=v) :
    2^n ≤ (univ.filter (fun x => f x=u ∧ f (x+z)=v)).card * 2^(5*d) := by
  classical
  let F (i : Fin d) (x : Cube n) := (1+u i)+f x i
  let D (i : Fin d) (x : Cube n) := (1+(v i-u i))+fwdDiff z (fun t => f t i) x
  let g := (∏ i, F i) * (∏ i, D i)
  have deg (i : Fin d) : Degree 3 (fun x => f x i) :=
    cubic_degree _ (Green52CubicPolar.scalar_cubic f hc (LinearMap.proj (R:=𝔽) (φ:=fun _:Fin d => 𝔽) i))
  have hF (i : Fin d) : Degree 3 (F i) := degree_add (degree_const _ _) (deg i)
  have hD (i : Fin d) : Degree 2 (D i) := degree_add (degree_const _ _) (deg i z)
  have hg : Degree (5*d) g := by
    have b := degree_mul (degree_prod F 3 univ (fun i _ => hF i))
      (degree_prod D 2 univ (fun i _ => hD i))
    simpa only [g,card_univ,Fintype.card_fin,←Nat.add_mul] using b
  have same (x : Cube n) : g x ≠ 0 ↔ f x=u ∧ f (x+z)=v := by
    have entry : ∀ a b : 𝔽, 1+a+b ≠ 0 ↔ b=a := by decide
    change ((∏ i, F i) * (∏ i, D i)) x ≠ 0 ↔ _
    simp only [Pi.mul_apply,Finset.prod_apply,Finset.prod_ne_zero_iff,mem_univ,true_implies,
      mul_ne_zero_iff,F,D,entry,fwdDiff]
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨funext ha,funext fun i => sub_left_inj.mp (by simpa only [ha i] using hb i)⟩
    · rintro ⟨h,h'⟩
      exact ⟨congrFun h,fun i => by rw [h,h']⟩
  obtain ⟨x,hx⟩ := hit
  have b := support_card g hg ⟨x,(same x).mpr hx⟩
  simpa only [Cube,Fintype.card_fun,Fintype.card_fin,ZMod.card,same] using b

/-- Every occupied fibre has a uniform positive density of representations on the same flat. -/
theorem common_popular_differences {n d : ℕ} (f : Cube n → (Fin d → 𝔽)) (hc : Cubic f) :
    ∃ W : AffineSubspace 𝔽 (Cube n), (W : Set (Cube n)).Nonempty ∧ n ≤ Module.finrank 𝔽 W.direction +
      horizontalCost ((2^d)^(2^d * 2^(3*d))) ∧ ∀ y ∈ Set.range f, ∀ z ∈ W,
      2^n ≤ (univ.filter (fun x => f x=y ∧ f (x+z)=y)).card * 2^(5*d) := by
  obtain ⟨W,ne,all,dim⟩ := cubic_fibres_common_flat f hc
  refine ⟨W,ne,dim,?_⟩
  intro y hit z hz
  obtain ⟨x,hx,v,hv,eq⟩ := all y hit hz
  apply fibre_pair_count f hc y y z
  have dbl : x+x=0 := by rw [←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul]
  exact ⟨x,hx,by simpa only [←eq,←add_assoc,dbl,zero_add] using (show f v=y from hv)⟩

end Green53PolynomialColours

#print axioms Green53PolynomialColours.shift_degree
#print axioms Green53PolynomialColours.degree_complement
#print axioms Green53PolynomialColours.degree_mul
#print axioms Green53PolynomialColours.support_shifts
#print axioms Green53PolynomialColours.cubic_degree
#print axioms Green53PolynomialColours.fibre_hits
#print axioms Green53PolynomialColours.cubic_fibre_flat
#print axioms Green53PolynomialColours.cubic_fibres_common_flat
#print axioms Green53PolynomialColours.cubic_colour_flat
#print axioms Green53PolynomialColours.cubic_partition_green53
#print axioms Green53PolynomialColours.support_card
#print axioms Green53PolynomialColours.fibre_pair_count
#print axioms Green53PolynomialColours.common_popular_differences
