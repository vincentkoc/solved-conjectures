import Green53PolynomialColours

/-!
# Common popular differences in quartic level sets

A missing pair of a particular value, away from an antiperiod, exposes a bounded
lower-degree factor. A family of quartics then gives one cubic fibre for all low-rank
members and a linear constraint for each remaining member.
-/

open Finset Green53PolynomialColours Green52Complements
open scoped Pointwise
namespace Green53Quartic
local notation "𝔽" => ZMod 2
variable {U : Type*} [AddCommGroup U]

/-- A Boolean function is determined by at most k coordinates of degree at most e. -/
def Factors (e k : ℕ) (f : U → 𝔽) : Prop :=
  ∃ (t : ℕ) (g : Fin t → U → 𝔽) (read : (Fin t → 𝔽) → 𝔽), t ≤ k ∧
    (∀ i, Degree e (g i)) ∧ ∀ x, f x=read (fun i => g i x)

/-- Constancy on the nonzero support of a lower-degree polynomial bounds functional rank. -/
theorem factor_of_constant_on_support [DecidableEq U] {e : ℕ} (f : U → 𝔽) (hf : Degree (e+1) f)
    (g : U → 𝔽) (hg : Degree e g) (hit : ∃ x, g x ≠ 0) (b : 𝔽)
    (forced : ∀ x, g x ≠ 0 → f x=b) : Factors e (2^(e+1)) f := by
  classical
  obtain ⟨S,bound,meet⟩ := support_shifts g hg hit
  let Idx := (↥S) ⊕ (↥S)
  let t := Fintype.card Idx
  let coords : Idx → U → 𝔽 := Sum.elim (fun s x => g (x+s.val)) (fun s => fwdDiff s.val f)
  have low (i : Idx) : Degree e (coords i) := by
    cases i with
    | inl s => exact shift_degree hg s.val
    | inr s => exact hf s.val
  have determines {x v : U} (eq : ∀ i, coords i x=coords i v) : f x=f v := by
    obtain ⟨s,hs,hsx⟩ := meet x
    have eg : g (x+s)=g (v+s) := eq (.inl ⟨s,hs⟩)
    have hsv : g (v+s) ≠ 0 := fun h => hsx (eg.trans h)
    have sv : f (x+s)=f (v+s) := (forced _ hsx).trans (forced _ hsv).symm
    have ds := eq (.inr ⟨s,hs⟩)
    change f (x+s)-f x=f (v+s)-f v at ds
    rw [sv] at ds
    exact sub_right_inj.mp ds
  let g (i : Fin t) := coords ((Fintype.equivFin Idx).symm i)
  let values (x : U) (i : Fin t) := g i x
  let read (v : Fin t → 𝔽) := if h : ∃ x, values x=v then f h.choose else 0
  refine ⟨t,g,read,?_,fun i => low _,fun x => ?_⟩
  · have sz : t = S.card+S.card := by simp [t,Idx]
    rw [sz,pow_succ]; omega
  · have hx : ∃ v, values v=values x := ⟨x,rfl⟩
    change f x = read (values x)
    rw [show read (values x)=f hx.choose by simp only [read,dif_pos hx]]
    apply determines
    intro i
    have he := congrFun hx.choose_spec ((Fintype.equivFin Idx) i)
    simpa only [values,g,Equiv.symm_apply_apply] using he.symm

/-- A missing equal-value pair away from an antiperiod forces bounded lower-degree rank. -/
theorem factor_of_missing_pair [DecidableEq U] {e : ℕ} (f : U → 𝔽) (hf : Degree (e+1) f)
    (a : U) (y : 𝔽) (same : ∃ x, f (x+a)=f x) (miss : ¬ ∃ x, f x=y ∧ f (x+a)=y) :
    Factors e (2^(e+1)) f := by
  let g (x : U) := 1+fwdDiff a f x
  obtain ⟨w,hw⟩ := same
  apply factor_of_constant_on_support f hf g (degree_complement (hf a)) ⟨w,by simp [g,fwdDiff,hw]⟩ (1+y)
  intro x hx
  have diff : fwdDiff a f x=0 := (show ∀ t : 𝔽, 1+t≠0 → t=0 by decide) _ hx
  have ne : f x ≠ y := fun h => miss ⟨x,h,(sub_eq_zero.mp diff).trans h⟩
  exact (show ∀ p q : 𝔽, p≠q → p=1+q by decide) _ _ ne
/-- Equality of every triple difference at x and at zero gives vanishing fourth differences. -/
private theorem cubic_of_degree {g : U → 𝔽} (hg : Degree 3 g) : Green52CubicPolar.Cubic g := by
  intro a b c d x
  exact sub_eq_zero.mpr (((hg a b c) (x+d)).trans (((hg a b c) x).symm))

private theorem tuple_cubic {t : ℕ} (g : Fin t → U → 𝔽) (hg : ∀ i, Degree 3 (g i)) :
    Green52CubicPolar.Cubic (fun x i => g i x) := by
  intro a b c d x
  funext i
  exact cubic_of_degree (hg i) a b c d x

private theorem scalar_directions {n : ℕ} (f : Cube n → 𝔽) :
    ∃ P : Submodule 𝔽 (Cube n), n ≤ Module.finrank 𝔽 P + 1 ∧
      ∀ z ∈ P, ∃ x, f (x+z)=f x := by
  obtain ⟨P,dim,all⟩ := Green52CubicFibres.horizontal_projections f
  refine ⟨P,by simpa [Cube] using dim,?_⟩
  intro z hz
  obtain ⟨x,hx⟩ := all ⟨z,hz⟩ LinearMap.id
  change f x+f (x+z)=0 at hx
  exact ⟨x,(show ∀ a b : 𝔽, a+b=0 → b=a by decide) _ _ hx⟩
/-- Unless all equal pairs of one colour disappear at a non-antiperiod,
both double sets contain the same linear hyperplane or the whole space. -/
theorem high_rank_common_hyperplane {n e : ℕ} (f : Cube n → 𝔽) (hf : Degree (e+1) f)
    (high : ¬ Factors e (2^(e+1)) f) :
    ∃ P : Submodule 𝔽 (Cube n), n ≤ Module.finrank 𝔽 P + 1 ∧ ∀ z ∈ P, ∀ y : 𝔽,
      ∃ x, f x=y ∧ f (x+z)=y := by
  classical
  obtain ⟨P,dim,all⟩ := scalar_directions f
  refine ⟨P,dim,?_⟩
  intro z hz y
  by_contra miss
  exact high (factor_of_missing_pair f hf z y (all z hz) miss)

open Green52CubicGraphs

private theorem count_mono {i j : ℕ} (le : i ≤ j) :
    (2^i)^(2^i * 2^(3*i)) ≤ (2^j)^(2^j * 2^(3*j)) := by
  have pos : 0 < (2:ℕ)^j := Nat.pow_pos (by decide)
  gcongr <;> omega


/-- Both levels of any Boolean quartic share a common flat whenever they are inhabited. -/
theorem quartic_common_flat {n k : ℕ} (hk : 16 ≤ k) (f : Cube n → 𝔽) (hf : Degree 4 f) :
    ∃ (W : AffineSubspace 𝔽 (Cube n)), (W : Set (Cube n)).Nonempty ∧
      n ≤ Module.finrank 𝔽 W.direction + (horizontalCost ((2^k)^(2^k * 2^(3*k)))+1) ∧
      ∀ y ∈ Set.range f, (W : Set (Cube n)) ⊆ {x | f x=y} + {x | f x=y} := by
  classical
  by_cases fac : Factors 3 16 f
  · obtain ⟨t,g,read,bt,hg,eq⟩ := fac
    let G (x : Cube n) (i : Fin t) := g i x
    obtain ⟨W,ne,cover,dim⟩ := cubic_fibres_common_flat G (tuple_cubic g hg)
    have mono : Monotone horizontalCost := by
      intro b c h; unfold horizontalCost Green52CubicRegularity.cost; dsimp only; gcongr <;> decide
    have bound := count_mono (bt.trans hk)
    refine ⟨W,ne,dim.trans (Nat.add_le_add_left ((mono bound).trans (Nat.le_succ _)) _),?_⟩
    rintro y ⟨x,rfl⟩
    have incl : {v | G v=G x} ⊆ {v | f v=f x} := by
      intro v hv
      exact (eq v).trans ((congrArg read hv).trans (eq x).symm)
    exact (cover (G x) ⟨x,rfl⟩).trans (Set.add_subset_add incl incl)
  · obtain ⟨P,dim,all⟩ := high_rank_common_hyperplane (e:=3) f hf fac
    refine ⟨AffineSubspace.mk' 0 P,⟨0,AffineSubspace.self_mem_mk' _ _⟩,?_,?_⟩
    · rw [AffineSubspace.direction_mk']
      exact dim.trans (Nat.add_le_add_left (Nat.le_add_left 1 _) _)
    · intro y _ z hz
      have hp : z ∈ P := by simpa using AffineSubspace.mem_mk'.mp hz
      obtain ⟨x,hx,hv⟩ := all z hp y
      refine ⟨x,hx,x+z,hv,?_⟩
      change x+(x+z)=z
      rw [←add_assoc,←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul,zero_add]
/-- Outside bounded lower-degree rank, both equal-value pairs occur at exactly the non-antiperiods. -/
theorem high_rank_pair_iff [DecidableEq U] {e : ℕ} (f : U → 𝔽) (hf : Degree (e+1) f)
    (high : ¬ Factors e (2^(e+1)) f) (a : U) (y : 𝔽) :
    (∃ x, f x=y ∧ f (x+a)=y) ↔ ∃ x, f (x+a)=f x := by
  refine ⟨?_,?_⟩
  · rintro ⟨x,h,h'⟩; exact ⟨x,h'.trans h.symm⟩
  · intro h
    by_contra miss
    exact high (factor_of_missing_pair f hf a y h miss)

private theorem indicator_degree {e : ℕ} {g : U → 𝔽} (hg : Degree e g) (y : 𝔽) :
    Degree e (fun x => 1+y+g x) := by
  rcases (show ∀ y : 𝔽, y=0 ∨ y=1 from by decide) y with rfl|rfl
  · simpa only [add_zero] using degree_complement hg
  · simpa only [show (1:𝔽)+1=0 by decide,zero_add] using hg

/-- A realized two-point pattern of a Boolean of degree e+1 has density at least 2^(-2e-1). -/
theorem boolean_pair_count {n e : ℕ} (f : Cube n → 𝔽) (hf : Degree (e+1) f)
    (u v : 𝔽) (a : Cube n) (hit : ∃ x, f x=u ∧ f (x+a)=v) :
    2^n ≤ (univ.filter (fun x => f x=u ∧ f (x+a)=v)).card * 2^(2*e+1) := by
  classical
  let g (x : Cube n) := (1+u+f x)*(1+(v-u)+fwdDiff a f x)
  have deg : Degree (2*e+1) g := by
    rw [show 2*e+1=e+1+e by omega]
    exact degree_mul (indicator_degree hf u) (indicator_degree (hf a) (v-u))
  have same (x : Cube n) : g x ≠ 0 ↔ f x=u ∧ f (x+a)=v := by
    have bit : ∀ i j u v : 𝔽, (1+u+i)*(1+(v-u)+(j-i)) ≠ 0 ↔ i=u ∧ j=v := by decide
    exact bit _ _ _ _
  obtain ⟨x,hx⟩ := hit
  have b := support_card g deg ⟨x,(same x).mpr hx⟩
  simpa only [Cube,Fintype.card_fun,Fintype.card_fin,ZMod.card,same] using b
/-- One level can be tested on equal low-degree data, or controlled by a linear kernel. -/
private theorem model_level {n : ℕ} (f : Cube n → 𝔽) (hf : Degree 4 f)
    (y : 𝔽) (hit : ∃ x, f x=y) :
    ∃ g : Fin 16 → Cube n → 𝔽, (∀ i, Degree 3 (g i)) ∧
      ∀ v w, (∀ i, g i v=g i 0) → (∀ i, g i w=g i 0) →
      ∃ x, f x=y ∧ f (x+(v+w))=y := by
  classical
  by_cases low : Factors 3 16 f
  · obtain ⟨t,c,read,cap,deg,val⟩ := low
    obtain ⟨x0,hx⟩ := hit
    let g (i : Fin 16) (x : Cube n) := if h : i.val < t then c ⟨i.val,h⟩ (x+x0) else 0
    refine ⟨g,?_,?_⟩
    · intro i
      by_cases h : i.val<t
      · simpa only [g,dif_pos h] using shift_degree (deg ⟨i.val,h⟩) x0
      · simp only [g,dif_neg h]
        intro a b c x
        simp [fwdDiff]
    · intro v w hv hw
      have eval0 (z : Cube n) (hz : ∀ i, g i z=g i 0) : f (z+x0)=y := by
        rw [val,←hx,val x0]
        apply congrArg read
        funext j
        have he := hz (j.castLE cap)
        change (if h : j.val<t then c ⟨j.val,h⟩ (z+x0) else 0) =
          (if h : j.val<t then c ⟨j.val,h⟩ (0+x0) else 0) at he
        simpa only [dif_pos j.isLt,zero_add] using he
      refine ⟨v+x0,eval0 v hv,?_⟩
      have dbl : v+v=0 := by rw [←two_smul 𝔽,show (2:𝔽)=0 by decide,zero_smul]
      rw [show v+x0+(v+w)=(v+v)+(w+x0) by abel,dbl,zero_add]
      exact eval0 w hw
  · obtain ⟨P,dim,all⟩ := high_rank_common_hyperplane (e:=3) f hf low
    have le : Module.finrank 𝔽 ((Cube n) ⧸ P) ≤ Module.finrank 𝔽 𝔽 := by
      rw [Module.finrank_self]
      have dd := P.finrank_quotient_add_finrank
      have dn : Module.finrank 𝔽 (Cube n)=n := by simp [Cube]
      omega
    obtain ⟨l,inj⟩ := finrank_le_iff_exists_linearMap.mp le
    let L := l.comp P.mkQ
    refine ⟨fun _ x => L x,fun _ => cubic_degree L ?_,?_⟩
    · intro a b c d x
      simp [fwdDiff,map_add]
    · intro v w hv hw
      apply all (v+w) _ y
      apply (Submodule.Quotient.mk_eq_zero P).mp
      apply inj
      change L (v+w)=l 0
      have hv' : L v=L 0 := hv 0
      have hw' : L w=L 0 := hw 0
      rw [map_add,hv',hw',map_zero,map_zero,zero_add]

/-- All specified nonempty quartic levels share a flat of popular differences. -/
theorem quartic_family {n m : ℕ} (f : Fin m → Cube n → 𝔽) (hf : ∀ i, Degree 4 (f i))
    (y : Fin m → 𝔽) (hit : ∀ i, ∃ x, f i x=y i) :
    ∃ W : AffineSubspace 𝔽 (Cube n), (W : Set (Cube n)).Nonempty ∧
      n ≤ Module.finrank 𝔽 W.direction +
        horizontalCost ((2^(m*16))^(2^(m*16) * 2^(3*(m*16)))) ∧
      ∀ i z, z ∈ W → 2^n ≤
        (univ.filter (fun x => f i x=y i ∧ f i (x+z)=y i)).card * 128 := by
  classical
  choose c deg cover using fun i => model_level (f i) (hf i) (y i) (hit i)
  let G (j : Fin (m*16)) := c (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  let vals (x : Cube n) (j : Fin (m*16)) := G j x
  have hc : Green52CubicPolar.Cubic vals := tuple_cubic G (fun j => deg _ _)
  obtain ⟨W,ne,all,dim⟩ := cubic_fibres_common_flat vals hc
  refine ⟨W,ne,dim,?_⟩
  intro i z hz
  obtain ⟨v,hv,w,hw,eq⟩ := all (vals 0) ⟨0,rfl⟩ hz
  have at0 (v : Cube n) (h : vals v=vals 0) (j : Fin 16) : c i j v=c i j 0 := by
    simpa only [vals,G,Equiv.symm_apply_apply] using congrFun h (finProdFinEquiv (i,j))
  have realized := cover i v w (at0 v hv) (at0 w hw)
  change v+w=z at eq
  rw [eq] at realized
  exact boolean_pair_count (e:=3) (f i) (hf i) (y i) (y i) z realized
/-- In Green 53 it suffices for a single colour class to contain an inhabited quartic level. -/
theorem quartic_class_green53 :
    ∃ c : ℕ → ℕ, ∀ (n k : ℕ) (A : Fin k → Set (Cube n)),
      (⋃ i, A i) = Set.univ → Pairwise (fun i j => Disjoint (A i) (A j)) →
      (∃ (i : Fin k) (f : Cube n → 𝔽) (y : 𝔽),
        Degree 4 f ∧ y ∈ Set.range f ∧ {x | f x=y} ⊆ A i) →
      ∃ i, Flat n (c k) (A i) := by
  refine ⟨fun _ => horizontalCost ((2^16)^(2^16 * 2^(3*16)))+1,?_⟩
  rintro n k A _ _ ⟨i,f,y,hf,hit,inc⟩
  obtain ⟨W,_,dim,sub⟩ := quartic_common_flat (k:=16) le_rfl f hf
  exact ⟨i,W,(sub y hit).trans (Set.add_subset_add inc inc),dim⟩

end Green53Quartic

#print axioms Green53Quartic.factor_of_constant_on_support
#print axioms Green53Quartic.factor_of_missing_pair
#print axioms Green53Quartic.high_rank_common_hyperplane
#print axioms Green53Quartic.high_rank_pair_iff
#print axioms Green53Quartic.quartic_common_flat
#print axioms Green53Quartic.boolean_pair_count
#print axioms Green53Quartic.quartic_family
#print axioms Green53Quartic.quartic_class_green53
