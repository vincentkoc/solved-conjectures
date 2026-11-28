import Green50QuadraticBogolyubov

/-!
# How many deletions change the sumsets of a binary graph?

A nonzero direction pairs the members of each derivative fibre. This gives an exact
uniform deletion budget for preserving all iterated sums of a quadratic graph.
-/

open Finset
open scoped Pointwise
namespace Green50GraphDeletions
local notation "F₂" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]

private theorem twice {E : Type*} [AddCommGroup E] [Module F₂ E] (x : E) : x+x=0 := by
  rw [← two_smul F₂ x,show (2:F₂)=0 by decide,zero_smul]

omit [Fintype U] [DecidableEq U] in
private theorem back (x a : U) : (x+a)+a=x := by rw [add_assoc,twice,add_zero]

/-- Points of the graph retained over a subset of the inputs. -/
def retained (f : U → V) (D : Finset U) := D.image (fun x => (x,f x))

/-- Inputs representing a fixed horizontal direction and vertical sum. -/
def fibre (f : U → V) (a : U) (b : V) := univ.filter (fun x => f x + f (x+a) = b)

omit [Module F₂ V] [Fintype V] in
private theorem mem_pair (f : U → V) (D : Finset U) (a : U) (b : V) :
    (a,b) ∈ (2:ℕ) • retained f D ↔ ∃ x ∈ fibre f a b, x∈D ∧ x+a∈D := by
  rw [two_nsmul,mem_add]
  constructor
  · rintro ⟨_,hx,_,hy,he⟩
    obtain ⟨x,hxd,rfl⟩ := mem_image.mp (show _ ∈ D.image (fun z => (z,f z)) from hx)
    obtain ⟨y,hyd,rfl⟩ := mem_image.mp (show _ ∈ D.image (fun z => (z,f z)) from hy)
    have h := congrArg Prod.fst he
    change x+y=a at h
    have e : x+a=y := by rw [←h,←add_assoc,twice,zero_add]
    have h' := congrArg Prod.snd he
    change f x + f y = b at h'
    exact ⟨x,mem_filter.mpr ⟨mem_univ _,e ▸ h'⟩,hxd,e ▸ hyd⟩
  · rintro ⟨x,hx,hy,hz⟩
    refine ⟨_,mem_image_of_mem _ hy,_,mem_image_of_mem _ hz,Prod.ext ?_ (mem_filter.mp hx).2⟩
    change x+(x+a)=a
    rw [←add_assoc,twice,zero_add]

omit [Module F₂ V] [Fintype V] [DecidableEq U] in
private theorem mem_shift (f : U → V) (a : U) (b : V) {x : U} (h : x∈fibre f a b) :
    x+a∈fibre f a b :=
  mem_filter.mpr ⟨mem_univ _, by simpa [back,add_comm (f (x+a)) (f x)] using (mem_filter.mp h).2⟩

omit [Module F₂ V] [Fintype V] in
/-- A missing direction-output pair costs at least half its ordered representations. -/
theorem deletion_bound (f : U → V) (D : Finset U) (a : U) (b : V)
    (h : (a,b) ∉ (2:ℕ) • retained f D) : (fibre f a b).card ≤ 2*Dᶜ.card := by
  let E := fibre f a b
  have hsub : E ⊆ Dᶜ ∪ Dᶜ.image (fun y => y-a) := by
    intro x hx
    by_cases hxD : x∈D
    · have hn : x+a ∉ D := fun hy => h ((mem_pair f D a b).mpr ⟨x,hx,hxD,hy⟩)
      exact mem_union_right _ (mem_image.mpr ⟨x+a,mem_compl.mpr hn,add_sub_cancel_right _ _⟩)
    · exact mem_union_left _ (mem_compl.mpr hxD)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by
    have := card_image_le (s:=Dᶜ) (f:=fun y => y-a); omega))

omit [Module F₂ V] [Fintype V] in
/-- For a nonzero horizontal direction this cost is attained by deleting one member of each pair. -/
theorem exact_deletion_cost (f : U → V) {a : U} (ha : a ≠ 0) (b : V) (m : ℕ) :
    (∃ D : Finset U, Dᶜ.card ≤ m ∧ (a,b) ∉ (2:ℕ) • retained f D) ↔ (fibre f a b).card ≤ 2*m := by
  constructor
  · rintro ⟨D,hd,h⟩
    have := deletion_bound f D a b h
    omega
  · intro hm
    obtain ⟨l,hl⟩ := Module.Projective.exists_dual_eq_one F₂ ha
    let E := fibre f a b
    let Z := E.filter fun x => l x=0
    let O := E.filter fun x => ¬l x=0
    have hflip (x : U) : l (x+a)=0 ↔ l x ≠ 0 := by
      rw [map_add,hl]
      generalize l x = t
      revert t
      decide
    have eq : Z.card = O.card := by
      apply card_bij' (fun x _ => x+a) (fun y _ => y+a)
      · intro x hx
        obtain ⟨he,hz⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨mem_shift f a b he,fun h => (hflip x).mp h hz⟩
      · intro x hx
        obtain ⟨he,ho⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨mem_shift f a b he,(hflip x).mpr ho⟩
      · intro x _; exact back x a
      · intro x _; exact back x a
    have cnt : Z.card+O.card=E.card := card_filter_add_card_filter_not _
    change E.card ≤ 2*m at hm
    refine ⟨Zᶜ,by rw [compl_compl]; omega,?_⟩
    intro h
    obtain ⟨x,hx,hD,hE⟩ := (mem_pair f Zᶜ a b).mp h
    by_cases hz : l x = 0
    · exact (mem_compl.mp hD) (mem_filter.mpr ⟨hx,hz⟩)
    · exact (mem_compl.mp hE) (mem_filter.mpr ⟨mem_shift f a b hx,(hflip x).mpr hz⟩)
omit [DecidableEq U] in
private theorem card_fibre (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (a : U) (x : U) :
    (fibre f a (f x+f (x+a))).card = Nat.card (B a).ker := by
  classical
  rw [Nat.card_eq_fintype_card,←card_univ (α:=(B a).ker)]
  let toKer (y : U) (hy : y∈fibre f a (f x+f (x+a))) : (B a).ker :=
    ⟨y-x,by
      have e := (mem_filter.mp hy).2
      change f y+f (y+a) = f x+f (x+a) at e
      rw [hf,hf] at e
      exact LinearMap.mem_ker.mpr (by rw [map_sub,add_right_cancel e,sub_self])⟩
  refine card_bij' toKer (fun z _ => z.val+x) (fun _ _ => mem_univ _) ?_ ?_ ?_
  · intro z _
    exact mem_filter.mpr ⟨mem_univ _,by rw [hf,hf,map_add,LinearMap.mem_ker.mp z.property,zero_add]⟩
  · intro y _
    exact sub_add_cancel y x
  · intro z _
    exact Subtype.ext (add_sub_cancel_right _ _)

/-- Every derivative fibre of a quadratic graph has size equal to the cardinality of
the directional kernel, whenever the fibre is nonempty. -/
theorem quadratic_deletion_cost (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) {a : U} (ha : a ≠ 0) (x : U) (m : ℕ) :
    (∃ D : Finset U, Dᶜ.card ≤ m ∧ (a,f x+f (x+a)) ∉ (2:ℕ) • retained f D) ↔
      Nat.card (B a).ker ≤ 2*m := by
  rw [exact_deletion_cost f ha,card_fibre f B hf]

private theorem propagate {E : Type*} [AddCommMonoid E] [DecidableEq E] (X Y : Finset E) (h : X⊆Y)
    (he : (2:ℕ) • X = (2:ℕ) • Y) (n : ℕ) : (n+2) • X = (n+2) • Y := by
  induction n with
  | zero => exact he
  | succ n ih =>
    apply Subset.antisymm (nsmul_subset_nsmul_left h)
    have hxy : X+Y ⊆ X+X := by
      have e := he
      simp only [two_nsmul] at e
      exact e.symm ▸ add_subset_add h (Subset.rfl : Y ⊆ Y)
    calc
      (n+1+2) • Y = (n+2) • Y + Y := succ_nsmul _ _
      _ = (n+2) • X + Y := by rw [ih]
      _ = (n+1) • X + (X+Y) := by rw [←add_assoc,←succ_nsmul]
      _ ⊆ (n+1) • X + (X+X) := add_subset_add (Subset.rfl) hxy
      _ = (n+1+2) • X := by rw [←add_assoc,←succ_nsmul,←succ_nsmul]

/-- Deletions smaller than half every directional kernel preserve all sums of order at least two. -/
theorem sums_preserved (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (D : Finset U)
    (h : ∀ a : U, 2*Dᶜ.card < Nat.card (B a).ker) (n : ℕ) :
    (n+2) • retained f D = (n+2) • Green50QuadraticGraphs.graph f := by
  have sub : retained f D ⊆ Green50QuadraticGraphs.graph f := image_subset_image (subset_univ _)
  apply propagate _ _ sub _ n
  apply Subset.antisymm (nsmul_subset_nsmul_left sub)
  rintro ⟨a,b⟩ hab
  obtain ⟨x,rfl⟩ := (Green50QuadraticGraphs.twofold_fibre f a b).mp hab
  by_contra hn
  have e := deletion_bound f D a _ hn
  rw [card_fibre f B hf] at e
  exact (h a).not_ge e

/-- Output cardinality alone gives a sufficient deletion budget. -/
theorem sums_preserved_of_card (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (D : Finset U)
    (h : (2*Dᶜ.card)*Fintype.card V < Fintype.card U) (n : ℕ) :
    (n+2) • retained f D = (n+2) • Green50QuadraticGraphs.graph f := by
  classical
  apply sums_preserved f B hf D _ n
  intro a
  let L := B a
  have eq : Nat.card U = Nat.card L.ker * Nat.card L.range := by
    simp only [Nat.card_eq_fintype_card]
    rw [Module.card_eq_pow_finrank (K:=F₂) (V:=U), Module.card_eq_pow_finrank (K:=F₂) (V:=L.ker),
      Module.card_eq_pow_finrank (K:=F₂) (V:=L.range),←pow_add]
    rw [Nat.add_comm,L.finrank_range_add_finrank_ker]
  have le : Nat.card L.range ≤ Fintype.card V := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective _ L.range.subtype_injective
  change 2*Dᶜ.card < Nat.card L.ker
  by_contra! hn
  have bound := Nat.mul_le_mul hn le
  rw [←eq,Nat.card_eq_fintype_card] at bound
  omega

/-- Uniform resilience against all deletions of at most m inputs, including a zero-dimensional
input space. Testing two graph summands decides simultaneous preservation for every larger sum. -/
theorem all_deletions_iff (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (m : ℕ) :
    (∀ D : Finset U, Dᶜ.card ≤ m → ∀ n : ℕ,
      (n+2) • retained f D = (n+2) • Green50QuadraticGraphs.graph f) ↔
    m < Fintype.card U ∧ ∀ a : U, a ≠ 0 → 2*m < Nat.card (B a).ker := by
  classical
  have full (a x : U) : (a,f x+f (x+a)) ∈ (2:ℕ) • Green50QuadraticGraphs.graph f :=
    (Green50QuadraticGraphs.twofold_fibre f a _).mpr ⟨x,rfl⟩
  constructor
  · intro hall
    constructor
    · by_contra! hn
      have he := hall ∅ (by simpa using hn) 0
      have hin := full 0 0
      change (2:ℕ) • retained f ∅ = _ at he
      rw [←he] at hin
      simp [retained,two_nsmul] at hin
    · intro a ha
      by_contra! hn
      obtain ⟨D,hd,hm⟩ := (quadratic_deletion_cost f B hf ha 0 m).mpr hn
      exact hm ((hall D hd 0).symm ▸ full a 0)
  · rintro ⟨hm,hr⟩ D hD n
    have sub : retained f D ⊆ Green50QuadraticGraphs.graph f := image_subset_image (subset_univ _)
    apply propagate _ _ sub _ n
    apply Subset.antisymm (nsmul_subset_nsmul_left sub)
    rintro ⟨a,b⟩ hab
    obtain ⟨x,rfl⟩ := (Green50QuadraticGraphs.twofold_fibre f a b).mp hab
    by_cases ha : a = 0
    · subst a
      have ex : D.Nonempty := by
        by_contra! he
        rw [he] at hD
        simp at hD
        omega
      obtain ⟨y,hy⟩ := ex
      apply (mem_pair f D 0 _).mpr
      exact ⟨y,mem_filter.mpr ⟨mem_univ _,by simp [twice]⟩,hy,by simpa using hy⟩
    · by_contra hn
      have hcost := (quadratic_deletion_cost f B hf ha x m).mp ⟨D,hD,hn⟩
      exact (hr a ha).not_ge hcost

/-- The tenfold bound survives a small exceptional set in the graph model inside A+A. -/
theorem approximate_model_green50 {n : ℕ} (A : Finset (Fin n → F₂))
    (U V : Submodule F₂ (Fin n → F₂)) (hc : IsCompl U V) (f : U → V)
    (B : U →ₗ[F₂] U →ₗ[F₂] V) (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a))
    (hmiss : (2*(Green50Graphs.graph U V f \ (A+A)).card)*Nat.card V < Nat.card U)
    (hd : (Module.finrank F₂ V : ℝ) ≤ Real.logb 2 (1/(A.dens:ℝ))) :
    ∃ (W : Submodule F₂ (Fin n → F₂)) (v : Fin n → F₂),
      v +ᵥ (W : Set (Fin n → F₂)) ⊆ ↑((10:ℕ) • A) ∧
      (n:ℝ)-Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W := by
  classical
  let e := U.prodEquivOfIsCompl V hc
  let emb (x : U) := e (x,f x)
  let D := univ.filter fun x : U => emb x ∈ A+A
  have inj : Function.Injective emb := fun _ _ h => congrArg Prod.fst (e.injective h)
  have h₁ : Dᶜ.image emb = Green50Graphs.graph U V f \ (A+A) := by
    ext x
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := mem_image.mp h
      exact mem_sdiff.mpr ⟨mem_image_of_mem _ (mem_univ u),fun ha => (mem_compl.mp hu)
        (mem_filter.mpr ⟨mem_univ _,ha⟩)⟩
    · intro h
      obtain ⟨hg,hn⟩ := mem_sdiff.mp h
      obtain ⟨u,_,hu⟩ := mem_image.mp hg
      exact mem_image.mpr ⟨u,mem_compl.mpr (fun hd => hn ((show emb u = x from hu) ▸ (mem_filter.mp hd).2)),hu⟩
  have hcnt := congrArg Finset.card h₁
  rw [card_image_of_injective _ inj] at hcnt
  rw [←hcnt,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card] at hmiss
  have heq := sums_preserved_of_card f B hf D hmiss 3
  change (5:ℕ) • retained f D = (5:ℕ) • Green50QuadraticGraphs.graph f at heq
  obtain ⟨S,t,hS,hs⟩ := Green50QuadraticBogolyubov.fivefold_quadratic_flat f B hf
  have hin : (retained f D).image e ⊆ A+A := by
    rintro _ hi
    obtain ⟨_,hu,rfl⟩ := mem_image.mp hi
    obtain ⟨u,hD,rfl⟩ := mem_image.mp hu
    exact (mem_filter.mp hD).2
  have hemb : ((5:ℕ) • Green50QuadraticGraphs.graph f).image e ⊆ (10:ℕ) • A := by
    rw [←heq,image_nsmul]
    simpa only [←two_nsmul,←mul_smul,show (5:ℕ)*2=10 by decide] using nsmul_subset_nsmul_left (n:=5) hin
  refine ⟨S.map e.toLinearMap,e t,?_,?_⟩
  · rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
    apply hemb
    change e t + e w ∈ _
    rw [←map_add]
    exact mem_image_of_mem _ (hS w hw)
  · have hdim := e.finrank_eq
    rw [Module.finrank_prod,Module.finrank_fintype_fun_eq_card,Fintype.card_fin] at hdim
    rw [← (S.equivMapOfInjective e.toLinearMap e.injective).finrank_eq]
    have hreal : (Module.finrank F₂ U:ℝ) + Module.finrank F₂ V = n := by exact_mod_cast hdim
    have hreal' : (Module.finrank F₂ U:ℝ) ≤ Module.finrank F₂ S := by exact_mod_cast hs
    linarith

section Sharp
variable {Z : Type*} [AddCommGroup Z] [Module F₂ Z] [Fintype Z] [DecidableEq Z]

private def gate (p : F₂ × V × Z) : V := p.1 • p.2.1

private def gatePolar : (F₂ × V × Z) →ₗ[F₂] (F₂ × V × Z) →ₗ[F₂] V :=
  LinearMap.mk₂ F₂ (fun a x => a.1 • x.2.1 + x.1 • a.2.1)
    (by intro a b x; simp only [Prod.fst_add,Prod.snd_add,add_smul,smul_add]; abel)
    (by intro c a x; simp only [Prod.smul_fst,Prod.smul_snd,smul_add,smul_eq_mul,mul_smul]; rw [smul_comm x.1 c])
    (by intro a x y; simp only [Prod.fst_add,Prod.snd_add,add_smul,smul_add]; abel)
    (by intro c a x; simp only [Prod.smul_fst,Prod.smul_snd,smul_add,smul_eq_mul,mul_smul]; rw [smul_comm a.1 c])

omit [DecidableEq V] [Fintype Z] [DecidableEq Z] in
private theorem gate_quadratic (a x : F₂ × V × Z) :
    gate x + gate (x+a) = gatePolar a x + (gate (0:F₂ × V × Z) + gate a) := by
  change _ = (a.1 • x.2.1 + x.1 • a.2.1) + _
  simp only [gate,Prod.fst_add,Prod.snd_add,Prod.fst_zero,zero_smul,zero_add,add_smul,smul_add]
  have := twice (x.1 • x.2.1)
  abel_nf at *
  rw [this]
  abel

/-- The codomain-size bound is sharp: a graph with domain F₂ × V × Z and output V
can lose a twofold sum after exactly |Z| deletions. -/
theorem sharp_output_bound :
    ∃ (f : F₂ × V × Z → V) (B : (F₂ × V × Z) →ₗ[F₂] (F₂ × V × Z) →ₗ[F₂] V)
      (D : Finset (F₂ × V × Z)), (∀ a x, f x + f (x+a) = B a x + (f 0+f a)) ∧
        Dᶜ.card = Fintype.card Z ∧
        (2:ℕ) • retained f D ≠ (2:ℕ) • Green50QuadraticGraphs.graph f := by
  classical
  let a : F₂ × V × Z := (1,0,0)
  let removed := (univ : Finset Z).image (fun z => ((0:F₂),(0:V),z))
  refine ⟨gate,gatePolar,removedᶜ,gate_quadratic,?_,?_⟩
  · rw [compl_compl,card_image_of_injective _ (fun _ _ h => congrArg (fun p : F₂ × V × Z => p.2.2) h),card_univ]
  · intro he
    have hw : (a,(0:V)) ∈ (2:ℕ) • Green50QuadraticGraphs.graph gate :=
      (Green50QuadraticGraphs.twofold_fibre _ _ _).mpr ⟨0,by simp [gate,a]⟩
    rw [←he] at hw
    obtain ⟨⟨t,v,z⟩,hx,hy,hz⟩ := (mem_pair _ _ _ _).mp hw
    have e := (mem_filter.mp hx).2
    change t • v + (t+1) • (v+0) = 0 at e
    rw [add_zero,add_smul,one_smul,←add_assoc,twice,zero_add] at e
    subst v
    rcases (show ∀ t:F₂, t=0 ∨ t=1 from by decide) t with rfl|rfl
    · exact (mem_compl.mp hy) (mem_image_of_mem _ (mem_univ z))
    · apply (mem_compl.mp hz)
      have h : ((0:F₂),(0:V),z) ∈ removed := mem_image_of_mem _ (mem_univ z)
      simpa [a,show (1:F₂)+1=0 by decide] using h
end Sharp

end Green50GraphDeletions

#print axioms Green50GraphDeletions.deletion_bound
#print axioms Green50GraphDeletions.exact_deletion_cost
#print axioms Green50GraphDeletions.quadratic_deletion_cost
#print axioms Green50GraphDeletions.sums_preserved
#print axioms Green50GraphDeletions.all_deletions_iff
#print axioms Green50GraphDeletions.sums_preserved_of_card
#print axioms Green50GraphDeletions.sharp_output_bound
#print axioms Green50GraphDeletions.approximate_model_green50
