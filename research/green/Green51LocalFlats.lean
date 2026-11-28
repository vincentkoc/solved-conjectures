import Green51AffineMatchings
import Green51SparseBounds

/-! # Local label sets representing an affine flat in a binary double -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51LocalFlats
local notation "F" => ZMod 2
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- Every represented flat has a finite witness whose affine span needs at
most one free endpoint per pair in addition to the dimension of the flat. -/
theorem local_labels (A : Finset G) (W : Submodule F G) (p : G)
    (inside : p +ᵥ (W : Set G) ⊆ ↑(A+A)) :
    ∃ (B : Finset G) (L : Submodule F G) (a : G), B⊆A ∧
      p +ᵥ (W : Set G) ⊆ ↑(B+B) ∧ (∀ x∈B,x+a∈L) ∧ W≤L ∧ p∈L ∧
      B.card≤2^(Module.finrank F W+1) ∧
      Module.finrank F L≤2^Module.finrank F W+Module.finrank F W := by
  classical
  have pair (w : W) : ∃ x∈A, ∃ y∈A, x+y=p+w.val :=
    mem_add.mp (inside ⟨w.val,w.property,rfl⟩)
  choose x hx y hy relation using pair
  let B := univ.image x ∪ univ.image y
  let a := x 0
  let points := (univ.erase (0:W)).image fun w => x w+a
  let basis := insert p points
  let V := Submodule.span F (basis : Set G)
  let L := V⊔W
  have pow : Fintype.card W=2^(Module.finrank F W) := by rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
  have pv : p∈V := Submodule.subset_span (s:= (basis:Set G)) (mem_insert_self _ _)
  have xv (w : W) : x w+a∈V := by
    by_cases h : w=0
    · subst w;change a+a∈V;simp [ZModModule.add_self]
    · apply Submodule.subset_span (s:= (basis:Set G))
      exact mem_insert_of_mem (mem_image.mpr ⟨w,mem_erase.mpr ⟨h,mem_univ _⟩,rfl⟩)
  have vl : V≤L := le_sup_left
  have wl : W≤L := le_sup_right
  refine ⟨B,L,a,?_,?_,?_,wl,vl pv,?_,?_⟩
  · intro z hz
    rcases mem_union.mp hz with l|r
    · obtain ⟨w,_,rfl⟩ := mem_image.mp l;exact hx w
    · obtain ⟨w,_,rfl⟩ := mem_image.mp r;exact hy w
  · rintro _ ⟨w,hw,rfl⟩
    let t : W := ⟨w,hw⟩
    apply mem_add.mpr
    exact ⟨x t,mem_union_left _ (mem_image_of_mem _ (mem_univ _)),y t,
      mem_union_right _ (mem_image_of_mem _ (mem_univ _)),relation t⟩
  · intro z hz
    rcases mem_union.mp hz with l|r
    · obtain ⟨w,_,rfl⟩ := mem_image.mp l;exact vl (xv w)
    · obtain ⟨w,_,rfl⟩ := mem_image.mp r
      have eq : y w+a=(x w+a)+(p+w.val) := by
        rw [←relation,add_add_add_comm, ZModModule.add_self,zero_add,add_comm]
      rw [eq]
      exact L.add_mem (vl (xv w)) (L.add_mem (vl pv) (wl w.property))
  · have bound := (card_union_le (univ.image x) (univ.image y)).trans (Nat.add_le_add card_image_le card_image_le)
    simpa [B,pow_succ,←pow,Nat.mul_two] using bound
  · have span := finrank_span_le_card (R:=F) (basis : Set G)
    have upper : basis.card≤Fintype.card W := by
      have h := (card_insert_le p points).trans (Nat.add_le_add_right (card_image_le (s:=univ.erase (0:W)) (f:=fun w => x w+a)) 1)
      rw [card_erase_of_mem (mem_univ _),card_univ] at h
      have pos : 0<Fintype.card W := Fintype.card_pos
      change (insert p points).card≤_;omega
    have sb : Module.finrank F V≤basis.card := by simpa [V] using span
    have h := Submodule.finrank_sup_add_finrank_inf_eq V W
    change Module.finrank F ↥(V⊔W)≤_
    rw [pow] at upper
    omega

/-- A positive lower bound on the largest affine dimension is witnessed by a coset of that dimension. -/
theorem le_iff_coset {G : Type*} [AddCommGroup G] [Module F G] [Module.Finite F G]
    {d : ℕ} (pos : 0<d) (A : Set G) :
    d ≤ maxCosetDim F G A ↔ ∃ (W : Submodule F G) (p : G),
      Module.finrank F W=d ∧ p +ᵥ (W:Set G) ⊆ A := by
  classical
  let D : Set ℕ := {Module.finrank F S.direction | (S : AffineSubspace F G) (_h : (S:Set G) ⊆ A)}
  have top : BddAbove D := ⟨Module.finrank F G,by
    rintro _ ⟨S,_,rfl⟩;exact Submodule.finrank_le S.direction⟩
  change d ≤ sSup D ↔ _
  constructor
  · intro bound
    have attained := Nat.sSup_mem (show D.Nonempty from ⟨0,⊥,by simp,by simp⟩) top
    obtain ⟨S,sub,rank⟩ := attained
    have non : ∃ p,p∈S := by
      by_contra! empty
      have bot : S=⊥ := by ext x;simp only [AffineSubspace.notMem_bot,iff_false];exact empty x
      rw [bot,AffineSubspace.direction_bot] at rank
      simp only [finrank_bot] at rank;omega
    obtain ⟨p,hp⟩ := non
    have fits : Module.finrank F (Cube d)≤Module.finrank F S.direction := by simpa [Cube,rank] using bound
    obtain ⟨j,ji⟩ := finrank_le_iff_exists_linearMap.mp fits
    let f := S.direction.subtype.comp j
    have injective : Function.Injective f := S.direction.subtype_injective.comp ji
    refine ⟨f.range,p,by simpa [Cube] using f.finrank_range_of_inj injective,?_⟩
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    apply sub
    simpa [f,vadd_eq_add,add_comm] using AffineSubspace.vadd_mem_of_mem_direction (j x).property hp
  · rintro ⟨W,p,size,sub⟩
    apply le_csSup top
    refine ⟨AffineSubspace.mk' p W,?_,by rwa [AffineSubspace.direction_mk']⟩
    intro y hy
    apply sub
    exact ⟨y-p,AffineSubspace.mem_mk'.mp hy,by change p+(y-p)=y;abel⟩

private theorem flat_iff {n d : ℕ} (pos : 0<d) (A : Finset (Cube n)) :
    d ≤ maxCosetDim F (Cube n) ↑(A+A) ↔ ∃ (W : Submodule F (Cube n)) (p : Cube n),
      Module.finrank F W=d ∧ p +ᵥ (W:Set (Cube n)) ⊆ ↑(A+A) :=
  le_iff_coset pos _

/-- At any fixed target dimension, the original Green guarantee can be tested
using a bounded number of labels in bounded affine dimension. -/
theorem guaranteed_iff {n d : ℕ} (pos : 0<d) {α : ℝ} (one : α≤1) :
    d≤Green51.guaranteedMaxCosetDim n α ↔
      ∀ A : Finset (Cube n), α≤(A.dens:ℝ) →
        ∃ B⊆A, ∃ (L W : Submodule F (Cube n)) (a p : Cube n),
          B.card≤2^(d+1) ∧ Module.finrank F L≤2^d+d ∧
          (∀ x∈B,x+a∈L) ∧ Module.finrank F W=d ∧ p +ᵥ (W:Set (Cube n)) ⊆ ↑(B+B) := by
  constructor
  · intro h A ha
    have upper : Green51.guaranteedMaxCosetDim n α ≤ maxCosetDim F (Cube n) ↑(A+A) :=
      csInf_le (OrderBot.bddBelow _) ⟨A,ha,rfl⟩
    obtain ⟨W,p,dim,inside⟩ := (flat_iff pos A).mp (h.trans upper)
    obtain ⟨B,L,a,sub,restricted,ambient,_,_,count,rank⟩ := local_labels A W p inside
    exact ⟨B,sub,L,W,a,p,dim ▸ count,dim ▸ rank,ambient,dim,restricted⟩
  · intro h
    apply le_csInf
    · refine ⟨_,univ,?_,rfl⟩;simpa using one
    · rintro _ ⟨A,ha,rfl⟩
      obtain ⟨B,sub,_,W,_,p,_,_,_,rank,inside⟩ := h A ha
      exact (flat_iff pos A).mpr ⟨W,p,rank,inside.trans (show (↑(B+B):Set (Cube n))⊆ ↑(A+A) from Finset.coe_subset.mpr (add_subset_add sub sub))⟩

abbrev Alphabet (d : ℕ) := Cube d
abbrev Ambient (d : ℕ) := (Alphabet d → F) × (F × Alphabet d)

def leftPoint {d : ℕ} (z : Alphabet d) : Ambient d := (Pi.single z 1,0,0)
def rightPoint {d : ℕ} (z : Alphabet d) : Ambient d := (Pi.single z 1,1,z)
def labels (d : ℕ) : Finset (Ambient d) :=
  univ.image leftPoint ∪ univ.image rightPoint

private theorem left_inj {d : ℕ} : Function.Injective (@leftPoint d) := by
  intro x y eq
  by_contra h
  have t := congrFun (congrArg Prod.fst eq) x
  change (Pi.single x 1 : Alphabet d → F) x=(Pi.single y 1 : Alphabet d → F) x at t
  simp [h] at t

private theorem right_inj {d : ℕ} : Function.Injective (@rightPoint d) := fun _ _ eq =>
  congrArg (fun z : Ambient d => z.2.2) eq

private theorem disjoint_images {d : ℕ} (X Y : Finset (Alphabet d)) :
    Disjoint (X.image leftPoint) (Y.image rightPoint) := by
  rw [disjoint_left];intro z hl hr
  obtain ⟨x,_,rfl⟩ := mem_image.mp hl
  obtain ⟨y,_,eq⟩ := mem_image.mp hr
  exact (by decide : (1:F)≠0) (congrArg (fun z : Ambient d => z.2.1) eq)

theorem label_count (d : ℕ) : (labels d).card=2^(d+1) := by
  rw [labels,card_union_of_disjoint (disjoint_images _ _),card_image_of_injective _ left_inj,
    card_image_of_injective _ right_inj,card_univ,pow_succ,Nat.mul_two]
  simp [Alphabet,Cube]

theorem label_free (d : ℕ) : ∀ T⊆labels d, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0 := by
  intro T sub sz zero
  let X := univ.filter fun x : Alphabet d => leftPoint x∈T
  let Y := univ.filter fun x : Alphabet d => rightPoint x∈T
  have split : T=X.image leftPoint∪Y.image rightPoint := by
    ext z
    constructor
    · intro hz;rcases mem_union.mp (sub hz) with l|r
      · obtain ⟨x,_,rfl⟩ := mem_image.mp l
        exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hz⟩))
      · obtain ⟨x,_,rfl⟩ := mem_image.mp r
        exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hz⟩))
    · intro hz;rcases mem_union.mp hz with l|r
      · obtain ⟨x,hx,rfl⟩ := mem_image.mp l;exact (mem_filter.mp hx).2
      · obtain ⟨x,hx,rfl⟩ := mem_image.mp r;exact (mem_filter.mp hx).2
  rw [split,sum_union (disjoint_images _ _),sum_image left_inj.injOn,sum_image right_inj.injOn] at zero
  have both : X=Y := by
    ext i
    have h := congrFun (congrArg Prod.fst zero) i
    simp only [Prod.fst_add,Prod.fst_sum,leftPoint,rightPoint,Prod.fst_zero,Finset.sum_apply,
      Pi.add_apply,Pi.zero_apply,Finset.sum_pi_single] at h
    by_cases l : i∈X <;> by_cases r : i∈Y <;> simp_all
  rw [split,card_union_of_disjoint (disjoint_images _ _),card_image_of_injective _ left_inj,
    card_image_of_injective _ right_inj,both] at sz
  have even : 2∣Y.card := by
    have h := congrArg (fun z : Ambient d => z.2.1) zero
    simpa [Prod.fst_sum,Prod.snd_sum,leftPoint,rightPoint,ZMod.natCast_eq_zero_iff] using h
  have two : Y.card=2 := by omega
  obtain ⟨x,y,ne,xy⟩ := card_eq_two.mp two
  have h := congrArg (fun z : Ambient d => z.2.2) zero
  have total : ∑ y∈Y,y=0 := by simpa [Prod.snd_sum,leftPoint,rightPoint] using h
  rw [xy,sum_pair ne] at total
  exact ne (add_right_cancel (total.trans (ZModModule.add_self _).symm))

theorem model_flat (d : ℕ) :
    ∃ (W : Submodule F (Ambient d)) (p : Ambient d), Module.finrank F W=d ∧
      p +ᵥ (W : Set (Ambient d)) ⊆ ↑(labels d+labels d) := by
  let j : Alphabet d →ₗ[F] Ambient d :=
    (LinearMap.inr F (Alphabet d → F) (F×Alphabet d)).comp (LinearMap.inr F F (Alphabet d))
  have inj : Function.Injective j := LinearMap.inr_injective.comp LinearMap.inr_injective
  refine ⟨j.range,(0,1,0),?_,?_⟩
  · simpa [Alphabet,Cube] using j.finrank_range_of_inj inj
  · rintro _ ⟨_,⟨z,hz⟩,rfl⟩;subst_vars
    apply mem_add.mpr
    refine ⟨leftPoint z,mem_union_left _ (mem_image_of_mem _ (mem_univ _)),rightPoint z,
      mem_union_right _ (mem_image_of_mem _ (mem_univ _)),?_⟩
    change (Pi.single z 1 + Pi.single z 1, _)=_
    simp [j,Prod.mk_add_mk,vadd_eq_add,leftPoint,rightPoint,ZModModule.add_self]

/-- The universal paired labels span their ambient linear space. -/
theorem full_of_labels {d : ℕ} (U : Submodule F (Ambient d))
    (raw : ∀ x∈labels d,x∈U) : U=⊤ := by
  have hl (z : Alphabet d) := raw (leftPoint z) (mem_union_left _ (mem_image_of_mem _ (mem_univ z)))
  have hr (z : Alphabet d) := raw (rightPoint z) (mem_union_right _ (mem_image_of_mem _ (mem_univ z)))
  have v (z : Alphabet d) : (0,1,z)∈U := by
    simpa [leftPoint,rightPoint,Prod.mk_add_mk,ZModModule.add_self] using U.add_mem (hl z) (hr z)
  have v0 (z : Alphabet d) : (0,0,z)∈U := by
    simpa [Prod.mk_add_mk,ZModModule.add_self] using U.add_mem (v z) (v 0)
  have hor (f : Alphabet d → F) : (f,0,0)∈U := by
    have h := U.sum_mem (t:=univ) (f:=fun z => f z • leftPoint z) (fun z _ => U.smul_mem _ (hl z))
    have eq : ∑ z,f z • leftPoint z=(f,0,0) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext i;simp [Prod.fst_sum,leftPoint,Finset.sum_apply,Pi.single_apply,mul_ite]
      · simp [Prod.snd_sum,leftPoint]
      · simp [Prod.snd_sum,leftPoint]
    exact eq ▸ h
  apply top_unique
  rintro ⟨f,b,z⟩ _
  rcases (show ∀ x:F,x=0 ∨ x=1 from by decide) b with h|h <;> subst b
  · simpa [Prod.mk_add_mk] using U.add_mem (hor f) (v0 z)
  · simpa [Prod.mk_add_mk] using U.add_mem (hor f) (v z)

theorem label_rank {d : ℕ} (L : Submodule F (Ambient d)) (a : Ambient d)
    (inside : ∀ x∈labels d,x+a∈L) : 2^d+d≤Module.finrank F L := by
  let V := Submodule.span F ({a}:Set (Ambient d))
  let U := L⊔V
  have lu : L≤U := le_sup_left
  have vu : V≤U := le_sup_right
  have au : a∈U := vu (Submodule.subset_span (Set.mem_singleton _))
  have raw (x : Ambient d) (hx : x∈labels d) : x∈U := by
    simpa only [add_assoc,ZModModule.add_self,add_zero] using U.add_mem (lu (inside x hx)) au
  have full := full_of_labels U raw
  have h := Submodule.finrank_sup_add_finrank_inf_eq L V
  change Module.finrank F U+_= _ at h
  rw [full,finrank_top] at h
  have dim : Module.finrank F (Ambient d)=2^d+(1+d) := by simp [Ambient,Alphabet,Cube,Module.finrank_prod]
  have vd : Module.finrank F V≤1 := by
    simpa [V] using finrank_span_le_card (R:=F) ({a}:Set (Ambient d))
  omega

/-- The universal local dimension bound is sharp for each rank at least
three. In this example, every subset representing a flat of that rank must
be the entire label set and has the indicated affine dimension. -/
theorem worst_case (d : ℕ) (large : 3≤d) :
    ∃ A : Finset (Ambient d), A.card=2^(d+1) ∧
      (¬∃ V : Submodule F (Ambient d), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A) ∧
      (∃ (W : Submodule F (Ambient d)) (p : Ambient d),
        Module.finrank F W=d ∧ p +ᵥ (W:Set (Ambient d)) ⊆ ↑(A+A)) ∧
      ∀ B⊆A, (∃ (W : Submodule F (Ambient d)) (p : Ambient d),
        Module.finrank F W=d ∧ p +ᵥ (W:Set (Ambient d)) ⊆ ↑(B+B)) →
        B=A ∧ ∀ (L : Submodule F (Ambient d)) (a : Ambient d),
          (∀ x∈B,x+a∈L) → 2^d+d≤Module.finrank F L := by
  let A := labels d
  have avoid : ¬∃ V : Submodule F (Ambient d), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A := by
    rintro ⟨V,sz,inside⟩
    have bound := Green51SparseDimensions.rank_without_relation A (label_free d) V inside
    omega
  refine ⟨A,label_count d,avoid,model_flat d,?_⟩
  intro B sub witness
  obtain ⟨W,p,dim,inside⟩ := witness
  have avoidB : ¬∃ V : Submodule F (Ambient d), Module.finrank F V=3 ∧ ∀ v∈V,v∈B+B := by
    rintro ⟨V,sz,mem⟩; exact avoid ⟨V,sz,fun w h => add_subset_add sub sub (mem w h)⟩
  have cost := Green51AffineMatchings.affine_flat_cost B avoidB W p inside (by omega)
  rw [dim,←label_count d] at cost
  have eq := eq_of_subset_of_card_le sub cost
  refine ⟨eq,?_⟩
  rw [eq]
  exact label_rank

/-- An affine flat in a binary double supplies a linear image of the
universal pair configuration. Its direction map remains injective. -/
theorem model_image {d : ℕ} (A : Finset G) (W : Submodule F G)
    (rank : Module.finrank F W=d) (p : G) (inside : p +ᵥ (W:Set G) ⊆ ↑(A+A)) :
    ∃ (f : Ambient d →ₗ[F] G) (j : Cube d ≃ₗ[F] W),
      (labels d).image f ⊆ A ∧ ∀ z : Cube d,f (0,1,z)=p+(j z).val := by
  classical
  let j : Cube d ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by simp [Cube,rank])
  have pair (z : Cube d) : ∃ x∈A,∃ y∈A,x+y=p+(j z).val := mem_add.mp (inside ⟨_,(j z).property,rfl⟩)
  choose x hx y hy eq using pair
  let h := Fintype.linearCombination F x
  let v := (LinearMap.toSpanSingleton F G p).coprod (W.subtype.comp j.toLinearMap)
  let f := h.coprod v
  have single (z : Cube d) : h (Pi.single z 1)=x z := by
    simp [h,Fintype.linearCombination_apply,Pi.single_apply,ite_smul]
  refine ⟨f,j,?_,?_⟩
  · rintro _ hz
    obtain ⟨pt,hpt,rfl⟩ := mem_image.mp hz
    rcases mem_union.mp hpt with hl|hr
    · obtain ⟨z,_,rfl⟩ := mem_image.mp hl
      simpa [f,v,leftPoint,LinearMap.coprod_apply,single] using hx z
    · obtain ⟨z,_,rfl⟩ := mem_image.mp hr
      simpa [f,v,rightPoint,LinearMap.coprod_apply,single,←eq,←add_assoc,ZModModule.add_self] using hy z
  · intro z;simp [f,v,LinearMap.coprod_apply]

end Green51LocalFlats

#print axioms Green51LocalFlats.local_labels
#print axioms Green51LocalFlats.guaranteed_iff
#print axioms Green51LocalFlats.worst_case

#print axioms Green51LocalFlats.label_rank
#print axioms Green51LocalFlats.full_of_labels
#print axioms Green51LocalFlats.label_count
#print axioms Green51LocalFlats.label_free
#print axioms Green51LocalFlats.model_flat
#print axioms Green51LocalFlats.model_image
#print axioms Green51LocalFlats.le_iff_coset
