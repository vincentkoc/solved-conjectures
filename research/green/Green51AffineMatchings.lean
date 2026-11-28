import Green51AffineSeparation

/-! # Pair representations on affine flats in binary doubles -/

open Finset Green50Downsets Green50Sharp Green51SparseDimensions
open scoped Classical Pointwise
namespace Green51AffineMatchings
local notation "F" => ZMod 2

private theorem weight_sum {n : ℕ} (u v : Cube n) :
    (supp (u+v)).card+2*(supp u∩supp v).card=(supp u).card+(supp v).card := by
  have dis : Disjoint (supp u\supp v) (supp v\supp u) := by
    rw [disjoint_left]; intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  have xor : supp (u+v)=(supp u\supp v)∪(supp v\supp u) := by
    ext i
    have bit (a:F) : a=0 ∨ a=1 := (show ∀ t:F,t=0 ∨ t=1 from by decide) a
    rcases bit (u i) with hu|hu <;> rcases bit (v i) with hv|hv <;> simp [supp,hu,hv,show (1:F)+1=0 by decide]
  rw [xor,card_union_of_disjoint dis]
  have h := card_sdiff_add_card_inter (supp u) (supp v)
  have j := card_sdiff_add_card_inter (supp v) (supp u)
  rw [inter_comm (supp v)] at j
  omega

private theorem outside_sum {n : ℕ} (u v : Cube n) (T : Finset (Fin n)) :
    (supp (u+v)\T).card≤(supp u\T).card+(supp v\T).card := by
  apply le_trans (card_le_card (t:=(supp u\T)∪(supp v\T)) ?_) (card_union_le _ _)
  intro i hi
  obtain ⟨sum,off⟩ := mem_sdiff.mp hi
  by_cases h : i∈supp u
  · exact mem_union_left _ (mem_sdiff.mpr ⟨h,off⟩)
  · refine mem_union_right _ (mem_sdiff.mpr ⟨?_,off⟩)
    simp [supp] at h sum ⊢
    simpa [h] using sum

private theorem weight_pos {n : ℕ} {u : Cube n} (nz : u≠0) : 0 < (supp u).card := by
  apply card_pos.mpr
  by_contra! empty
  apply nz
  funext i
  have h : i∉supp u := by simp [empty]
  simpa [supp] using h

/-- In distance at least seven, the distinct weight-two representatives of an
affine flat of dimension at least three have disjoint coordinate supports. -/
theorem disjoint_supports {G : Type*} [AddCommGroup G] [Module F G]
    {N : ℕ} (P : Cube N →ₗ[F] G)
    (kernel : ∀ z, (supp z).card≤6 → P z=0 → z=0)
    (W : Submodule F G) (t : G) (f : W → Cube N)
    (two : ∀ u, (supp (f u)).card=2) (maps : ∀ u, P (f u)=t+u.val)
    (rank : 3≤Module.finrank F W) :
    ∀ a b : W, a≠b → Disjoint (supp (f a)) (supp (f b)) := by
  intro a b distinct
  by_contra overlap
  let D := f a+f b
  have imageD : P D=a.val+b.val := by
    dsimp only [D]; rw [map_add,maps,maps,add_add_add_comm,ZModModule.add_self,zero_add]
  have nz : D≠0 := by
    intro eq
    have h := imageD.symm.trans (eq ▸ P.map_zero)
    exact distinct (Subtype.ext (add_right_cancel (h.trans (ZModModule.add_self b.val).symm)))
  have wt : (supp D).card=2 := by
    have both : 0 < (supp (f a)∩supp (f b)).card :=
      card_pos.mpr (not_disjoint_iff_nonempty_inter.mp overlap)
    have count := weight_sum (f a) (f b)
    rw [two,two] at count
    have pos := weight_pos nz
    change (supp D).card+_= _ at count
    omega
  let T := supp D
  have changed (u : W) : f (u+(a+b))=f u+D := by
    let z := f (u+(a+b))+(f u+D)
    have small : (supp z).card≤6 := by
      have sum := weight_sum (f (u+(a+b))) (f u+D)
      have other := weight_sum (f u) D
      rw [two] at sum
      rw [two,wt] at other
      dsimp only [z]; omega
    have zero : P z=0 := by
      simp only [z,map_add,maps,imageD,Submodule.coe_add]
      convert ZModModule.add_self (t+(u.val+(a.val+b.val))) using 1; abel
    exact add_right_cancel ((kernel z small zero).trans (ZModModule.add_self (f u+D)).symm)
  have outside (u : W) : (supp (f u)\T).card≤1 := by
    have cnt := weight_sum (f u) D
    rw [←changed,two,two,wt] at cnt
    have rest := card_sdiff_add_card_inter (supp (f u)) T
    rw [two] at rest
    dsimp only [T] at *
    omega
  have short (u v : W) : (f (u+v)+f 0)+(f u+f v)=0 := by
    let z := (f (u+v)+f 0)+(f u+f v)
    have small : (supp z).card≤6 := by
      have p := outside_sum (f (u+v)+f 0) (f u+f v) T
      have q := outside_sum (f (u+v)) (f 0) T
      have r := outside_sum (f u) (f v) T
      have h := card_sdiff_add_card_inter (supp z) T
      have sh : (supp z∩T).card≤2 := (card_le_card inter_subset_right).trans_eq wt
      change (supp z\T).card≤_ at p
      have := outside (u+v); have := outside (0:W)
      have := outside u; have := outside v
      omega
    apply kernel z small
    simp only [z,map_add,maps,Submodule.coe_add,Submodule.coe_zero,add_zero]
    calc
      _ = ((t+t)+(t+t))+((u.val+u.val)+(v.val+v.val)) := by abel
      _ = 0 := by simp [ZModModule.add_self]
  have small := Green50BCH.affine_lift_dimension (r:=2) P W t f
    (fun u => mem_filter.mpr ⟨mem_univ _,(two u).le⟩) maps short
  omega

private theorem five_labels {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (A : Finset G) (W : Submodule F G) (t : G)
    (inside : t +ᵥ (W : Set G) ⊆ ↑(A+A)) (high : 3≤Module.finrank F W) : 5≤A.card := by
  classical
  have cover : A+A⊆insert 0 ((A.powersetCard 2).image fun T => ∑ a∈T,a) := by
    rintro _ h
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
    by_cases eq : a=b
    · rw [eq,ZModModule.add_self]; exact mem_insert_self _ _
    · apply mem_insert_of_mem
      refine mem_image.mpr ⟨{a,b},mem_powersetCard.mpr ⟨by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro ha hb,by simp [eq]⟩,?_⟩
      rw [sum_pair eq]
  have bound := (card_le_card cover).trans (card_insert_le _ _)
  have pairs := card_image_le (s:=A.powersetCard 2) (f:=fun T => ∑ a∈T,a)
  rw [card_powersetCard] at pairs
  let inj : W ↪ G := ⟨fun w => t+w.val,fun _ _ eq => Subtype.ext (add_left_cancel eq)⟩
  have embeds : (univ.map inj)⊆A+A := by
    rintro _ hw; obtain ⟨w,_,rfl⟩ := mem_map.mp hw
    exact inside ⟨w.val,w.property,rfl⟩
  have count := card_le_card embeds
  rw [card_map,card_univ,Module.card_eq_pow_finrank (K:=F),ZMod.card] at count
  by_contra! few
  have small := Nat.choose_le_choose 2 (show A.card≤4 by omega)
  have big := Nat.pow_le_pow_right (by decide : 0 < 2) high
  rw [show (4:ℕ).choose 2=6 by decide] at small
  norm_num at big
  omega

/-- Any affine flat of dimension d≥3 in a double with no linear three-space
requires at least 2^(d+1) points in the original set. -/
theorem affine_flat_cost {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (A : Finset G) (avoid : ¬∃ V : Submodule F G, Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A)
    (W : Submodule F G) (t : G) (inside : t +ᵥ (W : Set G) ⊆ ↑(A+A))
    (rank : 3≤Module.finrank F W) : 2^(Module.finrank F W+1)≤A.card := by
  classical
  have large := five_labels A W t inside rank
  have free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ a∈T,a)≠0 :=
    fun T sub num sum => avoid ((linear_three_iff A large).mpr ⟨T,sub,num,sum⟩)
  have notIn : t∉W := by
    intro ht
    have dim := rank_without_relation A free W (fun w hw => inside
      ⟨t+w,W.add_mem ht hw,by change t+(t+w)=w; rw [←add_assoc,ZModModule.add_self,zero_add]⟩)
    omega
  obtain ⟨P,kernel,lifts⟩ := pair_check A free
  let J := LinearMap.inr F F G
  have inj : Function.Injective J := LinearMap.inr_injective
  let V := W.map J
  have dims : Module.finrank F W=Module.finrank F V := (W.equivMapOfInjective J inj).finrank_eq
  have ex (v : V) : ∃ z, P z=J t+v.val ∧ (supp z).card=2 := by
    obtain ⟨w,hw,h⟩ := v.property
    have nz : t+w≠0 := fun eq => notIn ((add_right_cancel (eq.trans (ZModModule.add_self w).symm) : t=w) ▸ hw)
    obtain ⟨z,eq,_,size⟩ := lifts (t+w) (inside ⟨w,hw,rfl⟩)
    exact ⟨z,by rw [←h,←map_add];exact eq,size nz⟩
  choose f fp two using ex
  have dis := disjoint_supports P kernel V (J t) f two fp (dims ▸ rank)
  let union := univ.biUnion fun v : V => supp (f v)
  have count : union.card=(Fintype.card V)*2 := by
    rw [show union.card=∑ v : V,(supp (f v)).card from card_biUnion (fun a _ b _ ne => dis a b ne)]
    simp [two]
  have cost := union.card_le_univ
  rwa [count,Fintype.card_fin,Module.card_eq_pow_finrank (K:=F),ZMod.card,←dims,←pow_succ] at cost

/-- Equality in the affine flat cost occurs in ambient dimension 3(d+1) at
every d≥3, using the classical graph (x,x³,x⁵). -/
theorem sharp_examples (d : ℕ) (hd : 3≤d) :
    ∃ A : Finset (Cube (3*(d+1))), A.card=2^(d+1) ∧
      (¬∃ V : Submodule F (Cube (3*(d+1))), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A) ∧
      ∃ (W : Submodule F (Cube (3*(d+1)))) (t : Cube (3*(d+1))),
        Module.finrank F W=d ∧ t +ᵥ (W : Set (Cube (3*(d+1)))) ⊆ ↑(A+A) := by
  classical
  let K := GaloisField 2 (d+1)
  let : Fintype K := Fintype.ofFinite K
  let A := univ.image (Green51AffineSeparation.graphPoint (K:=K))
  have fieldDim : Module.finrank F K=d+1 := GaloisField.finrank 2 (by omega)
  have fieldSize : Fintype.card K=2^(d+1) := by
    rw [←Nat.card_eq_fintype_card]; exact GaloisField.card 2 (d+1) (by omega)
  have large : 5≤Fintype.card K := by
    rw [fieldSize]; exact le_trans (by decide : 5≤2^4) (Nat.pow_le_pow_right (by decide) (by omega))
  let e : (Fin 3 → K) ≃ₗ[F] Cube (3*(d+1)) := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi_fintype,Module.finrank_pi,Fintype.card_fin]; simp [fieldDim])
  let B := A.image e
  have forward {y : Fin 3 → K} (h : y∈A+A) : e y∈B+B := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
    rw [map_add]; exact add_mem_add (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
  have back {y} (h : y∈B+B) : e.symm y∈A+A := by
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hb
    simpa only [map_add,LinearEquiv.symm_apply_apply] using add_mem_add hx hz
  refine ⟨B,?_,?_,?_⟩
  · dsimp only [B,A]; rw [card_image_of_injective _ e.injective,Green51AffineSeparation.graph_size,fieldSize]
  · rintro ⟨V,rank,inside⟩
    apply Green51AffineSeparation.graph_linear_avoidance large
    refine ⟨V.map e.symm.toLinearMap,(V.equivMapOfInjective _ e.symm.injective).finrank_eq.symm.trans rank,?_⟩
    rintro _ ⟨v,hv,rfl⟩; exact back (inside v hv)
  · obtain ⟨W,t,rank,inside⟩ := Green51AffineSeparation.graph_derivative_flat (K:=K)
    refine ⟨W.map e.toLinearMap,e t,(W.equivMapOfInjective _ e.injective).finrank_eq.symm.trans (by omega),?_⟩
    rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
    have h : t+w∈A+A := inside ⟨w,hw,rfl⟩
    change e t+e w∈B+B
    simpa only [map_add] using forward h

/-- Over all binary cubes, 2^(d+1) is the least label count supporting
an affine d-space in a double which contains no linear three-space. -/
theorem least_labels (d : ℕ) (hd : 3≤d) :
    IsLeast {k : ℕ | ∃ n, ∃ A : Finset (Cube n), A.card=k ∧
      (¬∃ V : Submodule F (Cube n), Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A) ∧
      ∃ (W : Submodule F (Cube n)) (t : Cube n),
        Module.finrank F W=d ∧ t +ᵥ (W : Set (Cube n)) ⊆ ↑(A+A)} (2^(d+1)) := by
  constructor
  · exact ⟨3*(d+1),sharp_examples d hd⟩
  · rintro _ ⟨n,A,rfl,avoid,W,t,rfl,inside⟩
    exact affine_flat_cost A avoid W t inside hd

end Green51AffineMatchings

#print axioms Green51AffineMatchings.disjoint_supports
#print axioms Green51AffineMatchings.affine_flat_cost
#print axioms Green51AffineMatchings.sharp_examples
#print axioms Green51AffineMatchings.least_labels

