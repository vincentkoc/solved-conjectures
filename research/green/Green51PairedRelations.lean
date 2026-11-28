import Green51Hadamard
import Green51LocalFlats

/-! # Even relations among sixteen paired labels -/

open Finset Green50Downsets Green50Sharp Green51LocalFlats
open scoped Classical Pointwise
namespace Green51PairedTypes
local notation "F" => ZMod 2
abbrev Positions := Cube 3
abbrev Slots := Positions × F
abbrev Space := Ambient 3

def label (i : Slots) : Space := (Pi.single i.1 1,i.2,i.2 • i.1)

private theorem label_zero (z : Positions) : label (z,0)=leftPoint z := by simp [label,leftPoint]
private theorem label_one (z : Positions) : label (z,1)=rightPoint z := by simp [label,rightPoint]

theorem labels_eq : labels 3=univ.image label := by
  ext x
  constructor
  · intro h;rcases mem_union.mp h with l|r
    · obtain ⟨z,_,rfl⟩ := mem_image.mp l
      exact mem_image.mpr ⟨(z,0),mem_univ _,label_zero z⟩
    · obtain ⟨z,_,rfl⟩ := mem_image.mp r
      exact mem_image.mpr ⟨(z,1),mem_univ _,label_one z⟩
  · intro h;obtain ⟨⟨z,b⟩,_,rfl⟩ := mem_image.mp h
    rcases (show ∀ u:F,u=0 ∨ u=1 from by decide) b with h|h <;> subst b
    · rw [label_zero];exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
    · rw [label_one];exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))

def parity : Space →ₗ[F] F := {
  toFun := fun h => ∑ i,h.1 i
  map_add' := by intros;simp [sum_add_distrib]
  map_smul' := by intros;simp [mul_sum] }

private def code : (Slots → F) →ₗ[F] Space := Fintype.linearCombination F label
private def support (w : Slots → F) := univ.filter fun i => w i≠0

private theorem eval (w : Slots → F) : code w=∑ i∈support w,label i := by
  simp only [code,Fintype.linearCombination_apply,support,sum_filter]
  apply sum_congr rfl
  intro i _
  rcases (show ∀ x:F,x=0 ∨ x=1 from by decide) (w i) with h|h <;> simp [h]

private theorem onto : Function.Surjective code := by
  rw [←LinearMap.range_eq_top]
  apply full_of_labels
  intro v hv
  rw [labels_eq] at hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  refine ⟨Pi.single i 1,?_⟩
  simp [code,Fintype.linearCombination_apply,Pi.single_apply,ite_smul]

theorem parity_label (i : Slots) : parity (label i)=1 := by simp [parity,label,Pi.single_apply]
private theorem parity_word (w : Slots → F) : parity (code w)=(support w).card := by simp [eval,map_sum,parity_label]

private theorem horizontal (w : Slots → F) (z : Positions) :
    (code w).1 z=w (z,0)+w (z,1) := by
  simp only [code,Fintype.linearCombination_apply,Prod.fst_sum,Finset.sum_apply,
    Prod.smul_fst,Pi.smul_apply,label,smul_eq_mul,Fintype.sum_prod_type]
  simp only [show ∀ f:F→F, (∑ b,f b)=f 0+f 1 from fun f => Fin.sum_univ_two f,
    Pi.single_apply,mul_ite,mul_one,mul_zero]
  simp [sum_add_distrib]

private theorem affine_in_kernel (l : Positions →ₗ[F] F) (c : F) :
    code (fun i => l i.1+c)=0 := by
  let b (j:Fin 3) := l (Pi.single j 1)
  have write (x : Positions) : l x=∑ j,b j*x j := by
    have expand : ∑ j:Fin 3,x j • Pi.single j (1:F)=x := by
      funext i;simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply];simp [mul_ite]
    conv_lhs => rw [←expand]
    simp [b,mul_comm]
  simp_rw [write]
  exact (show ∀ (b:Cube 3) (c:F),code (fun i => (∑ j,b j*i.1 j)+c)=0 from by decide +kernel) b c

variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem lift_distance (A : Finset G) (large : 5≤A.card)
    (avoid : ¬∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A)
    (f : Space →ₗ[F] G) (inside : ∀ i,f (label i)∈A) (inj : Function.Injective (fun i => f (label i)))
    (w : Slots → F) (nz : code w≠0) (zero : f (code w)=0) (even : parity (code w)=0) :
    8≤(support w).card := by
  classical
  let T := (support w).image (fun i => f (label i))
  have size : T.card=(support w).card := card_image_of_injective _ inj
  have sub : T⊆A := by
    rintro t ht
    obtain ⟨i,_,rfl⟩ := mem_image.mp ht;exact inside i
  have total : ∑ t∈T,t=0 := by
    rw [eval,map_sum] at zero
    simpa [T,sum_image inj.injOn] using zero
  have par : 2∣(support w).card := by rwa [parity_word,ZMod.natCast_eq_zero_iff] at even
  have pos : 0<(support w).card := by
    by_contra! h
    exact nz (by rw [eval,card_eq_zero.mp (by omega : (support w).card=0),sum_empty])
  have noTwo : T.card≠2 := by
    intro h;obtain ⟨a,b,ab,e⟩ := card_eq_two.mp h
    rw [e,sum_pair ab] at total
    exact ab (add_right_cancel (total.trans (ZModModule.add_self _).symm))
  by_contra! low
  exact avoid ((Green51SparseDimensions.linear_three_iff A large).mpr ⟨T,sub,by omega,total⟩)

private theorem flip_count (w : Slots → F) :
    (support (fun i => w i+1)).card+(support w).card=16 := by
  have eq : support (fun i => w i+1)=univ\support w := by
    ext i
    rcases (show ∀ x:F,x=0 ∨ x=1 from by decide) (w i) with h|h <;> simp [support,h,ZModModule.add_self]
  rw [eq,card_sdiff_add_card_eq_card (subset_univ _),card_univ]
  simp [Slots,Positions,Cube]

private theorem split_count (w : Slots → F) :
    (support w).card=(univ.filter fun z:Positions => w (z,0)≠0).card+
      (univ.filter fun z:Positions => w (z,1)≠0).card := by
  simp only [support,card_filter,Fintype.sum_prod_type,
    show ∀ f:F→ℕ,(∑ x,f x)=f 0+f 1 from fun f => Fin.sum_univ_two f,sum_add_distrib]

/-- Every nonzero even relation on the paired model has all eight
horizontal entries set. Its preimages select exactly one label per pair. -/
theorem full_horizontal (A : Finset G) (large : 5≤A.card)
    (avoid : ¬∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A)
    (f : Space →ₗ[F] G) (inside : ∀ i,f (label i)∈A) (inj : Function.Injective (fun i => f (label i)))
    {s : Space} (nz : s≠0) (zero : f s=0) (even : parity s=0) : s.1=(fun _ => 1) := by
  obtain ⟨w,rfl⟩ := onto s
  have distance (x : Slots→F) (same : code x=code w) : 8≤(support x).card :=
    lift_distance A large avoid f inside inj x (same.trans_ne nz) (by rw [same,zero]) (by rw [same,even])
  have shifted (l : Positions →ₗ[F] F) (c : F) :
      code (fun i => w i+(l i.1+c))=code w := by
    let v : Slots→F := fun i => l i.1+c
    have hv : code v=0 := affine_in_kernel l c
    exact (code.map_add w v).trans (by rw [hv,add_zero])
  have opp : ∀ z,w (z,0)≠w (z,1) := by
    apply Green51Hadamard.opposite_on_pairs
    intro l
    let u (i:Slots) := w i+l i.1
    have base : code u=code w := by simpa only [u,add_zero] using shifted l 0
    have low := distance u base
    have flipped : code (fun i => u i+1)=code w := by simpa only [u,add_assoc] using shifted l 1
    have flip := distance _ flipped
    have sum := flip_count u
    have eight : (support u).card=8 := by omega
    rw [split_count] at eight
    exact eight
  funext z;rw [horizontal]
  exact (show ∀ x y:F,x≠y → x+y=1 from by decide) _ _ (opp z)

end Green51PairedTypes

#print axioms Green51PairedTypes.labels_eq
#print axioms Green51PairedTypes.parity_label
#print axioms Green51PairedTypes.full_horizontal
