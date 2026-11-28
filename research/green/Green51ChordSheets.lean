import Green51PermutedTopFlats

/-! # Even and odd parts of a quadratic chord family -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

def chord (t x:Cube n) := quad x+quad (x+t)
theorem chord_translate (t x:Cube n) : chord t (x+t)=chord t x := by
  unfold chord
  rw [add_assoc x t t,ZModModule.add_self,add_zero,add_comm]
theorem fiber_chord (t:Cube n) (h:Target n) : h∈fiber t ↔ ∃ x:Cube n,h=chord t x := by
  constructor
  · rintro ⟨z,⟨x,rfl⟩,rfl⟩
    exact ⟨x,(derivative t x).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨polar t x,⟨x,rfl⟩,(derivative t x).symm⟩
theorem chord_cases (f:Cube n→Cube n) {t:Cube n} (tn:t≠0) (x:Cube n) (v:V n)
    (hit:(chord t x,v)∈labels f 0+labels f 0) :
    v=0 ∨ v=delta f x ∨ v=delta f (x+t) ∨ v=(0,f x+f (x+t)) := by
  obtain ⟨a,b,e⟩:=(chord_slice f 0 (show x≠x+t by simpa using tn) v).mp hit
  rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) a with rfl|rfl <;>
    rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) b with rfl|rfl <;>
    simp only [Pi.zero_apply,zero_smul,one_smul,zero_add,add_zero] at e
  · exact Or.inl e
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inr (e.trans (Prod.ext (ZModModule.add_self _) rfl))))

theorem even_heights (f:Cube n→Cube n) {t:Cube n} (tn:t≠0)
    (constant:∀x:Cube n,f x+f (x+t)=f 0+f t) {h:Target n} {v:V n}
    (hor:h∈fiber t) (hit:(h,v)∈labels f 0+labels f 0) (even:v.1=0) :
    v=0 ∨ v=(0,f 0+f t) := by
  obtain ⟨x,rfl⟩:=(fiber_chord _ _).mp hor
  rcases chord_cases f tn x v hit with e|e|e|e
  · exact Or.inl e
  · exact False.elim (zero_ne_one (even.symm.trans (congrArg Prod.fst e)))
  · exact False.elim (zero_ne_one (even.symm.trans (congrArg Prod.fst e)))
  · exact Or.inr (by rwa [constant] at e)

theorem odd_chord (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0) {h:Target n} {v:V n}
    (hor:h∈fiber t) (hit:(h,v)∈labels f 0+labels f 0) (odd:v.1=1) :
    h=chord t (f.symm v.2) := by
  obtain ⟨x,rfl⟩:=(fiber_chord _ _).mp hor
  rcases chord_cases f tn x v hit with e|e|e|e
  · exact False.elim (one_ne_zero (odd.symm.trans (congrArg Prod.fst e)))
  · simp only [e,delta,Equiv.symm_apply_apply]
  · simp only [e,delta,Equiv.symm_apply_apply,chord_translate]
  · exact False.elim (one_ne_zero (odd.symm.trans (congrArg Prod.fst e)))
theorem affine_triple_mem {G:Type*} [AddCommGroup G] [Module F G]
    {p:G} {W:Submodule F G} {a b c:G}
    (ha:a∈p +ᵥ (W:Set G)) (hb:b∈p +ᵥ (W:Set G)) (hc:c∈p +ᵥ (W:Set G)) :
    a+b+c∈p +ᵥ (W:Set G) := by
  obtain ⟨u,hu,rfl⟩:=ha
  obtain ⟨v,hv,rfl⟩:=hb
  obtain ⟨w,hw,rfl⟩:=hc
  refine ⟨u+v+w,W.add_mem (W.add_mem hu hv) hw,?_⟩
  change p+(u+v+w)=(p+u)+(p+v)+(p+w)
  rw [add_add_add_comm p u p v,ZModModule.add_self,zero_add]
  abel

/-- On a largest nonvertical flat all heights have the same first coordinate. -/
theorem tag_constant (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0)
    (constant:∀x:Cube n,f x+f (x+t)=f 0+f t)
    (P:E n) (W:Submodule F (E n)) (large:3≤Module.finrank F W)
    (inside:P +ᵥ (W:Set (E n))⊆↑(labels f 0+labels f 0)) (proj:baseFlat P W=fiber t) :
    (∀z∈P +ᵥ (W:Set (E n)),z.2.1=0) ∨ (∀z∈P +ᵥ (W:Set (E n)),z.2.1=1) := by
  let D:=P +ᵥ (W:Set (E n))
  have hor {z:E n} (hz:z∈D):z.1∈fiber t := proj ▸ (mem_baseFlat P W _).mpr ⟨z.2,hz⟩
  have bit (b:F) : b=0 ∨ b=1 := (show ∀i:F,i=0 ∨ i=1 from by decide) b
  by_contra! mix
  obtain ⟨⟨o,ho,one⟩,⟨e,he,zero⟩⟩:=mix
  have o1: o.2.1=1 := (bit _).resolve_left one
  have e0: e.2.1=0 := (bit _).resolve_right zero
  have inj : Set.InjOn (Prod.snd : E n→V n) D := by
    intro a ha b hb eq
    have mem:=affine_triple_mem ho ha hb
    have v:(o+a+b).2=o.2 := by
      change o.2+a.2+b.2=o.2
      rw [show a.2=b.2 from eq,add_assoc,ZModModule.add_self,add_zero]
    have h1:=odd_chord f tn (hor mem) (inside mem) (show (o+a+b).2.1=1 by rw [v,o1])
    have h2:=odd_chord f tn (hor ho) (inside ho) o1
    change (o+a+b).1=chord t (f.symm (o+a+b).2.2) at h1
    rw [v] at h1
    have same:o+(a+b)=o := by rw [←add_assoc];exact Prod.ext (h1.trans h2.symm) v
    have h:=add_eq_left.mp same
    rwa [←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at h
  let k:V n:=(0,f 0+f t)
  let s:=e.2+o.2
  have small : D.toFinset.image Prod.snd⊆{0,k,s,k+s} := by
    intro v hv
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hv
    rw [Set.mem_toFinset] at hz
    rcases bit z.2.1 with even|odd
    · rcases even_heights f tn constant (hor hz) (inside hz) even with eq|eq <;> simp [eq,k]
    · have mem:=affine_triple_mem hz he ho
      have even:(z+e+o).2.1=0 := by change z.2.1+e.2.1+o.2.1=0;rw [odd,e0,o1,add_zero];decide
      have recover:z.2=(z+e+o).2+s := by
        change z.2=(z.2+e.2+o.2)+(e.2+o.2)
        rw [add_assoc z.2 e.2 o.2,add_assoc,ZModModule.add_self,add_zero]
      rcases even_heights f tn constant (hor mem) (inside mem) even with eq|eq <;> simp [recover.trans (congrArg (·+s) eq),k]
  have bound:=card_le_card small
  rw [card_image_of_injOn (by simpa using inj),show D.toFinset.card=2^(Module.finrank F W) from flat_card _ _] at bound
  have upper:({0,k,s,k+s}:Finset (V n)).card≤4 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right ((card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_le_two 1)) 1)
  have enough:=Nat.pow_le_pow_right (by decide : 0<2) large
  omega

def shiftValue (f:Cube n→Cube n) (t:Cube n) : V n := (0,f 0+f t)
def evenSheet (f:Cube n→Cube n) (t:Cube n) : Set (E n) := fiber t ×ˢ ({0,shiftValue f t}:Set _)
def oddPoint (f:Cube n→Cube n) (t x:Cube n) : E n := (chord t x,delta f x)
def oddSheet (f:Cube n→Cube n) (t:Cube n) : Set (E n) := Set.range (oddPoint f t)

theorem evenSheet_card (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0) :
    (evenSheet f t).ncard=2^n := by
  have nz: shiftValue f t≠0 := by
    intro e
    have k:f 0+f t=0:=congrArg Prod.snd e
    rw [←neg_eq_iff_add_eq_zero,ZModModule.neg_eq_self] at k
    exact tn (f.injective k).symm
  rw [evenSheet,Set.ncard_prod,Set.ncard_pair nz.symm,Set.ncard_eq_toFinset_card',fiber,flat_card,←pow_succ,fiber_dimension tn]
theorem oddSheet_card (f:Cube n ≃ Cube n) (t:Cube n) : (oddSheet f t).ncard=2^n := by
  have inj:Function.Injective (oddPoint f t) := fun _ _ e=>f.injective (congrArg (fun z:E n=>z.2.2) e)
  rw [oddSheet,Set.ncard_range_of_injective inj,Nat.card_eq_fintype_card]
  simp [Cube]
theorem sheet_classification (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0)
    (constant:∀ x:Cube n,f x+f (x+t)=f 0+f t) (large:3≤n)
    (P:E n) (W:Submodule F (E n)) (dim:Module.finrank F W=n)
    (inside:P +ᵥ (W:Set (E n))⊆↑(labels f 0+labels f 0)) (proj:baseFlat P W=fiber t) :
    P +ᵥ (W:Set (E n))=evenSheet f t ∨ P +ᵥ (W:Set (E n))=oddSheet f t := by
  let D:=P +ᵥ (W:Set (E n))
  have hor {z:E n} (hz:z∈D):z.1∈fiber t := proj ▸ (mem_baseFlat P W _).mpr ⟨z.2,hz⟩
  have cardD:D.toFinset.card=2^n := by rw [show D.toFinset.card=2^(Module.finrank F W) from flat_card _ _,dim]
  rcases tag_constant f tn constant P W (by omega) inside proj with even|odd
  · left
    apply Set.toFinset_inj.mp
    apply eq_of_subset_of_card_le
    · apply Set.toFinset_subset_toFinset.mpr
      intro z hz
      refine ⟨hor hz,?_⟩
      rcases even_heights f tn constant (hor hz) (inside hz) (even z hz) with h|h <;> simp [h,shiftValue]
    · rw [←Set.ncard_eq_toFinset_card',evenSheet_card f tn];exact cardD.ge
  · right
    apply Set.toFinset_inj.mp
    apply eq_of_subset_of_card_le
    · apply Set.toFinset_subset_toFinset.mpr
      intro z hz
      refine ⟨f.symm z.2.2,Prod.ext (odd_chord f tn (hor hz) (inside hz) (odd z hz)).symm ?_⟩
      exact Prod.ext (odd z hz).symm (f.apply_symm_apply _)
    · rw [←Set.ncard_eq_toFinset_card',oddSheet_card];exact cardD.ge

end Green51PermutedPairs

#print axioms Green51PermutedPairs.tag_constant
#print axioms Green51PermutedPairs.evenSheet_card
#print axioms Green51PermutedPairs.oddSheet_card
#print axioms Green51PermutedPairs.sheet_classification
