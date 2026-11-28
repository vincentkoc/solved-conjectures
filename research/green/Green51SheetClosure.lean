import Green51ChordSheets
import Green51WitnessIncidence

/-! # Affine closure and the induced map on a quotient -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

theorem affine_iff_closure {G:Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
    (S:Set G) (p:G) (hp:p∈S) (dim:ℕ) (size:S.ncard=2^dim) :
    (∃ W:Submodule F G,Module.finrank F W=dim ∧ S=p +ᵥ (W:Set G)) ↔
    ∀ x∈S,∀ y∈S,x+y+p∈S := by
  constructor
  · rintro ⟨W,_,rfl⟩ x hx y hy
    exact affine_triple_mem hx hy hp
  · intro closed
    let W:Submodule F G := {
      carrier := {x | p+x∈S}
      zero_mem' := by simpa using hp
      add_mem' := by
        intro x y hx hy
        have h:=closed (p+x) hx (p+y) hy
        rw [add_add_add_comm p x p y,ZModModule.add_self,zero_add,add_comm] at h
        exact h
      smul_mem' := by
        intro a x hx
        rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) a with rfl|rfl
        · simpa using hp
        · simpa using hx }
    have same:S=p +ᵥ (W:Set G) := by
      ext x
      constructor
      · intro hx
        exact ⟨p+x,show p+(p+x)∈S by simpa only [←add_assoc,ZModModule.add_self,zero_add] using hx,
          by change p+(p+x)=x;rw [←add_assoc,ZModModule.add_self,zero_add]⟩
      · rintro ⟨w,hw,rfl⟩;exact hw
    refine ⟨W,?_,same⟩
    have h:=flat_card p W
    rw [←same,←Set.ncard_eq_toFinset_card',size] at h
    exact (Nat.pow_right_injective (by decide : 2≤2) h).symm

theorem chord_eq_iff {t:Cube n} (tn:t≠0) (x y:Cube n) :
    chord t x=chord t y ↔ x=y ∨ x=y+t := by
  constructor
  · intro h
    rcases chord_unique (show x≠x+t by simpa using tn) h with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · rintro (rfl|rfl)
    · rfl
    · exact chord_translate _ _
theorem chord_add (t x y:Cube n) : chord t x+chord t y+chord t 0=chord t (x+y) := by
  simp only [chord,derivative,map_zero,map_add,add_zero]
  rw [add_add_add_comm (quad 0+quad t) _ (quad 0+quad t) _,ZModModule.add_self,zero_add,add_comm]

/-- The permutation becomes affine after identifying the two ends of each chord. -/
def affineModulo (f:Cube n→Cube n) (t:Cube n) : Prop :=
  ∀x y:Cube n,f x+f y+f 0=f (x+y) ∨ f x+f y+f 0=f (x+y+t)

private theorem output_sum (f:Cube n→Cube n) (t x y:Cube n) :
    oddPoint f t x+oddPoint f t y+oddPoint f t 0=(chord t (x+y),1,f x+f y+f 0) := by
  exact Prod.ext (chord_add _ _ _) (Prod.ext (by change (1:F)+1+1=1;decide) rfl)

theorem odd_closed_iff (f:Cube n→Cube n) {t:Cube n} (tn:t≠0) :
    (∀ a∈oddSheet f t,∀ b∈oddSheet f t,a+b+oddPoint f t 0∈oddSheet f t) ↔ affineModulo f t := by
  constructor
  · intro h x y
    have c:=h _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    rw [output_sum] at c
    obtain ⟨z,eq⟩:=c
    have hor:chord t z=chord t (x+y):=congrArg Prod.fst eq
    have vert:f z=f x+f y+f 0:=congrArg (fun p:E n=>p.2.2) eq
    rcases (chord_eq_iff tn _ _).mp hor with h|h <;> subst z
    · exact Or.inl vert.symm
    · exact Or.inr vert.symm
  · intro h
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
    rw [output_sum]
    rcases h x y with good|good
    · exact ⟨x+y,Prod.ext rfl (Prod.ext rfl good.symm)⟩
    · exact ⟨x+y+t,Prod.ext (chord_translate t (x+y)) (Prod.ext rfl good.symm)⟩

open Green51WitnessIncidence
theorem oddSheet_mem_iff (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0) :
    oddSheet f t∈familyAt n (labels f 0) ↔ affineModulo f t := by
  have hp : oddPoint f t 0∈oddSheet f t := ⟨0,rfl⟩
  constructor
  · rintro ⟨P,W,_,eq,_⟩
    apply (odd_closed_iff f tn).mp
    intro x hx y hy
    rw [eq] at hx hy hp ⊢
    exact affine_triple_mem hx hy hp
  · intro good
    obtain ⟨W,dim,eq⟩:=(affine_iff_closure _ _ hp n (oddSheet_card f t)).mpr ((odd_closed_iff f tn).mpr good)
    refine ⟨_,W,dim,eq,?_⟩
    rintro _ ⟨x,rfl⟩
    apply (chord_slice f 0 (show x≠x+t by simpa using tn) _).mpr
    exact ⟨1,0,by simp⟩

def constantAlong (f:Cube n→Cube n) (t:Cube n) := ∀x:Cube n,f x+f (x+t)=f 0+f t

theorem evenSheet_mem (f:Cube n ≃ Cube n) {t:Cube n} (tn:t≠0) (constant:constantAlong f t) :
    evenSheet f t∈familyAt n (labels f 0) := by
  let P:E n:=(chord t 0,0)
  have h0:chord t 0∈fiber t:=(fiber_chord _ _).mpr ⟨0,rfl⟩
  have hp:P∈evenSheet f t:=⟨h0,Or.inl rfl⟩
  have closed : ∀ z∈evenSheet f t,∀ w∈evenSheet f t,z+w+P∈evenSheet f t := by
    rintro ⟨u,v⟩ ⟨hu,hv⟩ ⟨a,b⟩ ⟨ha,hb⟩
    refine ⟨affine_triple_mem hu ha h0,?_⟩
    change v+b+0∈({0,shiftValue f t}:Set (V n))
    change (v=0 ∨ v=shiftValue f t) at hv
    change (b=0 ∨ b=shiftValue f t) at hb
    rcases hv with hv|hv <;> rcases hb with hb|hb <;>
      rw [hv,hb] <;> simp [ZModModule.add_self]
  obtain ⟨W,dim,eq⟩:=(affine_iff_closure _ _ hp n (evenSheet_card f tn)).mpr closed
  refine ⟨P,W,dim,eq,?_⟩
  rintro ⟨z,v⟩ ⟨hz,hv⟩
  obtain ⟨x,rfl⟩:=(fiber_chord _ _).mp hz
  apply (chord_slice f 0 (show x≠x+t by simpa using tn) v).mpr
  rcases hv with h|h
  · exact ⟨0,0,by simp [show v=0 from h]⟩
  · refine ⟨1,1,?_⟩
    simp only [Pi.zero_apply,one_smul,zero_add]
    rw [show v=shiftValue f t from h]
    exact Prod.ext (ZModModule.add_self _).symm (constant x).symm

theorem distinguished_mem (f:Cube n ≃ Cube n) (b:Cube n→V n) :
    distinguished n∈familyAt n (labels f b) := by
  let L := (LinearMap.inr F (Target n) (V n)).comp (LinearMap.inr F F (Cube n))
  have inj:Function.Injective L:=LinearMap.inr_injective.comp LinearMap.inr_injective
  let P:E n:=(0,1,0)
  have eq:distinguished n=P +ᵥ (L.range:Set (E n)) := by
    ext z
    obtain ⟨a,c,x⟩:=z
    constructor
    · rintro ⟨rfl,rfl⟩
      refine ⟨L x,⟨x,rfl⟩,?_⟩
      change (0+0,1+0,0+x)=((0,1,x):E n)
      simp
    · rintro ⟨_,⟨x,rfl⟩,h⟩
      have fc:=congrArg Prod.fst h
      have sc:=congrArg (fun z:E n=>z.2.1) h
      exact ⟨(by simpa [P,L] using fc.symm),(by simpa [P,L] using sc.symm)⟩
  refine ⟨P,L.range,?_,eq,?_⟩
  · rw [L.finrank_range_of_inj inj];simp [Cube]
  · rintro ⟨a,c,x⟩ ⟨rfl,rfl⟩
    let z:=f.symm x
    have e : lower b z+upper f b z=((0,1,x):E n) := by
      apply Prod.ext
      · exact ZModModule.add_self _
      · change b z+(b z+delta f z)=(1,x)
        rw [←add_assoc,ZModModule.add_self,zero_add]
        exact Prod.ext rfl (f.apply_symm_apply x)
    exact e ▸ add_mem_add (mem_union_left _ (mem_image_of_mem (lower b) (mem_univ z)))
      (mem_union_right _ (mem_image_of_mem (upper f b) (mem_univ z)))

end Green51PermutedPairs

#print axioms Green51PermutedPairs.chord_eq_iff
#print axioms Green51PermutedPairs.odd_closed_iff
#print axioms Green51PermutedPairs.oddSheet_mem_iff
#print axioms Green51PermutedPairs.evenSheet_mem
#print axioms Green51PermutedPairs.distinguished_mem
