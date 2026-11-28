import Green51SheetCount

/-! # Four cosets determine every nonzero parallelogram defect -/

open Finset Green50Downsets Green51QuadraticFlats Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

/-- The defect of the affine parallelogram identity. -/
def defect (f:Cube n→Cube n) (x y:Cube n) := f x+f y+f 0+f (x+y)

private theorem cancel_twice {G:Type*} [AddCommGroup G] [Module F G] (a b:G) :
    a+b+b=a := by rw [add_assoc,ZModModule.add_self,add_zero]

theorem defect_zero_iff (f:Cube n→Cube n) (x y:Cube n) :
    defect f x y=0 ↔ f x+f y+f 0=f (x+y) := by
  rw [defect,← ZModModule.sub_eq_add,sub_eq_zero]

theorem defect_swap (f:Cube n→Cube n) (x y:Cube n) : defect f x y=defect f y x := by
  unfold defect
  rw [add_comm x y,add_comm (f x) (f y)]

theorem defect_shear (f:Cube n→Cube n) (x y:Cube n) : defect f x (x+y)=defect f x y := by
  unfold defect
  rw [←add_assoc x x y,ZModModule.add_self,zero_add]
  ac_rfl

theorem constant_iff_shift (f:Cube n→Cube n) (t:Cube n) :
    constantAlong f t ↔ ∀x,f (x+t)=f x+(f 0+f t) := by
  unfold constantAlong
  constructor
  · intro h x
    rw [←h x,←add_assoc,ZModModule.add_self,zero_add]
  · intro h x
    rw [h x,←add_assoc,ZModModule.add_self,zero_add]

theorem constant_iff_defect (f:Cube n→Cube n) (t:Cube n) :
    constantAlong f t ↔ ∀x,defect f x t=0 := by
  rw [constant_iff_shift]
  simp_rw [defect_zero_iff]
  constructor
  · intro h x;rw [h x];ac_rfl
  · intro h x;rw [←h x];ac_rfl

def structures (f:Cube n→Cube n) : Submodule F (Cube n) where
  carrier := {t | constantAlong f t}
  zero_mem' := by intro x;simp [ZModModule.add_self]
  add_mem' := by
    intro t u ht hu
    rw [Set.mem_ofPred_eq,constant_iff_shift] at ht hu ⊢
    intro x
    rw [←add_assoc,hu,ht,hu t]
    ac_rfl
  smul_mem' := by
    intro c t ht
    rcases (show ∀a:F,a=0 ∨ a=1 from by decide) c with rfl|rfl
    · simp only [zero_smul,Set.mem_ofPred_eq];intro x;simp [ZModModule.add_self]
    · simpa only [one_smul] using ht

theorem defect_translate (f:Cube n→Cube n) (x y:Cube n) {t:Cube n}
    (h:t∈structures f) : defect f (x+t) y=defect f x y := by
  have shift:=(constant_iff_shift f t).mp h
  unfold defect
  rw [show x+t+y=x+y+t by ac_rfl,shift,shift]
  rw [←one_smul F (f x+f y+f 0+f (x+y))]
  match_scalars <;> decide

theorem defect_congr (f:Cube n→Cube n) {x y u v:Cube n}
    (hx:(structures f).mkQ x=(structures f).mkQ u)
    (hy:(structures f).mkQ y=(structures f).mkQ v) : defect f x y=defect f u v := by
  have shift {a b:Cube n} (eq:(structures f).mkQ a=(structures f).mkQ b) (c:Cube n) :
      defect f a c=defect f b c := by
    have h : a+b∈structures f := (ZModModule.sub_eq_add a b) ▸ (Submodule.Quotient.eq _).mp eq
    have e:=defect_translate f b c h
    rwa [add_left_comm b a b,ZModModule.add_self,add_zero] at e
  rw [shift hx,defect_swap f u,shift hy,defect_swap]

private theorem quotient_pair (f:Cube n→Cube n) {x y:Cube n} (h:defect f x y≠0) :
    (structures f).mkQ x≠0 ∧ (structures f).mkQ y≠0 ∧
    (structures f).mkQ x≠(structures f).mkQ y := by
  let p:=(structures f).mkQ
  have z (v:Cube n) : defect f v 0=0 := by
    apply (defect_zero_iff ..).mpr
    simp [cancel_twice]
  have same (v:Cube n) : defect f v v=0 := by
    simpa only [add_zero] using (defect_shear f v 0).trans (z v)
  refine ⟨fun e=>h ?_,fun e=>h ?_,fun e=>h ?_⟩
  · exact (defect_congr f (e.trans p.map_zero.symm) rfl).trans ((defect_swap ..).trans (z _))
  · exact (defect_congr f rfl (e.trans p.map_zero.symm)).trans (z _)
  · exact (defect_congr f e rfl).trans (same _)

private theorem four_cosets {G:Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
    {a b:G} (ha:a≠0) (hb:b≠0) (hab:a≠b) :
    ({0,a,b,a+b}:Finset G).card=4 := by
  have hs : a+b≠0 := by rwa [←ZModModule.sub_eq_add,sub_ne_zero]
  simp [ha,hb,hab,Ne.symm ha,Ne.symm hb,Ne.symm hs]

theorem four_cosets_of_nonaffine (f:Cube n→Cube n) {x y:Cube n} (h:defect f x y≠0) :
    4≤Nat.card (Cube n ⧸ structures f) := by
  classical
  let _:=Fintype.ofFinite (Cube n ⧸ structures f)
  obtain ⟨ha,hb,hab⟩:=quotient_pair f h
  rw [Nat.card_eq_fintype_card,←four_cosets ha hb hab]
  apply Finset.card_le_univ

theorem common_defect (f:Cube n→Cube n) (dim:Nat.card (Cube n ⧸ structures f)=4)
    {x y:Cube n} (h:defect f x y≠0) (u v:Cube n) :
    defect f u v=0 ∨ defect f u v=defect f x y := by
  classical
  by_cases zero:defect f u v=0
  · exact Or.inl zero
  right
  let _:=Fintype.ofFinite (Cube n ⧸ structures f)
  let p:=(structures f).mkQ
  obtain ⟨ha,hb,hab⟩:=quotient_pair f h
  obtain ⟨hu,hv,huv⟩:=quotient_pair f zero
  have cover : ({0,p x,p y,p x+p y}:Finset _) = univ :=
    eq_univ_of_card _ ((four_cosets ha hb hab).trans (dim.symm.trans Nat.card_eq_fintype_card))
  have options {z:Cube n} (nz:p z≠0) : p z=p x ∨ p z=p y ∨ p z=p (x+y) := by
    have mem:=cover.symm ▸ (mem_univ (p z))
    simpa only [mem_insert,mem_singleton,nz,false_or,map_add] using mem
  have a:=(defect_shear f x y)
  have b:defect f y (x+y)=defect f x y := by
    rw [add_comm x y,defect_shear,defect_swap f y x]
  have c:=(defect_swap f (x+y) x).trans a
  have d:=(defect_swap f (x+y) y).trans b
  rcases options hu with A|A|A <;> rcases options hv with B|B|B <;>
    first | exact False.elim (huv (A.trans B.symm)) | exact defect_congr f A B |
      exact (defect_congr f A B).trans (defect_swap f y x) |
      exact (defect_congr f A B).trans a | exact (defect_congr f A B).trans b |
      exact (defect_congr f A B).trans c | exact (defect_congr f A B).trans d

end Green51PermutedPairs

#print axioms Green51PermutedPairs.structures
#print axioms Green51PermutedPairs.defect_congr
#print axioms Green51PermutedPairs.four_cosets_of_nonaffine
#print axioms Green51PermutedPairs.common_defect
