import Green51AffineProfileCount

/-! # Integer profiles for four-point fibres -/

namespace Green51FrameIsomorphisms
open Finset
open scoped Classical

private noncomputable def axes : Fin 3 ≃ Direction := Fintype.equivOfCardEq (by decide)

def six (a c d x y z : ℕ) : Profile := (![a,c,d],{x,y,z})

private theorem dir_sum (f : Direction→ℕ) : (∑ u,f u)=f (axes 0)+f (axes 1)+f (axes 2) := by
  rw [←axes.sum_comp f]
  simp [Fin.sum_univ_succ,add_assoc]

private theorem dir_values (f : Direction→ℕ) :
    (univ : Finset Direction).val.map f = {f (axes 0),f (axes 1),f (axes 2)} := by
  have eq := congrArg Finset.val (map_univ_equiv axes)
  rw [←eq,map_val,Multiset.map_map]
  have three : (univ : Finset (Fin 3)).val={0,1,2} := by decide
  rw [three]
  rfl

private theorem six_form (h : RowKind→ℕ) :
    let a := h (.inl 0)
    let c := h (.inl 1)
    let d := h (.inl 2)
    let x := h (.inr (axes 0))
    let y := h (.inr (axes 1))
    let z := h (.inr (axes 2))
    (∑ t,h t)=a+c+d+(x+y+z) ∧
      (∑ t,h t*sizeOfKind t)=a+3*c+4*d+2*(x+y+z) ∧ profile h = six a c d x y z := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [Fintype.sum_sum_type,dir_sum]
    simp [Fin.sum_univ_succ,add_assoc]
  · rw [Fintype.sum_sum_type,dir_sum]
    simp [Fin.sum_univ_succ,sizeOfKind]
    omega
  · apply Prod.ext
    · funext j;fin_cases j <;> rfl
    · exact dir_values _

theorem valid_six {g k : ℕ} {p : Profile} : Valid g k p ↔
    ∃ a c d x y z : ℕ, a+c+d+(x+y+z)=g ∧ a+3*c+4*d+2*(x+y+z)=k ∧ six a c d x y z=p := by
  constructor
  · rintro ⟨h,n,w,rfl⟩
    obtain ⟨total,mass,eq⟩ := six_form h
    exact ⟨_,_,_,_,_,_,total.symm.trans n,mass.symm.trans w,eq.symm⟩
  · rintro ⟨a,c,d,x,y,z,n,w,rfl⟩
    let h : RowKind→ℕ := Sum.elim ![a,c,d] (fun i => ![x,y,z] (axes.symm i))
    obtain ⟨total,mass,eq⟩ := six_form h
    exact ⟨h,by simpa [h] using total.trans (by simpa [h] using n),
      by simpa [h] using mass.trans (by simpa [h] using w),by simpa [h] using eq⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.valid_six
