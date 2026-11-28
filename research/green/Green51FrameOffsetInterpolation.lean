import Green51CircuitEquivalence

/-! # Independent translations in the fibres of an odd binary circuit -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51NearThreshold Green51GirthFrame
open scoped Classical Pointwise
variable {V P : Type*} [AddCommGroup V] [Module F V] [AddCommGroup P] [Module F P] [DecidableEq V]

/-- Prescribing a translation on every fibre of an odd circuit determines its constant
part. The linear part can always be extended to the ambient space. -/
theorem interpolate_offsets {C D : Finset V} (m : ShortestOddCircuit D C) (u : V → P) :
    ∃ f : V →ₗ[F] P, ∀ x∈C, f x+(∑ y∈C,u y)=u x := by
  classical
  let b := ∑ y∈C,u y
  let w (x : V) := u x + b
  have odd := m.2.1
  obtain ⟨p,hp⟩ := card_pos.mp (show 0<C.card by rw [Nat.odd_iff] at odd; omega)
  obtain ⟨f,hf⟩ := extend_values (independent_erase m hp) w
  have zero : ∑ x∈C,w x=0 := by
    simp only [w,sum_add_distrib,sum_const]
    obtain ⟨j,hj⟩ := odd
    rw [hj,add_nsmul,one_nsmul,show 2*j=j*2 by omega,mul_nsmul,two_nsmul,ZModModule.add_self,zero_add]
    exact ZModModule.add_self _
  have rest : (∑ x∈C.erase p,f x)=∑ x∈C.erase p,w x := sum_congr rfl hf
  have value : f p=w p := by
    apply add_left_cancel (a := ∑ x∈C.erase p,f x)
    calc
      _ = ∑ x∈C,f x := sum_erase_add C _ hp
      _ = 0 := by rw [←map_sum,m.2.2.1,map_zero]
      _ = (∑ x∈C.erase p,f x)+w p := by rw [rest,sum_erase_add C _ hp,zero]
  refine ⟨f,fun x hx => ?_⟩
  have h : f x=w x := by
    by_cases eq : x=p
    · exact eq ▸ value
    · exact hf x (mem_erase.mpr ⟨eq,hx⟩)
  change f x+b=u x
  rw [h,show w x=u x+b from rfl,add_assoc,ZModModule.add_self,add_zero]

/-- An involutive linear shear on the product of a fibre and its quotient. -/
def shear (f : V →ₗ[F] P) : (P×V) ≃ₗ[F] (P×V) where
  toFun z := (z.1+f z.2,z.2)
  invFun z := (z.1+f z.2,z.2)
  left_inv z := by simp [add_assoc,ZModModule.add_self]
  right_inv z := by simp [add_assoc,ZModModule.add_self]
  map_add' x y := by ext <;> simp [map_add]; abel
  map_smul' c x := by ext <;> simp [smul_add]

theorem independent_fibre_translations {C D : Finset V} (m : ShortestOddCircuit D C) (u : V → P) :
    ∃ e : (P×V) ≃ₗ[F] (P×V), ∃ b : P, ∀ i∈C, ∀ p : P, e (p,i)+(b,0)=(p+u i,i) := by
  obtain ⟨f,hf⟩ := interpolate_offsets m u
  refine ⟨shear f,∑ y∈C,u y,fun i hi p => ?_⟩
  change (p+f i+_,i+0)=(p+u i,i)
  rw [add_assoc,hf i hi,add_zero]

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.interpolate_offsets
#print axioms Green51FrameIsomorphisms.independent_fibre_translations
