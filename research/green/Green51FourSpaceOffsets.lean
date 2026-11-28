import Green51FourSpaceCover

/-! # Allowed offsets for two eight-coordinate halves -/
namespace Green51FourSpace.Certificate
open Lean

def options (u:Nat) := (List.range 256).filter (allowed u)
elab "offsetRows%" : term => return toExpr ((List.range 256).map options).toArray
def offsets : Array (List Nat) := offsetRows%
elab "offsetMasks%" : term => return toExpr (offsets.map collectBits)
def offsetMasks : Array Nat := offsetMasks%

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem offsets_exact : ∀ g:Fin 32,(List.range 8).all (fun j=>options (g.val*8+j) == offsets[g.val*8+j]?.getD [])=true := by
  intro g
  fin_cases g <;> decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem offsetMasks_exact : offsets.map collectBits=offsetMasks := by decide +kernel

theorem in_offsets {u v:Nat} (hu:u<256) (hv:v<256) (ok:allowed u v=true) :
    v∈offsets[u]?.getD [] := by
  have e := List.all_eq_true.mp (offsets_exact ⟨u/8,by omega⟩) (u%8) (List.mem_range.mpr (by omega))
  change (options (u/8*8+u%8) == offsets[u/8*8+u%8]?.getD [])=true at e
  rw [show u/8*8+u%8=u by omega] at e
  rw [←beq_iff_eq.mp e]
  simp [options,hv,ok]
theorem in_offsetMask {u v:Nat} (hu:u<256) (hv:v<256) (ok:allowed u v=true) :
    (offsetMasks[u]?.getD 0).testBit v=true := by
  have good := in_offsets hu hv ok
  cases h : offsets[u]? with
  | none => simp [h] at good
  | some l =>
    rw [←offsetMasks_exact,Array.getElem?_map,h]
    exact (collectBits_iff l v).mpr (by simpa [h] using good)

end Green51FourSpace.Certificate
#print axioms Green51FourSpace.Certificate.in_offsetMask
