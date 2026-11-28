import Green51FourSpaceChecks
import Green51FourSpaceParity
import Green51FourSpaceLifts

/-! # The dimension obstruction for a pair of eight-coordinate halves -/
open Green50Downsets
open scoped Classical
namespace Green51FourSpace
local notation "F" => ZMod 2

private theorem contained_shape (R:Submodule F (Cube 8)) (dim:5≤Module.finrank F R) :
    ∃ B∈Certificate.shapes,∀ u∈B,u<256 ∧ decode 8 u∈R := by
  have cod := R.finrank_quotient_add_finrank
  have d8 : Module.finrank F (Cube 8)=8 := by simp [Cube]
  have d3 : Module.finrank F (Cube 3)=3 := by simp [Cube]
  have bound : Module.finrank F (Cube 8⧸R)≤Module.finrank F (Cube 3) := by omega
  obtain ⟨j,inj⟩ := finrank_le_iff_exists_linearMap.mp bound
  let P := j.comp R.mkQ
  let row (i:Fin 3) := (LinearMap.proj (R:=F) (φ:=fun _:Fin 3=>F) i).comp P
  let key (i:Fin 3) := encode (fun t:Fin 8=>row i (Pi.single t 1))
  have lim (i:Fin 3) : key i<256 := encode_lt _
  obtain ⟨B,hB,all⟩ := Certificate.three_checks _ _ _ (lim 0) (lim 1) (lim 2)
  have size : Certificate.shapes.all (fun b=>b.all (fun u=>decide (u<256)))=true := by decide +kernel
  refine ⟨B,hB,fun u hu=>?_⟩
  have small : u<256 := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp size _ hB) _ hu)
  refine ⟨small,?_⟩
  obtain ⟨h0,h1,h2⟩:=all u hu
  have vanished : P (decode 8 u)=0 := by
    funext i
    fin_cases i
    · exact (orthogonal_check (row 0) u small).mp h0
    · exact (orthogonal_check (row 1) u small).mp h1
    · exact (orthogonal_check (row 2) u small).mp h2
  exact (Submodule.Quotient.mk_eq_zero R).mp (inj (vanished.trans j.map_zero.symm))

theorem no_linear_offsets (R:Submodule F (Cube 8)) (L:R→ₗ[F] Cube 8)
    (valid:∀ x:R, Certificate.allowed (encode x.val) (encode (L x))=true) :
    Module.finrank F R≤4 := by
  classical
  by_contra! dim
  obtain ⟨B,hB,all⟩ := contained_shape R dim
  let S:Set Nat := {u | u<256 ∧ decode 8 u∈R}
  let f (u:Nat) : Nat := if h:decode 8 u∈R then encode (L ⟨_,h⟩) else 0
  have closed (u:Nat) (hu:u∈S) (v:Nat) (hv:v∈S) : u ^^^ v∈S := by
    refine ⟨Nat.xor_lt_two_pow (n:=8) hu.1 hv.1,?_⟩
    rw [decode_xor]
    exact R.add_mem hu.2 hv.2
  apply Certificate.no_shape S f ⟨by decide,by rw [decode_zero];exact R.zero_mem⟩ ?_ closed ?_
    (fun _ hu=>hu.1) ?_ ?_ hB all
  · simp [f,decode_zero]
    change encode (L 0)=0
    rw [map_zero,encode_zero]
  · intro u hu v hv
    have hm:decode 8 (u ^^^ v)∈R := (closed u hu v hv).2
    simp only [f,dif_pos hu.2,dif_pos hv.2,dif_pos hm]
    rw [show (⟨decode 8 (u ^^^ v),hm⟩:R)=⟨_,hu.2⟩+⟨_,hv.2⟩ from Subtype.ext (decode_xor _ _ _),map_add,encode_add]
  · intro u hu
    simp only [f,dif_pos hu.2]
    exact encode_lt _
  · intro u hu
    simpa only [f,dif_pos hu.2,encode_decode (n:=8) hu.1] using valid ⟨_,hu.2⟩

end Green51FourSpace
#print axioms Green51FourSpace.no_linear_offsets
