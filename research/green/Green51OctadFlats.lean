import Green51OctadSlices
import Green51ElevenRelations
import Green51WitnessIncidence

/-! # The fifteen affine three-spaces associated with an octad complement -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PairedTypes Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51PerfectColumns
local notation "F" => ZMod 2
local notation "V" => Cube 11

theorem full_sum {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) : syndrome A=0 := by
  classical
  let H:=octadFamily A
  have rows (O:Finset V) (ho:O∈H) :
      (∑x∈A,if x∈O then x else 0)=0 := by
    obtain ⟨o,zero⟩:=mem_filter.mp ho
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (mem_powersetCard.mp o).1]
    exact zero
  have counted (x:V) (hx:x∈A) : (∑O∈H,if x∈O then x else 0)=x := by
    rw [←sum_filter,sum_const,octads_through_label size avoid hx]
    change (253:ℕ)•x=x
    rw [←Nat.cast_smul_eq_nsmul F,show ((253:ℕ):F)=1 by decide,one_smul]
  calc
    syndrome A = ∑x∈A,∑O∈H,if x∈O then x else 0 := sum_congr rfl fun x hx => (counted x hx).symm
    _ = ∑O∈H,∑x∈A,if x∈O then x else 0 := sum_comm
    _ = 0 := sum_eq_zero rows

private theorem small_directions {B:Finset V} (non:B.Nonempty)
    (proper:Submodule.span F ((fun x:V => ((1:F),x)) '' (B:Set V))≠⊤) :
    directions B≠⊤ := by
  classical
  let S:=Submodule.span F ((fun x:V => ((1:F),x)) '' (B:Set V))
  have base (x:V) (hx:x∈B) : ((1:F),x)∈S := Submodule.subset_span ⟨x,hx,rfl⟩
  intro h
  let Z:=LinearMap.inr F F V
  have sub : directions B≤S.comap Z := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hx
    have e:=S.add_mem (base a ha) (base b hb)
    change ((0:F),a+b)∈S
    simpa only [Prod.mk_add_mk,show (1:F)+1=0 by decide] using e
  have all (x:V) : ((0:F),x)∈S := sub (h ▸ Submodule.mem_top)
  obtain ⟨a,ha⟩:=non
  have one:((1:F),(0:V))∈S := by
    simpa only [Prod.mk_add_mk,add_zero,ZModModule.add_self] using S.add_mem (base a ha) (all a)
  apply proper
  apply top_unique
  rintro ⟨k,x⟩ _
  rcases (show ∀k:F,k=0 ∨ k=1 from by decide) k with rfl|rfl
  · exact all x
  · simpa only [Prod.mk_add_mk,add_zero,zero_add] using S.add_mem one (all x)

theorem complement_fifteen {A O:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ho:O∈octadFamily A) :
    (family (A\O)).ncard=15 ∧ Partitions (A\O) := by
  classical
  obtain ⟨range,zero⟩:=mem_filter.mp ho
  obtain ⟨oa,oz⟩:=mem_powersetCard.mp range
  have len : (A\O).card=16 := by rw [card_sdiff_of_subset oa,size,oz]
  have total : (∑x∈A\O,x)=0 := by
    have h:=sum_sdiff oa (f:=id)
    change (∑x∈A\O,x)+syndrome O=syndrome A at h
    simpa only [zero,full_sum size avoid,add_zero] using h
  have no : ¬FlatAt (A\O) 0 := by
    rintro ⟨W,d,hw⟩
    exact avoid ⟨W,d,fun _ hx => add_subset_add sdiff_subset sdiff_subset (hw hx)⟩
  have witness:Witness (A\O):=⟨len,no,Green51ElevenRelations.affine_of_sixteen_sum _ len total⟩
  have octadNon:=card_pos.mp (show 0<O.card by omega)
  have proper:=outside_span oa octadNon (relation_even size avoid ho)
  have neq:=small_directions (card_pos.mp (show 0<(A\O).card by omega)) proper
  have lt:=Submodule.finrank_lt neq
  rw [show Module.finrank F V=11 by simp [Cube]] at lt
  rcases exact_count _ witness with high|low
  · omega
  exact ⟨low.2,unique_through_nonzero _ witness low.1⟩

end Green51PerfectColumns
#print axioms Green51PerfectColumns.full_sum
#print axioms Green51PerfectColumns.complement_fifteen
