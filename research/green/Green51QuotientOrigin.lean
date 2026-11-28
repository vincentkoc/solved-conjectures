import Green51FrameAutocorrelation

/-! # The sum of the occupied quotient labels locates the origin -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- The distinct occupied cosets of a circuit section sum to zero in the quotient. -/
theorem quotient_labels {C E D : Finset G} (m : ShortestOddCircuit E C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (sub : D ⊆ (P : Set G).toFinset+C) (hit : ∀ c ∈ C, ∃ p ∈ P, p+c ∈ D) :
    (D.image P.mkQ).card=C.card ∧ (∑ z ∈ D.image P.mkQ, z)=0 := by
  classical
  have same : D.image P.mkQ=C.image P.mkQ := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      obtain ⟨p,hp,c,hc,rfl⟩ := mem_add.mp (sub hx)
      exact mem_image.mpr ⟨c,hc,by rw [map_add,show P.mkQ p=0 from
        (Submodule.Quotient.mk_eq_zero _).mpr (Set.mem_toFinset.mp hp),zero_add]⟩
    · intro hz
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hz
      obtain ⟨p,hp,inside⟩ := hit c hc
      exact mem_image.mpr ⟨p+c,inside,by rw [map_add,show P.mkQ p=0 from
        (Submodule.Quotient.mk_eq_zero _).mpr hp,zero_add]⟩
  have one : Set.InjOn P.mkQ (C : Set G) := by
    intro c hc d hd eq
    have ker : c-d ∈ P := (Submodule.Quotient.mk_eq_zero P).mp (by
      change P.mkQ (c-d)=0
      rw [map_sub,eq,sub_self])
    have span : c-d ∈ Submodule.span F (C : Set G) :=
      Submodule.sub_mem _ (Submodule.subset_span hc) (Submodule.subset_span hd)
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp comp.disjoint _ ker span)
  rw [same,card_image_of_injOn one,sum_image one,←map_sum,m.2.2.1,map_zero]
  exact ⟨rfl,rfl⟩

omit [Fintype G] [DecidableEq G] in
/-- Translating the mask translates its occupied quotient labels; their odd count recovers the shift. -/
theorem shifted_label_sum (P : Submodule F G) (D : Finset G) (b : G)
    (odd : Odd (D.image P.mkQ).card) (zero : (∑ z ∈ D.image P.mkQ, z)=0) :
    (∑ z ∈ (D.map (Equiv.addRight b).toEmbedding).image P.mkQ, z)=P.mkQ b := by
  classical
  let Y := D.image P.mkQ
  let e := (Equiv.addRight (P.mkQ b)).toEmbedding
  have eq : (D.map (Equiv.addRight b).toEmbedding).image P.mkQ=Y.map e := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      exact mem_map.mpr ⟨P.mkQ a,mem_image_of_mem _ ha,(map_add P.mkQ a b).symm⟩
    · intro hz
      obtain ⟨x,hx,rfl⟩ := mem_map.mp hz
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      exact mem_image.mpr ⟨a+b,mem_map_of_mem _ ha,map_add P.mkQ a b⟩
  rw [eq,sum_map]
  change (∑ x ∈ Y, (x+P.mkQ b))=P.mkQ b
  rw [sum_add_distrib,zero,zero_add,sum_const]
  obtain ⟨d,hd⟩ := odd
  change Y.card=2*d+1 at hd
  rw [hd,add_nsmul,one_nsmul,show 2*d=d*2 by omega,mul_nsmul,two_nsmul,ZModModule.add_self,zero_add]

end Green51OriginRecovery
#print axioms Green51OriginRecovery.quotient_labels
#print axioms Green51OriginRecovery.shifted_label_sum
