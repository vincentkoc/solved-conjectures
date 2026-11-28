import Green51CircuitOverlap

/-! # Recovering the period subspace from intersections of translates -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G] [Fintype G]

def lag (D : Finset G) (t : G) : ℕ := (D.filter fun x => x+t ∈ D).card

omit [Module F G] [Fintype G] in
theorem lag_shift (D : Finset G) (a t : G) :
    lag (D.map (Equiv.addRight a).toEmbedding) t = lag D t := by
  classical
  unfold lag
  have eq : (D.map (Equiv.addRight a).toEmbedding).filter
      (fun x => x+t ∈ D.map (Equiv.addRight a).toEmbedding) =
      (D.filter (fun x => x+t ∈ D)).map (Equiv.addRight a).toEmbedding := by
    ext x
    obtain ⟨y,rfl⟩ := (Equiv.addRight a).surjective x
    simp only [mem_filter,Finset.mem_map_equiv,Equiv.symm_apply_apply]
    change (y∈D ∧ (Equiv.addRight a).symm (y+a+t) ∈ D) ↔ y∈D ∧ y+t∈D
    rw [add_right_comm y a t,show (Equiv.addRight a).symm (y+t+a)=y+t from
      (Equiv.addRight a).symm_apply_apply (y+t)]
  rw [eq,card_map]

omit [Fintype G] in
private theorem lag_lower {D U : Finset G} (inside : D ⊆ U)
    (t : G) (stable : ∀ x ∈ D, x+t ∈ U) : 2*D.card ≤ U.card+lag D t := by
  classical
  let E := D.map (Equiv.addRight t).toEmbedding
  have sub : E ⊆ U := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hy
    exact stable x hx
  have eq : D ∩ E = D.filter (fun x => x+t ∈ D) := by
    ext x
    simp only [mem_inter,mem_filter,and_congr_right_iff]
    intro _
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := mem_map.mp hx
      change a+t+t ∈ D
      simpa only [add_assoc,ZModModule.add_self,add_zero] using ha
    · intro hx
      exact mem_map.mpr ⟨x+t,hx,by change x+t+t=x; rw [add_assoc,ZModModule.add_self,add_zero]⟩
  have ct := card_union_add_card_inter D E
  have ub := card_le_card (union_subset inside sub)
  rw [eq,show E.card=D.card from card_map _] at ct
  unfold lag
  omega

/-- Outside the period subspace, each lag can hit at most two full circuit cosets. -/
theorem outer_lag {C E D : Finset G} (m : ShortestOddCircuit E C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (sub : D ⊆ (P : Set G).toFinset+C) (t : G) (out : t ∉ P) :
    lag D t ≤ 2*(P : Set G).toFinset.card := by
  classical
  let V := Submodule.span F (C : Set G)
  let π : G →ₗ[F] G := V.subtype.comp (V.projectionOnto P comp.symm)
  have reduce (p i : G) (hp : p ∈ P) (hi : i ∈ C) : π (p+i)=i := by
    change (((V.projectionOnto P comp.symm) (p+i) : V) : G) = i
    have hV : i ∈ V := Submodule.subset_span hi
    rw [map_add,Submodule.projectionOnto_apply_of_mem_right comp.symm hp,
      Submodule.projectionOnto_apply_of_mem_left comp.symm hV,zero_add]
  have nz : π t ≠ 0 := by
    intro h
    exact out ((Submodule.projectionOnto_apply_eq_zero_iff comp.symm).mp (Subtype.ext h))
  let H := C.filter fun c => c+π t ∈ C
  have carrier : (D.filter fun x => x+t ∈ D) ⊆ (P : Set G).toFinset+H := by
    intro x hx
    obtain ⟨hx,hy⟩ := mem_filter.mp hx
    obtain ⟨p,hp,c,hc,rfl⟩ := mem_add.mp (sub hx)
    obtain ⟨b,hb,d,hd,eq⟩ := mem_add.mp (sub hy)
    have pr := congrArg π eq
    rw [reduce b d (Set.mem_toFinset.mp hb) hd,map_add,reduce p c (Set.mem_toFinset.mp hp) hc] at pr
    exact mem_add.mpr ⟨p,hp,c,mem_filter.mpr ⟨hc,pr ▸ hd⟩,rfl⟩
  have cap : H.card ≤ 2 := circuit_shift_overlap m _ nz
  unfold lag
  calc
    _ ≤ _ := card_le_card carrier
    _ ≤ (P : Set G).toFinset.card*H.card := card_add_le
    _ ≤ _ := by simpa only [mul_comm 2 _] using Nat.mul_le_mul_left (P : Set G).toFinset.card cap

/-- Above the overlap bound the missing mask itself determines every period direction of its frame. -/
theorem recover_period {C E D : Finset G} (m : ShortestOddCircuit E C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (sub : D ⊆ (P : Set G).toFinset+C)
    (enough : ((P : Set G).toFinset+C).card + 2*(P : Set G).toFinset.card < 2*D.card) (t : G) :
    t ∈ P ↔ 2*(P : Set G).toFinset.card < lag D t := by
  classical
  constructor
  · intro ht
    have lower := lag_lower sub t (by
      intro x hx
      obtain ⟨p,hp,c,hc,rfl⟩ := mem_add.mp (sub hx)
      exact mem_add.mpr ⟨p+t,Set.mem_toFinset.mpr (P.add_mem (Set.mem_toFinset.mp hp) ht),c,hc,
        add_right_comm p t c⟩)
    omega
  · intro large
    by_contra hn
    exact (not_lt_of_ge (outer_lag m P comp sub t hn)) large

end Green51OriginRecovery
#print axioms Green51OriginRecovery.lag_shift
#print axioms Green51OriginRecovery.outer_lag
#print axioms Green51OriginRecovery.recover_period
