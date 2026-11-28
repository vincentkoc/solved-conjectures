import Green51FibreWordCount

/-! # Reconstructing omission words from their nonzero differences to row origins -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

variable {I H : Type*} [AddCommGroup H]

noncomputable def rowOrigin (s : Finset H) : H :=
  if hs : s.Nonempty then hs.choose else 0

theorem rowOrigin_mem (s : Finset H) (hs : s.Nonempty) : rowOrigin s ∈ s := by
  simpa only [rowOrigin,dif_pos hs] using hs.choose_spec

noncomputable def rowCore (s : Finset H) : Finset H := by
  classical
  exact (s.erase (rowOrigin s)).image (fun x => x-rowOrigin s)

theorem core_occupancy (s : Finset H) :
    (rowCore s).card+(if s.Nonempty then 1 else 0)=s.card := by
  classical
  by_cases hs : s.Nonempty
  · rw [if_pos hs,rowCore,card_image_of_injective _ (sub_left_injective),card_erase_of_mem (rowOrigin_mem s hs)]
    have := card_pos.mpr hs
    omega
  · simp [not_nonempty_iff_eq_empty.mp hs,rowCore]

private theorem recover_site (s : Finset H) (x : H) :
    x∈s ↔ (s.Nonempty ∧ x=rowOrigin s) ∨ x-rowOrigin s∈rowCore s := by
  classical
  simp only [rowCore,mem_image,mem_erase,sub_left_inj,exists_eq_right]
  constructor
  · intro h
    by_cases eq : x=rowOrigin s
    · exact Or.inl ⟨⟨x,h⟩,eq⟩
    · exact Or.inr ⟨eq,h⟩
  · rintro (⟨hs,rfl⟩|⟨_,h⟩)
    · exact rowOrigin_mem s hs
    · exact h

theorem match_of_cores [Module F H] (A B : I → Finset H) (u : H ≃ₗ[F] H)
    (support : ∀ i,(A i).Nonempty ↔ (B i).Nonempty)
    (cores : ∀ i,(rowCore (A i)).map u.toEquiv.toEmbedding=rowCore (B i)) :
    WordMatch A B := by
  classical
  let t (i : I) := rowOrigin (B i) - u (rowOrigin (A i))
  refine ⟨Equiv.refl _,u,t,fun i => ?_⟩
  let e := u.toEquiv.trans (Equiv.addRight (t i))
  change (A i).map e.toEmbedding=B i
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [mem_map_equiv,Equiv.symm_apply_apply,recover_site (A i) x,recover_site (B i) (e x)]
  have diff : e x - rowOrigin (B i) = u (x-rowOrigin (A i)) := by
    change u x + (rowOrigin (B i) - u (rowOrigin (A i))) - rowOrigin (B i) = _
    rw [map_sub]
    abel
  have at_origin : e x=rowOrigin (B i) ↔ x=rowOrigin (A i) := by
    rw [←sub_eq_zero, diff, ←u.map_zero, u.injective.eq_iff,sub_eq_zero]
  rw [support i,at_origin,diff,←cores i]
  simp

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.rowOrigin_mem
#print axioms Green51FrameIsomorphisms.core_occupancy
#print axioms Green51FrameIsomorphisms.match_of_cores
