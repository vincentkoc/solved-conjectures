import Green51AnchoredOmissionRows

/-! # Recovering words by restoring their empty rows -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

noncomputable def occupiedRows {I H : Type*} [Fintype I] (A : I → Finset H) : Finset I := by
  classical
  exact univ.filter fun i => (A i).Nonempty

theorem WordMatch.occupied_card {I J H : Type*} [Fintype I] [Fintype J] [AddCommGroup H] [Module F H]
    {A : I → Finset H} {B : J → Finset H} (m : WordMatch A B) :
    (occupiedRows A).card=(occupiedRows B).card := by
  classical
  obtain ⟨σ,u,t,rows⟩ := m
  have same : (occupiedRows A).map σ.toEmbedding=occupiedRows B := by
    ext j
    obtain ⟨i,rfl⟩ := σ.surjective j
    simp [occupiedRows,←rows i]
  rw [←same,card_map]

variable {I H : Type*} [Fintype I] [AddCommGroup H] [Module F H]
omit [AddCommGroup H] [Module F H] in
theorem occupied_sum (A : I → Finset H) :
    (∑ i : occupiedRows A,(A i.val).card)= ∑ i,(A i).card := by
  classical
  change (∑ i ∈ (occupiedRows A).attach,(A i.val).card)=_
  rw [sum_attach (occupiedRows A) (fun i => (A i).card)]
  apply sum_subset (subset_univ _) (fun i hi hn => ?_)
  exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp (by simpa [occupiedRows] using hn))

theorem restore_empty_rows (A B : I → Finset H) {J : Type*}
    (ea : J ≃ ↥(occupiedRows A)) (eb : J ≃ ↥(occupiedRows B))
    (w : WordMatch (fun i => A (ea i)) (fun i => B (eb i))) : WordMatch A B := by
  classical
  obtain ⟨ρ,u,t,rows⟩ := w
  let live := (ea.symm.trans ρ).trans eb
  let S : Set I := ↑(occupiedRows A)
  let T : Set I := ↑(occupiedRows B)
  let live' : S ≃ T := live
  have eqCard : Fintype.card S=Fintype.card T := Fintype.card_congr live'
  let empty : (Sᶜ : Set I) ≃ (Tᶜ : Set I) := Fintype.equivOfCardEq (by
    rw [Fintype.card_compl_set,Fintype.card_compl_set,eqCard])
  let extend := (Equiv.Set.compl live').symm empty
  let σ := extend.val
  have inside (j : J) : σ (ea j)=eb (ρ j) := by simpa [σ,live',live] using extend.property (ea j)
  have outside (i : I) (hi : i ∉ occupiedRows A) : σ i ∉ occupiedRows B := by
    intro bad
    obtain ⟨j,hj⟩ := eb.surjective ⟨σ i,bad⟩
    obtain ⟨k,rfl⟩ := ρ.surjective j
    have eq : σ (ea k)=σ i := (inside k).trans (congrArg Subtype.val hj)
    exact hi (σ.injective eq ▸ (ea k).property)
  let shifts (i : I) := if hi : i∈occupiedRows A then t (ea.symm ⟨i,hi⟩) else 0
  refine ⟨σ,u,shifts,fun i => ?_⟩
  by_cases hi : i∈occupiedRows A
  · obtain ⟨j,hj⟩ := ea.surjective ⟨i,hi⟩
    have eq : (ea j).val=i := congrArg Subtype.val hj
    rw [show shifts i=t j by simp [shifts,hi,←hj],←eq,inside]
    exact rows j
  · have a : A i=∅ := not_nonempty_iff_eq_empty.mp (by simpa [occupiedRows] using hi)
    have b : B (σ i)=∅ := not_nonempty_iff_eq_empty.mp (by simpa [occupiedRows] using outside i hi)
    simp [a,b]

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.WordMatch.occupied_card
#print axioms Green51FrameIsomorphisms.occupied_sum
#print axioms Green51FrameIsomorphisms.restore_empty_rows
