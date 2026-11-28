import Green51HighDimensionCount

/-! # The fibre dimension needed for almost every dense sumset class -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical

theorem fibre_classes_le_stable {s r h : ℕ} (hs : 5 ≤ s) (rows : h≤2*s+3) (small : h<2^r) :
    fibreClasses s r h ≤ universalDefectNumber h := by
  by_cases enough : h-1≤r
  · exact (stable_dense_number hs rows small enough).le
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  rw [count_omission_words hs small (stable_omission_margin hs small) ref size full]
  let e : ↥B ≃ Fin (2*s+3) := Fintype.equivOfCardEq (by simpa using size)
  rw [reindex_word_classes e h,←stable_row_count (H := 𝔽₂ r) rows]
  obtain ⟨f,hf⟩ := (finrank_le_iff_exists_linearMap (R := F) (M := 𝔽₂ r) (M' := 𝔽₂ (h-1))).mp
    (by simpa [𝔽₂,𝔽] using (show r≤h-1 by omega))
  obtain ⟨embed,_⟩ := word_class_embedding (I := Fin h) f hf h
  exact Nat.card_le_card_of_injective _ embed.injective

theorem high_dimension_fibre_classes {s r h D : ℕ} (hs : 5 ≤ s) (rows : h≤2*s+3)
    (small : h<2^r) (large : 10≤h) (gap : 64*h*(Nat.log 2 h+2)≤D^2) (high : h+D≤2*(r+1)) :
    2^(D^2/8)*(universalDefectNumber h-fibreClasses s r h) ≤ universalDefectNumber h := by
  classical
  by_cases enough : h-1≤r
  · rw [stable_dense_number hs rows small enough,Nat.sub_self,Nat.mul_zero]
    exact Nat.zero_le _
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  rw [count_omission_words hs small (stable_omission_margin hs small) ref size full]
  let e : ↥B ≃ Fin (2*s+3) := Fintype.equivOfCardEq (by simpa using size)
  rw [reindex_word_classes e h,←stable_row_count (H := 𝔽₂ r) rows]
  obtain ⟨f,hf⟩ := (finrank_le_iff_exists_linearMap (R := F) (M := 𝔽₂ r) (M' := 𝔽₂ (h-1))).mp
    (by simpa [𝔽₂,𝔽] using (show r≤h-1 by omega))
  apply high_embedding_deficit (I := Fin h) f hf large gap
  simpa [𝔽₂,𝔽] using high

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.fibre_classes_le_stable
#print axioms Green51FrameIsomorphisms.high_dimension_fibre_classes
