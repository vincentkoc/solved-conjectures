import Green51RowDirectionSpace

/-! # Inequivalent row configurations at prescribed direction rank -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

theorem count_active_at_rank {Q H : Type*} [Finite Q] [AddCommGroup H] [Module F H]
    [FiniteDimensional F H] (h b d : ℕ) (hd : d≤h-b) (A : Q → Fin b → Finset H)
    (total : ∀ q,∑ i,(A q i).card=h) (live : ∀ q i,(A q i).Nonempty)
    (rank : ∀ q,Module.finrank F (rowDirectionSpace (A q))=d)
    (separate : ∀ p q,WordMatch (A p) (A q) → p=q) :
    Nat.card Q ≤ b^(h-b)*2^((h-b-d)*d+(h-b-d)) := by
  classical
  obtain ⟨row,v,mem_core⟩ := active_core_labels h b A total live
  apply marked_span_bound (h-b) b d hd row v
  · intro q
    rw [span_of_row_cores (A q) (row q) (v q) (mem_core q)]
    exact rank q
  · rintro p q sr ⟨u,hu⟩
    apply separate p q
    apply match_labelled_cores u (fun i => ⟨fun _ => live q i,fun _ => live p i⟩) hu (mem_core p)
    rw [sr]
    exact mem_core q

theorem direction_live_rows {I H : Type*} [Fintype I] [AddCommGroup H] [Module F H] {b : ℕ}
    (A : I → Finset H) (e : Fin b ≃ ↥(occupiedRows A)) :
    rowDirectionSpace (fun j => A (e j))=rowDirectionSpace A := by
  classical
  unfold rowDirectionSpace
  apply congrArg (Submodule.span F)
  ext z
  constructor
  · rintro ⟨j,x,y,hx,hy,eq⟩
    exact ⟨(e j).val,x,y,hx,hy,eq⟩
  · rintro ⟨i,x,y,hx,hy,eq⟩
    let i' : ↥(occupiedRows A) := ⟨i,mem_filter.mpr ⟨mem_univ _,⟨x,hx⟩⟩⟩
    exact ⟨e.symm i',x,y,by simpa only [e.apply_symm_apply] using hx,
      by simpa only [e.apply_symm_apply] using hy,eq⟩

theorem count_ambient_at_rank {Q H I : Type*} [Finite Q] [Fintype I]
    [AddCommGroup H] [Module F H] [FiniteDimensional F H] (h b d : ℕ) (hd : d≤h-b)
    (A : Q → I → Finset H) (total : ∀ q,∑ i,(A q i).card=h) (occ : ∀ q,(occupiedRows (A q)).card=b)
    (rank : ∀ q,Module.finrank F (rowDirectionSpace (A q))=d)
    (separate : ∀ p q,WordMatch (A p) (A q) → p=q) :
    Nat.card Q ≤ b^(h-b)*2^((h-b-d)*d+(h-b-d)) := by
  classical
  let e (q : Q) : Fin b ≃ ↥(occupiedRows (A q)) := Fintype.equivOfCardEq (by simp [occ])
  let C (q : Q) (j : Fin b) := A q (e q j)
  apply count_active_at_rank h b d hd C
  · intro q
    exact ((e q).sum_comp (fun i => (A q i.val).card)).trans ((occupied_sum (A q)).trans (total q))
  · intro q i
    exact (mem_filter.mp (e q i).property).2
  · intro q
    rw [show rowDirectionSpace (C q)=rowDirectionSpace (A q) from direction_live_rows _ (e q)]
    exact rank q
  · intro p q m
    exact separate p q (restore_empty_rows _ _ (e p) (e q) m)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.direction_live_rows
#print axioms Green51FrameIsomorphisms.count_ambient_at_rank
#print axioms Green51FrameIsomorphisms.count_active_at_rank
