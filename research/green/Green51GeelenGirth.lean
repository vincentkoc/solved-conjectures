import Green51DiameterTwoSlices
import Green51GirthColouring

/-! # Geelen's odd-girth bound in a finite binary vector space -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff

namespace Green51GirthFrame
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]


/-- Binary sum of a circuit word and its outside coordinates. -/
def sliceValue (Q S : Finset G) := (∑ s ∈ S, s) + ∑ q ∈ Q, q

/-- Odd presentations in one outside-coordinate slice. -/
def sliceWords (D C Q : Finset G) := C.powerset.filter fun S =>
  Odd (S.card + Q.card) ∧ sliceValue Q S ∈ D

omit [Fintype G] in
/-- Circuit slices have at most one point per circuit coordinate. Equality forces a translate. -/
theorem slice_shape {D C : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card) (Q : Finset G) :
    (sliceWords D C Q).card ≤ C.card ∧ ((sliceWords D C Q).card = C.card →
      ∃ T ⊆ C, sliceWords D C Q = C.image fun x => T ∆ {x}) := by
  apply Green51SliceExtrema.slice_bound C g _ (fun _ hs => mem_powerset.mp (mem_filter.mp hs).1)
  intro S hs R hr
  obtain ⟨sc, so, sx⟩ := mem_filter.mp hs
  obtain ⟨rc, ro, rx⟩ := mem_filter.mp hr
  have dist := slice_dist m (mem_powerset.mp sc) (mem_powerset.mp rc) so ro sx rx rfl rfl
  obtain ⟨parts, par⟩ := card_symmDiff_parts S R
  rw [Nat.odd_iff] at so ro
  omega

omit [Fintype G] [Module F G] in
/-- The slice presentations cover all directions. -/
theorem cover_by_slices {D C Z : Finset G}
    (reps : ∀ x ∈ D, ∃ Q ⊆ Z, ∃ S ⊆ C,
      Odd (S.card + Q.card) ∧ sliceValue Q S = x) :
    D ⊆ Z.powerset.biUnion (fun Q => (sliceWords D C Q).image (sliceValue Q)) := by
  intro x hx
  obtain ⟨Q, qz, S, sc, od, rep⟩ := reps x hx
  exact mem_biUnion.mpr ⟨Q, mem_powerset.mpr qz, mem_image.mpr
    ⟨S, mem_filter.mpr ⟨mem_powerset.mpr sc, od, rep ▸ hx⟩, rep⟩⟩

private theorem scaled_nat {u v : ℕ} (hu : 0 < u) (h : u ≤ v) : v ≤ u * 2 ^ (v - u) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ←Nat.mul_assoc]
    omega

/-- Geelen's bound for a nonaffine binary set with no odd circuit of size below `g`. -/
theorem geelen_bound (D : Finset G) (g : ℕ) (hg : 5 ≤ g)
    (short : ∀ R ⊆ D, Odd R.card → (∑ a ∈ R, a) = 0 → g ≤ R.card)
    (nonaffine : ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1) :
    D.card ≤ g * 2 ^ (Module.finrank F G + 1 - g) := by
  classical
  rcases choose_circuit D with flat | ⟨C, m⟩
  · exact (nonaffine flat).elim
  have minSize := short C m.1 m.2.1 m.2.2.1
  have pos : 0 < C.card := by omega
  obtain ⟨p, hp⟩ := card_pos.mp pos
  let B := C.erase p
  obtain ⟨H, bh, hd, ind, hRank, reps⟩ := coordinates m hp
  let Z := H \ B
  have bc : B.card = C.card - 1 := card_erase_of_mem hp
  have zc : Z.card + B.card = H.card := card_sdiff_add_card_eq_card bh
  have cover := cover_by_slices (D := D) (C := C) (Z := Z) reps
  have upper : D.card ≤ 2 ^ Z.card * C.card := by
    refine ((card_le_card cover).trans card_biUnion_le).trans ?_
    exact (sum_le_sum (fun Q (_ : Q ∈ Z.powerset) => card_image_le.trans (slice_shape m (by omega) Q).1)).trans (by simp [smul_eq_mul])
  have linear := scaled_nat (show 0 < g by omega) minSize
  calc
    _ ≤ 2 ^ Z.card * (g * 2 ^ (C.card - g)) := upper.trans (Nat.mul_le_mul_left _ linear)
    _ = g * 2 ^ (Z.card + (C.card - g)) := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))

end Green51GirthFrame
#print axioms Green51GirthFrame.slice_shape
#print axioms Green51GirthFrame.cover_by_slices
#print axioms Green51GirthFrame.geelen_bound
