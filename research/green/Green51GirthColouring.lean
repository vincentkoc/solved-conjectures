import Green51OddCircuitSlices

/-! # A linear four-colouring for binary directions of large odd girth -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff

namespace Green51GirthFrame
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem odd_cast {n : ℕ} (odd : Odd n) : (n : F) = 1 := by
  obtain ⟨k, rfl⟩ := odd
  push_cast
  rw [show (2 : F) = 0 by decide, zero_mul, zero_add]

/-- A binary coordinate vanishes at one marked circuit element and takes value one
at every other circuit element and every additional basis direction. -/
theorem coordinate_colour {D C H : Finset G} (m : ShortestOddCircuit D C) {p : G} (hp : p ∈ C)
    (bh : C.erase p ⊆ H) (ih : LinearIndepOn F id (H : Set G)) {i : G} (hi : i ∈ C.erase p) :
    ∃ f : G →ₗ[F] F, (∀ z ∈ C, z ≠ i → f z = 1) ∧ (∀ z ∈ H \ (C.erase p), f z = 1) := by
  classical
  let B := C.erase p
  let v (z : G) := (1 : F) + (if z = i then 1 else 0)
  obtain ⟨f, hf⟩ := extend_values ih v
  have sumB : (∑ x ∈ B, x) = p := by
    have h := circuit_complement_sum (singleton_subset_iff.mpr hp) m.2.2.1
    simpa [B, sdiff_singleton_eq_erase] using h
  have zeroB : (B.card : F) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    have eq := card_erase_of_mem hp
    have par := m.2.1
    rw [Nat.odd_iff] at par
    change 2 ∣ (C.erase p).card
    omega
  change i ∈ B at hi
  have fp : f p = 1 := by
    rw [←sumB, map_sum]
    calc
      ∑ x ∈ B, f x = ∑ x ∈ B, v x := sum_congr rfl (fun x hx => hf x (bh hx))
      _ = 1 := by simp [v, sum_add_distrib, Finset.sum_ite_eq', hi, zeroB]
  refine ⟨f, ?_, ?_⟩
  · intro z hz nz
    by_cases atp : z = p
    · simpa [atp] using fp
    · rw [hf z (bh (mem_erase.mpr ⟨atp, hz⟩))]; simp [v, nz]
  · intro z hz
    obtain ⟨zh, zb⟩ := mem_sdiff.mp hz
    rw [hf z zh]; simp [v, show z ≠ i from fun eq => zb (eq ▸ hi)]

end Green51GirthFrame

namespace Green51GirthFrame
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- A binary set of large odd girth admits a linear map to four colours that avoids zero. -/
theorem linear_four_colouring (D : Finset G) (g d : ℕ)
    (rank : Module.finrank F G ≤ g - 1 + d) (room : 2 ^ d * (d + 2) + 4 ≤ 2 * (g - 1))
    (short : ∀ R ⊆ D, Odd R.card → (∑ a ∈ R, a) = 0 → g ≤ R.card) :
    ∃ f : G →ₗ[F] F × F, ∀ x ∈ D, f x ≠ 0 := by
  classical
  rcases choose_circuit D with ⟨f, one⟩|⟨C, m⟩
  · exact ⟨f.prod 0, fun x hx e => one_ne_zero ((one x hx).symm.trans (congrArg Prod.fst e))⟩
  have minSize := short C m.1 m.2.1 m.2.2.1
  have pos : 0 < C.card := by omega
  obtain ⟨p, hp⟩ := card_pos.mp pos
  let B := C.erase p
  obtain ⟨H, bh, hd, ind, hRank, reps⟩ := coordinates m hp
  let Z := H \ B
  have bCard : B.card = C.card - 1 := card_erase_of_mem hp
  have zr : Z.card + B.card = H.card := card_sdiff_add_card_eq_card bh
  have zd : Z.card ≤ d := by omega
  let slices (Q : Finset G) := C.powerset.filter fun S =>
    Odd (S.card + Q.card) ∧ (∑ s ∈ S, s) + (∑ q ∈ Q, q) ∈ D
  have size (Q) (hq : Q ∈ Z.powerset) (S) (hs : S ∈ slices Q) : S.card ≤ Q.card + 1 := by
    obtain ⟨inC, odd, rep⟩ := mem_filter.mp hs
    have qz := mem_powerset.mp hq
    have qd : Q ⊆ D := fun x hx => hd (mem_sdiff.mp (qz hx)).1
    exact slice_size m (mem_powerset.mp inC) qd odd rep rfl
  have dist (Q) (_ : Q ∈ Z.powerset) (S) (hs : S ∈ slices Q) (R) (hr : R ∈ slices Q) :
      (S \ R).card + (R \ S).card ≤ 2 := by
    obtain ⟨inS, oddS, rx⟩ := mem_filter.mp hs
    obtain ⟨inR, oddR, ry⟩ := mem_filter.mp hr
    exact slice_dist m (mem_powerset.mp inS) (mem_powerset.mp inR) oddS oddR rx ry rfl rfl
  have count : (∑ q ∈ Z.powerset, (q.card + 1)) + 2 ≤ B.card := by
    have exactSum := Green51GirthSlices.powerset_budget Z
    have bound := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0 < 2) zd) (Nat.add_le_add_right zd 2)
    omega
  obtain ⟨i, hi, j, hj, _, miss⟩ := Green51GirthSlices.unused_pair B Z.powerset slices (fun q => q.card + 1) size dist count
  obtain ⟨f, fc, fz⟩ := coordinate_colour m hp bh ind hi
  obtain ⟨e, ec, ez⟩ := coordinate_colour m hp bh ind hj
  refine ⟨f.prod e, ?_⟩
  intro x hx zero
  obtain ⟨Q, qz, S, sc, odd, rep⟩ := reps x hx
  have avoid := miss Q (mem_powerset.mpr qz) S
    (mem_filter.mpr ⟨mem_powerset.mpr sc, odd, rep ▸ hx⟩)
  have value (l : G →ₗ[F] F) (ls : ∀ s ∈ S, l s = 1) (lq : ∀ q ∈ Q, l q = 1) : l x = 1 := by
    have h := congrArg l rep
    rw [map_add, map_sum, map_sum, sum_eq_card_nsmul ls, sum_eq_card_nsmul lq] at h
    simpa only [nsmul_eq_mul, mul_one, ←Nat.cast_add, odd_cast odd] using h.symm
  rcases avoid with left|right
  · have fx := value f (fun s hs => fc s (sc hs) (fun eq => left (eq ▸ hs))) (fun z hz => fz z (qz hz))
    exact one_ne_zero (fx.symm.trans (congrArg Prod.fst zero))
  · have ex := value e (fun s hs => ec s (sc hs) (fun eq => right (eq ▸ hs))) (fun z hz => ez z (qz hz))
    exact one_ne_zero (ex.symm.trans (congrArg Prod.snd zero))
end Green51GirthFrame

#print axioms Green51GirthFrame.coordinate_colour
#print axioms Green51GirthFrame.linear_four_colouring
