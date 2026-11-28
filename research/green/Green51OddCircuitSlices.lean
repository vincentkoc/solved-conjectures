import Green51OddCircuitBasis
import Green51FourSpaceProjection

/-! # Odd presentations and the diameter of their slices -/

open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff

namespace Green51GirthFrame
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
omit [AddCommGroup G] [Module F G] in
private theorem card_change (P Q : Finset G) :
    (P ∆ Q).card = (P \ Q).card + (Q \ P).card ∧
    (P ∆ Q).card + 2 * (P ∩ Q).card = P.card + Q.card := by
  have dis : Disjoint (P \ Q) (Q \ P) := by
    rw [disjoint_left]; exact fun _ hp hq => (mem_sdiff.mp hp).2 (mem_sdiff.mp hq).1
  have left := card_sdiff_add_card_inter P Q
  have right := card_sdiff_add_card_inter Q P
  rw [inter_comm Q P] at right
  rw [Finset.symmDiff_def, card_union_of_disjoint dis]
  exact ⟨rfl, by omega⟩

omit [AddCommGroup G] [Module F G] in
private theorem change_subset {P Q D : Finset G} (p : P ⊆ D) (q : Q ⊆ D) : P ∆ Q ⊆ D := by
  intro x h
  rcases mem_symmDiff.mp h with h|h
  · exact p h.1
  · exact q h.1

/-- An odd equality of words in the directions is at least as long as the shortest odd circuit. -/
theorem word_bound {C D : Finset G} (minC : ShortestOddCircuit D C) {P Q : Finset G}
    (pd : P ⊆ D) (qd : Q ⊆ D) (odd : Odd (P.card + Q.card))
    (eq : (∑ x ∈ P, x) = ∑ x ∈ Q, x) : C.card ≤ P.card + Q.card := by
  have wt := (card_change P Q).2
  have even := Green51FourSpace.subset_sum_add id P Q
  change (∑ x ∈ P ∆ Q, x) = (∑ x ∈ P, x) + ∑ x ∈ Q, x at even
  rw [eq, ZModModule.add_self] at even
  have size := minC.2.2.2 _ (change_subset pd qd) (by rw [Nat.odd_iff] at odd ⊢; omega) even
  omega

/-- An odd presentation with extra coordinates Q uses at most |Q| + 1 circuit coordinates. -/
theorem slice_size {D C S Q : Finset G} (m : ShortestOddCircuit D C) (sc : S ⊆ C) (qd : Q ⊆ D)
    (odd : Odd (S.card + Q.card)) {x : G} (hx : x ∈ D)
    (rep : (∑ s ∈ S, s) + (∑ q ∈ Q, q) = x) : S.card ≤ Q.card + 1 := by
  let E := Q ∆ {x}
  have size := (card_change Q {x}).2
  change E.card + 2 * (Q ∩ {x}).card = Q.card + ({x} : Finset G).card at size
  rw [card_singleton] at size
  dsimp only [E] at size
  have eq := Green51FourSpace.subset_sum_add id Q {x}
  change (∑ y ∈ E, y) = (∑ q ∈ Q, q) + ∑ y ∈ ({x} : Finset G), y at eq
  rw [sum_singleton, ←rep, add_left_comm, ZModModule.add_self, add_zero] at eq
  have co := card_sdiff_add_card_eq_card sc
  have par := m.2.1
  have bound := word_bound m (sdiff_subset.trans m.1 : C \ S ⊆ D)
    (change_subset qd (singleton_subset_iff.mpr hx) : E ⊆ D)
    (by rw [Nat.odd_iff] at odd par ⊢; omega) ((circuit_complement_sum sc m.2.2.1).trans eq.symm)
  omega

/-- Two presentations using the same extra coordinates differ on at most two circuit positions. -/
theorem slice_dist {D C S R Q : Finset G} (m : ShortestOddCircuit D C) (sc : S ⊆ C) (rc : R ⊆ C)
    (oddS : Odd (S.card + Q.card)) (oddR : Odd (R.card + Q.card)) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (rx : (∑ s ∈ S, s) + (∑ q ∈ Q, q) = x) (ry : (∑ s ∈ R, s) + (∑ q ∈ Q, q) = y) :
    (S \ R).card + (R \ S).card ≤ 2 := by
  let E := ({x} : Finset G) ∆ {y}
  have sz := (card_change {x} {y}).2
  change E.card + 2 * (({x} : Finset G) ∩ {y}).card = ({x} : Finset G).card + ({y} : Finset G).card at sz
  simp only [card_singleton, E] at sz
  have ss := change_subset sc rc
  have eq := Green51FourSpace.subset_sum_add id {x} {y}
  change (∑ a ∈ E, a) = _ at eq
  simp only [sum_singleton, id_eq] at eq
  have left := Green51FourSpace.subset_sum_add id S R
  simp only [id_eq] at left
  have same : (∑ a ∈ C \ (S ∆ R), a) = ∑ a ∈ E, a := by
    rw [circuit_complement_sum ss m.2.2.1, left, eq, ←rx, ←ry, add_add_add_comm, ZModModule.add_self, add_zero]
  obtain ⟨sumSize, parSize⟩ := card_change S R
  have co := card_sdiff_add_card_eq_card ss
  have par := m.2.1
  have low := word_bound m (sdiff_subset.trans m.1 : C \ (S ∆ R) ⊆ D)
    (change_subset (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hy) : E ⊆ D)
    (by rw [Nat.odd_iff] at oddS oddR par ⊢; omega) same
  omega
end Green51GirthFrame

namespace Green51GirthSlices
open Finset
variable {α β : Type*} [DecidableEq α]

/-- A largest member leaves at most one uncovered position in every member of its slice. -/
theorem maximal_slice (S : Finset (Finset α)) (d : ℕ) (size : ∀ a ∈ S, a.card ≤ d)
    (dist : ∀ a ∈ S, ∀ b ∈ S, (a \ b).card + (b \ a).card ≤ 2) :
    ∃ t : Finset α, t.card ≤ d ∧ ∀ a ∈ S, (a \ t).card ≤ 1 := by
  rcases S.eq_empty_or_nonempty with empty|ne
  · exact ⟨∅, by simp, by simp [empty]⟩
  obtain ⟨t, ht, maximal⟩ := S.exists_max_image Finset.card ne
  refine ⟨t, size t ht, fun a ha => ?_⟩
  have one := dist a ha t ht
  have two := card_sdiff_le_card_sdiff_iff.mpr (maximal a ha)
  omega

/-- Two positions outside all chosen largest members cannot occur together in any slice. -/
theorem unused_pair (C : Finset α) (Q : Finset β) (S : β → Finset (Finset α)) (budget : β → ℕ)
    (size : ∀ q ∈ Q, ∀ a ∈ S q, a.card ≤ budget q)
    (dist : ∀ q ∈ Q, ∀ a ∈ S q, ∀ b ∈ S q, (a \ b).card + (b \ a).card ≤ 2)
    (room : (∑ q ∈ Q, budget q) + 2 ≤ C.card) :
    ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ ∀ q ∈ Q, ∀ a ∈ S q, i ∉ a ∨ j ∉ a := by
  classical
  choose t sz small using fun (q : Q) => maximal_slice (S q.val) (budget q.val) (size _ q.property) (dist _ q.property)
  let T := univ.biUnion t
  have bound : T.card ≤ ∑ q ∈ Q, budget q := by
    calc
      _ ≤ ∑ q : Q, (t q).card := card_biUnion_le
      _ ≤ ∑ q : Q, budget q.val := sum_le_sum fun q _ => sz q
      _ = _ := sum_coe_sort Q budget
  obtain ⟨p, hp, pc⟩ := exists_subset_card_eq (show 2 ≤ (C \ T).card by
    have := le_card_sdiff T C; omega)
  obtain ⟨i, j, ne, rfl⟩ := card_eq_two.mp pc
  have hi := mem_sdiff.mp (hp (mem_insert_self i {j}))
  have hj := mem_sdiff.mp (hp (mem_insert_of_mem (mem_singleton_self j)))
  refine ⟨i, hi.1, j, hj.1, ne, fun q hq a ha => ?_⟩
  by_contra! bad
  let b : Q := ⟨q, hq⟩
  have ni : i ∉ t b := fun hz => hi.2 (mem_biUnion.mpr ⟨b, mem_univ _, hz⟩)
  have nj : j ∉ t b := fun hz => hj.2 (mem_biUnion.mpr ⟨b, mem_univ _, hz⟩)
  have both : {i, j} ⊆ a \ t b := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_sdiff]
    exact ⟨⟨bad.1, ni⟩, bad.2, nj⟩
  have lower := card_le_card both
  rw [card_pair ne] at lower
  have upper := small b a ha
  omega
end Green51GirthSlices

namespace Green51GirthSlices
open Finset
variable {α : Type*} [DecidableEq α]
/-- Sum the size bounds of the slices by pairing each subset with its complement. -/
theorem powerset_budget (Z : Finset α) :
    2 * (∑ q ∈ Z.powerset, (q.card + 1)) = 2 ^ Z.card * (Z.card + 2) := by
  have flips (q : Finset α) (_ : q ∈ Z.powerset) : Z \ q ∈ Z.powerset := mem_powerset.mpr sdiff_subset
  have inverse (q : Finset α) (hq : q ∈ Z.powerset) : Z \ (Z \ q) = q := by
    ext x
    have inside := mem_powerset.mp hq
    simp only [mem_sdiff]
    by_cases hx : x ∈ q
    · simp [hx, inside hx]
    · simp [hx]
  have eq : ∑ q ∈ Z.powerset, (q.card + 1) = ∑ q ∈ Z.powerset, ((Z \ q).card + 1) :=
    sum_nbij' (fun q => Z \ q) (fun q => Z \ q) flips flips inverse inverse
      (fun q hq => by rw [inverse q hq])
  rw [two_mul]
  calc
    _ = (∑ q ∈ Z.powerset, ((Z \ q).card + 1)) + ∑ q ∈ Z.powerset, (q.card + 1) := by rw [←eq]
    _ = ∑ _q ∈ Z.powerset, (Z.card + 2) := by
      rw [←sum_add_distrib]
      apply sum_congr rfl
      intro q hq
      have := card_sdiff_add_card_eq_card (mem_powerset.mp hq)
      omega
    _ = _ := by simp [smul_eq_mul]
end Green51GirthSlices

#print axioms Green51GirthFrame.word_bound
#print axioms Green51GirthFrame.slice_size
#print axioms Green51GirthFrame.slice_dist
#print axioms Green51GirthSlices.maximal_slice
#print axioms Green51GirthSlices.unused_pair
#print axioms Green51GirthSlices.powerset_budget
