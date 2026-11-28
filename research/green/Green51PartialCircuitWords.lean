import Green51CircuitCentres

/-! # Partial translates of a shortest odd circuit -/

namespace Green51SliceStability
open Finset
open scoped Classical symmDiff

variable {ι : Type*} [DecidableEq ι]

private theorem flip_card_lower (S : Finset ι) (i : ι) : S.card ≤ (S ∆ {i}).card + 1 := by
  have inc : S ⊆ (S ∆ {i}) ∪ {i} := le_symmDiff_sup_right S {i}
  simpa using (card_le_card inc).trans (card_union_le (S ∆ {i}) {i})

private theorem flip_outside (S : Finset ι) (i : ι) (hi : i ∉ S) : S ∆ {i} = insert i S := by
  ext x
  by_cases h : x = i <;> simp [mem_symmDiff, h, hi]

/-- Two sets of at least five possible letters force the odd word to be a singleton. -/
theorem two_large_slices (T I J : Finset ι) (hi : 5 ≤ I.card) (hj : 5 ≤ J.card)
    (odd : Odd T.card)
    (small : ∀ i ∈ I, ∀ j ∈ J, ((T ∆ {i}) ∆ {j}).card ≤ 3) : T.card = 1 := by
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < I.card by omega)
  obtain ⟨b, hb⟩ := card_pos.mp (show 0 < J.card by omega)
  have three : T.card ≤ 3 := by
    by_contra! high
    have cap := small a ha b hb
    have five : T.card ≤ 5 := by
      have := flip_card_lower T a
      have := flip_card_lower (T ∆ {a}) b
      omega
    have forced (i : ι) (h : i ∈ I) : i ∈ T := by
      by_contra out
      have init := small i h b hb
      have low := flip_card_lower (T ∆ {i}) b
      rw [flip_outside _ _ out, card_insert_of_notMem out] at low
      rw [flip_outside _ _ out] at init
      omega
    have same : I = T := eq_of_subset_of_card_le (fun _ => forced _) (by omega)
    have belongs : b ∈ T := by
      by_contra out
      have comm : (T ∆ {b}) ∆ {a} = (T ∆ {a}) ∆ {b} := symmDiff_right_comm _ _ _
      have low := flip_card_lower (T ∆ {b}) a
      rw [comm, flip_outside _ _ out, card_insert_of_notMem out] at low
      omega
    have self := small b (same.symm ▸ belongs) b hb
    rw [symmDiff_symmDiff_cancel_right] at self
    omega
  obtain ⟨i, iI, out⟩ := exists_mem_notMem_of_card_lt_card (show T.card < I.card by omega)
  have four := card_insert_of_notMem out
  obtain ⟨j, jJ, away⟩ := exists_mem_notMem_of_card_lt_card (show (insert i T).card < J.card by omega)
  have cap := small i iI j jJ
  rw [flip_outside _ _ out, flip_outside _ _ away, card_insert_of_notMem away, card_insert_of_notMem out] at cap
  rw [Nat.odd_iff] at odd
  omega

end Green51SliceStability
#print axioms Green51SliceStability.two_large_slices

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

omit [AddCommGroup G] [Module F G] in
private theorem near_subset {P Q Z : Finset G} (p : P ⊆ Z) (q : Q ⊆ Z) : P ∆ Q ⊆ Z := by
  intro x hx
  rcases mem_symmDiff.mp hx with h | h
  · exact p h.1
  · exact q h.1

private def near_letters (a b c : G) := (({a} : Finset G) ∆ {b}) ∆ {c}

private theorem near_letters_spec {a b c : G} {D : Finset G} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) :
    near_letters a b c ⊆ D ∧ Odd (near_letters a b c).card ∧ (near_letters a b c).card ≤ 3 ∧
    (∑ x ∈ near_letters a b c, x) = a + b + c := by
  let R := ({a} : Finset G) ∆ {b}
  have ab := (card_symmDiff_parts {a} {b}).2
  have abc := (card_symmDiff_parts R {c}).2
  change R.card + 2 * (({a} : Finset G) ∩ {b}).card = _ at ab
  change (near_letters a b c).card + 2 * (R ∩ {c}).card = _ at abc
  simp only [card_singleton] at ab abc
  refine ⟨near_subset (near_subset (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr hb))
    (singleton_subset_iff.mpr hc), ?_, by omega, ?_⟩
  · rw [Nat.odd_iff]; omega
  · unfold near_letters
    simp only [sum_word, sum_singleton]

private theorem near_word_cap {C D S E : Finset G} (m : ShortestOddCircuit D C)
    (sc : S ⊆ C) (ed : E ⊆ D) (par : Even (S.card + E.card))
    (eq : (∑ x ∈ S, x) = ∑ x ∈ E, x) : S.card ≤ E.card := by
  have cc := card_sdiff_add_card_eq_card sc
  have odd := m.2.1
  have bound := word_bound m (sdiff_subset.trans m.1 : C \ S ⊆ D) ed
    (by rw [Nat.odd_iff] at odd ⊢; rw [Nat.even_iff] at par; omega)
    ((circuit_complement_sum sc m.2.2.1).trans eq)
  omega


/-- Two large partial circuit translates determine a container for the entire sum fibre. -/
theorem two_fibre_container {D C I J : Finset G} (m : ShortestOddCircuit D C)
    (iC : I ⊆ C) (jC : J ⊆ C) (i5 : 5 ≤ I.card) (j5 : 5 ≤ J.card) {a b x : G}
    (first : ∀ i ∈ I, a + i ∈ D) (second : ∀ j ∈ J, b + j ∈ D) (mem : x ∈ D)
    (same : a + b + x ∈ Submodule.span F (C : Set G)) :
    ∃ i ∈ C, a + b + x = i := by
  obtain ⟨U, uc, rep⟩ := subset_sum C (a + b + x) same
  have presentation : ∃ T ⊆ C, Odd T.card ∧ (∑ t ∈ T, t) = a + b + x := by
    by_cases par : Odd U.card
    · exact ⟨U, uc, par, rep⟩
    · have n := card_sdiff_add_card_eq_card uc
      have o := m.2.1
      exact ⟨C \ U, sdiff_subset, by rw [Nat.odd_iff] at o par ⊢; omega,
        (circuit_complement_sum uc m.2.2.1).trans rep⟩
  obtain ⟨T, tc, odd, total⟩ := presentation
  have one := Green51SliceStability.two_large_slices T I J i5 j5 odd (by
    intro i hi j hj
    obtain ⟨subD, oddD, three, rhs⟩ := near_letters_spec (first i hi) (second j hj) mem
    let P := (T ∆ {i}) ∆ {j}
    have pC : P ⊆ C := near_subset (near_subset tc (singleton_subset_iff.mpr (iC hi))) (singleton_subset_iff.mpr (jC hj))
    have q1 := (card_symmDiff_parts T {i}).2
    have q2 := (card_symmDiff_parts (T ∆ {i}) {j}).2
    simp only [card_singleton] at q1 q2
    have ev : Even (P.card + (near_letters (a+i) (b+j) x).card) := by
      dsimp only [P]; rw [Nat.odd_iff] at odd oddD; rw [Nat.even_iff]; omega
    have word : (∑ t ∈ P, t) = ∑ y ∈ near_letters (a+i) (b+j) x, y := by
      dsimp only [P]; rw [sum_word, sum_word, sum_singleton, sum_singleton, total, rhs]; abel
    exact (near_word_cap m pC subD ev word).trans three)
  obtain ⟨i, rfl⟩ := card_eq_one.mp one
  exact ⟨i, tc (mem_singleton_self i), by simpa using total.symm⟩

end Green51GirthFrame
#print axioms Green51GirthFrame.two_fibre_container

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Three labels in a common partial translate determine its centre. -/
theorem partial_centres_unique {D C I : Finset G} (m : ShortestOddCircuit D C) (inc : I ⊆ C)
    (three : 3 ≤ I.card) {a b : G} (cover : ∀ i ∈ I, ∃ j ∈ C, a + i = b + j) :
    a = b := by
  obtain ⟨i, ii⟩ := card_pos.mp (show 0 < I.card by omega)
  obtain ⟨j, jc, same⟩ := cover i ii
  have v := Submodule.add_mem (Submodule.span F (C : Set G))
    (Submodule.subset_span (inc ii)) (Submodule.subset_span jc)
  have eq : a + b = i + j := by
    calc
      _ = (a + i) + (b + i) := by rw [add_add_add_comm, ZModModule.add_self, add_zero]
      _ = i + j := by rw [same, add_add_add_comm, ZModModule.add_self, zero_add, add_comm]
  rw [←eq] at v
  obtain ⟨U, uc, value⟩ := subset_sum C (a + b) v
  have chooseEven : ∃ T ⊆ C, Even T.card ∧ (∑ t ∈ T, t) = a + b := by
    by_cases par : Even U.card
    · exact ⟨U, uc, par, value⟩
    · have n := card_sdiff_add_card_eq_card uc
      have o := m.2.1
      exact ⟨C \ U, sdiff_subset, by rw [Nat.even_iff] at par ⊢; rw [Nat.odd_iff] at o; omega,
        (circuit_complement_sum uc m.2.2.1).trans value⟩
  obtain ⟨T, tc, even, total⟩ := chooseEven
  have cap (k : G) (hk : k ∈ I) : (T ∆ {k}).card ≤ 1 := by
    obtain ⟨l, lc, h⟩ := cover k hk
    have par := (card_symmDiff_parts T {k}).2
    simp only [card_singleton] at par
    have relation : (∑ z ∈ T ∆ {k}, z) = ∑ z ∈ ({l} : Finset G), z := by
      rw [sum_word, sum_singleton, sum_singleton, total, add_right_comm, h, add_right_comm, ZModModule.add_self, zero_add]
    simpa using near_word_cap m (near_subset tc (singleton_subset_iff.mpr (inc hk))) (singleton_subset_iff.mpr (m.1 lc))
      (by rw [Nat.even_iff] at even ⊢; simp only [card_singleton]; omega) relation
  have low : T.card ≤ 2 := by
    have inc : T ⊆ (T ∆ {i}) ∪ {i} := le_symmDiff_sup_right _ _
    have h := (card_le_card inc).trans (card_union_le (T ∆ {i}) {i})
    have := cap i ii
    simp only [card_singleton] at h
    omega
  obtain ⟨k, hk, outside⟩ := exists_mem_notMem_of_card_lt_card (show T.card < I.card by omega)
  have add : T ∆ {k} = insert k T := by ext x; by_cases h : x = k <;> simp [mem_symmDiff, h, outside]
  have lim := cap k hk
  rw [add, card_insert_of_notMem outside] at lim
  have empty := card_eq_zero.mp (show T.card = 0 by omega)
  rw [empty, sum_empty] at total
  calc
    a = a + (a + b) := by rw [←total, add_zero]
    _ = b := by rw [←add_assoc, ZModModule.add_self, zero_add]

end Green51GirthFrame
#print axioms Green51GirthFrame.partial_centres_unique

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

omit [AddCommGroup G] [Module F G] in
private theorem flip_margin {S I : Finset G} {n : ℕ} (room : n + 2 ≤ I.card)
    (cap : ∀ i ∈ I, (S ∆ {i}).card ≤ n) : S.card + 1 ≤ n := by
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < I.card by omega)
  have sub : S ⊆ (S ∆ {j}) ∪ {j} := le_symmDiff_sup_right _ _
  have bound := (card_le_card sub).trans (card_union_le _ _)
  simp only [card_singleton] at bound
  obtain ⟨i, hI, out⟩ := exists_mem_notMem_of_card_lt_card (show S.card < I.card by have := cap j hj; omega)
  have flip : S ∆ {i} = insert i S := by ext x; by_cases h : x = i <;> simp [mem_symmDiff, h, out]
  have sz := cap i hI
  rwa [flip, card_insert_of_notMem out] at sz

/-- Four partial translates with six labels each preserve every pair-sum relation among their fibres. -/
theorem four_fibre_relation {D C I J K L : Finset G} (m : ShortestOddCircuit D C)
    (iC : I ⊆ C) (jC : J ⊆ C) (kC : K ⊆ C) (lC : L ⊆ C)
    (i6 : 6 ≤ I.card) (j6 : 6 ≤ J.card) (k6 : 6 ≤ K.card) (l6 : 6 ≤ L.card)
    {a b c d : G} (aI : ∀ i ∈ I, a+i ∈ D) (bJ : ∀ j ∈ J, b+j ∈ D)
    (cK : ∀ k ∈ K, c+k ∈ D) (dL : ∀ l ∈ L, d+l ∈ D)
    (same : a+b+c+d ∈ Submodule.span F (C : Set G)) : a+b = c+d := by
  obtain ⟨U, uc, rep⟩ := subset_sum C (a+b+c+d) same
  have evenRep : ∃ T ⊆ C, Even T.card ∧ (∑ x ∈ T, x) = a+b+c+d := by
    by_cases ev : Even U.card
    · exact ⟨U, uc, ev, rep⟩
    · have n := card_sdiff_add_card_eq_card uc
      have o := m.2.1
      exact ⟨C \ U, sdiff_subset, by rw [Nat.even_iff] at ev ⊢; rw [Nat.odd_iff] at o; omega,
        (circuit_complement_sum uc m.2.2.1).trans rep⟩
  obtain ⟨T, tc, ev, total⟩ := evenRep
  have four (i : G) (hi : i ∈ I) (j : G) (hj : j ∈ J) (k : G) (hk : k ∈ K) (l : G) (hl : l ∈ L) :
      ((((T ∆ {i}) ∆ {j}) ∆ {k}) ∆ {l}).card ≤ 4 := by
    obtain ⟨threeD, od, three, rhs⟩ := near_letters_spec (aI i hi) (bJ j hj) (cK k hk)
    let E := near_letters (a+i) (b+j) (c+k) ∆ {d+l}
    have inside : E ⊆ D := near_subset threeD (singleton_subset_iff.mpr (dL l hl))
    let W := (((T ∆ {i}) ∆ {j}) ∆ {k}) ∆ {l}
    have wc : W ⊆ C := near_subset (near_subset (near_subset (near_subset tc
      (singleton_subset_iff.mpr (iC hi))) (singleton_subset_iff.mpr (jC hj))) (singleton_subset_iff.mpr (kC hk))) (singleton_subset_iff.mpr (lC hl))
    have wp := (card_symmDiff_parts T {i}).2
    have xp := (card_symmDiff_parts (T ∆ {i}) {j}).2
    have yp := (card_symmDiff_parts ((T ∆ {i}) ∆ {j}) {k}).2
    have zp := (card_symmDiff_parts (((T ∆ {i}) ∆ {j}) ∆ {k}) {l}).2
    have ep := (card_symmDiff_parts (near_letters (a+i) (b+j) (c+k)) {d+l}).2
    simp only [card_singleton] at wp xp yp zp ep
    have par : Even (W.card + E.card) := by
      dsimp only [W,E]; rw [Nat.even_iff] at ev ⊢; rw [Nat.odd_iff] at od; omega
    have value : (∑ x ∈ W, x) = ∑ x ∈ E, x := by
      dsimp only [W,E]; simp only [sum_word, sum_singleton, total, rhs]; abel
    have small : E.card ≤ 4 := by dsimp only [E]; omega
    exact (near_word_cap m wc inside par value).trans small
  have three (i) (hi : i ∈ I) (j) (hj : j ∈ J) (k) (hk : k ∈ K) :
      (((T ∆ {i}) ∆ {j}) ∆ {k}).card ≤ 3 := by
    have := flip_margin l6 (four i hi j hj k hk); omega
  have two (i) (hi : i ∈ I) (j) (hj : j ∈ J) : ((T ∆ {i}) ∆ {j}).card ≤ 2 := by
    have := flip_margin (show 3+2 ≤ K.card by omega) (three i hi j hj); omega
  have one (i) (hi : i ∈ I) : (T ∆ {i}).card ≤ 1 := by
    have := flip_margin (show 2+2 ≤ J.card by omega) (two i hi); omega
  have last := flip_margin (show 1+2 ≤ I.card by omega) one
  have empty := card_eq_zero.mp (show T.card=0 by omega)
  rw [empty, sum_empty, add_assoc (a+b)] at total
  calc
    a+b = (a+b+(c+d))+(c+d) := by rw [add_assoc, ZModModule.add_self, add_zero]
    _ = c+d := by rw [←total, zero_add]

end Green51GirthFrame
#print axioms Green51GirthFrame.four_fibre_relation
