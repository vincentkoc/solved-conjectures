import Green51GeelenGirth

/-! # Compatible centres of full circuit translates -/

open Finset
open scoped Classical symmDiff
namespace Green51SliceExtrema
variable {α : Type*} [DecidableEq α]

/-- An even word that stays of weight at most three after every triple change is empty. -/
theorem triple_defect {C T : Finset α} (g : 5 ≤ C.card) (odd : Odd C.card)
    (inside : T ⊆ C) (even : Even T.card)
    (small : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, (((T ∆ {x}) ∆ {y}) ∆ {z}).card ≤ 3) : T = ∅ := by
  classical
  have add (U : Finset α) (u : α) (hu : u ∉ U) : U ∆ {u} = insert u U := by
    ext z
    simp only [mem_symmDiff, mem_singleton, mem_insert]
    aesop
  have sz := card_sdiff_add_card_eq_card inside
  have ne : (C \ T).Nonempty := by
    apply card_pos.mp
    rw [Nat.odd_iff] at odd
    rw [Nat.even_iff] at even
    omega
  obtain ⟨a, ha⟩ := ne
  obtain ⟨ac, at'⟩ := mem_sdiff.mp ha
  have initial := small a ac a ac a ac
  rw [symmDiff_symmDiff_cancel_right, add _ _ at', card_insert_of_notMem at'] at initial
  by_contra nonempty
  have enough : 3 ≤ (C \ T).card := by omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (C \ T).card by omega)
  have left := card_erase_of_mem hx
  obtain ⟨y, hy⟩ := card_pos.mp (show 0 < ((C \ T).erase x).card by omega)
  have rest := card_erase_of_mem hy
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (((C \ T).erase x).erase y).card by omega)
  obtain ⟨yx, hy⟩ := mem_erase.mp hy
  obtain ⟨zy, hxz⟩ := mem_erase.mp hz
  obtain ⟨zx, hz⟩ := mem_erase.mp hxz
  obtain ⟨xc, xt⟩ := mem_sdiff.mp hx
  obtain ⟨yc, yt⟩ := mem_sdiff.mp hy
  obtain ⟨zc, zt⟩ := mem_sdiff.mp hz
  have yi : y ∉ insert x T := by simp [yx, yt]
  have zi : z ∉ insert y (insert x T) := by simp [zy, zx, zt]
  have lower := small x xc y yc z zc
  rw [add _ _ xt, add _ _ yi, add _ _ zi, card_insert_of_notMem zi, card_insert_of_notMem yi,
    card_insert_of_notMem xt] at lower
  exact nonempty (card_eq_zero.mp (by omega))

end Green51SliceExtrema

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51NearThreshold
open scoped Classical Pointwise symmDiff
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

omit [AddCommGroup G] [Module F G] in
private theorem diff_subset {P Q Z : Finset G} (p : P ⊆ Z) (q : Q ⊆ Z) : P ∆ Q ⊆ Z := by
  intro x hx
  rcases mem_symmDiff.mp hx with h | h
  · exact p h.1
  · exact q h.1

/-- Addition of binary subset sums is symmetric difference of their indexing sets. -/
theorem sum_word (P Q : Finset G) : (∑ x ∈ P ∆ Q, x) = (∑ x ∈ P, x) + ∑ x ∈ Q, x :=
  Green51FourSpace.subset_sum_add id P Q

private def letters (a b c : G) := (({a} : Finset G) ∆ {b}) ∆ {c}

private theorem letters_spec {a b c : G} {D : Finset G} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) :
    letters a b c ⊆ D ∧ Odd (letters a b c).card ∧ (letters a b c).card ≤ 3 ∧
    (∑ x ∈ letters a b c, x) = a + b + c := by
  let R := ({a} : Finset G) ∆ {b}
  have ab := (card_symmDiff_parts {a} {b}).2
  have abc := (card_symmDiff_parts R {c}).2
  change R.card + 2 * (({a} : Finset G) ∩ {b}).card = _ at ab
  change (letters a b c).card + 2 * (R ∩ {c}).card = _ at abc
  simp only [card_singleton] at ab abc
  refine ⟨diff_subset (diff_subset (singleton_subset_iff.mpr ha) (singleton_subset_iff.mpr hb))
    (singleton_subset_iff.mpr hc), ?_, by omega, ?_⟩
  · rw [Nat.odd_iff]; omega
  · unfold letters
    simp only [sum_word, sum_singleton]

private theorem odd_word_cap {C D S E : Finset G} (m : ShortestOddCircuit D C)
    (sc : S ⊆ C) (ed : E ⊆ D) (par : Even (S.card + E.card))
    (eq : (∑ x ∈ S, x) = ∑ x ∈ E, x) : S.card ≤ E.card := by
  have cc := card_sdiff_add_card_eq_card sc
  have odd := m.2.1
  have bound := word_bound m (sdiff_subset.trans m.1 : C \ S ⊆ D) ed
    (by rw [Nat.odd_iff] at odd ⊢; rw [Nat.even_iff] at par; omega)
    ((circuit_complement_sum sc m.2.2.1).trans eq)
  omega

/-- Three translates of a shortest circuit are compatible across their quotient classes. -/
theorem centres_compatible {C D : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    {a b c : G} (insideA : ∀ i ∈ C, a + i ∈ D) (insideB : ∀ i ∈ C, b + i ∈ D)
    (insideC : ∀ i ∈ C, c + i ∈ D) (defect : a + b + c ∈ Submodule.span F (C : Set G)) :
    a + b + c = 0 := by
  obtain ⟨U, uc, rep⟩ := subset_sum C (a + b + c) defect
  have even_rep : ∃ T ⊆ C, Even T.card ∧ (∑ x ∈ T, x) = a + b + c := by
    by_cases h : Even U.card
    · exact ⟨U, uc, h, rep⟩
    · have sz := card_sdiff_add_card_eq_card uc
      have odd := m.2.1
      exact ⟨C \ U, sdiff_subset, by rw [Nat.even_iff] at h ⊢; rw [Nat.odd_iff] at odd; omega,
        (circuit_complement_sum uc m.2.2.1).trans rep⟩
  obtain ⟨T, tc, even, sumT⟩ := even_rep
  have empty := Green51SliceExtrema.triple_defect g m.2.1 tc even (by
    intro i hi j hj k hk
    obtain ⟨lC, op, _, sl⟩ := letters_spec hi hj hk
    obtain ⟨lD, oq, sq, sr⟩ := letters_spec (insideA _ hi) (insideB _ hj) (insideC _ hk)
    let P := letters i j k
    let Q := letters (a + i) (b + j) (c + k)
    have ct := (card_symmDiff_parts T P).2
    have eq : (∑ x ∈ T ∆ P, x) = ∑ x ∈ Q, x := by
      rw [sum_word, sumT, sl, sr]
      abel
    have cap := odd_word_cap m (diff_subset tc lC) lD
      (by change Even ((T ∆ P).card + Q.card); change Odd P.card at op
          change Odd Q.card at oq; rw [Nat.odd_iff] at op oq; rw [Nat.even_iff] at even ⊢; omega) eq
    simpa only [P, letters, symmDiff_assoc] using cap.trans sq)
  simpa [empty] using sumT.symm


/-- Centres of full circuit translates in every quotient class form a complement. -/
theorem centre_complement {D C : Finset G} (m : ShortestOddCircuit D C) (g : 5 ≤ C.card)
    (cover : ∀ x : G, ∃ t, (∀ i ∈ C, t + i ∈ D) ∧ x + t ∈ Submodule.span F (C : Set G))
    (full : ∀ x ∈ D, ∃ t, (∀ i ∈ C, t + i ∈ D) ∧ ∃ i ∈ C, x = t + i) :
    ∃ P : Submodule F G, IsCompl P (Submodule.span F (C : Set G)) ∧
      ∀ x, x ∈ D ↔ ∃ t ∈ P, ∃ i ∈ C, x = t + i := by
  classical
  let V := Submodule.span F (C : Set G)
  let centre (a : G) := ∀ i ∈ C, a + i ∈ D
  have zero : centre 0 := fun i hi => by simpa using m.1 hi
  have add {a b : G} (ha : centre a) (hb : centre b) : centre (a + b) := by
    obtain ⟨c, hc, v⟩ := cover (a + b)
    have eq := centres_compatible m g ha hb hc v
    have same : a + b = c := by
      calc
        a + b = a + b + (c + c) := by rw [ZModModule.add_self, add_zero]
        _ = c := by rw [←add_assoc, eq, zero_add]
    rwa [same]
  let P : Submodule F G := {
    carrier := {x | centre x}
    zero_mem' := zero
    add_mem' := add
    smul_mem' := by
      intro c x hx
      rcases (show ∀ z : F, z = 0 ∨ z = 1 from by decide) c with rfl | rfl
      · simpa using zero
      · simpa using hx }
  have dis : Disjoint P V := by
    apply Submodule.disjoint_def.mpr
    intro x hx hv
    have v : x + 0 + 0 ∈ V := by simpa using hv
    simpa using centres_compatible m g hx zero zero v
  have top : P ⊔ V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨t, ht, ht'⟩ := cover x
    exact Submodule.mem_sup.mpr ⟨t, ht, x + t, ht', by rw [add_left_comm, ZModModule.add_self, add_zero]⟩
  refine ⟨P, ⟨dis, codisjoint_iff.mpr top⟩, ?_⟩
  intro x
  constructor
  · exact full x
  · rintro ⟨t, ht, i, hi, rfl⟩
    exact ht i hi

end Green51GirthFrame

#print axioms Green51SliceExtrema.triple_defect
#print axioms Green51GirthFrame.sum_word
#print axioms Green51GirthFrame.centres_compatible
#print axioms Green51GirthFrame.centre_complement
