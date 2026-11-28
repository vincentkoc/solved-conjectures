import Green51OmissionRowTail
import Green51UniversalDefectNumber

/-! # Few incomplete rows in almost every affine class of actual dense binary doubles -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

noncomputable abbrev DoubleFamily (s r h : ℕ) := countedDoubles (2*(s+1)+r) ((2*s+3)*2^r-h) (threshold (2*s))

/-- A representative has at least B circuit rows that omit a site of the full fibre. -/
def SpreadClass {s r h : ℕ} (C : Finset (𝔽₂ (2*(s+1)))) (B : ℕ)
    (q : Quotient (affineSetoid (DoubleFamily s r h))) : Prop :=
  ∃ (d : DoubleFamily s r h), Quotient.mk _ d=q ∧
    ∃ row : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r), (∀ i∈C,(row i).Nonempty) ∧
      (layers C row).card=(2*s+3)*2^r-h ∧ FibrePresents C row d.val ∧
      B ≤ (occupiedRows (fun i : C => (row i.val)ᶜ)).card

private theorem total_unused {s r h : ℕ} (C : Finset (𝔽₂ (2*(s+1))))
    (w : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r)) (small : h<2^r) (size : C.card=2*s+3)
    (sz : (layers C w).card=(2*s+3)*2^r-h) :
    (∑ i : C,(w i.val)ᶜ.card)=h := by
  classical
  have both : (layers C w).card + ∑ i : C,(w i.val)ᶜ.card = (2*s+3)*2^r := by
    rw [all_card_layers,←sum_add_distrib]
    simp [card_add_card_compl,size,𝔽₂,𝔽]
  have limit : h≤(2*s+3)*2^r := small.le.trans (Nat.le_mul_of_pos_left _ (by omega))
  rw [sz] at both
  omega

theorem dense_row_exception {s r h B : ℕ} (large : 10 ≤ h) (cut : 64*(Nat.log 2 h+2) ≤ B)
    (small : h<2^r)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*((2*s+3)*2^r-h))
    {C : Finset (𝔽₂ (2*(s+1)))} (circuit : ShortestOddCircuit C C) (size : C.card=2*s+3)
    (span : Submodule.span F (C : Set (𝔽₂ (2*(s+1))))=⊤) :
    2^(B*h/8)*Nat.card {q // SpreadClass (r := r) (h := h) C B q} ≤ universalDefectNumber h := by
  classical
  let Q := {q // SpreadClass (r := r) (h := h) C B q}
  choose d eq row live sz presentation many using fun q : Q => q.property
  let defects (q : Q) (i : C) := (row q i.val)ᶜ
  have total (q : Q) : ∑ i,(defects q i).card=h := total_unused C (row q) small size (sz q)
  apply many_active_presentations_rare large cut defects total many
  intro p q w
  have matched : WordMatch (fun i : C => row p i.val) (fun i : C => row q i.val) := by
    simpa only [defects,compl_compl] using w.compl
  have aff := (presented_fibre_equivalence near circuit size span (live p) (live q) (sz p) (sz q)
    (presentation p) (presentation q)).mpr ((word_histogram C _ _).mp matched)
  apply Subtype.ext
  exact (eq p).symm.trans ((Quotient.sound (s := affineSetoid (DoubleFamily s r h)) aff).trans (eq q))

/-- In the stable range this is a bound relative to the count of all actual affine classes. -/
theorem dense_row_fraction {s r h B : ℕ} (hs : 5 ≤ s) (rows : h ≤ 2*s+3)
    (small : h<2^r) (rank : h-1 ≤ r) (large : 10 ≤ h) (cut : 64*(Nat.log 2 h+2) ≤ B)
    {C : Finset (𝔽₂ (2*(s+1)))} (circuit : ShortestOddCircuit C C) (size : C.card=2*s+3)
    (span : Submodule.span F (C : Set (𝔽₂ (2*(s+1))))=⊤) :
    2^(B*h/8)*Nat.card {q // SpreadClass (r := r) (h := h) C B q} ≤ fibreClasses s r h := by
  have le := Nat.mul_le_mul_right (2^r) (min_le_right (5*(2*s+3)+12) (4*(2*s+3)+20))
  have base : 13 ≤ 2*s+3 := by omega
  have prod := Nat.mul_le_mul_right (2^r) base
  have room : h≤(2*s+3)*2^r := small.le.trans (Nat.le_mul_of_pos_left _ (by omega))
  have near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*((2*s+3)*2^r-h) := by
    have sub := Nat.sub_add_cancel room
    nlinarith only [le,prod,sub,small]
  rw [stable_dense_number hs rows small rank]
  exact dense_row_exception large cut small near circuit size span

/-- Some presentation has at most L unused sites in each individual row. -/
def SmallRowsClass {s r h : ℕ} (C : Finset (𝔽₂ (2*(s+1)))) (L : ℕ)
    (q : Quotient (affineSetoid (DoubleFamily s r h))) : Prop :=
  ∃ (d : DoubleFamily s r h), Quotient.mk _ d=q ∧
    ∃ row : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r), (∀ i∈C,(row i).Nonempty) ∧
      (layers C row).card=(2*s+3)*2^r-h ∧ FibrePresents C row d.val ∧
      ∀ i∈C,(row i)ᶜ.card ≤ L

theorem dense_small_rows_fraction {s r h B L : ℕ} (hs : 5 ≤ s) (rows : h ≤ 2*s+3)
    (small : h<2^r) (rank : h-1 ≤ r) (large : 10 ≤ h) (cut : 64*(Nat.log 2 h+2) ≤ B)
    (gap : (B-1)*L<h) {C : Finset (𝔽₂ (2*(s+1)))} (circuit : ShortestOddCircuit C C)
    (size : C.card=2*s+3) (span : Submodule.span F (C : Set (𝔽₂ (2*(s+1))))=⊤) :
    2^(B*h/8)*Nat.card {q // SmallRowsClass (r := r) (h := h) C L q} ≤ fibreClasses s r h := by
  classical
  have include' (q) (smallRows : SmallRowsClass (r := r) (h := h) C L q) : SpreadClass C B q := by
    obtain ⟨d,eq,row,live,sz,pres,bound⟩ := smallRows
    refine ⟨d,eq,row,live,sz,pres,?_⟩
    let A (i : C) := (row i.val)ᶜ
    have sum := (occupied_sum A).trans (total_unused C row small size sz)
    have lim := sum_le_sum (s := univ) (f := fun i : occupiedRows A => (A i.val).card)
      (g := fun _ => L) (fun i _ => bound i.val.val i.val.property)
    rw [sum] at lim
    simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id] at lim
    by_contra! lt
    have fewer : (occupiedRows A).card ≤ B-1 := by exact Nat.le_pred_of_lt lt
    exact (not_lt_of_ge (lim.trans (Nat.mul_le_mul_right L fewer))) gap
  let f (x : {q // SmallRowsClass (r := r) (h := h) C L q}) : {q // SpreadClass (r := r) (h := h) C B q} :=
    ⟨x.val,include' x.val x.property⟩
  have inj : Function.Injective f := by
    intro x y eq
    apply Subtype.ext
    exact congrArg (fun u : {q // SpreadClass (r := r) (h := h) C B q} => u.val) eq
  exact (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective f inj)).trans
    (dense_row_fraction hs rows small rank large cut circuit size span)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.dense_row_exception
#print axioms Green51FrameIsomorphisms.dense_row_fraction
#print axioms Green51FrameIsomorphisms.dense_small_rows_fraction
