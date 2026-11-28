import Green51DenseOmissionRowTail
import Green51DirectionRankTail

/-! # The middle direction rank in the affine classes of dense binary doubles -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

/-- Some presentation has within-row direction rank at distance at least D/2 from h/2. -/
def FarRankClass {s r h : ℕ} (C : Finset (𝔽₂ (2*(s+1)))) (D : ℕ)
    (q : Quotient (affineSetoid (DoubleFamily s r h))) : Prop :=
  ∃ (d : DoubleFamily s r h), Quotient.mk _ d=q ∧
    ∃ row : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r), (∀ i∈C,(row i).Nonempty) ∧
      (layers C row).card=(2*s+3)*2^r-h ∧ FibrePresents C row d.val ∧
      (let d := Module.finrank F (rowDirectionSpace (fun i : C => (row i.val)ᶜ));
       2*d+D≤h ∨ h+D≤2*d)

theorem dense_rank_exception {s r h D : ℕ} (large : 10 ≤ h) (cut : 64*h*(Nat.log 2 h+2) ≤ D^2)
    (small : h<2^r)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*((2*s+3)*2^r-h))
    {C : Finset (𝔽₂ (2*(s+1)))} (circuit : ShortestOddCircuit C C) (size : C.card=2*s+3)
    (span : Submodule.span F (C : Set (𝔽₂ (2*(s+1))))=⊤) :
    2^(D^2/8)*Nat.card {q // FarRankClass (r := r) (h := h) C D q} ≤ universalDefectNumber h := by
  classical
  let Q := {q // FarRankClass (r := r) (h := h) C D q}
  choose d eq row live sz presentation many using fun q : Q => q.property
  let defects (q : Q) (i : C) := (row q i.val)ᶜ
  have total (q : Q) : ∑ i,(defects q i).card=h := total_unused C (row q) small size (sz q)
  apply far_rank_presentations_rare large cut defects total many
  intro p q w
  have eq' := class_eq_of_omission_match near circuit size span (live p) (live q) (sz p) (sz q)
    (presentation p) (presentation q) w
  exact Subtype.ext ((eq p).symm.trans (eq'.trans (eq q)))

/-- In the stable range this is a bound relative to the count of all actual affine classes. -/
theorem dense_rank_fraction {s r h D : ℕ} (hs : 5 ≤ s) (rows : h ≤ 2*s+3)
    (small : h<2^r) (rank : h-1 ≤ r) (large : 10 ≤ h) (cut : 64*h*(Nat.log 2 h+2) ≤ D^2)
    {C : Finset (𝔽₂ (2*(s+1)))} (circuit : ShortestOddCircuit C C) (size : C.card=2*s+3)
    (span : Submodule.span F (C : Set (𝔽₂ (2*(s+1))))=⊤) :
    2^(D^2/8)*Nat.card {q // FarRankClass (r := r) (h := h) C D q} ≤ fibreClasses s r h := by
  have near := stable_omission_margin hs small
  rw [stable_dense_number hs rows small rank]
  exact dense_rank_exception large cut small near circuit size span

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.dense_rank_exception
#print axioms Green51FrameIsomorphisms.dense_rank_fraction
