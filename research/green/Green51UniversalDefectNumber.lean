import Green51EmptyRowStability
import Green51DenseFibreStability

/-! # A single stable class number independent of both dimensions -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame
open scoped Classical
variable {I J H : Type*} [AddCommGroup H] [Module F H]

private theorem permute_word (e : I ≃ J) (A : I → Finset H) :
    WordMatch A (fun j => A (e.symm j)) := by
  refine ⟨e,LinearEquiv.refl F H,fun _ => 0,fun i => ?_⟩
  change (A i).map _=A (e.symm (e i))
  rw [e.symm_apply_apply]
  convert (map_refl (s := A i)) using 2
  ext x
  simp

theorem reindex_word_classes [Fintype I] [Fintype J] (e : I ≃ J) (h : ℕ) :
    Nat.card (Quotient (wordSetoid I H h))=Nat.card (Quotient (wordSetoid J H h)) := by
  let lift (w : {w : I → Finset H // (∑ i,(w i).card)=h}) :
      {w : J → Finset H // (∑ i,(w i).card)=h} :=
    ⟨fun j => w.val (e.symm j),(Equiv.sum_comp e.symm (fun i => (w.val i).card)).trans w.property⟩
  have relate (w) : WordMatch w.val (lift w).val := permute_word e w.val
  let q := Quotient.map (sa := wordSetoid I H h) (sb := wordSetoid J H h) lift
    (fun a b hab => ((relate a).symm.trans hab).trans (relate b))
  apply Nat.card_congr (Equiv.ofBijective q ⟨?_,?_⟩)
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact fun eq => Quotient.sound (((relate a).trans (Quotient.exact eq)).trans (relate b).symm)
  · intro x
    induction x using Quotient.inductionOn with | _ w =>
      let a := fun i => w.val (e i)
      have sz : (∑ i,(a i).card)=h := (Equiv.sum_comp e (fun j => (w.val j).card)).trans w.property
      refine ⟨Quotient.mk (wordSetoid I H h) ⟨a,sz⟩,Quotient.sound ?_⟩
      change WordMatch (fun j => w.val (e (e.symm j))) w.val
      simpa only [e.apply_symm_apply] using WordMatch.refl w.val

theorem stable_row_count [Fintype H] [DecidableEq H] {g h : ℕ} (enough : h≤g) :
    Nat.card (Quotient (wordSetoid (Fin h) H h))=Nat.card (Quotient (wordSetoid (Fin g) H h)) := by
  induction g, enough using Nat.le_induction with
  | base => rfl
  | succ g hg ih =>
    let e : Option (Fin g) ≃ Fin (g+1) := Fintype.equivOfCardEq (by simp)
    exact (ih.trans (add_empty_row_count (I := Fin g) h (by simpa using hg))).trans (reindex_word_classes e h)

private theorem defect_in_band {s r h : ℕ} (hs : 5 ≤ s) (small : h<2^r) :
    min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*((2*s+3)*2^r-h) := by
  let g := 2*s+3
  let Q := 2^r
  change min (5*g+12) (4*g+20)*Q < 8*(g*Q-h)
  have v : min (5*g+12) (4*g+20)*Q+8*h < (4*g+20+8)*Q := by
    rw [Nat.add_mul]
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right Q (min_le_right _ _))
      (Nat.mul_lt_mul_of_pos_left small (by decide))
  have b : 4*g+20+8≤8*g := by dsimp [g];omega
  have w : (4*g+20+8)*Q≤8*(g*Q) := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right Q b
  have e := v.trans_le w
  rw [Nat.mul_sub]
  omega

/-- Finite model with exactly h rows and the universal fibre dimension h−1. -/
noncomputable def universalDefectNumber (h : ℕ) : ℕ :=
  Nat.card (Quotient (wordSetoid (Fin h) (𝔽₂ (h-1)) h))

/-- Once the rows and fibre have room for h unused points, the number of affine classes
of actual near-extremal doubles depends only on h. -/
theorem stable_dense_number {s r h : ℕ} (hs : 5 ≤ s) (rows : h≤2*s+3)
    (small : h<2^r) (rank : h-1≤r) : fibreClasses s r h=universalDefectNumber h := by
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  rw [count_omission_words hs small (defect_in_band hs small) ref size full]
  let e : ↥B ≃ Fin (2*s+3) := Fintype.equivOfCardEq (by simpa using size)
  rw [reindex_word_classes e h,←stable_row_count (H := 𝔽₂ r) rows]
  obtain ⟨f,hf⟩ := (finrank_le_iff_exists_linearMap (R := F) (M := 𝔽₂ (h-1)) (M' := 𝔽₂ r)).mp
    (by simpa [𝔽₂,𝔽] using rank)
  exact (stable_fibre_count f hf h (by simp [𝔽₂,𝔽])).symm

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.reindex_word_classes
#print axioms Green51FrameIsomorphisms.stable_row_count
#print axioms Green51FrameIsomorphisms.stable_dense_number
