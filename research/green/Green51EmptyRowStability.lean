import Green51FibreWordCount

/-! # Stabilization of configuration classes under the addition of empty rows -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51OriginRecovery
open scoped Classical
variable {I J H : Type*} [AddCommGroup H] [Module F H] [Fintype H] [DecidableEq H]

private def padded (w : I → Finset H) : Option I → Finset H := Option.elim' ∅ w

private theorem option_frequency {K : Type*} [DecidableEq K] [Fintype I] (f : I → K) (a k : K) :
    frequency (Option.elim' a f) k=(if a=k then 1 else 0)+frequency f k := by
  classical
  simp only [frequency,Fintype.card_subtype,card_filter,Fintype.sum_option]
  rfl

theorem padded_match_iff [Fintype I] [Fintype J] (A : I → Finset H) (C : J → Finset H) :
    WordMatch (padded A) (padded C) ↔ WordMatch A C := by
  classical
  rw [word_frequency_iff,word_frequency_iff]
  apply exists_congr
  intro u
  have l : (fun i => translationClass (((padded A) i).map u.toEquiv.toEmbedding)) =
      Option.elim' (translationClass (∅ : Finset H)) (fun i => translationClass ((A i).map u.toEquiv.toEmbedding)) := by
    funext i
    cases i <;> simp [padded]
  have r : (fun i => translationClass ((padded C) i)) =
      Option.elim' (translationClass (∅ : Finset H)) (fun i => translationClass (C i)) := by
    funext i
    cases i <;> rfl
  rw [l,r]
  simp only [option_frequency,Nat.add_left_cancel_iff]

theorem add_empty_row_count [Fintype I] (h : ℕ) (enough : h≤Fintype.card I) :
    Nat.card (Quotient (wordSetoid I H h))=Nat.card (Quotient (wordSetoid (Option I) H h)) := by
  classical
  let lift (w : {w : I → Finset H // (∑ i,(w i).card)=h}) :
      {w : Option I → Finset H // (∑ i,(w i).card)=h} :=
    ⟨padded w.val,by simpa [Fintype.sum_option,padded] using w.property⟩
  have iff (a b) : (wordSetoid (Option I) H h).r (lift a) (lift b) ↔ (wordSetoid I H h).r a b :=
    padded_match_iff _ _
  let q := Quotient.map lift (fun a b hab => (iff a b).mpr hab)
  apply Nat.card_congr (Equiv.ofBijective q ⟨?_,?_⟩)
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact fun eq => Quotient.sound ((iff a b).mp (Quotient.exact eq))
  · intro x
    induction x using Quotient.inductionOn with | _ w =>
      have blank : ∃ i,w.val i=∅ := by
        by_contra! no
        have all := sum_le_sum (s := univ) (f := fun _ : Option I => 1)
          (g := fun i => (w.val i).card) (fun i _ => card_pos.mpr (no i))
        exact (not_lt_of_ge enough) (by simpa [w.property] using all)
      obtain ⟨j,hj⟩ := blank
      let e := Equiv.swap none j
      let A (i : I) := w.val (e (some i))
      have points (i : Option I) : padded A i=w.val (e i) := by
        cases i with
        | none => simp [padded,e,hj]
        | some i => rfl
      have total := Equiv.sum_comp e (fun i => (w.val i).card)
      simp_rw [←points] at total
      have size : (∑ i,(A i).card)=h := by simpa [Fintype.sum_option,padded,w.property] using total
      refine ⟨Quotient.mk (wordSetoid I H h) ⟨A,size⟩,Quotient.sound ?_⟩
      change WordMatch (padded A) w.val
      refine ⟨e,LinearEquiv.refl F H,fun _ => 0,fun i => ?_⟩
      rw [←points]
      convert (map_refl (s := padded A i)) using 2
      ext x
      simp

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.padded_match_iff
#print axioms Green51FrameIsomorphisms.add_empty_row_count
