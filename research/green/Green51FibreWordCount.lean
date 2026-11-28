import Green51StableFibreRank
import Green51DenseFibreClassification

/-! # Orbit counts of fixed-size words after an injective change of fibre space -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51OriginRecovery
open scoped Classical
variable {I J L H : Type*} [AddCommGroup H] [Module F H]

namespace WordMatch
theorem refl (A : I → Finset H) : WordMatch A A := by
  refine ⟨Equiv.refl _,LinearEquiv.refl F H,fun _ => 0,fun i => ?_⟩
  change (A i).map _=A i
  convert (map_refl (s := A i)) using 2
  ext x
  simp

theorem symm {A : I → Finset H} {B : J → Finset H} (w : WordMatch A B) : WordMatch B A := by
  obtain ⟨σ,u,t,h⟩ := w
  refine ⟨σ.symm,u.symm,fun j => -u.symm (t (σ.symm j)),fun j => ?_⟩
  have hh := h (σ.symm j)
  rw [σ.apply_symm_apply] at hh
  rw [←hh,map_map]
  convert (map_refl (s := A (σ.symm j))) using 2
  ext x
  simp

theorem trans {A : I → Finset H} {B : J → Finset H} {C : L → Finset H}
    (w : WordMatch A B) (w' : WordMatch B C) : WordMatch A C := by
  obtain ⟨σ,u,t,h⟩ := w
  obtain ⟨τ,v,s,k⟩ := w'
  refine ⟨σ.trans τ,u.trans v,fun i => v (t i)+s (σ i),fun i => ?_⟩
  change _=C (τ (σ i))
  rw [←k,←h,map_map]
  congr 1
  ext x
  simp [add_assoc]

omit [AddCommGroup H] [Module F H] in
private theorem map_full_compl [Fintype H] [DecidableEq H] (w : Finset H) (e : H ≃ H) :
    wᶜ.map e.toEmbedding=(w.map e.toEmbedding)ᶜ := by
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  simp

theorem compl [Fintype H] [DecidableEq H] {A : I → Finset H} {B : J → Finset H}
    (w : WordMatch A B) : WordMatch (fun i => (A i)ᶜ) (fun j => (B j)ᶜ) := by
  obtain ⟨σ,u,t,h⟩ := w
  exact ⟨σ,u,t,fun i => (map_full_compl _ _).trans (congrArg (fun C : Finset H => Cᶜ) (h i))⟩

end WordMatch

private theorem row_class_map [Fintype H] [DecidableEq H] (A B : Finset H) (u : H ≃ₗ[F] H) :
    translationClass (A.map u.toEquiv.toEmbedding)=translationClass B ↔
      ∃ t, A.map ((u.toEquiv.trans (Equiv.addRight t)).toEmbedding)=B := by
  rw [eq_comm,same_class_iff]
  simp only [Green51OriginRecovery.translate,map_map]
  rfl

theorem word_frequency_iff [Fintype H] [DecidableEq H] [Fintype I] [Fintype J]
    (A : I → Finset H) (C : J → Finset H) :
    WordMatch A C ↔ ∃ u : H ≃ₗ[F] H,∀ t : Finset (Finset H),
      frequency (fun i => translationClass ((A i).map u.toEquiv.toEmbedding)) t=
      frequency (fun j => translationClass (C j)) t := by
  classical
  constructor
  · rintro ⟨σ,u,t,h⟩
    exact ⟨u,(match_iff_frequency _ _).mp ⟨σ,fun i => (row_class_map _ _ _).mpr ⟨t i,h i⟩⟩⟩
  · rintro ⟨u,hh⟩
    obtain ⟨σ,h⟩ := (match_iff_frequency _ _).mpr hh
    choose t ids using fun i => (row_class_map _ _ _).mp (h i)
    exact ⟨σ,u,t,ids⟩

theorem word_histogram [Fintype H] [DecidableEq H] (B : Finset I) (A C : I → Finset H) :
    WordMatch (fun i : B => A i.val) (fun j : B => C j.val) ↔ FibreMatch B A C :=
  word_frequency_iff _ _

/-- Unlabelled configurations of h sites, with independent translations in each row. -/
def wordSetoid (I H : Type*) [Fintype I] [AddCommGroup H] [Module F H] (h : ℕ) :
    Setoid {w : I → Finset H // (∑ i,(w i).card)=h} where
  r a b := WordMatch a.val b.val
  iseqv := ⟨fun a => WordMatch.refl a.val,WordMatch.symm,WordMatch.trans⟩

theorem stable_fibre_count [Fintype I] [Fintype H] [DecidableEq H] {K : Type*}
    [AddCommGroup K] [Module F K] [Fintype K] [DecidableEq K]
    (f : H →ₗ[F] K) (inj : Function.Injective f) (h : ℕ) (enough : h-1 ≤ Module.finrank F H) :
    Nat.card (Quotient (wordSetoid I H h))=Nat.card (Quotient (wordSetoid I K h)) := by
  let lift (w : {w : I → Finset H // (∑ i,(w i).card)=h}) :
      {w : I → Finset K // (∑ i,(w i).card)=h} :=
    ⟨fun i => (w.val i).map ⟨f,inj⟩,by simpa only [card_map] using w.property⟩
  have iff (a b) : (wordSetoid I K h).r (lift a) (lift b) ↔ (wordSetoid I H h).r a b :=
    word_embedding_iff _ _ f inj
  let q := Quotient.map lift (fun a b hab => (iff a b).mpr hab)
  apply Nat.card_congr (Equiv.ofBijective q ⟨?_,?_⟩)
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact fun eq => Quotient.sound ((iff a b).mp (Quotient.exact eq))
  · intro x
    induction x using Quotient.inductionOn with | _ w =>
      obtain ⟨a,sz,rel⟩ := compress_of_total f inj w.val (by simpa only [w.property] using enough)
      have size : (∑ i,(a i).card)=h := (Finset.sum_congr rfl (fun i _ => sz i)).trans w.property
      exact ⟨Quotient.mk (wordSetoid I H h) ⟨a,size⟩,Quotient.sound rel.symm⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.word_histogram
#print axioms Green51FrameIsomorphisms.stable_fibre_count
