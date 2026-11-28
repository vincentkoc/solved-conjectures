import Green51CompressDirectionRank
import Green51LowDimensionCount

/-! # Classes gained by enlarging the fibre above the middle dimension -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

theorem word_class_embedding {I H K : Type*} [Fintype I] [AddCommGroup H] [Module F H]
    [Fintype H] [DecidableEq H] [AddCommGroup K] [Module F K] [Fintype K] [DecidableEq K]
    (f : H →ₗ[F] K) (inj : Function.Injective f) (h : ℕ) :
    ∃ e : Quotient (wordSetoid I H h) ↪ Quotient (wordSetoid I K h),
      ∀ w : {a : I → Finset H // (∑ i,(a i).card)=h},
      e (Quotient.mk (wordSetoid I H h) w) = Quotient.mk (wordSetoid I K h)
        ⟨fun i => (w.val i).map ⟨f,inj⟩,by simpa only [card_map] using w.property⟩ := by
  let X := wordSetoid I H h
  let Y := wordSetoid I K h
  let lift (a : {w : I → Finset H // (∑ i,(w i).card)=h}) :
      {w : I → Finset K // (∑ i,(w i).card)=h} :=
    ⟨fun i => (a.val i).map ⟨f,inj⟩,by simpa only [card_map] using a.property⟩
  have iff (a b) : Y.r (lift a) (lift b) ↔ X.r a b := word_embedding_iff _ _ f inj
  let embed : Quotient X → Quotient Y := Quotient.map lift (fun a b w => (iff a b).mpr w)
  have emb : Function.Injective embed := by
    intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact fun eq => Quotient.sound ((iff a b).mp (Quotient.exact eq))
  exact ⟨⟨embed,emb⟩,fun _ => rfl⟩

theorem high_embedding_deficit {I H K : Type*} [Fintype I] [AddCommGroup H] [Module F H]
    [Fintype H] [DecidableEq H] [AddCommGroup K] [Module F K] [Fintype K] [DecidableEq K]
    (f : H →ₗ[F] K) (inj : Function.Injective f) {h D : ℕ} (large : 10≤h)
    (gap : 64*h*(Nat.log 2 h+2)≤D^2) (high : h+D≤2*(Module.finrank F H+1)) :
    2^(D^2/8)*(Nat.card (Quotient (wordSetoid I K h))-Nat.card (Quotient (wordSetoid I H h))) ≤
      universalDefectNumber h := by
  classical
  let X := wordSetoid I H h
  let Y := wordSetoid I K h
  obtain ⟨embed,mk⟩ := word_class_embedding (I := I) f inj h
  let Bad := {q : Quotient Y // q ∉ Set.range embed}
  have count : Nat.card Bad=Nat.card (Quotient Y)-Nat.card (Quotient X) := by
    let _ := Fintype.ofFinite (Quotient X)
    let _ := Fintype.ofFinite (Quotient Y)
    simp only [Bad,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    congr 1
    exact Fintype.card_congr (Equiv.ofInjective (fun x : Quotient X => embed x) embed.injective).symm
  rw [←count]
  let A (q : Bad) := q.val.out.val
  apply far_rank_presentations_rare large gap A (fun q => q.val.out.property)
  · intro q
    right
    by_contra! lt
    have cap : Module.finrank F (rowDirectionSpace (A q))≤Module.finrank F H := by omega
    obtain ⟨a,sz,rel⟩ := compress_direction_rank f inj (A q) cap
    have total : (∑ i,(a i).card)=h := (sum_congr rfl fun i _ => sz i).trans q.val.out.property
    let x := Quotient.mk X ⟨a,total⟩
    have eq : embed x=Quotient.mk Y q.val.out := (mk ⟨a,total⟩).trans (Quotient.sound rel.symm)
    exact q.property ⟨x,eq.trans q.val.out_eq⟩
  · intro p q w
    have eq : Quotient.mk Y p.val.out=Quotient.mk Y q.val.out := Quotient.sound w
    exact Subtype.ext (p.val.out_eq.symm.trans (eq.trans q.val.out_eq))

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.word_class_embedding
#print axioms Green51FrameIsomorphisms.high_embedding_deficit
