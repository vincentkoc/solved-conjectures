import Green51FibreWordCount
import Green51AffineProfileCount

/-! # Counting actual dense sumsets by configurations of unused sites -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51GirthFrame Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

theorem all_card_layers {H V : Type*} [DecidableEq H] [DecidableEq V] (B : Finset V) (w : V→Finset H) :
    (layers B w).card=∑ i : B,(w i.val).card := by
  classical
  rw [layers,card_biUnion,←sum_attach B]
  · apply sum_congr rfl
    intro i _
    exact card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
  · intro i _ j _ ne
    apply disjoint_left.mpr
    intro x ha hb
    obtain ⟨a,_,rfl⟩ := mem_image.mp ha
    obtain ⟨b,_,eq⟩ := mem_image.mp hb
    exact ne (congrArg Prod.snd eq).symm

private theorem complement_total {I H : Type*} [Fintype I] [Fintype H] [DecidableEq H] (w : I→Finset H) :
    (∑ i,(w i).card)+(∑ i,(w i)ᶜ.card)=Fintype.card I*Fintype.card H := by
  rw [←sum_add_distrib]
  simp [card_add_card_compl]

/-- The number of affine classes of dense doubles at a given defect and fibre dimension. -/
noncomputable def fibreClasses (s r h : ℕ) : ℕ :=
  Nat.card (Quotient (affineSetoid (countedDoubles (2*(s+1)+r) ((2*s+3)*2^r-h) (threshold (2*s)))))

theorem count_omission_words {s r h : ℕ} (hs : 5 ≤ s) (small : h<2^r)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*((2*s+3)*2^r-h))
    {B : Finset (𝔽₂ (2*(s+1)))} (ref : ShortestOddCircuit B B) (size : B.card=2*s+3)
    (full : Submodule.span F (B : Set (𝔽₂ (2*(s+1))))=⊤) :
    fibreClasses s r h=Nat.card (Quotient (wordSetoid ↥B (𝔽₂ r) h)) := by
  classical
  let k := (2*s+3)*2^r-h
  let D := countedDoubles (2*(s+1)+r) k (threshold (2*s))
  have slots : Fintype.card (𝔽₂ r)=2^r := by simp [𝔽₂,𝔽]
  have avail : h≤(2*s+3)*2^r := small.le.trans (Nat.le_mul_of_pos_left _ (by omega))
  have total (w : 𝔽₂ (2*(s+1))→Finset (𝔽₂ r)) :
      (layers B w).card+(∑ i : B,(w i.val)ᶜ.card)=(2*s+3)*2^r := by
    simpa only [all_card_layers,Fintype.card_coe,size,slots] using complement_total (fun i : B => w i.val)
  choose row live sz pres using fun S : D => present_counted_fibres hs near ref size full S.property
  let defects (S : D) : {w : ↥B → Finset (𝔽₂ r) // (∑ i,(w i).card)=h} :=
    ⟨fun i => (row S i.val)ᶜ,by
      change (∑ i : B,(row S i.val)ᶜ.card)=h
      have sum := total (row S)
      rw [sz S] at sum
      omega⟩
  have compare {S T : D} (v : 𝔽₂ (2*(s+1)) → Finset (𝔽₂ r))
      (hv : ∀ i∈B,(v i).Nonempty) (sv : (layers B v).card=k) (pv : FibrePresents B v T.val) :
      AffineRelated S.val T.val ↔ WordMatch (defects S).val (fun i : B => (v i.val)ᶜ) := by
    rw [presented_fibre_equivalence near ref size full (live S) hv (sz S) sv (pres S) pv,
      ←word_histogram]
    exact ⟨WordMatch.compl,fun m => by simpa only [defects,compl_compl] using m.compl⟩
  let W := wordSetoid ↥B (𝔽₂ r) h
  let q : Quotient (affineSetoid D) → Quotient W := Quotient.map defects
    (fun a b eq => (compare (row b) (live b) (sz b) (pres b)).mp eq)
  apply Nat.card_congr (Equiv.ofBijective q ⟨?_,?_⟩)
  · intro x y
    induction x using Quotient.inductionOn with | _ a =>
      induction y using Quotient.inductionOn with | _ b =>
        exact fun eq => Quotient.sound ((compare (row b) (live b) (sz b) (pres b)).mpr (Quotient.exact eq))
  · intro x
    induction x using Quotient.inductionOn with | _ w =>
      let v (i : 𝔽₂ (2*(s+1))) := if hi : i∈B then (w.val ⟨i,hi⟩)ᶜ else ∅
      have point (i : B) : (v i.val)ᶜ=w.val i := by simp [v,i.property]
      have vn (i : _) (hi : i∈B) : (v i).Nonempty := by
        have part := single_le_sum (f := fun j : B => (w.val j).card) (fun j _ => Nat.zero_le _) (mem_univ (⟨i,hi⟩ : B))
        rw [w.property] at part
        apply card_pos.mp
        simp only [v,dif_pos hi,card_compl,slots]
        omega
      have mass := total v
      simp_rw [point,w.property] at mass
      have vs : (layers B v).card=k := by dsimp [k];omega
      obtain ⟨S,hm,hp⟩ := realize_fibre_rows hs near ref size full v vn vs
      let y : D := ⟨S,hm⟩
      have rr := (compare (S := y) (T := y) v vn vs hp).mp ((affineSetoid D).iseqv.refl y)
      refine ⟨Quotient.mk (affineSetoid D) y,Quotient.sound ?_⟩
      change WordMatch (defects y).val w.val
      simpa only [point] using rr

/-- Once the fibre has room for the defect and dimension at least h−1, further fibre
dimensions leave the number of affine classes of the original sumsets unchanged. -/
theorem stable_fibre_doubles {s r t h : ℕ} (hs : 5 ≤ s) (le : r≤t) (small : h<2^r) (rank : h-1≤r)
    (low : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*((2*s+3)*2^r-h))
    (high : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^t < 8*((2*s+3)*2^t-h)) :
    fibreClasses s r h=fibreClasses s t h := by
  obtain ⟨B,ref,size,full⟩ := spanning_reference s (by omega)
  have grow : 2^r≤2^t := Nat.pow_le_pow_right (by decide) le
  rw [count_omission_words hs small low ref size full,count_omission_words hs (small.trans_le grow) high ref size full]
  obtain ⟨f,hf⟩ := (finrank_le_iff_exists_linearMap (R := F) (M := 𝔽₂ r) (M' := 𝔽₂ t)).mp (by simpa [𝔽₂,𝔽])
  exact stable_fibre_count f hf h (by simpa [𝔽₂,𝔽] using rank)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.count_omission_words
#print axioms Green51FrameIsomorphisms.stable_fibre_doubles
