import Erdos722RectangleCovers

/-!
# Graph blocks for local covers

When three finite points have distinct first coordinates, their second
coordinates prescribe a function on a three-element domain. A unique word
extending every admissible prescription gives a unique covering graph.
-/

namespace Erdos722.PointedProduct
open Finset Function
noncomputable section

variable {U V : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]

def wordGraph (f : U → V) : Finset (Grid U V) :=
  univ.map ⟨fun x => some (x,f x),fun _ _ h => congrArg Prod.fst (Option.some.inj h)⟩

omit [DecidableEq U] [DecidableEq V] in
theorem mem_wordGraph {f : U → V} {x y} : some (x,y)∈wordGraph f ↔ f x=y := by
  constructor
  · intro h
    obtain ⟨z,_,he⟩ := mem_map.mp h
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
    rfl
  · rintro rfl
    exact mem_map.mpr ⟨x,mem_univ _,rfl⟩

omit [DecidableEq V] in
private theorem finite_graph_subset {f : U → V} {T : Finset (Grid U V)} (h : T⊆wordGraph f) :
    (leftTrace T).card=T.card := by
  have hn : none∉T := by
    intro hm
    obtain ⟨x,_,hx⟩ := mem_map.mp (h hm)
    cases hx
  rw [leftTrace,← card_eraseNone_of_not_mem hn]
  apply card_image_iff.mpr
  rintro ⟨x,y⟩ hp ⟨z,w⟩ hq rfl
  have hy := mem_wordGraph.mp (h (mem_eraseNone.mp hp))
  have hw := mem_wordGraph.mp (h (mem_eraseNone.mp hq))
  exact Prod.ext rfl (hy.symm.trans hw)

omit [Fintype U] in
private theorem trace_values {T : Finset (Grid U V)} {d : leftTrace T → V}
    (hd : ∀ x : leftTrace T, some (x.val,d x)∈T)
    (hu : ∀ {x y z}, some (x,y)∈T → some (x,z)∈T → y=z) :
    univ.image d=rightTrace T := by
  ext y
  constructor
  · intro h
    obtain ⟨x,_,rfl⟩ := mem_image.mp h
    exact mem_rightTrace.mpr ⟨x,hd x⟩
  · intro h
    obtain ⟨x,hx⟩ := mem_rightTrace.mp h
    let a : leftTrace T := ⟨x,mem_leftTrace.mpr ⟨y,hx⟩⟩
    exact mem_image.mpr ⟨a,mem_univ _,hu (hd a) hx⟩

/-- Graph construction for a circle first coordinate and an arbitrary second shape. -/
def word_cover {q : ℕ} {t : Shape} (hU : Fintype.card U=q+1) (words : (U → V) → Prop)
    (inside : ∀ f, words f → ∀ (S : Finset U), S.card=3 →
      t.accepts (univ.image (fun x : S => f x.val)).card)
    (extend : ∀ (S : Finset U), S.card=3 → ∀ d : S → V, t.accepts (univ.image d).card →
      ∃! f : U → V, words f ∧ ∀ x : S, f x.val=d x) [Fintype V] : RectangleCover q .circle t U V := by
  classical
  let H := (univ.filter words).image wordGraph
  have memH (B) : B∈H ↔ ∃ f, words f ∧ wordGraph f=B := by simp [H]
  refine ⟨H,?_,?_,?_⟩
  · intro B hB
    obtain ⟨f,_,rfl⟩ := (memH B).mp hB
    simpa [wordGraph] using hU
  · intro B hB T hs hc
    obtain ⟨f,hf,rfl⟩ := (memH B).mp hB
    have hl := (finite_graph_subset hs).trans hc
    refine ⟨hl,?_⟩
    have hd (x : leftTrace T) : some (x.val,f x.val)∈T := by
      obtain ⟨y,hy⟩ := mem_leftTrace.mp x.prop
      rwa [mem_wordGraph.mp (hs hy)]
    have hu {x y z} (hy : some (x,y)∈T) (hz : some (x,z)∈T) : y=z :=
      (mem_wordGraph.mp (hs hy)).symm.trans (mem_wordGraph.mp (hs hz))
    rw [← trace_values hd hu]
    exact inside f hf _ hl
  · intro T hc ha
    obtain ⟨hl,hr⟩ := ha
    change (leftTrace T).card=3 at hl
    have hle : (leftTrace T).card≤T.eraseNone.card := card_image_le
    have hge := card_eraseNone_le T
    have hfin : T.eraseNone.card=3 := by omega
    have hn : none∉T := by
      intro hm
      rw [card_eraseNone_of_mem hm,hc] at hfin
      contradiction
    have hi : Set.InjOn (Prod.fst : U × V → U) (↑T.eraseNone : Set (U × V)) := card_image_iff.mp (hl.trans hfin.symm)
    have hu {x y z} (hy : some (x,y)∈T) (hz : some (x,z)∈T) : y=z :=
      congrArg Prod.snd (hi (mem_eraseNone.mpr hy) (mem_eraseNone.mpr hz) rfl)
    have hx (x : leftTrace T) := mem_leftTrace.mp x.prop
    choose d hd using hx
    have he (f : U → V) : T⊆wordGraph f ↔ ∀ x : leftTrace T, f x.val=d x := by
      constructor
      · exact fun h x => mem_wordGraph.mp (h (hd x))
      · intro h z hz
        obtain _ | ⟨x,y⟩ := z
        · exact (hn hz).elim
        · let a : leftTrace T := ⟨x,mem_leftTrace.mpr ⟨y,hz⟩⟩
          exact mem_wordGraph.mpr ((h a).trans (hu (hd a) hz))
    obtain ⟨f,⟨hf,heq⟩,uf⟩ := extend _ hl d (by rwa [trace_values hd hu])
    refine ⟨wordGraph f,⟨(memH _).mpr ⟨f,hf,rfl⟩,(he f).mpr heq⟩,?_⟩
    rintro B ⟨hB,hs⟩
    obtain ⟨g,hg,rfl⟩ := (memH B).mp hB
    exact congrArg wordGraph (uf g ⟨hg,(he g).mp hs⟩)

#print axioms word_cover
end
end Erdos722.PointedProduct
