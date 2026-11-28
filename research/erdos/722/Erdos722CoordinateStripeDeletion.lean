import Erdos722RectangleCovers
import Mathlib.Tactic

/-!
# Removing two classes of pointed coordinate lines

Every triple with a constant finite projection belongs to a row or
column through infinity. Uniqueness in the original design permits
deletion of precisely those blocks.
-/

namespace Erdos722.PointedProduct
open Finset
open scoped Classical
noncomputable section

variable {U V A : Type*} [Fintype U] [Fintype V]

def stripe (f : U × V → A) (a : A) : Finset (Grid U V) :=
  univ.filter (fun z => match z with
    | none => True
    | some p => f p=a)

theorem none_mem_stripe (f : U × V → A) (a : A) : none∈stripe f a := by simp [stripe]
theorem some_mem_stripe {f : U × V → A} {p : U × V} {a : A} : some p∈stripe f a ↔ f p=a := by
  simp [stripe]

private theorem contained_stripe [DecidableEq A] {T : Finset (Grid U V)} {f : U × V → A} {a : A} :
    T⊆stripe f a ↔ T.eraseNone.image f⊆{a} := by
  constructor
  · intro h y hy
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hy
    exact mem_singleton.mpr (some_mem_stripe.mp (h (mem_eraseNone.mp hp)))
  · intro h z hz
    cases z with
    | none => exact none_mem_stripe ..
    | some p => exact some_mem_stripe.mpr (mem_singleton.mp (h (mem_image_of_mem f (mem_eraseNone.mpr hz))))

variable [DecidableEq U] [DecidableEq V] [Nonempty U] [Nonempty V]

def stripe_deletion {q : ℕ} (H : Finset (Finset (Grid U V))) (design : H.IsBlockDesign 3 (q+1))
    (rows : ∀ x : U, stripe Prod.fst x∈H) (cols : ∀ y : V, stripe Prod.snd y∈H) :
    RectangleCover q .line .line U V := by
  classical
  let keep (B : Finset (Grid U V)) := (∀ x : U, B≠stripe Prod.fst x) ∧ (∀ y : V, B≠stripe Prod.snd y)
  have eligible {T : Finset (Grid U V)} : localEvent .line .line T ↔
      (∀ x : U, ¬T⊆stripe Prod.fst x) ∧ (∀ y : V, ¬T⊆stripe Prod.snd y) := by
    simp only [localEvent,Shape.accepts,leftTrace,rightTrace,contained_stripe,← not_exists,
      ← card_le_one_iff_subset_singleton]
    omega
  refine ⟨H.filter keep,fun B hB => design.1 B (mem_filter.mp hB).1,?_,?_⟩
  · intro B hB T hs hc
    obtain ⟨hb,hkeep⟩ := mem_filter.mp hB
    apply eligible.mpr
    exact ⟨fun x hx => hkeep.1 x ((design.2 T hc).unique ⟨hb,hs⟩ ⟨rows x,hx⟩),
      fun y hy => hkeep.2 y ((design.2 T hc).unique ⟨hb,hs⟩ ⟨cols y,hy⟩)⟩
  · intro T hc ha
    obtain ⟨B,⟨hb,hs⟩,hu⟩ := design.2 T hc
    obtain ⟨hr,hc'⟩ := eligible.mp ha
    exact ⟨B,⟨mem_filter.mpr ⟨hb,fun x h => hr x (h ▸ hs),fun y h => hc' y (h ▸ hs)⟩,hs⟩,
      fun D hD => hu D ⟨(mem_filter.mp hD.1).1,hD.2⟩⟩

#print axioms stripe_deletion
end
end Erdos722.PointedProduct
