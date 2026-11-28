import Erdos722NonlinearLatinCubes

/-! # Detecting affine transversal blocks directly in the completion rule -/

namespace Erdos722.AffineStar
open Finset QuadCompletion FourPoint QuadSwitch LatinFillings Equiv
open scoped Classical
noncomputable section

/-- Ternary closure of a family of sections of the four-point fibres. -/
def Closed {I : Type*} (L : (I → Fibre) → Prop) : Prop :=
  ∀ f g h, L f → L g → L h → L (fun i => f i+g i+h i)

theorem closed_congr {I : Type*} {L K : (I → Fibre) → Prop}
    (eq : ∀ f, L f ↔ K f) : Closed L ↔ Closed K := by
  rw [show L=K from funext fun f => propext (eq f)]

theorem graph_affine_iff (q : Quasigroup) :
    (∀ a b c : Symbol → Symbol, graph q a → graph q b → graph q c →
      graph q (fun j => mix (a j) (b j) (c j))) ↔ AffineCube q := by
  constructor
  · intro H x y z
    let row (v : Inputs) : Symbol → Symbol := ![v 0,v 1,v 2,evaluate q v]
    exact H (row x) (row y) (row z) rfl rfl rfl
  · intro H a b c ha hb hc
    let cut (s : Symbol → Symbol) : Inputs := ![s 0,s 1,s 2]
    exact (H (cut a) (cut b) (cut c)).trans (congrArg₂ (fun a b => mix a b _) ha hb |>.trans
      (congrArg (mix (a 3) (b 3)) hc))

variable {I : Type*} [DecidableEq I]

/-- The four-coordinate graph is affine exactly when the predicate on full sections is closed. -/
theorem cubeLaw_closed_iff {B : Finset I} (e : Symbol ≃ B) (q : Quasigroup) :
    Closed (cubeLaw e symbols q).accepts ↔ AffineCube q := by
  rw [← graph_affine_iff]
  let read (f : I → Fibre) (j : Symbol) := symbols (f (e j).val)
  have adds (f g h : I → Fibre) : read (fun i => f i+g i+h i)=
      (fun j => mix (read f j) (read g j) (read h j)) := funext fun _ => (mix_symbols ..).symm
  change Closed (fun f => graph q (read f)) ↔ _
  constructor
  · intro H a b c ha hb hc
    obtain ⟨f,hf⟩ := realize_symbols e symbols a
    obtain ⟨g,hg⟩ := realize_symbols e symbols b
    obtain ⟨h,hh⟩ := realize_symbols e symbols c
    have ea : read f=a := funext hf
    have eb : read g=b := funext hg
    have ec : read h=c := funext hh
    have out := H f g h (show graph q (read f) by rwa [ea]) (show graph q (read g) by rwa [eb])
      (show graph q (read h) by rwa [ec])
    change graph q (read (fun i => f i+g i+h i)) at out
    rwa [adds,ea,eb,ec] at out
  · intro H f g h hf hg hh
    rw [adds]
    exact H _ _ _ hf hg hh

def OnGraph (Q : Rule I) (R : Rule (I × Fibre)) (i j k : I) (f : I → Fibre) : Prop :=
  R.complete (i,f i) (j,f j) (k,f k)=(Q.complete i j k,f (Q.complete i j k))

/-- Every transversal quadruple through the specified base point has an affine graph. -/
def HasAffineStar (Q : Rule I) (R : Rule (I × Fibre)) (o : I) : Prop :=
  ∀ i j k, i≠j → i≠k → j≠k → o ∈ baseQuad Q i j k → Closed (OnGraph Q R i j k)

theorem patch_closed_iff (Q : Rule I) (P : Rule (I × Fibre)) {S : Finset (Finset I)}
    (L : Laws S Fibre) (sizes : ∀ B∈S,B.card=4)
    (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    {i j k : I} (m : baseQuad Q i j k ∈ S) :
    Closed (OnGraph Q (patch Q P L sizes proj) i j k) ↔ Closed (L ⟨_,m⟩).accepts :=
  closed_congr (patch_graph Q P L sizes proj i j k m)

#print axioms Closed
#print axioms closed_congr
#print axioms graph_affine_iff
#print axioms cubeLaw_closed_iff
#print axioms OnGraph
#print axioms HasAffineStar
#print axioms patch_closed_iff
end
end Erdos722.AffineStar
