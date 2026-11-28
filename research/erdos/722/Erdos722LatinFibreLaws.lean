import Erdos722LatinCubeCount

/-! # Latin cube graphs as four-coordinate completion laws -/

namespace Erdos722.LatinFillings
open Equiv Finset Function
open scoped Classical
noncomputable section

/-- The graph distinguishes the output position, while the completion law treats all four equally. -/
def graph (q : Quasigroup) (x : Symbol → Symbol) : Prop := q.val (x 0) (x 1) (x 2)=x 3

theorem graph_recovers {p q : Quasigroup} (same : ∀ x, graph p x ↔ graph q x) : p=q := by
  apply Subtype.ext
  funext a b c
  let x : Symbol → Symbol := ![a,b,c,p.val a b c]
  exact ((same x).mp (show graph p x from rfl)).symm

theorem graph_complete (q : Quasigroup) (i : Symbol) (x : Symbol → Symbol) :
    ∃! y, graph q (update x i y) := by
  have solve (f : Symbol → Symbol) (hf : Injective f) (z : Symbol) : ∃! y, f y=z := by
    obtain ⟨y,hy⟩ := Finite.surjective_of_injective hf z
    exact ⟨y,hy,fun t ht => hf (ht.trans hy.symm)⟩
  fin_cases i
  · simpa [graph,update,Fin.isValue] using solve _ (q.prop.1 (x 1) (x 2)) (x 3)
  · simpa [graph,update,Fin.isValue] using solve _ (q.prop.2.1 (x 0) (x 2)) (x 3)
  · simpa [graph,update,Fin.isValue] using solve _ (q.prop.2.2 (x 0) (x 1)) (x 3)
  · exact ⟨q.val (x 0) (x 1) (x 2),by simp [graph,update],fun y hy => by simpa [graph,update] using hy.symm⟩

/-- Independent symbol permutations relabel a local transversal code. -/
def relabel (q : Quasigroup) (f : Symbol → Perm Symbol) : Quasigroup :=
  ⟨fun a b c => f 3 (q.val ((f 0).symm a) ((f 1).symm b) ((f 2).symm c)),
   fun _ _ => (f 3).injective.comp ((q.prop.1 ..).comp (f 0).symm.injective),
   fun _ _ => (f 3).injective.comp ((q.prop.2.1 ..).comp (f 1).symm.injective),
   fun _ _ => (f 3).injective.comp ((q.prop.2.2 ..).comp (f 2).symm.injective)⟩

theorem graph_relabel (q : Quasigroup) (f : Symbol → Perm Symbol) (x : Symbol → Symbol) :
    graph (relabel q f) (fun i => f i (x i)) ↔ graph q x := by
  simp [graph,relabel]

/-- A predicate on assignments to base points, determined by its values on one block. -/
structure BlockLaw {I : Type*} (B : Finset I) (F : Type*) [DecidableEq I] where
  accepts : (I → F) → Prop
  localize {f g} : (∀ i ∈ B, f i=g i) → accepts f → accepts g
  complete (i) : i ∈ B → ∀ f, ∃! y, accepts (update f i y)

variable {I F : Type*} [DecidableEq I] {B : Finset I}

def cubeLaw (e : Symbol ≃ B) (s : F ≃ Symbol) (q : Quasigroup) : BlockLaw B F where
  accepts f := graph q fun k => s (f (e k).val)
  localize {f g} same h := by
    have eq : (fun k => s (f (e k).val))=(fun k => s (g (e k).val)) :=
      funext fun k => congrArg s (same _ (e k).prop)
    rwa [← eq]
  complete i hi f := by
    let j := e.symm ⟨i,hi⟩
    let v (k) := s (f (e k).val)
    have upd (y : F) : (fun k => s (update f i y (e k).val))=update v j (s y) := by
      funext k
      by_cases h : k=j
      · subst k
        have h0 : (e j).val=i := congrArg Subtype.val (e.apply_symm_apply ⟨i,hi⟩)
        rw [h0,update_self,update_self]
      · have ne : (e k).val≠i := fun eq => h (e.eq_symm_apply.mpr (Subtype.ext eq))
        rw [update_of_ne ne,update_of_ne h]
    obtain ⟨z,hz,uniq⟩ := graph_complete q j v
    refine ⟨s.symm z,?_,?_⟩
    · change graph q (fun k => s (update f i (s.symm z) (e k).val))
      rwa [upd,s.apply_symm_apply]
    · intro y hy
      rw [upd] at hy
      exact s.eq_symm_apply.mpr (uniq (s y) hy)

theorem realize_symbols (e : Symbol ≃ B) (s : F ≃ Symbol) (x : Symbol → Symbol) :
    ∃ f : I → F, ∀ k, s (f (e k).val)=x k := by
  let f (i : I) := if hi : i∈B then s.symm (x (e.symm ⟨i,hi⟩)) else s.symm 0
  exact ⟨f,fun k => by simp [f,(e k).prop]⟩

theorem cubeLaw_recovers (e : Symbol ≃ B) (s : F ≃ Symbol) {p q : Quasigroup}
    (same : ∀ f, (cubeLaw e s p).accepts f ↔ (cubeLaw e s q).accepts f) : p=q := by
  apply graph_recovers
  intro x
  obtain ⟨f,h⟩ := realize_symbols e s x
  have eq := funext h
  change graph p x ↔ graph q x
  rw [← eq]
  exact same f

#print axioms graph
#print axioms graph_recovers
#print axioms graph_complete
#print axioms relabel
#print axioms graph_relabel
#print axioms BlockLaw
#print axioms cubeLaw
#print axioms realize_symbols
#print axioms cubeLaw_recovers
end
end Erdos722.LatinFillings
