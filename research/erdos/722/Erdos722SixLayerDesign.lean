import Erdos722QuartetCovers

/-!
# Developing starter blocks in several cyclic layers

Translate the second coordinate of every point by the same group element.
A pair is classified by its two layer labels and its oriented difference.
Exactly one representative of each class suffices for a pair design.
-/

namespace Erdos722.Six
open Finset Erdos722.Quartet

theorem layer_design {I A : Type*} [Fintype I] [AddCommGroup A] [Fintype A] {b k : ℕ}
    (f : Fin b → Fin k → I × A) (hinj : ∀ l, Function.Injective (f l))
    (hd : ∀ (u v : I) (d : A), u ≠ v ∨ d ≠ 0 →
      ∃! w : Fin b × Fin k × Fin k, (f w.1 w.2.1).1 = u ∧
        (f w.1 w.2.2).1 = v ∧ (f w.1 w.2.1).2 - (f w.1 w.2.2).2 = d) :
    Has (· = k) (Fintype.card I * Fintype.card A) := by
  classical
  let shift (g : A) (x : I × A) : I × A := (x.1,x.2+g)
  let entry (p : Fin b × A) : Fin k ↪ I × A := ⟨fun i => shift p.2 (f p.1 i),
    fun i j h => by
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      exact hinj _ (Prod.ext h₁ (add_right_cancel (show (f p.1 i).2+p.2=(f p.1 j).2+p.2 from h₂)))⟩
  let L (p : Fin b × A) := univ.map (entry p)
  have mem (p) (x : I × A) : x ∈ L p ↔ ∃ i, shift p.2 (f p.1 i) = x := by
    simp only [L,mem_map,mem_univ,true_and]
    rfl
  apply (Cover.ofLines (R := AllPairs _) L (by simp [L]) (fun _ _ _ _ _ _ => trivial) ?_).has (by simp)
  intro x y hxy _
  have hne : x.1 ≠ y.1 ∨ x.2-y.2 ≠ 0 := by
    by_contra! h
    exact hxy (Prod.ext h.1 (sub_eq_zero.mp h.2))
  obtain ⟨⟨l,i,j⟩,⟨hl,hr,hδ⟩,hu⟩ := hd x.1 y.1 (x.2-y.2) hne
  change (f l i).2-(f l j).2 = x.2-y.2 at hδ
  let g := x.2-(f l i).2
  have hjval : (f l j).2+g = y.2 := calc
    _ = x.2-((f l i).2-(f l j).2) := by dsimp [g]; abel
    _ = y.2 := by rw [hδ]; abel
  refine ⟨(l,g),⟨(mem _ _).mpr ⟨i,Prod.ext hl (by dsimp [shift,g]; abel)⟩,
    (mem _ _).mpr ⟨j,Prod.ext hr hjval⟩⟩,?_⟩
  rintro ⟨l',g'⟩ ⟨hx,hy⟩
  obtain ⟨i',hi⟩ := (mem _ _).mp hx
  obtain ⟨j',hj⟩ := (mem _ _).mp hy
  have ei : (f l' i').2+g'=x.2 := congrArg Prod.snd hi
  have ej : (f l' j').2+g'=y.2 := congrArg Prod.snd hj
  have fi := congrArg Prod.fst hi
  have fj := congrArg Prod.fst hj
  have hw := hu (l',i',j') ⟨fi,fj,(by
    change (f l' i').2-(f l' j').2=x.2-y.2
    rw [← ei,← ej]; abel)⟩
  cases hw
  exact Prod.ext rfl (by change g'=x.2-(f l i).2; rw [← ei]; abel)

#print axioms layer_design

end Erdos722.Six
