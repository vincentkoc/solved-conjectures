import Erdos722QuartetSeeds

/-!
# Relative difference families at orders 45 and 145

Clayton Smith's five-layer construction develops a block from each orbit of
the fourth roots of unity on the nonzero field elements. The fibers of the
second projection supply the short blocks.
-/

namespace Erdos722.Five.Relative
open Erdos722.Quartet

theorem five_layers {A : Type} [AddCommGroup A] [Fintype A] {b : ℕ}
    (f : Fin b → Fin 5 → ZMod 5 × A) (hs : ∀ l, Function.Injective (Prod.snd ∘ f l))
    (hd : ∀ d : ZMod 5 × A, d.2 ≠ 0 →
      ∃! v : Fin b × Fin 5 × Fin 5, f v.1 v.2.1 - f v.1 v.2.2 = d) :
    Has (· = 5) (5*Fintype.card A) := by
  classical
  let col := AddMonoidHom.snd (ZMod 5) A
  let C := Seeds.developmentBetween col f hs hd
  apply (Cover.fillFibers col C _).has (by simp)
  intro q
  let e : ZMod 5 ≃ {x : ZMod 5 × A // col x = q} :=
    ⟨fun i => ⟨(i,q),rfl⟩,fun x => x.val.1,fun _ => rfl,by rintro ⟨⟨i,j⟩,rfl⟩; rfl⟩
  exact (Has.single (s := (· = 5)) rfl).realize ((Fintype.card_congr e.symm).trans (ZMod.card 5))

set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

private def blocks45 : Fin 2 → Fin 5 → ZMod 5 × ZMod 3 × ZMod 3 :=
  ![![(0,0,0),(1,1,0),(1,2,0),(4,0,1),(4,0,2)],
    ![(0,0,0),(1,1,1),(1,2,2),(4,2,1),(4,1,2)]]

theorem order45 : Has (· = 5) 45 := by
  simpa using five_layers blocks45 (by unfold Function.Injective; decide +kernel)
    (by
      rintro ⟨i,x,y⟩ h
      fin_cases i <;> fin_cases x <;> fin_cases y <;>
        first | exact (h rfl).elim | unfold ExistsUnique; decide +kernel)

#print axioms order45

private def blocks145 : Fin 7 → Fin 5 → ZMod 5 × ZMod 29 :=
  ![![(0,0),(1,1),(1,28),(4,12),(4,17)],
    ![(0,0),(1,2),(1,27),(4,24),(4,5)],
    ![(0,0),(1,3),(1,26),(4,7),(4,22)],
    ![(0,0),(1,4),(1,25),(4,19),(4,10)],
    ![(0,0),(1,6),(1,23),(4,14),(4,15)],
    ![(0,0),(1,8),(1,21),(4,9),(4,20)],
    ![(0,0),(1,11),(1,18),(4,16),(4,13)]]

theorem order145 : Has (· = 5) 145 := by
  simpa using five_layers blocks145 (by unfold Function.Injective; decide +kernel)
    (by unfold ExistsUnique; decide +kernel)

#print axioms order145

#print axioms five_layers

end Erdos722.Five.Relative
