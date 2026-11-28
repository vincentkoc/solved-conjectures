import Erdos722QuartetCovers
import Erdos722HermitianUnitals

/-!
# Small seeds for the four-point spectrum

Developed difference families give the orders 13, 25 and 37. The remaining
seeds are the affine plane of order four and the Hermitian unital of order three.
-/

namespace Erdos722.Quartet
open Finset

namespace Seeds

variable {G : Type*} [AddCommGroup G] {b k : ℕ}

private def translate (f : Fin b → Fin k → G) (hf : ∀ k, Function.Injective (f k))
    (p : Fin b × G) : Fin k ↪ G :=
  ⟨fun i => f p.1 i+p.2,fun _ _ h => hf _ (add_right_cancel h)⟩

/-- Develop a relative difference family. Pairs in a common fiber are left
for a separate group design. -/
noncomputable def developmentBetween {Q : Type*} [AddCommGroup Q] (col : G →+ Q)
    (f : Fin b → Fin k → G) (hs : ∀ l, Function.Injective (col ∘ f l))
    (hd : ∀ d : G, col d ≠ 0 → ∃! v : Fin b × Fin k × Fin k, f v.1 v.2.1 - f v.1 v.2.2 = d) :
    Cover G (fun x y => col x ≠ col y) (· = k) := by
  classical
  have hf (l) : Function.Injective (f l) := fun _ _ h => hs l (congrArg col h)
  let L := fun p => univ.map (translate f hf p)
  have mem (p : Fin b × G) (x : G) : x ∈ L p ↔ ∃ i, f p.1 i + p.2 = x := by
    simp only [L,mem_map,mem_univ,true_and]
    rfl
  apply Cover.ofLines L (by simp [L]) _ _
  · intro p x hx y hy hxy he
    obtain ⟨i,rfl⟩ := (mem p x).mp hx
    obtain ⟨j,rfl⟩ := (mem p y).mp hy
    rw [map_add,map_add] at he
    exact hxy (congrArg (fun u => f p.1 u+p.2) (hs _ (add_right_cancel he)))
  intro x y _ hcol
  obtain ⟨⟨k,i,j⟩,hv,hu⟩ := hd (x-y) (by rw [map_sub]; exact sub_ne_zero.mpr hcol)
  change f k i - f k j = x-y at hv
  refine ⟨(k,x-f k i),⟨(mem _ _).mpr ⟨i,by simp⟩,(mem _ _).mpr ⟨j,by dsimp; abel_nf at hv ⊢; grind⟩⟩,?_⟩
  rintro ⟨l,g⟩ ⟨hx,hy⟩
  obtain ⟨i',hi⟩ := (mem _ _).mp hx
  obtain ⟨j',hj⟩ := (mem _ _).mp hy
  have hu' := hu (l,i',j') (by change f l i' - f l j' = x-y; rw [← hi,← hj]; abel)
  cases hu'
  congr 1
  change f k i+g=x at hi
  rw [← hi]
  abel

/-- Develop all translates of uniform base blocks whose oriented differences
partition the nonzero group elements. -/
theorem development [Fintype G] (f : Fin b → Fin k → G) (hf : ∀ k, Function.Injective (f k))
    (hd : ∀ d : G, d ≠ 0 → ∃! v : Fin b × Fin k × Fin k, f v.1 v.2.1 - f v.1 v.2.2 = d) :
    Has (· = k) (Fintype.card G) := by
  let C := developmentBetween (AddMonoidHom.id G) f hf hd
  exact (C.change (fun _ _ hxy => ⟨fun _ => trivial,fun _ => hxy⟩) (fun _ => id)).has rfl

private def base13 : Fin 1 → Fin 4 → ZMod 13 := ![![0,1,3,9]]
private def base25 : Fin 2 → Fin 4 → ZMod 5 × ZMod 5 :=
  ![![(0,0),(0,1),(1,2),(3,0)],![(0,0),(0,2),(1,0),(2,4)]]
private def base37 : Fin 3 → Fin 4 → ZMod 37 :=
  ![![0,1,3,24],![0,4,9,15],![0,7,17,25]]

set_option maxRecDepth 8192
set_option maxHeartbeats 3200000

theorem thirteen : Has (· = 4) 13 := by
  exact (ZMod.card 13) ▸
    development base13 (by unfold Function.Injective; decide) (by unfold ExistsUnique; decide)

theorem twenty_five : Has (· = 4) 25 := by
  exact (show Fintype.card (ZMod 5 × ZMod 5) = 25 by simp) ▸
    development base25 (by unfold Function.Injective; decide) (by unfold ExistsUnique; decide)

theorem thirty_seven : Has (· = 4) 37 := by
  exact (ZMod.card 37) ▸
    development base37 (by unfold Function.Injective; decide) (by unfold ExistsUnique; decide)

theorem sixteen : Has (· = 4) 16 := by
  obtain ⟨D,hD⟩ := Denniston.exists_denniston_design 2 2 (by decide) (by decide)
  exact ⟨Cover.ofDesign hD⟩

theorem twenty_eight : Has (· = 4) 28 := by
  obtain ⟨D,hD⟩ := HermitianUnital.prime_power_unital 3 1 (by decide)
  exact ⟨Cover.ofDesign hD⟩

#print axioms developmentBetween
#print axioms thirteen
#print axioms twenty_five
#print axioms thirty_seven

end Seeds
end Erdos722.Quartet
