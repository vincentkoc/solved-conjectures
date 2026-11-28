import Erdos722QuartetCovers

/-!
# Five-column fillings from orthogonal arrays

Rows of a strength-two array give transversal blocks. The finite certificate
checks that each projection onto two columns covers every ordered pair.
Since there are exactly as many rows as pairs, each occurs once.
-/

namespace Erdos722.Five.Array
open Erdos722.Quartet Finset

private def mask : List ℕ → ℕ
  | [] => 0
  | x::xs => 2^x ||| mask xs

private theorem mask_bit (xs : List ℕ) (i : ℕ) : (mask xs).testBit i = true ↔ i ∈ xs := by
  induction xs with
  | nil => simp [mask]
  | cons x xs ih =>
    simp only [mask,Nat.testBit_or,Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq,ih,List.mem_cons]
    tauto

def codes {t : ℕ} (A : Fin (t*t) → Fin 5 → Fin t) (i j : Fin 5) : ℕ :=
  mask ((List.finRange (t*t)).map fun r => (finProdFinEquiv (A r i,A r j)).val)

private theorem projection {t : ℕ} (A : Fin (t*t) → Fin 5 → Fin t) (i j : Fin 5)
    (h : codes A i j = 2^(t*t)-1) : Function.Bijective (fun r => (A r i,A r j)) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_,by simp⟩
  intro p
  let k := finProdFinEquiv p
  have hit : (codes A i j).testBit k.val = true := by
    rw [h, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true k.isLt
  obtain ⟨r,_,hr⟩ := List.mem_map.mp ((mask_bit _ _).mp hit)
  exact ⟨r,finProdFinEquiv.injective (Fin.ext hr)⟩

private def row {t : ℕ} (A : Fin (t*t) → Fin 5 → Fin t) (r : Fin (t*t)) : Fin 5 ↪ Fin 5 × Fin t :=
  ⟨fun i => (i,A r i),fun _ _ h => congrArg Prod.fst h⟩

private def transversal {t : ℕ} (A : Fin (t*t) → Fin 5 → Fin t)
    (h : ∀ i j, i ≠ j → codes A i j = 2^(t*t)-1) :
    Cover (Fin 5 × Fin t) (fun x y => x.1 ≠ y.1) (· = 5) := by
  let L := fun r => univ.map (row A r)
  have mem (r x) : x ∈ L r ↔ A r x.1 = x.2 := by
    rcases x with ⟨i,a⟩
    simp only [L,mem_map,mem_univ,true_and]
    change (∃ j, (j,A r j)=(i,a)) ↔ _
    simp
  apply Cover.ofLines L (by simp [L]) _ _
  · intro r x hx y hy hxy he
    apply hxy
    exact Prod.ext he (by rw [← (mem r x).mp hx,← (mem r y).mp hy,he])
  · intro x y _ hxy
    have bij := projection A x.1 y.1 (h _ _ hxy)
    obtain ⟨r,hr⟩ := bij.2 (x.2,y.2)
    exact ⟨r,⟨(mem _ _).mpr (congrArg Prod.fst hr),(mem _ _).mpr (congrArg Prod.snd hr)⟩,
      fun s hs => bij.1 ((Prod.ext ((mem _ _).mp hs.1) ((mem _ _).mp hs.2)).trans hr.symm)⟩

/-- Fill each column separately or add the same new point to all five. -/
theorem fill {t a : ℕ} {S : ℕ → Prop} (A : Fin (t*t) → Fin 5 → Fin t)
    (h : ∀ i j, i ≠ j → codes A i j = 2^(t*t)-1) (h5 : S 5) (ha : a≤1)
    (ht : Has S (t+a)) : Has S (5*t+a) := by
  classical
  let C := (transversal A h).change (fun _ _ _ => Iff.rfl) (fun _ he => he ▸ h5)
  let e (i : Fin 5) : Fin t ≃ {x : Fin 5 × Fin t // x.1=i} :=
    ⟨fun y => ⟨(i,y),rfl⟩,fun x => x.val.2,fun _ => rfl,by rintro ⟨⟨j,y⟩,rfl⟩; rfl⟩
  rcases (show a=0 ∨ a=1 by omega) with rfl | rfl
  · apply (Cover.fillFibers Prod.fst C _).has (by simp)
    exact fun i => (ht.realize (Fintype.card_fin t)).relabel (e i)
  · apply (Cover.adjoin Prod.fst C _).has (by simp)
    exact fun i => (ht.realize (V := Option (Fin t)) (by simp)).relabel (Equiv.optionCongr (e i))

#print axioms fill

end Erdos722.Five.Array
