import Erdos478ReflectedReturnRoots
import Erdos478ReturnCapacitySums

/-! # A common degree budget for all selected factorial fibres -/

namespace Erdos478.ReturnConcentration
open Finset WindowAverage
open scoped Classical
noncomputable section

private abbrev edges (p : ℕ) (A : Finset ℕ) := returns (value p) A
private def gap (e : ℕ × ℕ) := e.2-e.1
private def part (p k : ℕ) (A : Finset ℕ) := (edges p A).filter (fun e => gap e = k)

private theorem edge_start {p k : ℕ} {A : Finset ℕ} (dom : A ⊆ Ico 1 p) {e : ℕ × ℕ}
    (he : e ∈ part p k A) : e.1 ∈ startsIn p k A := by
  obtain ⟨hh,eq⟩ := mem_filter.mp he
  obtain ⟨ha,hb,lt,collision⟩ := returns_mem hh
  have lo := (mem_Ico.mp (dom ha)).1
  have up := (mem_Ico.mp (dom hb)).2
  change e.2-e.1=k at eq
  have sum : e.1+k=e.2 := by omega
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_starts.mpr ⟨lo,by omega⟩,
    by rw [Nat.add_zero,sum]; exact (ZMod.natCast_eq_natCast_iff' ..).mp collision⟩,
    ha,sum.symm ▸ hb⟩

private theorem part_le {p k : ℕ} {A : Finset ℕ} (dom : A ⊆ Ico 1 p) :
    (part p k A).card ≤ (startsIn p k A).card := by
  apply card_le_card_of_injOn Prod.fst (fun _ h => edge_start dom h)
  intro x hx y hy he
  have xx := mem_filter.mp hx
  have yy := mem_filter.mp hy
  have gx : x.2-x.1=k := xx.2
  have gy : y.2-y.1=k := yy.2
  have lx := (returns_mem xx.1).2.2.1
  have ly := (returns_mem yy.1).2.2.1
  exact Prod.ext he (by omega)

private theorem no_unit {p : ℕ} (hp : p.Prime) {A : Finset ℕ} (dom : A ⊆ Ico 1 p) :
    part p 1 A = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  have h := (mem_filter.mp (edge_start dom he)).1
  have empty := adjacent_starts_empty (r:=0) (H:=1) hp (by decide)
  rw [empty] at h
  exact notMem_empty _ h

private theorem no_zero (p : ℕ) (A : Finset ℕ) : part p 0 A=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨hh,eq⟩ := mem_filter.mp he
  have lt := (returns_mem hh).2.2.1
  change e.2-e.1=0 at eq
  omega

/-- One artificial gap of length one pays for the exact finite boundary terms. -/
private def augmented (p : ℕ) (A : Finset ℕ) := insert (0,1) (edges p A)

private theorem fresh {p : ℕ} {A : Finset ℕ} (dom : A ⊆ Ico 1 p) : (0,1) ∉ edges p A := by
  intro h
  exact (by decide : ¬(1 ≤ 0)) (mem_Ico.mp (dom (returns_mem h).1)).1

private theorem finite_budget {p : ℕ} (hp : p.Prime) {A : Finset ℕ} (dom : A ⊆ Ico 1 p)
    (c : ℕ → ℕ) (unit : c 1 = 1) (cap : ∀ k, 2 ≤ k → (startsIn p k A).card ≤ c k) (h : ℕ) :
    h*((edges p A).card+1) ≤ totalWidth (value p) A + 1 + ∑ k ∈ range h,(h-k)*c k := by
  have hc (k : ℕ) : ((augmented p A).filter (fun e => gap e = k)).card ≤ c k := by
    rw [augmented,filter_insert]
    change (if gap (0,1) = k then insert (0,1) (part p k A) else part p k A).card ≤ c k
    have one : gap (0,1)=1 := rfl
    rw [one]
    split_ifs with hk
    · subst k
      simp [unit,no_unit hp dom]
    · rcases Nat.eq_zero_or_pos k with rfl | pos
      · simp [no_zero]
      · exact (part_le dom).trans (cap k (by omega))
  have b := cutoff (augmented p A) gap c hc h
  rw [augmented,card_insert_of_notMem (fresh dom),sum_insert (fresh dom)] at b
  change h*((edges p A).card+1) ≤ 1+(∑ e ∈ edges p A,(e.2-e.1)) + _ at b
  simpa only [returns_sum, Nat.add_comm 1] using b

theorem factorial_cubic {p : ℕ} (hp : p.Prime) {A : Finset ℕ} (dom : A ⊆ Ico 1 p) :
    8*(A.card-(A.image (value p)).card+1)^3 ≤ 9*(totalWidth (value p) A+1)^2 := by
  have count := returns_card (value p) A
  have eq : A.card-(A.image (value p)).card = (edges p A).card := by dsimp [edges]; omega
  rw [eq]
  apply unrestricted_cubic
  intro h _
  have b := finite_budget hp dom id rfl (fun k hk => startsIn_card_le hp (by omega) _) h
  change h*((edges p A).card+1) ≤ _ + ∑ k ∈ range h,(h-k)*k at b
  have e := degree_cost h
  nlinarith

theorem separated_factorial_cubic {p : ℕ} (hp : p.Prime) {A : Finset ℕ}
    (dom : A ⊆ Ico 1 p) (hs : separated p A) :
    32*(A.card-(A.image (value p)).card)^3 ≤ 27*(totalWidth (value p) A+1)^2 := by
  have count := returns_card (value p) A
  have eq : A.card-(A.image (value p)).card = (edges p A).card := by dsimp [edges]; omega
  rw [eq]
  apply reflected_cubic
  intro t _
  have cap (k : ℕ) (hk : 2 ≤ k) : (startsIn p k A).card ≤ reflectedCapacity k := by
    unfold reflectedCapacity
    split_ifs with ev
    · have b := twice_startsIn_card_le hp (by omega : 0<k) (Nat.even_iff.mpr ev) hs
      omega
    · exact startsIn_card_le hp (by omega) _
  have b := finite_budget hp dom reflectedCapacity rfl cap (2*t)
  rw [reflected_cost] at b
  omega

#print axioms factorial_cubic
#print axioms separated_factorial_cubic

end
end Erdos478.ReturnConcentration
