import Erdos722SwitchIsomorphismLaw
import Erdos722TwistedSwitchCounts
import Mathlib.Data.Fintype.Perm

/-! # Counting switches whose double has an automorphism moving its point fibres -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}

def exceptional (hH : H.IsBlockDesign 3 4) :=
  (univ : Finset (H → Bool)).filter fun s =>
    ∃ e : Perm (V × Bool), e.finsetCongr.finsetCongr (doubling hH s)=doubling hH s ∧
      ¬∃ f, e=fibrePerm (Equiv.refl V) f

/-- Every symmetry of a nonexceptional double is a vertical flip by a parity check. -/
theorem nonexceptional_automorphisms (hH : H.IsBlockDesign 3 4) (s : H → Bool) (hs : s∉exceptional hH)
    (e : Perm (V × Bool)) : e.finsetCongr.finsetCongr (doubling hH s)=doubling hH s ↔
      ∃ f, e=fibrePerm (Equiv.refl V) f ∧ Check H (bitValue ∘ f) := by
  constructor
  · intro he
    obtain ⟨f,rfl⟩ : ∃ f, e=fibrePerm (Equiv.refl V) f := by
      by_contra hn
      exact hs (mem_filter.mpr ⟨mem_univ _,e,he,hn⟩)
    exact ⟨f,rfl,(vertical_iff_check hH s f).mp he⟩
  · rintro ⟨f,rfl,hf⟩
    exact (vertical_iff_check hH s f).mpr hf

def gaugeAssignments (H : Finset (Finset V)) :=
  (univ : Finset (V → ZMod 2)).image fun u (i : H) => decide (blockSum u i.val=1)

theorem gauge_mem {s : H → Bool} (hs : Coboundary s) : s∈gaugeAssignments H := by
  obtain ⟨u,hu⟩ := hs
  exact mem_image.mpr ⟨u,mem_univ _,funext fun i => by
    rw [hu i]; exact (show ∀ b : Bool, decide (bitValue b=1)=b by decide) _⟩

theorem gauge_card_le : (gaugeAssignments H).card≤2^Fintype.card V := by
  simpa [gaugeAssignments] using (card_image_le (s:=(univ : Finset (V → ZMod 2)))
    (f:=fun u (i : H) => decide (blockSum u i.val=1)))

def movingSolutions (H : Finset (Finset V)) (p : Perm V × (V → Bool)) : Finset (H → Bool) :=
  if h : p.1.finsetCongr.finsetCongr H=H ∧ p.1≠Equiv.refl V then
    solutions (blockPerm p.1 h.1) (fun i => blockSum (bitValue ∘ p.2) i.val)
  else ∅

/-- A uniform lower bound on moved block pairs saves one binary choice per pair. -/
theorem exceptional_bound [Nonempty V] (hH : H.IsBlockDesign 3 4) (sep : Separates H) (q : ℕ)
    (motion : ∀ (σ : Perm V) (hp : σ.finsetCongr.finsetCongr H=H), σ≠Equiv.refl V →
      2*q≤(blockPerm σ hp).support.card) :
    (exceptional hH).card≤2^Fintype.card V +
      (Fintype.card V).factorial*2^Fintype.card V*2^(H.card-q) := by
  classical
  let P := Perm V × (V → Bool)
  have cover : exceptional hH ⊆ gaugeAssignments H ∪ univ.biUnion (movingSolutions H) := by
    intro s hs
    by_cases cg : Coboundary s
    · exact mem_union_left _ (gauge_mem cg)
    obtain ⟨e,he,hn⟩ := (mem_filter.mp hs).2
    obtain ⟨σ,f,rfl⟩ := intrinsic_isomorphism hH sep cg e he
    have rel := (maps_doubling_iff hH s s σ f).mp he
    have hp := matches_preserves rel
    have ne : σ≠Equiv.refl V := by rintro rfl; exact hn ⟨f,rfl⟩
    apply mem_union_right _ (mem_biUnion.mpr ⟨(σ,f),mem_univ _,?_⟩)
    simpa [movingSolutions,hp,ne,solutions] using (matches_iff_equations s s σ f hp).mp rel
  have limit (p : P) (_ : p∈univ) : (movingSolutions H p).card≤2^(H.card-q) := by
    unfold movingSolutions
    split
    · rename_i h
      apply (solutions_cycles ..).trans
      apply Nat.pow_le_pow_right (by decide)
      have m := motion p.1 h.1 h.2
      have budget := cycle_budget (blockPerm p.1 h.1)
      rw [Fintype.card_coe] at budget
      omega
    · simp
  refine (card_le_card cover).trans ((card_union_le ..).trans (Nat.add_le_add gauge_card_le ?_))
  simpa [P,Fintype.card_perm] using card_biUnion_le_card_mul univ (movingSolutions H) _ limit

#print axioms exceptional
#print axioms nonexceptional_automorphisms
#print axioms gaugeAssignments
#print axioms gauge_mem
#print axioms gauge_card_le
#print axioms movingSolutions
#print axioms exceptional_bound
end
end Erdos722.QuadSwitch
