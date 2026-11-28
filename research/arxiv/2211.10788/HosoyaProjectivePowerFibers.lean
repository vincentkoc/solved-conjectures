import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic

/-! Counts of power-map fibers in the cyclic groups of the Hosoya index forms. -/

namespace Arxiv.«2211.10788»

open scoped Classical

/-- The number of dth roots of an element of a finite cyclic group. -/
theorem cyclic_power_fiber_card {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    (d : ℕ) (t : G) :
    Nat.card {u : G // u^d=t} =
      if t^(Nat.card G / (Nat.card G).gcd d)=1 then (Nat.card G).gcd d else 0 := by
  classical
  let N := Nat.card G
  let g := N.gcd d
  let e := N/g
  let f : G →* G := powMonoidHom d
  have hg : g ∣ N := Nat.gcd_dvd_left ..
  have hd : g ∣ d := Nat.gcd_dvd_right ..
  have hN : e*g=N := Nat.div_mul_cancel hg
  have he : e ∣ N := ⟨g,hN.symm⟩
  have hr : f.range=(powMonoidHom e : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x,rfl⟩
      change (x^d)^e=1
      obtain ⟨k,hk⟩ := hd
      rw [← pow_mul, show d*e=N*k by rw [hk,←hN]; ring, pow_mul, pow_card_eq_one', one_pow]
    · simp only [f,IsCyclic.card_powMonoidHom_ker,IsCyclic.card_powMonoidHom_range]
      exact (Nat.gcd_eq_right he).le
  change Nat.card {u : G // u^d=t} = if t^e=1 then g else 0
  split_ifs with h
  · obtain ⟨u,hu⟩ : t ∈ f.range := hr ▸ h
    change f u=t at hu
    subst t
    exact (Nat.card_congr (f.fiberEquivKer u)).trans (IsCyclic.card_powMonoidHom_ker G d)
  · have : IsEmpty {u : G // u^d=t} := ⟨fun ⟨u,hu⟩ => h (show t ∈ (powMonoidHom e : G →* G).ker from
        hr ▸ (show t ∈ f.range from ⟨u,hu⟩))⟩
    exact Nat.card_of_isEmpty

#print axioms cyclic_power_fiber_card

end Arxiv.«2211.10788»
