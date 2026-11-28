import Erdos478PrimeStepPermutations
import Erdos478PrimeAffineOrder

/-! # A group containing the prime-field translations -/

namespace Erdos478.PrimeDifferences
open Equiv Finset
noncomputable section
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- The orbit of an ordered pair defines an invariant set of differences. -/
theorem affine_or_pair_orbit (ρ : G →* Perm (ZMod p)) (hinj : Function.Injective ρ)
    (ht : ∀ t : ZMod p, ∃ g : G, ∀ x, ρ g x=t+x) :
    Nat.card G∣p*(p-1) ∨ ∀ x y : ZMod p, x≠y → ∃ g : G, ρ g 0=x ∧ ρ g 1=y := by
  classical
  let R (x y : ZMod p) := ∃ g : G, ρ g 0=x ∧ ρ g 1=y
  have mapR (g : G) {x y : ZMod p} : R x y → R (ρ g x) (ρ g y) := by
    rintro ⟨h,rfl,rfl⟩
    exact ⟨g*h,by simp,by simp⟩
  have invariant (g : G) (x y : ZMod p) : R (ρ g x) (ρ g y) ↔ R x y :=
    ⟨fun h => by simpa using mapR g⁻¹ h,mapR g⟩
  have centered (x y : ZMod p) : R 0 (y-x) ↔ R x y := by
    obtain ⟨g,hg⟩ := ht (-x)
    simpa only [hg,neg_add_cancel,sub_eq_neg_add] using invariant g x y
  let S := univ.filter (R 0)
  have hS (u : ZMod p) : u∈S ↔ R 0 u := by simp [S]
  have hSn : S.Nonempty := ⟨1,(hS _).mpr ⟨1,by simp,by simp⟩⟩
  have hS₀ : 0∉S := by
    intro h
    obtain ⟨g,h₀,h₁⟩ := (hS _).mp h
    exact zero_ne_one ((ρ g).injective (h₀.trans h₁.symm))
  have keep (g : G) (x u : ZMod p) : ρ g (x+u)-ρ g x∈S ↔ u∈S := by
    rw [hS,centered,invariant,← centered,hS,add_sub_cancel_left]
  let T := (univ.erase 0) \ S
  have hT (u : ZMod p) : u∈T ↔ u≠0 ∧ u∉S := by simp [T]
  by_cases hTn : T.Nonempty
  · left
    apply card_dvd_of_affine ρ hinj
    have hs : S⊆univ.erase 0 := fun u hu => mem_erase.mpr ⟨fun he => hS₀ (he ▸ hu),mem_univ _⟩
    have size : T.card+S.card=p-1 := by
      calc
        _ = (univ.erase (0 : ZMod p)).card := card_sdiff_add_card_eq_card hs
        _ = _ := by simp [card_erase_of_mem]
    intro g
    by_cases hh : 2*S.card<p
    · exact affine_of_step_preserving hSn hS₀ hh (ρ g) (fun x u hu => (keep g x u).mpr hu)
    · have hp := (Fact.out : p.Prime).pos
      have htcard : 2*T.card<p := by omega
      apply affine_of_step_preserving hTn (by simp [hT]) htcard (ρ g)
      intro x u hu
      obtain ⟨hu₀,huS⟩ := (hT _).mp hu
      apply (hT _).mpr
      refine ⟨?_,fun h => huS ((keep g x u).mp h)⟩
      simpa only [ne_eq,sub_eq_zero,Equiv.apply_eq_iff_eq,add_eq_left] using hu₀
  · right
    intro x y hxy
    apply (centered x y).mp
    apply (hS _).mp
    by_contra hu
    exact hTn ⟨y-x,(hT _).mpr ⟨sub_ne_zero.mpr hxy.symm,hu⟩⟩

#print axioms affine_or_pair_orbit
end
end Erdos478.PrimeDifferences
