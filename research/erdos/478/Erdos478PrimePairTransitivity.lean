import Erdos478PrimeOrbitals
import Erdos478PrimeCycleCoordinates

/-!
# The non-affine case of Burnside's prime-degree theorem

A faithful action of degree p whose group order is divisible by p and does not
divide p(p−1) is doubly transitive. The finite-field argument is due to Müller.
-/

namespace Erdos478.PrimeDifferences
open Equiv
noncomputable section
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] {Y : Type*} [Fintype Y]

theorem two_transitive_of_order (ρ : G →* Perm Y) (hi : Function.Injective ρ)
    (hc : Fintype.card Y=p) (hd : p∣Nat.card G) (hna : ¬Nat.card G∣p*(p-1))
    {a b c d : Y} (hab : a≠b) (hcd : c≠d) : ∃ g : G, ρ g a=c ∧ ρ g b=d := by
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨e,he⟩ := prime_cycle_coordinates hc (ρ s) ((orderOf_injective ρ hi s).trans hs)
  let τ := e.symm.permCongrHom.toMonoidHom.comp ρ
  have hτ (g : G) (x : ZMod p) : τ g x=e.symm (ρ g (e x)) := rfl
  have ht (t : ZMod p) : ∃ g : G, ∀ x, τ g x=t+x := by
    refine ⟨s^t.val,fun x => ?_⟩
    rw [hτ,map_pow,he,e.symm_apply_apply]
  have horb := (affine_or_pair_orbit τ (e.symm.permCongrHom.injective.comp hi) ht).resolve_left hna
  have base (v w : Y) (hvw : v≠w) : ∃ g : G, ρ g (e 0)=v ∧ ρ g (e 1)=w := by
    obtain ⟨g,hv,hw⟩ := horb (e.symm v) (e.symm w) (e.symm.injective.ne hvw)
    exact ⟨g,e.symm.injective hv,e.symm.injective hw⟩
  obtain ⟨g,hga,hgb⟩ := base a b hab
  obtain ⟨h,hhc,hhd⟩ := base c d hcd
  exact ⟨h*g⁻¹,by simpa [← hga] using hhc,by simpa [← hgb] using hhd⟩

#print axioms two_transitive_of_order
end
end Erdos478.PrimeDifferences
