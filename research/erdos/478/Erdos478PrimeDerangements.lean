import Erdos478PrimePairTransitivity

/-!
# A derangement criterion for prime-degree double transitivity

In the affine group of a prime field every fixed-point-free element
is a translation. Its p-th power is the identity. A derangement that
fails this power test rules out the affine case of Burnside's theorem.
-/

namespace Erdos478.PrimeDifferences
open Equiv Function
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private theorem affine_derangement_pow (g : Perm (ZMod p)) (hf : ∀ x, g x≠x)
    (ha : ∃ a b : ZMod p, ∀ x, g x=a*x+b) : g^p=1 := by
  obtain ⟨a,b,h⟩ := ha
  have ha : a=1 := by
    by_contra hn
    apply hf (b/(1-a))
    rw [h]
    field_simp [sub_ne_zero.mpr (Ne.symm hn)]
    ring
  subst a
  have step (x : ZMod p) : g x=x+b := by simp [h]
  have iterate (n : ℕ) (x : ZMod p) : (g^n) x=x+(n : ZMod p)*b := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',Perm.mul_apply,step,ih,Nat.cast_succ]; ring
  apply Equiv.ext
  intro x
  simp [iterate]

/-- A faithful prime-degree action containing a derangement whose
p-th power is nonidentity has just one orbit on distinct ordered pairs. -/
theorem two_transitive_of_derangement {G Y : Type*} [Group G] [Finite G] [Fintype Y]
    (ρ : G →* Perm Y) (hi : Injective ρ) (hc : Fintype.card Y=p) (hd : p∣Nat.card G)
    {σ : G} (hf : ∀ x, ρ σ x≠x) (hp : σ^p≠1)
    {a b c d : Y} (hab : a≠b) (hcd : c≠d) : ∃ g : G, ρ g a=c ∧ ρ g b=d := by
  apply two_transitive_of_nonaffine ρ hi hc hd _ hab hcd
  intro e ha
  let τ := e.symm.permCongrHom.toMonoidHom.comp ρ
  have ht : Injective τ := e.symm.permCongrHom.injective.comp hi
  apply hp
  apply ht
  rw [map_pow,map_one]
  apply affine_derangement_pow _ _ (ha σ)
  intro x hx
  exact hf (e x) (e.symm.injective (hx.trans (e.symm_apply_apply x).symm))

#print axioms two_transitive_of_derangement
end
end Erdos478.PrimeDifferences
