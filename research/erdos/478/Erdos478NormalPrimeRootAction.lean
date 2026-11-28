import Erdos478PrimeDerangements

/-!
# Ordered pairs in normal subgroups of prime-degree root actions

Müller's prime-degree alternative applies in coordinates in which a
prime cycle is translation by one. A normal subgroup containing this
cycle can only be affine if its ambient group is also affine.
-/

namespace Erdos478.PrimeDifferences
open Equiv Function
noncomputable section
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]

private theorem affine_of_normal_translations (τ : G →* Perm (ZMod p))
    (N : Subgroup G) [N.Normal]
    (ht : ∃ s : N, ∀ x : ZMod p, τ s.val x=1+x)
    (ha : ∀ s : N, ∃ a b : ZMod p, ∀ x, τ s.val x=a*x+b) :
    ∀ g : G, ∃ a b : ZMod p, ∀ x, τ g x=a*x+b := by
  intro g
  obtain ⟨s,hs⟩ := ht
  let c : N := ⟨g*s.val*g⁻¹,Subgroup.Normal.conj_mem (inferInstance : N.Normal) _ s.property _⟩
  obtain ⟨a,b,hc⟩ := ha c
  have conj (x : ZMod p) : τ c.val (τ g x) = τ g (1+x) := by
    change τ (g*s.val*g⁻¹) (τ g x) = _
    simp [hs]
  have fixed : ∀ x, τ c.val x ≠ x := by
    intro x
    obtain ⟨y,rfl⟩ := (τ g).surjective x
    rw [conj]
    exact (τ g).injective.ne (by simp)
  have a_one : a=1 := by
    by_contra hne
    apply fixed (b/(1-a))
    rw [hc]
    field_simp [sub_ne_zero.mpr (Ne.symm hne)]
    ring
  have step (x : ZMod p) : τ g (1+x)=τ g x+b := by
    rw [← conj,hc,a_one,one_mul]
  have natStep (k : ℕ) : τ g (k : ZMod p) = b*(k : ZMod p)+τ g 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ,add_comm (k : ZMod p) 1,step,ih]
      ring
  refine ⟨b,τ g 0,fun x => ?_⟩
  simpa using natStep x.val

/-- Over a normal subgroup of order divisible by p, a nonaffine
faithful prime-degree action stays doubly transitive. -/
theorem normal_pair_transitive {Y : Type*} [Fintype Y] [Finite G]
    (ρ : G →* Perm Y) (hi : Injective ρ) (hc : Fintype.card Y=p)
    (N : Subgroup G) [N.Normal] (hd : p∣Nat.card N)
    (hna : ∀ e : ZMod p ≃ Y, ¬∀ g, ∃ a b : ZMod p, ∀ x, e.symm (ρ g (e x))=a*x+b)
    {a b c d : Y} (hab : a≠b) (hcd : c≠d) :
    ∃ g : N, ρ g.val a=c ∧ ρ g.val b=d := by
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' p hd
  have faithful : Injective (ρ.comp N.subtype) := hi.comp Subtype.val_injective
  obtain ⟨e,he⟩ := prime_cycle_coordinates hc (ρ s.val)
    ((orderOf_injective (ρ.comp N.subtype) faithful s).trans hs)
  let τ := e.symm.permCongrHom.toMonoidHom.comp ρ
  have coord (g : G) (x : ZMod p) : τ g x=e.symm (ρ g (e x)) := rfl
  have ht (t : ZMod p) : ∃ g : N, ∀ x, τ g.val x=t+x := by
    refine ⟨s^t.val,fun x => ?_⟩
    rw [coord,Subgroup.coe_pow,map_pow,he,e.symm_apply_apply]
  have exclude : ¬∀ g : N, ∃ u v : ZMod p, ∀ x, τ g.val x=u*x+v :=
    fun ha => hna e (affine_of_normal_translations τ N (ht 1) ha)
  have orbit := (affine_or_pair_transitive (τ.comp N.subtype) ht).resolve_left exclude
  have base (v w : Y) (hvw : v≠w) : ∃ g : N, ρ g.val (e 0)=v ∧ ρ g.val (e 1)=w := by
    obtain ⟨g,hv,hw⟩ := orbit (e.symm v) (e.symm w) (e.symm.injective.ne hvw)
    exact ⟨g,e.symm.injective hv,e.symm.injective hw⟩
  obtain ⟨g,hga,hgb⟩ := base a b hab
  obtain ⟨h,hhc,hhd⟩ := base c d hcd
  exact ⟨h*g⁻¹,by simpa [← hga] using hhc,by simpa [← hgb] using hhd⟩

/-- In a common group, the kernel of any representation with p-free
image order can still move the two chosen roots arbitrarily. Raising a
lift of a prime cycle to the size of the auxiliary group proves that
the image of the kernel still has order divisible by p. -/
theorem kernel_pair_transitive {H B Y : Type*} [Group H] [Finite H]
    [Group B] [Finite B] [Fintype Y] (π : G →* H) (surj : Surjective π) (φ : G →* B)
    (ρ : H →* Perm Y) (hi : Injective ρ) (hc : Fintype.card Y=p)
    (hd : p ∣ Nat.card H) (hB : ¬p ∣ Nat.card B)
    (hna : ∀ e : ZMod p ≃ Y, ¬∀ h, ∃ a b : ZMod p, ∀ x, e.symm (ρ h (e x))=a*x+b)
    {a b c d : Y} (hab : a≠b) (hcd : c≠d) :
    ∃ g : G, φ g=1 ∧ ρ (π g) a=c ∧ ρ (π g) b=d := by
  let N := φ.ker.map π
  let : N.Normal := φ.normal_ker.map π surj
  obtain ⟨s,hs⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨v,hv⟩ := surj s
  let m := Nat.card B
  have member : s^m ∈ N := by
    refine Subgroup.mem_map.mpr ⟨v^m,?_,by rw [map_pow,hv]⟩
    change φ (v^m)=1
    rw [map_pow]
    exact pow_card_eq_one'
  have horder : orderOf (⟨s^m,member⟩ : N) = p := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (s^m)=p
    rw [orderOf_pow,hs,((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hB).gcd_eq_one,Nat.div_one]
  have hdN : p ∣ Nat.card N := horder ▸ orderOf_dvd_natCard (⟨s^m,member⟩ : N)
  obtain ⟨u,hu,hu'⟩ := normal_pair_transitive ρ hi hc N hdN hna hab hcd
  obtain ⟨g,hg,he⟩ := Subgroup.mem_map.mp u.property
  exact ⟨g,hg,he ▸ hu,he ▸ hu'⟩

#print axioms kernel_pair_transitive
#print axioms normal_pair_transitive
end
end Erdos478.PrimeDifferences
