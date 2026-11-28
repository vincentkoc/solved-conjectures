import CunninghamPrimeDirichletMass

/-! Normalized logarithmic prime mass of a set of reduced residue classes. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Finset Filter Topology CunninghamChain.PrimeMass

/-- Naturals represented by a finite collection of reduced residues. -/
def represented {M : ℕ} (S : Finset (ZMod M)ˣ) : Set ℕ :=
  {n | ∃ u ∈ S, (n : ZMod M) = (u : ZMod M)}

private theorem mass_union {A B : Set ℕ} (hd : Disjoint A B) {x : ℝ} (hx : 1<x) :
    mass (A ∪ B) x = mass A x + mass B x := by
  rw [mass,mass,mass,←(summable_weight A hx).tsum_add (summable_weight B hx)]
  apply tsum_congr
  intro n
  rw [←add_div]
  congr 1
  have sep : n∈A → n∉B := fun hn => Set.disjoint_left.mp hd hn
  by_cases ha : n∈A <;> by_cases hb : n∈B <;> by_cases hp : n.Prime <;> simp_all [weight]

/-- The prime mass of a union of reduced classes is its fraction of all units. -/
theorem mass_represented {M : ℕ} [NeZero M] (S : Finset (ZMod M)ˣ) :
    Tendsto (fun x : ℝ => (x-1)*mass (represented S) x) (𝓝[>] 1)
      (𝓝 ((S.card:ℝ) / M.totient)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [represented,mass,weight]
  | @insert u S hu ih =>
    let A : Set ℕ := {n | (n:ZMod M)=(u:ZMod M)}
    have he : represented (insert u S) = A ∪ represented S := by
      ext n
      simp [represented,A]
    have hd : Disjoint A (represented S) := by
      apply Set.disjoint_left.mpr
      rintro n (hn : (n:ZMod M)=(u:ZMod M)) ⟨v,hv,hnv⟩
      exact hu ((Units.ext (hnv.symm.trans hn)) ▸ hv)
    have lim := (mass_progression (u:ZMod M) u.isUnit).add ih
    rw [card_insert_of_notMem hu,Nat.cast_add_one,add_div,one_div,add_comm,he]
    apply lim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [mass_union hd hx,mul_add]

#print axioms mass_represented

end Arxiv.«2211.10788».PrimeObstruction
