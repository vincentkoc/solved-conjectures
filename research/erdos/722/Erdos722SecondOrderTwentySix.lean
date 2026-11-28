import Erdos722OrdinaryOrderSeparation

/-!
# The second ordinary order at block size five

The cyclic Steiner system on 26 points was studied by Grannell, Griggs
and Phelan. The ten translation starters below were obtained by an exact
cover of triple orbits, using the multiplier 7. A finite difference test
at the origin verifies every triple of points in their development.
-/

namespace Erdos722.SecondOrder
open Finset

private def translate {n : ℕ} (t : Fin n) (B : Finset (Fin n)) : Finset (Fin n) :=
  B.image (t+·)

private theorem mem_translate {n : ℕ} [NeZero n] {x t : Fin n} {B : Finset (Fin n)} :
    x∈translate t B ↔ x-t∈B := by
  constructor
  · rintro h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    simpa using hj
  · intro h
    exact mem_image.mpr ⟨_,h,by abel⟩

/-- Develop translation starters. The ordered differences at a fixed
origin determine their block and their translating element uniquely. -/
theorem triple_development {n m k : ℕ} [NeZero n] (seed : Fin m → Finset (Fin n))
    (size : ∀ i, (seed i).card=k)
    (cover : ∀ a b : Fin n, a≠0 → b≠0 → a≠b → ∃! u : Fin m × Fin n,
      u.2∈seed u.1 ∧ u.2+a∈seed u.1 ∧ u.2+b∈seed u.1) :
    ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 k := by
  let D := (univ : Finset (Fin m)).biUnion fun i => (univ : Finset (Fin n)).image fun t =>
    translate t (seed i)
  have memD {B} : B∈D ↔ ∃ i t, translate t (seed i)=B := by simp [D]
  refine ⟨D,?_,?_⟩
  · intro B hB
    obtain ⟨i,t,rfl⟩ := memD.mp hB
    exact (Finset.card_image_of_injective _ (add_right_injective t)).trans (size i)
  · intro A hA
    obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hA
    obtain ⟨u,hu,uniq⟩ := cover (y-x) (z-x) (sub_ne_zero.mpr hxy.symm)
      (sub_ne_zero.mpr hxz.symm) (fun e => hyz (sub_left_inj.mp e))
    let W := translate (x-u.2) (seed u.1)
    refine ⟨W,⟨memD.mpr ⟨u.1,x-u.2,rfl⟩,?_⟩,?_⟩
    · simp only [insert_subset_iff,singleton_subset_iff,W,mem_translate]
      exact ⟨(by convert hu.1 using 1; abel),
        (by convert hu.2.1 using 1; abel),(by convert hu.2.2 using 1; abel)⟩
    · rintro B ⟨hB,hsub⟩
      obtain ⟨i,t,rfl⟩ := memD.mp hB
      simp only [insert_subset_iff,singleton_subset_iff,mem_translate] at hsub
      have adjust (w : Fin n) : x-t+(w-x)=w-t := by abel
      have he : (i,x-t)=u := uniq (i,x-t) ⟨hsub.1,
        (adjust y).symm ▸ hsub.2.1,(adjust z).symm ▸ hsub.2.2⟩
      have h₁ : i=u.1 := congrArg Prod.fst he
      have h₂ : x-t=u.2 := congrArg Prod.snd he
      dsimp [W]
      rw [← h₁,← h₂]
      congr 1
      abel

private def starters : Fin 10 → Finset (Fin 26) := ![
  {0,1,2,5,23}, {0,2,4,9,21}, {0,2,11,14,17}, {0,1,6,11,12}, {0,1,7,8,17},
  {0,3,7,10,18}, {0,1,3,9,13}, {0,2,10,15,22}, {0,1,14,18,24}, {0,2,6,13,18}]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
theorem order_twenty_six : ∃ H : Finset (Finset (Fin 26)), H.IsBlockDesign 3 5 := by
  apply triple_development starters
  · decide +kernel
  · unfold ExistsUnique
    decide +kernel

/-- A cyclic witness attains the exact signed lower threshold at q=4. -/
theorem first_two_quintuple_orders :
    IsLeast (MinimumOrder.orders 3 5) 17 ∧ IsLeast (aboveSquare 4) 26 := by
  have hp : IsPrimePow 4 := (isPrimePow_nat_iff _).mpr ⟨2,2,Nat.prime_two,by decide,rfl⟩
  have hs : IsPrimePow (4+1) := (isPrimePow_nat_iff _).mpr ⟨5,1,by decide,by decide,by decide⟩
  refine ⟨MinimumOrder.prime_power_minimum hp (by decide) (by decide) (by decide),
    ⟨by decide,order_twenty_six⟩,?_⟩
  rintro v ⟨hv,H,hH⟩
  have ht := (IntegralDesign.signed_steiner_iff v 3 5 (by decide) (by omega)).mp
    ⟨_,IntegralDesign.design_weights hH⟩
  exact (adjacent_primary_minimum (q:=4) (by decide) hp hs).2 ⟨hv,ht⟩

#print axioms triple_development
#print axioms order_twenty_six
#print axioms first_two_quintuple_orders
end Erdos722.SecondOrder
