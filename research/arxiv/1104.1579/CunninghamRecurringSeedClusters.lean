import CunninghamSeedOrbitMask
import CunninghamPrimeReturnTimes

/-! Recurring bounded patterns of consecutive prime seeds with simultaneous
composite stretches in both Cunningham orbits. -/

namespace CunninghamChain.SeedClusters

open Finset PrimeReturns

/-- A single subset of the translates works at every isolation depth. The
seed-primality equivalence includes every unlisted integer in the interval. -/
theorem recurring_isolated_tuple (clusters : MaynardAffineClusters) (m : ℕ) :
    ∃ K : ℕ, ∀ (A : Finset ℕ) (D : ℕ), K≤A.card →
      (∀ u∈A, 0<u ∧ u≤D) → (∀ p : ℕ, p.Prime → ∃ x, ∀ u∈A, ¬p ∣ x+u) →
      ∃ U ⊆ A, m≤U.card ∧ ∀ H X : ℕ, ∃ x≥X,
        (∀ i≤D, (x+i).Prime ↔ i∈U) ∧
        ∀ u∈U, ∀ b : Bool, ∀ j<H, ¬(seedTerm b (x+u) (j+1)).Prime := by
  classical
  obtain ⟨K,maynard⟩ := clusters m
  refine ⟨K,?_⟩
  intro A D size bounds admissible
  have atDepth (H : ℕ) : ∃ x≥H, m≤(A.filter fun u => (x+u).Prime).card ∧
      (∀ i≤D, i∉A → ¬(x+i).Prime) ∧
      ∀ u∈A, ∀ b : Bool, ∀ j<H, ¬(seedTerm b (x+u) (j+1)).Prime := by
    obtain ⟨W,B,wp,_,skipSite,stop,allowed⟩ := orbit_mask A D H (fun u hu => (bounds u hu).1) admissible
    have distinct : ∀ u∈A, ∀ v∈A, u≠v → W*(B+v)≠W*(B+u) := by
      intro u _ v _ ne e
      exact ne (Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left wp e)).symm
    obtain ⟨n,hn,count⟩ := maynard A (fun _ => W) (fun u => B+u) size
      (fun _ _ => wp) distinct (by simpa only [←Nat.add_assoc] using allowed) H
    refine ⟨W*n+B,hn.trans ((Nat.le_mul_of_pos_left n wp).trans (Nat.le_add_right ..)),?_,skipSite n,stop n⟩
    simpa only [←Nat.add_assoc] using count
  choose x large count outside isolated using atDepth
  let U (z : ℕ) : ↥A.powerset :=
    ⟨A.filter (fun u => (x z+u).Prime),mem_powerset.mpr (filter_subset ..)⟩
  obtain ⟨V,inf⟩ := Finite.exists_infinite_fiber U
  have unbounded : (U ⁻¹' {V}).Infinite := Set.infinite_coe_iff.mp inf
  have eq {z : ℕ} (hz : z∈U ⁻¹' {V}) : (A.filter fun u => (x z+u).Prime)=V.val :=
    congrArg Subtype.val (show U z=V from hz)
  obtain ⟨z,hz⟩ := unbounded.nonempty
  refine ⟨V.val,mem_powerset.mp V.property,eq hz ▸ count z,?_⟩
  intro H X
  obtain ⟨z,hz,high⟩ := Set.infinite_iff_exists_gt.mp unbounded (H+X)
  refine ⟨x z,by have := large z;omega,?_,?_⟩
  · intro i hi
    rw [←eq hz,mem_filter]
    exact ⟨fun prime => ⟨by by_contra miss; exact outside z i hi miss prime,prime⟩,And.right⟩
  · intro u hu b j hj
    exact isolated z u (mem_powerset.mp V.property hu) b j (by omega)

/-- Both exact singleton predicates and the first H positive composite steps on both orbits. -/
def isolatedSingleton (p H : ℕ) : Prop :=
  IsFirstKindChainOfLength p 1 ∧ IsSecondKindChainOfLength p 1 ∧
  ∀ j<H, ¬(firstKindTerm p (j+1)).Prime ∧ ¬(secondKindTerm p (j+1)).Prime

/-- Every prescribed divisibility modulus is compatible with a fixed bounded
tuple of consecutive primes whose joint isolation depth is arbitrarily large. -/
theorem consecutive_cluster (clusters : MaynardAffineClusters) (m M : ℕ) (modpos : 0<M) :
    ∃ D : ℕ, ∃ U : Finset ℕ, m≤U.card ∧ (∀ u∈U, u≤D ∧ M∣u) ∧
      ∀ H X : ℕ, ∃ x≥X, (∀ i≤D, (x+i).Prime ↔ i∈U) ∧
        ∀ u∈U, isolatedSingleton (x+u) H := by
  classical
  obtain ⟨K,supply⟩ := recurring_isolated_tuple clusters m
  let L := M*K.factorial
  have lp : 0<L := Nat.mul_pos modpos K.factorial_pos
  let f (i : ℕ) := L*(i+1)
  let A := (range K).image f
  have injective : Function.Injective f := fun _ _ h => by
    have := Nat.eq_of_mul_eq_mul_left lp h
    omega
  have card : A.card=K := (card_image_of_injective _ injective).trans (card_range _)
  have spec {u : ℕ} (hu : u∈A) : 0<u ∧ u≤L*K ∧ M∣u := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hu
    exact ⟨Nat.mul_pos lp (by omega),Nat.mul_le_mul_left _ (mem_range.mp hi),
      (dvd_mul_right ..).trans (dvd_mul_right ..)⟩
  have adm (p : ℕ) (pp : p.Prime) : ∃ x, ∀ u∈A, ¬p ∣ x+u := by
    by_cases small : p≤K
    · refine ⟨1,?_⟩
      intro u hu d
      obtain ⟨i,_,rfl⟩ := mem_image.mp hu
      have hL : p∣L := (Nat.dvd_factorial pp.pos small).trans (dvd_mul_left ..)
      have du : p∣f i := hL.trans (dvd_mul_right ..)
      exact pp.not_dvd_one ((Nat.dvd_add_iff_left du).mpr d)
    · let : Fact p.Prime := ⟨pp⟩
      let roots := A.image (fun u : ℕ => -(u:ZMod p))
      have size : roots.card≤A.card := by
        exact card_image_le (s:=A) (f:=fun u : ℕ => -(u:ZMod p))
      have hc : roots.card<p := by omega
      have ne : roots ≠ univ := by intro eq; rw [eq,card_univ,ZMod.card] at hc;omega
      obtain ⟨z,miss⟩ : ∃ z : ZMod p, z∉roots := by
        by_contra! all
        exact ne (Finset.eq_univ_iff_forall.mpr all)
      obtain ⟨x,hx⟩ := ZMod.natCast_zmod_surjective z
      refine ⟨x,fun u hu dv => miss ?_⟩
      apply mem_image.mpr
      have e := (ZMod.natCast_eq_zero_iff ..).mpr dv
      rw [Nat.cast_add,hx] at e
      exact ⟨u,hu,(eq_neg_of_add_eq_zero_left e).symm⟩
  obtain ⟨U,sub,size,recur⟩ := supply A (L*K) card.ge (fun u hu => ⟨(spec hu).1,(spec hu).2.1⟩) adm
  refine ⟨L*K,U,size,fun u hu => ⟨(spec (sub hu)).2.1,(spec (sub hu)).2.2⟩,?_⟩
  intro H X
  obtain ⟨x,hx,sites,clear⟩ := recur (H+1) X
  refine ⟨x,hx,sites,?_⟩
  intro u hu
  have prime := (sites u (spec (sub hu)).2.1).mpr hu
  have first j (hj : j<H+1) : ¬(firstKindTerm (x+u) (j+1)).Prime := clear u hu true j hj
  have second j (hj : j<H+1) : ¬(secondKindTerm (x+u) (j+1)).Prime := clear u hu false j hj
  exact ⟨⟨by decide,fun i hi => by interval_cases i;exact prime,first 0 (by omega)⟩,
    ⟨by decide,fun i hi => by interval_cases i;exact prime,second 0 (by omega)⟩,
    fun j hj => ⟨first j (by omega),second j (by omega)⟩⟩

/-- One positive gap, divisible by a prescribed modulus, recurs between
consecutive primes whose four orbits all start with H composites, for every H. -/
theorem recurring_consecutive_gap (clusters : MaynardAffineClusters) {M : ℕ} (modpos : 0<M) :
    ∃ g : ℕ, 0<g ∧ M∣g ∧ ∀ H : ℕ, {p : ℕ | isolatedSingleton p H ∧
      isolatedSingleton (p+g) H ∧ ∀ i : ℕ, (0 < i) → (i < g) → ¬(p+i).Prime}.Infinite := by
  classical
  obtain ⟨D,U,size,bounds,supply⟩ := consecutive_cluster clusters 2 M modpos
  have un : U.Nonempty := card_pos.mp (by omega)
  let a := U.min' un
  have ha : a∈U := min'_mem ..
  have card := card_erase_add_one ha
  have vn : (U.erase a).Nonempty := card_pos.mp (by omega)
  let b := (U.erase a).min' vn
  have hb : b∈U.erase a := min'_mem ..
  obtain ⟨neq,bmem⟩ := mem_erase.mp hb
  have le : a≤b := U.min'_le b bmem
  have less : a<b := by omega
  refine ⟨b-a,by omega,Nat.dvd_sub (bounds b bmem).2 (bounds a ha).2,?_⟩
  intro H
  apply Set.infinite_of_forall_exists_gt
  intro X
  obtain ⟨x,hx,sites,isolated⟩ := supply H (X+1)
  have next : x+a+(b-a)=x+b := by omega
  refine ⟨x+a,⟨isolated a ha,next ▸ isolated b bmem,?_⟩,by omega⟩
  intro i ip short prime
  have limit := (bounds b bmem).1
  have mem : a+i∈U := (sites (a+i) (by omega)).mp (by simpa only [Nat.add_assoc] using prime)
  have hi : a+i∈U.erase a := mem_erase.mpr ⟨by omega,mem⟩
  have order : b≤a+i := (U.erase a).min'_le (a+i) hi
  omega

#print axioms recurring_consecutive_gap
#print axioms consecutive_cluster

#print axioms recurring_isolated_tuple

end CunninghamChain.SeedClusters
