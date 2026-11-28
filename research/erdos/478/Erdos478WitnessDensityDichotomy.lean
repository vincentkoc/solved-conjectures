import Erdos478SimultaneousModularWitness
import Erdos478ExactEndpointCorrection
import Erdos478RegularGapPrimes
import Erdos478IntegerGapObservables

/-! # Positive density or explicitly exceptional primes for any finite factorial collision profile -/

namespace Erdos478.LocalWitness
open Finset Polynomial Filter Topology NumberField FrobeniusCounts GapDensity FirstCollision
open RootMoments SplittingDensity
open scoped Classical
noncomputable section

def realizes (S : Finset ℕ) (E : (S → ℕ) → Prop) (p : ℕ) := E (fun i => (endpoints i.val p).card)

theorem modeled_mass {S : Finset ℕ} (hs : ∀ k∈S, 2≤k) (E : (S → ℕ) → Prop)
    (g : Aut (FieldOf S)) (hg : E (fun i => fixedGap (FieldOf S) i.val g)) :
    ((∏ k∈S,k.factorial : ℕ) : ℝ)⁻¹≤density S E := by
  let K := FieldOf S
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal _ }
  let w (h : Aut K) : ℝ := if E (fun i => fixedGap K i.val h) then 1 else 0
  have sum : 1≤∑ h,w h := (show w g=1 from if_pos hg) ▸ single_le_sum (f:=w)
    (fun h _ => by dsimp [w]; split_ifs <;> norm_num) (mem_univ g)
  have bound := density_lower_bound (by decide : 0<1) S (fun k hk => (by decide : 0<2).trans_le (hs k hk))
  simp only [Nat.totient_one,one_mul] at bound
  apply bound.trans
  change (Module.finrank ℚ K : ℝ)⁻¹≤(∑ h,w h)/Fintype.card (Aut K)
  rw [← IsGalois.card_aut_eq_finrank ℚ K,Nat.card_eq_fintype_card,← one_div]
  exact div_le_div_of_nonneg_right sum (Nat.cast_nonneg _)

/-- Even a small witness prime suffices: its modular counts at every tested
length can be reproduced at a positive density of prime moduli on the actual factorial interval. -/
theorem modular_witness_mass {S : Finset ℕ} (hs : ∀ k∈S, 2≤k) (E : (S → ℕ) → Prop)
    (p : ℕ) [Fact p.Prime] (reg : ∀ k∈S, ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable)
    (witness : E (fun i => primeRoots (gapPoly i.val) p)) :
    ((∏ k∈S,k.factorial : ℕ) : ℝ)⁻¹≤density S E := by
  let K := FieldOf S
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal _ }
  obtain ⟨g,hg⟩ := simultaneous_witness K p
  have pos (k) (hk : k∈S) := (by decide : 0<2).trans_le (hs k hk)
  have eq (i : S) : fixedGap K i.val g=primeRoots (gapPoly i.val) p := by
    let f := gapPoly i.val
    have deg := gap_degree (pos i.val i.prop)
    have rat : f.map (Int.castRingHom ℚ)=BinaryGap.rationalGap i.val := by simp [f,gapPoly,BinaryGap.rationalGap]
    have split := gap_splits pos i.prop
    rw [← rat,map_integer_poly] at split
    have sepQ : (f.map (Int.castRingHom ℚ)).Separable := by
      simpa [f,gapPoly] using (GapFamilies.irreducible_gap_rat (pos i.val i.prop)).separable
    have sep := sepQ.map (f:=algebraMap ℚ K)
    rw [map_integer_poly] at sep
    have h := hg f deg.monic sep split (reg i.val i.prop)
    unfold fixed rootType at h
    rw [rat] at h
    exact h
  exact modeled_mass hs E g ((funext eq).symm ▸ witness)

theorem regular_witness_mass {S : Finset ℕ} (hs : ∀ k∈S, 2≤k) (E : (S → ℕ) → Prop)
    {p : ℕ} (hp : p.Prime) (good : ¬p∣exceptionalProduct S) (event : realizes S E p) :
    ((∏ k∈S,k.factorial : ℕ) : ℝ)⁻¹≤density S E := by
  let : Fact p.Prime := ⟨hp⟩
  have reg (i) (hi : i∈S) := regular_gap hi (hs i hi) good
  apply modular_witness_mass hs E p (fun i hi => (reg i hi).1)
  have eq (i : S) : primeRoots (gapPoly i.val) p=(endpoints i.val p).card := by
    simp [endpoint_correction,(reg i.val i.prop).2]
  exact (funext eq).symm ▸ event

/-- A zero-density event occurs only at primes dividing one explicit nonzero
integer. Conversely confinement to that divisor forces zero ordinary density. -/
theorem zero_iff_exceptional (pit : DegreeOnePrimeIdealTheorem) {S : Finset ℕ}
    (hs : ∀ k∈S, 2≤k) (E : (S → ℕ) → Prop) :
    density S E=0 ↔ ∀ p : ℕ, p.Prime → realizes S E p → p∣exceptionalProduct S := by
  constructor
  · intro zero p hp occurs
    by_contra bad
    have low := regular_witness_mass hs E hp bad occurs
    rw [zero] at low
    have pos : (0:ℝ)< ((∏ k∈S,k.factorial : ℕ) : ℝ)⁻¹ := by positivity
    exact pos.not_ge low
  · intro all
    have lim := density_limit pit S hs E (fun _ => False) (exceptionalProduct S) (by
      intro p hlarge hp
      refine ⟨False.elim,fun he => ?_⟩
      exact hlarge.not_ge (Nat.le_of_dvd (exceptionalProduct_pos S hs) (all p hp he)))
    have z : (fun X : ℕ => GapSieve.fraction X (fun _ => False))=fun _ => (0:ℝ) := by
      funext X
      simp [GapSieve.fraction]
    rw [z] at lim
    exact tendsto_nhds_unique lim tendsto_const_nhds

#print axioms realizes
#print axioms modeled_mass
#print axioms modular_witness_mass
#print axioms regular_witness_mass
#print axioms zero_iff_exceptional
end
end Erdos478.LocalWitness
