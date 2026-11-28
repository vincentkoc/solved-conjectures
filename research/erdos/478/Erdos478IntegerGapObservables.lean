import Erdos478LowerDegreeActions
import Erdos478GapObservableLaw
import Erdos478GapSplittingDegrees
import Erdos478SieveProportions

/-! # Prime densities for events on a finite set of integer collision lengths -/

namespace Erdos478.FirstCollision
open Polynomial Finset Filter Topology BinaryGap FrobeniusCounts CollisionLaw
open SplittingDensity RootMoments GapDensity
open scoped Classical
noncomputable section

abbrev FieldOf (s : Finset ℕ) := SplitField (test 1 s)

theorem gap_splits {s : Finset ℕ} (pos : ∀ k∈s, 0<k) {k : ℕ} (hk : k∈s) :
    ((rationalGap k).map (algebraMap ℚ (FieldOf s))).Splits := by
  let f := (test 1 s).map (Int.castRingHom ℚ)
  have hmon := (test_properties (by decide : 0<1) pos).1
  have dvd : gapPoly k ∣ test 1 s := Finset.dvd_prod_of_mem _
    (mem_insert_of_mem (mem_image_of_mem gapPoly hk) : gapPoly k∈factors 1 s)
  have eq : (gapPoly k).map (Int.castRingHom ℚ)=rationalGap k := by simp [gapPoly,rationalGap]
  rw [← eq]
  exact (SplittingField.splits f).of_dvd ((hmon.map _).map _).ne_zero
    (Polynomial.map_dvd _ (Polynomial.map_dvd _ dvd))

def density (s : Finset ℕ) (E : (s → ℕ) → Prop) :=
  uniform (Aut (FieldOf s)) (fun g => if E (fun i => fixedGap (FieldOf s) i.val g) then 1 else 0)

theorem density_limit (pit : DegreeOnePrimeIdealTheorem) (s : Finset ℕ) (hs : ∀ k∈s, 2≤k)
    (E : (s → ℕ) → Prop) (P : ℕ → Prop) (B : ℕ)
    (eq : ∀ p>B, p.Prime → (P p ↔ E (fun i => (endpoints i.val p).card))) :
    Tendsto (fun X => GapSieve.fraction X P) atTop (𝓝 (density s E)) := by
  let K := FieldOf s
  let A := countingAverage pit
  let : Normal ℚ K := SplittingField.instNormal _
  have pos (k) (hk : k∈s) : 0<k := lt_of_lt_of_le (by decide : 0<2) (hs k hk)
  have hf (i : s) : Good (gapPoly i.val) ∧ ((gapPoly i.val).map (Int.castRingHom K)).Splits := by
    have d := SplittingDensity.gap_degree (pos i i.prop)
    refine ⟨⟨d.monic,d.natDegree_eq.symm ▸ pos i i.prop,?_⟩,?_⟩
    · simpa [gapPoly] using (GapFamilies.irreducible_gap_rat (pos i i.prop)).separable
    · simpa [gapPoly,rationalGap] using gap_splits pos i.prop
  let w (a : s → ℕ) : ℝ := if E a then 1 else 0
  have fixed_eq (k : ℕ) (g : Aut K) : fixed K (gapPoly k) g=fixedGap K k g := by
    unfold fixed rootType fixedGap GapRoots
    rw [show (gapPoly k).map (Int.castRingHom ℚ)=rationalGap k by simp [gapPoly,rationalGap]]
  have h := observable_mean A (fun i : s => gapPoly i.val) K hf w
  simp_rw [fixed_eq] at h
  have lim := mean_of_change A (a:=fun p => if P p then (1:ℝ) else 0)
    (b:=fun p => w (fun i => primeRoots (gapPoly i.val) p)) (max B (s.sup cutoff)) (by
      intro p hp hpr
      have he : (fun i : s => (endpoints i.val p).card)=(fun i : s => primeRoots (gapPoly i.val) p) :=
        funext fun i => ConditionalGaps.endpoint_roots (hs i i.prop) hpr
          ((le_sup i.prop).trans_lt ((le_max_right ..).trans_lt hp))
      simp only [w,eq p ((le_max_left ..).trans_lt hp) hpr,he]) h
  exact lim.congr fun X => GapSieve.ordinary_eq X P

/-- Two presentations of the same event on prime moduli have the same density,
including when one presentation uses a larger splitting field. -/
theorem density_congr (pit : DegreeOnePrimeIdealTheorem) {s t : Finset ℕ}
    (hs : ∀ k∈s, 2≤k) (ht : ∀ k∈t, 2≤k) (E : (s → ℕ) → Prop) (F : (t → ℕ) → Prop)
    (eq : ∀ p, p.Prime → (E (fun i => (endpoints i.val p).card) ↔ F (fun i => (endpoints i.val p).card))) :
    density s E=density t F := by
  let P (p : ℕ) := E (fun i => (endpoints i.val p).card)
  exact tendsto_nhds_unique (density_limit pit s hs E P 0 (fun _ _ _ => Iff.rfl))
    (density_limit pit t ht F P 0 (fun p _ hp => eq p hp))

#print axioms FieldOf
#print axioms gap_splits
#print axioms density
#print axioms density_limit
#print axioms density_congr
end
end Erdos478.FirstCollision
