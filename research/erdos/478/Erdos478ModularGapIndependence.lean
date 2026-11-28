import Erdos478RelativeGapIndependence
import Erdos478CommonModularProfile
import Erdos478LeastPrimeCollision

/-! # A finite modular test for independence of a prime-length factorial gap -/

namespace Erdos478.RelativeGap
open Equiv Polynomial Finset Filter Topology LocalWitness FirstCollision BinaryGap FrobeniusCounts
open LowGapAction GapDensity SplittingDensity GapSieve
open scoped Classical
noncomputable section

theorem modular_relative (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (s : Finset ℕ) {l : ℕ} (prime : l.Prime) (small : ∀ k∈s, 0<k ∧ k<l)
    (split : ∀ k∈insert l s, ((rationalGap k).map (algebraMap ℚ K)).Splits)
    (p : ℕ) [Fact p.Prime] (reg : ∀ k∈insert l s, ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable)
    (low : ∀ k∈s, primeRoots (gapPoly k) p=k) (two : primeRoots (gapPoly l) p+2=l)
    (e : GapRoots K l ≃ Fin l) : Function.Surjective ((numberedAction K e).comp (LowerKernel K s).subtype) := by
  obtain ⟨g,h⟩ := regular_profile K (insert l s) (fun k hk =>
    (mem_insert.mp hk).elim (fun eq => eq ▸ prime.pos) (fun hi => (small k hi).1)) split p reg
  exact full_relative K s prime small split e ⟨g,fun k hk => (h k (mem_insert_of_mem hk)).trans (low k hk),
    by rw [h l (mem_insert_self ..)]; exact two⟩

/-- After a regular prime certifies a pure transposition, every old count event
and every statistic of the number of new roots have independent ordinary-prime laws. -/
theorem modular_independent_density (pit : DegreeOnePrimeIdealTheorem) (s : Finset ℕ) {l : ℕ}
    (prime : l.Prime) (small : ∀ k∈s, 2≤k ∧ k<l)
    (p : ℕ) [Fact p.Prime] (reg : ∀ k∈insert l s, ((gapPoly k).map (Int.castRingHom (ZMod p))).Separable)
    (low : ∀ k∈s, primeRoots (gapPoly k) p=k) (two : primeRoots (gapPoly l) p+2=l)
    (E : (s → ℕ) → Prop) (F : ℕ → Bool) :
    Tendsto (fun X => fraction X (fun q => E (fun i => (endpoints i.val q).card) ∧ F (endpoints l q).card))
      atTop (𝓝 (density s E*uniform (Perm (Fin l)) (fun z => if F (pointCount z) then 1 else 0))) := by
  let T := insert l s
  let K := FieldOf T
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := Polynomial.SplittingField.instNormal _ }
  have ht (k) (hk : k∈T) : 2≤k := (mem_insert.mp hk).elim (fun eq => eq ▸ prime.two_le) (fun h => (small k h).1)
  have sp (k) (hk : k∈T) := gap_splits (fun j hj => (by decide : 0<2).trans_le (ht j hj)) hk
  let e := rootLabels K prime.pos (sp l (mem_insert_self ..))
  have full := modular_relative K s prime (fun k h => ⟨(by decide : 0<2).trans_le (small k h).1,(small k h).2⟩)
    sp p reg low two e
  let W (g : Aut K) : ℝ := if E (fun i => fixedGap K i.val g) then 1 else 0
  let V (z : Perm (Fin l)) : ℝ := if F (pointCount z) then 1 else 0
  have stab (n : LowerKernel K s) (g : Aut K) : W (n.val*g)=W g := by
    have h : (fun i : s => fixedGap K i.val (n.val*g))=(fun i : s => fixedGap K i.val g) :=
      funext fun i => stable_count K n g i.prop
    simp only [W,h]
  have joint := quotient_independent _ _ full W V stab
  let E₀ (a : T → ℕ) := E (earlier l a)
  have old := density_congr pit (fun k h => (small k h).1) ht E E₀ (fun _ _ => Iff.rfl)
  change density s E=uniform (Aut K) W at old
  let event (a : T → ℕ) := E₀ a ∧ F (a ⟨l,mem_insert_self ..⟩)
  have eq : density T event=density s E*uniform (Perm (Fin l)) V := by
    rw [old,mul_comm,← joint]
    unfold density
    congr 1
    funext g
    let A := E (fun i : s => fixedGap K i.val g)
    change (@ite ℝ (A ∧ F (fixedGap K l g)) (Classical.propDecidable _) 1 0)=
      (if A then 1 else 0)*(if F (pointCount (numberedAction K e g)) then 1 else 0)
    rw [numbered_fixed]
    by_cases ha : A <;> simp [ha]
  rw [← eq]
  exact density_limit pit T ht event _ 0 (fun _ _ _ => Iff.rfl)

#print axioms modular_relative
#print axioms modular_independent_density
end
end Erdos478.RelativeGap
