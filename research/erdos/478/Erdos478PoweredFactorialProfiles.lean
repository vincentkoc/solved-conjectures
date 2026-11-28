import Erdos478CosetUnionMass
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Distinct integer residues of powers of factorials in a moving interval -/

namespace Erdos478.CyclotomicProfiles
open Finset
open scoped Classical
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]

abbrev powerKernel (p : ℕ) [Fact p.Prime] (k : ℕ) := (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).ker

theorem power_kernel_card (k : ℕ) : Nat.card (powerKernel p k)=(p-1).gcd k := by
  rw [powerKernel,IsCyclic.card_powMonoidHom_ker,Nat.card_eq_fintype_card,ZMod.card_units]

def powerCode (k : ℕ) (c : (ZMod p)ˣ ⧸ powerKernel p k) : ℕ :=
  ((QuotientGroup.quotientKerEquivRange (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ) c).val.val).val

theorem powerCode_injective (k : ℕ) : Function.Injective (powerCode (p:=p) k) :=
  (ZMod.val_injective p).comp (Units.val_injective.comp (Subtype.val_injective.comp
    (QuotientGroup.quotientKerEquivRange (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ)).injective))

theorem powerCode_factorial (k i : ℕ) (hi : i<p) :
    powerCode k (factorialLabel (powerKernel p k) i)=i.factorial^k%p := by
  have nz : (i.factorial : ZMod p)≠0 := by rw [Ne,ZMod.natCast_eq_zero_iff,hp.out.dvd_factorial]; omega
  rw [factorialLabel,label,dif_neg nz]
  change ((i.factorial : ZMod p)^k).val=_
  rw [← Nat.cast_pow,ZMod.val_natCast]

theorem occupied_power_card (k a b : ℕ) (hb : b<p) :
    (occupied (powerKernel p k) a b).card=((Icc a b).image fun i => i.factorial^k%p).card := by
  let : DecidablePred (·∈powerKernel p k) := fun _ => Classical.propDecidable _
  rw [← card_image_of_injective _ (powerCode_injective (p:=p) k),occupied,image_image]
  apply congrArg Finset.card
  exact image_congr fun i hi => powerCode_factorial k i ((mem_Icc.mp hi).2.trans_lt hb)

/-- The gcd with p-1 measures precisely the multiplicative information lost by exponentiation. -/
theorem powered_window_bound (k a b : ℕ) (hb : b<p) :
    let h := (p-1).gcd k
    (b-a-1)^2≤((Icc a b).image (fun i => i.factorial^k%p)).card^3*((b-a-1)+(h-1)*(h-2)) := by
  have bound := occupied_bound (powerKernel p k) a b hb
  rwa [power_kernel_card,occupied_power_card _ _ _ hb] at bound

/-- A target set of integer power residues can be chosen independently in each interval. -/
theorem powered_excess_mass (k a b : ℕ) (hb : b<p) (T : Finset ℕ) :
    let M := ((Icc a b).filter fun i => i.factorial^k%p∈T).card
    let h := (p-1).gcd k
    (3*M-(2*(Icc a b).card+2))^2 ≤ T.card^3*((b-a-1)+(h-1)*(h-2)) := by
  let H := powerKernel p k
  let : DecidablePred (·∈H) := fun _ => Classical.propDecidable _
  let S := (occupied H a b).filter fun c => powerCode k c∈T
  have small : S.card≤T.card := card_le_card_of_injOn (powerCode k)
    (fun _ h => (mem_filter.mp h).2) (powerCode_injective k).injOn
  have eq : visits H a b S=(Icc a b).filter (fun i => i.factorial^k%p∈T) := by
    ext i
    constructor
    · intro h
      obtain ⟨hi,inside⟩ := mem_filter.mp h
      have code := (mem_filter.mp inside).2
      rw [powerCode_factorial k i ((mem_Icc.mp hi).2.trans_lt hb)] at code
      exact mem_filter.mpr ⟨hi,code⟩
    · intro h
      obtain ⟨hi,code⟩ := mem_filter.mp h
      refine mem_filter.mpr ⟨hi,mem_filter.mpr ⟨mem_image_of_mem _ hi,?_⟩⟩
      rwa [powerCode_factorial k i ((mem_Icc.mp hi).2.trans_lt hb)]
  have bound := excess_mass H a b hb S
  rw [eq,show Nat.card H=_ from power_kernel_card (p:=p) k] at bound
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left small 3))

#print axioms powered_excess_mass
#print axioms powerKernel
#print axioms power_kernel_card
#print axioms powerCode
#print axioms powerCode_injective
#print axioms powerCode_factorial
#print axioms occupied_power_card
#print axioms powered_window_bound
end
end Erdos478.CyclotomicProfiles
