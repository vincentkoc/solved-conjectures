import ThetaCompatibleUnits
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.GCD.BigOperators

/-! Small, rough inverse representatives on a prescribed residue class. -/
namespace Arxiv.«2501.03234».ThetaRoughInverseClasses
open Finset
noncomputable section

/-- Lift the inverse of an arbitrary a simultaneously on every divisor
coprime to it, including when a has several prime factors in m. -/
theorem lift {a m : ℕ} (hm : 0 < m) :
    ∃ n < m, n.Coprime m ∧ ∀ d, d∣m → d.Coprime a → (n:ZMod d)*(a:ZMod d)=1 := by
  let D := m.divisors.filter (·.Coprime a)
  let B := ∏ d∈D,d
  have hc : a.Coprime B := Nat.coprime_prod_right_iff.mpr (fun d hd => (mem_filter.mp hd).2.symm)
  have hdB {d : ℕ} (hd : d∣m) (h : d.Coprime a) : d∣B :=
    dvd_prod_of_mem _ (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd,hm.ne'⟩,h⟩)
  have hunit : (a+B).Coprime m := by
    by_contra h
    obtain ⟨p,hp,hp₁,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    by_cases hpa : p∣a
    · have hpB := (Nat.dvd_add_right hpa).mp hp₁
      exact hp.not_dvd_one (Nat.dvd_gcd hpa hpB |> fun H => by simpa only [hc] using H)
    · have hpB := hdB hpm (hp.coprime_iff_not_dvd.mpr hpa)
      exact hpa ((Nat.dvd_add_left hpB).mp hp₁)
  let u := ZMod.unitOfCoprime (a+B) hunit
  let : NeZero m := ⟨hm.ne'⟩
  let n := ((u⁻¹:(ZMod m)ˣ):ZMod m).val
  refine ⟨n,ZMod.val_lt _,ZMod.val_coe_unit_coprime _,?_⟩
  intro d hd hcop
  have h : (n:ZMod m)*(↑(a+B:ℕ):ZMod m)=1 := by
    change (↑((u⁻¹:(ZMod m)ˣ):ZMod m).val : ZMod m)*_=1
    rw [ZMod.natCast_zmod_val,←ZMod.coe_unitOfCoprime (a+B) hunit]; exact u.inv_mul
  simpa only [map_mul,map_add,map_natCast,map_one,Nat.cast_add,(ZMod.natCast_eq_zero_iff _ _).mpr (hdB hd hcop),add_zero]
    using congrArg (ZMod.castHom hd (ZMod d)) h

/-- Every reduced class has an inverse with no prime factor through P and
size at most twice the modulus times the primorial of P. -/
theorem rough {q r P : ℕ} (hq : 0 < q) (_hr : r < q) (hc : r.Coprime q) :
    ∃ a : ℕ, 0<a ∧ a≤2*q*4^P ∧ a.Coprime q ∧ (a:ZMod q)*(r:ZMod q)=1 ∧
      ∀ p∈a.primeFactors,P<p := by
  let B := primorial P
  let M := q*B
  let : NeZero q := ⟨hq.ne'⟩
  have hB : 0<B := primorial_pos _
  have hM : 0<M := Nat.mul_pos hq hB
  let : NeZero M := ⟨hM.ne'⟩
  let hqM : q∣M := dvd_mul_right _ _
  let u := ZMod.unitOfCoprime r hc
  obtain ⟨v,hv⟩ := ZMod.unitsMap_surjective hqM (u⁻¹)
  let a := M+(v:ZMod M).val
  have ham : a.Coprime M := by dsimp [a]; simpa using ZMod.val_coe_unit_coprime v
  refine ⟨a,by dsimp [a]; omega,?_,ham.of_dvd_right hqM,?_,?_⟩
  · have hvlt := ZMod.val_lt (v:ZMod M)
    calc a ≤2*M := by dsimp [a]; omega
         _ ≤2*(q*4^P) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left q (primorial_le_four_pow _))
         _ = _ := by ring
  · have he : (a:ZMod q)=(↑(u⁻¹):(ZMod q)) := by
      rw [←hv,ZMod.unitsMap_val,←ZMod.natCast_zmod_val (v:ZMod M),ZMod.cast_natCast hqM]
      simp [a,(ZMod.natCast_eq_zero_iff _ _).mpr hqM]
    rw [he,←ZMod.coe_unitOfCoprime r hc]; exact u.inv_mul
  · intro p hp; by_contra! h
    have hpr := (Nat.mem_primeFactors.mp hp).1
    have hd : p∣B := hpr.dvd_primorial_iff.mpr h
    have hh := Nat.dvd_gcd (Nat.mem_primeFactors.mp hp).2.1 (hd.trans (dvd_mul_left B q))
    exact hpr.not_dvd_one (by simpa only [show a.gcd (q*B)=1 from ham] using hh)

#print axioms lift
#print axioms rough
end
end Arxiv.«2501.03234».ThetaRoughInverseClasses
