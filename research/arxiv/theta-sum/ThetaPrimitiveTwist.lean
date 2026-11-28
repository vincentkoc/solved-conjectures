import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-! Orthogonality to any periodic function whose period misses the conductor. -/
namespace Arxiv.«2501.03234».ThetaPrimitiveTwist
open Finset DirichletCharacter

/-- A character twist annihilates any test lifted from a period not divisible by its conductor. -/
theorem missing_conductor {q d P : ℕ} [NeZero P] (χ : DirichletCharacter ℂ q)
    (hq : q∣P) (hd : d∣P) (hm : ¬χ.conductor∣d) (f : (ZMod d)ˣ → ℂ) :
    ∑ u : (ZMod P)ˣ,(changeLevel hq χ) u*f (ZMod.unitsMap hd u)=0 := by
  let ψ := changeLevel hq χ
  have hn : ¬(ZMod.unitsMap hd).ker ≤ ψ.toUnitHom.ker := by
    intro h
    have hf := (factorsThrough_iff_ker_unitsMap hd).mpr h
    have hc := (mem_conductorSet_iff_conductor_dvd ψ hd).mp hf
    exact hm ((conductor_changeLevel χ hq) ▸ hc)
  obtain ⟨v,hv,hψ⟩ := SetLike.not_le_iff_exists.mp hn
  have h1 : ZMod.unitsMap hd v=1 := hv
  have hμ : ψ (v:ZMod P)≠1 := by
    contrapose! hψ
    apply Units.ext
    exact hψ
  let F (u : (ZMod P)ˣ) := ψ (u:ZMod P)*f (ZMod.unitsMap hd u)
  have he (u : (ZMod P)ˣ) : F (v*u)=ψ (v:ZMod P)*F u := by
    simp [F,Units.val_mul,map_mul,h1,mul_assoc]
  have H : (∑ u,F u)=ψ (v:ZMod P)*∑ u,F u := by
    rw [mul_sum]
    simp_rw [←he]
    exact (Equiv.sum_comp (Equiv.mulLeft v) F).symm
  exact (mul_eq_zero.mp (show (1-ψ (v:ZMod P))*(∑ u,F u)=0 by linear_combination H)).resolve_left
    (sub_ne_zero.mpr hμ.symm)

#print axioms missing_conductor
end Arxiv.«2501.03234».ThetaPrimitiveTwist
