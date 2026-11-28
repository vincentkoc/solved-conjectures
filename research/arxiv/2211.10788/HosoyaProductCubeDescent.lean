import HosoyaAuxiliaryPrime

/-! Cube norms at multiples of eighteen in the real quadratic ring of discriminant 44. -/

namespace Arxiv.«2211.10788».HosoyaCubeNorm
open RealEleven
open scoped RealEleven

private def rePart {R : Type*} [CommRing R] (A B a b : R) :=
  A*(a^3+33*a*b^2)+11*B*(3*a^2*b+11*b^3)

private def imPart {R : Type*} [CommRing R] (A B a b : R) :=
  B*(a^3+33*a*b^2)+A*(3*a^2*b+11*b^3)

private theorem parts (A B a b : ℤ) :
    (⟨A,B⟩ : RingEleven)*(⟨a,b⟩ : RingEleven)^3 =
      ⟨rePart A B a b,imPart A B a b⟩ := by
  ext <;> simp [pow_succ,rePart,imPart] <;> ring

private theorem reject {A B a b f : ℤ} (h₁ : rePart A B a b=1) (h₂ : imPart A B a b=f)
    (hf : 9 ∣ f) (local_test : ∀ x y : ZMod 9, ¬(rePart (A:ZMod 9) B x y=1 ∧ imPart (A:ZMod 9) B x y=0)) : False := by
  have r := congrArg (fun n : ℤ => (n:ZMod 9)) h₁
  have s := congrArg (fun n : ℤ => (n:ZMod 9)) h₂
  simp only [rePart,imPart] at r s
  push_cast at r s
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd f 9).mpr hf] at s
  exact local_test a b ⟨r,s⟩

/-- At an integer multiple of eighteen, y³ + 1 = 11f² has only the solution f=0, y=−1. -/
theorem cube_norm_at_eighteen (f y : ℤ) (hf : 18 ∣ f) (h : y^3+1=11*f^2) :
    f=0 ∧ y= -1 := by
  obtain ⟨i,⟨a,b⟩,eqn⟩ :=
    HosoyaAuxiliaryPrime.odd_norm_unit_twists (p:=3) (by decide) ((by decide : (2:ℤ) ∣ 18).trans hf) h
  have h₉ := (by decide : (9:ℤ) ∣ 18).trans hf
  fin_cases i
  · change (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^0 * _ at eqn
    rw [pow_zero,one_mul] at eqn
    have hf₀ := HosoyaAuxiliaryPrime.pure_power (p:=3) (by decide) (by decide) eqn
    subst f
    refine ⟨rfl,?_⟩
    have hz : (y+1)*(y^2-y+1)=0 := by linear_combination h
    rcases mul_eq_zero.mp hz with hz|hz
    · omega
    · nlinarith [sq_nonneg (2*y-1)]
  · change (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^1 * _ at eqn
    rw [show (baseUnit:RingEleven)^1 = ⟨10,3⟩ by decide,parts] at eqn
    exact False.elim (reject (congrArg Zsqrtd.re eqn).symm (congrArg Zsqrtd.im eqn).symm h₉ (by decide))
  · change (⟨1,f⟩ : RingEleven) = (baseUnit:RingEleven)^2 * _ at eqn
    rw [show (baseUnit:RingEleven)^2 = ⟨199,60⟩ by decide,parts] at eqn
    exact False.elim (reject (congrArg Zsqrtd.re eqn).symm (congrArg Zsqrtd.im eqn).symm h₉ (by decide))

#print axioms cube_norm_at_eighteen

end Arxiv.«2211.10788».HosoyaCubeNorm
