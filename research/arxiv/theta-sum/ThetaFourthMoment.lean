import ThetaVarianceExhaustion

/-! A finite fourth-moment estimate for Dirichlet polynomials on the unit group. -/
namespace Arxiv.«2501.03234».ThetaFourthMoment
open Finset Complex DirichletCharacter
open scoped ComplexConjugate
noncomputable section

private theorem young {G : Type*} [CommGroup G] [Fintype G] (b : G → ℝ) :
    ∑ x, (∑ u, b u ^ 3 * b (x/u) ^ 3)^2 ≤ (∑ u, b u^4)^3 := by
  let A := ∑ u, b u^4
  have hpoint (x : G) : (∑ u, b u^3*b (x/u)^3)^2 ≤ (∑ u,b u^4*b (x/u)^4)*A := by
    have hc := sum_mul_sq_le_sq_mul_sq univ (fun u => b u^2*b (x/u)^2) (fun u => b u*b (x/u))
    have hh : ∑ u,(b u*b (x/u))^2 ≤ A := by
      have he : ∑ u,b (x/u)^4=A := (Equiv.divLeft x).sum_comp (fun u => b u^4)
      have hf : ∑ u,2*(b u*b (x/u))^2 ≤ ∑ u,(b u^4+b (x/u)^4) :=
        sum_le_sum fun u _ => by nlinarith only [sq_nonneg (b u^2-b (x/u)^2)]
      rw [←mul_sum,sum_add_distrib,he] at hf
      dsimp only [A] at *
      linarith
    have he (u : G) : b u^2*b (x/u)^2*(b u*b (x/u))=b u^3*b (x/u)^3 := by ring
    have hd (u : G) : (b u^2*b (x/u)^2)^2=b u^4*b (x/u)^4 := by ring
    simp only [he,hd] at hc
    exact hc.trans (mul_le_mul_of_nonneg_left hh (sum_nonneg (fun _ _ => by positivity)))
  calc _ ≤ ∑ x,(∑ u,b u^4*b (x/u)^4)*A := sum_le_sum (fun x _ => hpoint x)
       _ = (∑ u,b u^4*(∑ x,b (x/u)^4))*A := by rw [←sum_mul,sum_comm]; simp only [mul_sum]
       _ = _ := by
         have he (u : G) : ∑ x,b (x/u)^4=A := (Equiv.divRight u).sum_comp (fun x => b x^4)
         simp_rw [he,←sum_mul]
         dsimp [A]; ring

variable {q : ℕ} [NeZero q]
local notation "U" => (ZMod q)ˣ
def transform (a : U → ℝ) (χ : DirichletCharacter ℂ q) : ℂ := ∑ u,(a u:ℂ)*χ (u:ZMod q)

private theorem plancherel (a : U → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, ‖transform a χ‖^2=(q.totient:ℝ)*∑ u,a u^2 := by
  classical
  have he (χ : DirichletCharacter ℂ q) :
      transform a χ * conj (transform a χ) =
      ∑ u : U,∑ v : U,(a u*a v:ℂ)*(χ (u:ZMod q)*conj (χ (v:ZMod q))) := by
    simp only [transform,map_sum,map_mul,conj_ofReal,sum_mul,mul_sum]
    conv_lhs => rw [sum_comm]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  have H := congrArg (fun t : DirichletCharacter ℂ q → ℂ => ∑ χ,t χ) (funext he)
  change ∑ χ, transform a χ*conj (transform a χ) = ∑ χ,∑ u,∑ v,_ at H
  rw [sum_comm] at H
  -- Move the character sum onto the unit-group kernel.
  have hk (u : U) : ∑ χ : DirichletCharacter ℂ q,∑ v : U,(a u*a v:ℂ)*(χ (u:ZMod q)*conj (χ (v:ZMod q))) =
      (a u:ℂ)^2*q.totient := by
    rw [sum_comm]
    simp_rw [←mul_sum,ThetaVarianceExhaustion.kernel]
    simp [mul_ite,sq]
  simp_rw [hk] at H
  have hR := congrArg Complex.re H
  simpa only [mul_conj,ofReal_re,re_sum,←Complex.sq_norm,←sum_mul,←ofReal_pow,
    ←ofReal_natCast,←ofReal_sum,←ofReal_mul,mul_comm (∑ _,_)] using hR

private theorem square_transform (b : U → ℝ) (χ : DirichletCharacter ℂ q) :
    (transform b χ)^2=transform (fun x => ∑ u,b u*b (x/u)) χ := by
  classical
  simp only [transform,sq,sum_mul,mul_sum,ofReal_sum,ofReal_mul]
  rw [sum_comm (f:=fun x u : U => ((b u:ℂ)*b (x/u))*χ (x:ZMod q))]
  apply sum_congr rfl
  intro u _
  have he := Equiv.sum_comp (Equiv.mulLeft u) (fun x : U => ((b u:ℂ)*b (x/u))*χ (x:ZMod q))
  rw [←he]
  simp only [Equiv.coe_mulLeft,mul_div_cancel_left,Units.val_mul,map_mul]
  apply sum_congr rfl
  intro v _
  ring

/-- The fourth moment divided by the number of characters is bounded by the
cube of the unnormalized four-thirds mass of the coefficients. -/
theorem fourth_bound (b : U → ℝ) :
    ∑ χ : DirichletCharacter ℂ q, ‖transform (fun u => b u^3) χ‖^4 ≤
      q.totient * (∑ u,b u^4)^3 := by
  have he (χ : DirichletCharacter ℂ q) :
      ‖transform (fun u => b u^3) χ‖^4 =
      ‖transform (fun x => ∑ u,b u^3*b (x/u)^3) χ‖^2 := by
    rw [←square_transform, norm_pow]; ring
  simp_rw [he]
  rw [plancherel]
  exact mul_le_mul_of_nonneg_left (young b) (Nat.cast_nonneg _)

#print axioms fourth_bound
end
end Arxiv.«2501.03234».ThetaFourthMoment
