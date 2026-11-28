import ThetaLValueMoment

/-! Conductor variance from the fourth moment at one. -/
namespace Arxiv.«2501.03234».ThetaConductorMoment
open Finset Complex DirichletCharacter ThetaPrimitiveSpectrum ThetaConductorDecay
open ThetaSpectralVariance ThetaNaturalPrimeMeans ThetaLevelCoefficients
noncomputable section

private def liftAt (q : ℕ) (u : Mode) : DirichletCharacter ℂ q :=
  if h : u.modulus=q then h ▸ u.character else 1

private theorem at_level (q : ℕ) [NeZero q] (u : Mode) (he : u.modulus=q) :
    (liftAt q u).IsPrimitive ∧ u.mass=‖value (m:=q) (liftAt q u)‖^2 := by
  rcases u with ⟨r,hr,χ,hχ⟩
  change r=q at he
  subst q
  simp only [liftAt,Mode.mass]
  exact ⟨hχ,rfl⟩

private theorem inj_level (q : ℕ) (u v : Mode) (hu : u.modulus=q) (hv : v.modulus=q)
    (he : liftAt q u=liftAt q v) : u=v := by
  rcases u with ⟨r,hr,χ,hχ⟩
  rcases v with ⟨t,ht,ψ,hψ⟩
  change r=q at hu
  change t=q at hv
  subst r; subst t
  simp [liftAt] at he
  subst ψ
  rfl

/-- All primitive characters at a single conductor have total mass O(1/(q φ(q))). -/
theorem level (s : Finset Mode) {q : ℕ} (hq : 1<q) (hs : ∀ u∈s,u.modulus=q)
    (hAP : ProgressionMangoldt) :
    ∑ u∈s,u.mass ≤ 1152*(ThetaLValueMoment.H^3+1)/((q:ℝ)*q.totient) := by
  classical
  let : NeZero q := ⟨by omega⟩
  let t := s.image (liftAt q)
  have hinj : Set.InjOn (liftAt q) ↑s := fun u hu v hv => inj_level q u v (hs u hu) (hs v hv)
  have ht (χ) (hχ : χ∈t) : χ.IsPrimitive := by
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hχ
    exact (at_level q u (hs u hu)).1
  have hnon (χ) (hχ : χ∈t) : χ≠1 := by
    have hc : χ.conductor=q := ht χ hχ
    intro he; rw [he,conductor_one] at hc; omega
  have hm := ThetaLValueMoment.moment t hnon
  have he : ∑ u∈s,u.mass=∑ χ∈t,‖value χ‖^2 := by
    rw [sum_image hinj]; exact sum_congr rfl (fun u hu => (at_level q u (hs u hu)).2)
  have hq' : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
  have hf : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  let K := 144/((q:ℝ)*q.totient^2)
  have hk : 0≤K := by dsimp only [K]; positivity
  have hpt (χ) (hχ : χ∈t) : ‖value χ‖^2 ≤ K*‖LFunction χ 1‖^4 := by
    apply (pow_le_pow_left₀ (norm_nonneg _) (primitive_lvalue_bound χ (ht χ hχ) hq hAP) 2).trans_eq
    dsimp only [K]
    rw [div_pow,mul_pow (Real.sqrt q),Real.sq_sqrt hq'.le]
    field_simp; ring
  rw [he]
  calc _ ≤ ∑ χ∈t,K*‖LFunction χ 1‖^4 := sum_le_sum hpt
       _ = _ := (mul_sum ..).symm
       _ ≤ K*(q.totient*(8*(ThetaLValueMoment.H^3+1))) := mul_le_mul_of_nonneg_left hm hk
       _ = _ := by dsimp only [K]; field_simp; ring

#print axioms level
end
end Arxiv.«2501.03234».ThetaConductorMoment
