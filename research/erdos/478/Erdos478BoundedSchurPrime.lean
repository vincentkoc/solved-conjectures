import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# An effective Schur prime avoiding a prescribed integer

A prime divisor of a suitably normalized polynomial value avoids every
divisor of the prescribed integer. Bounding all complex roots gives an
explicit upper bound for that prime.
-/

namespace Erdos478.EffectiveResolvent
open Finset Polynomial
open scoped Polynomial

/-- The explicit size bound in the Schur construction. -/
def schurBound (m U B : ℕ) : ℕ := (2*U+2+(2*U+1)*B*((2*U+2)^m)^2)^m

private theorem abs_eval {I : Type*} [Fintype I] (g : ℤ[X]) (a : I → ℂ)
    (h : g.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i))) (x : ℕ) :
    ((g.eval (x:ℤ)).natAbs : ℝ) = ∏ i, ‖(x:ℂ)-a i‖ := by
  have hv := congrArg (eval (x:ℂ)) h
  have he : (g.map (Int.castRingHom ℂ)).eval (x:ℂ) = ((g.eval (x:ℤ) : ℤ):ℂ) := by
    simp
  rw [he,eval_prod] at hv
  simp only [eval_sub,eval_X,eval_C] at hv
  simpa only [Nat.cast_natAbs,Int.cast_abs,Complex.norm_intCast,norm_prod] using
    congrArg (fun z : ℂ => ‖z‖) hv

private theorem eval_bound {I : Type*} [Fintype I] (g : ℤ[X]) (a : I → ℂ)
    (h : g.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i))) (U : ℕ)
    (ha : ∀ i, ‖a i‖ ≤ U) (x : ℕ) : (g.eval (x:ℤ)).natAbs ≤ (x+U)^(Fintype.card I) := by
  have he (i : I) : ‖(x:ℂ)-a i‖ ≤ (x:ℝ)+U := (norm_sub_le ..).trans (by simp [ha i])
  have hh := prod_le_prod (s := univ) (fun i _ => norm_nonneg ((x:ℂ)-a i)) (fun i _ => he i)
  rw [← abs_eval g a h x] at hh
  simpa only [prod_const,card_univ,← Nat.cast_add,← Nat.cast_pow,Nat.cast_le] using hh

theorem bounded_prime_root {I : Type*} [Fintype I] [Nonempty I] (g : ℤ[X]) (a : I → ℂ)
    (h : g.map (Int.castRingHom ℂ) = ∏ i, (X-C (a i))) (U B : ℕ) (hB : 0<B)
    (ha : ∀ i, ‖a i‖ ≤ U) :
    ∃ p ≤ schurBound (Fintype.card I) U B, p.Prime ∧ ¬p ∣ B ∧
      ∃ x : ZMod p, (g.map (Int.castRingHom (ZMod p))).IsRoot x := by
  classical
  let t := U+2
  let c := g.eval (t:ℤ)
  have hpos (i : I) : 0 < ‖(t:ℂ)-a i‖ := by
    have hl := norm_sub_norm_le (t:ℂ) (a i)
    rw [Complex.norm_natCast] at hl
    have ht : (t:ℝ) = U+2 := by simp [t]
    rw [ht] at hl
    linarith [ha i]
  have hc : 0<c.natAbs := by
    have hh : 0 < (c.natAbs:ℝ) := (abs_eval g a h t) ▸ prod_pos (fun i _ => hpos i)
    exact_mod_cast hh
  let j := (2*U+1)*B*c.natAbs^2
  let w := t+j
  have hj : 2*U < j := by
    have h1 : 1 ≤ B*c.natAbs^2 := Nat.one_le_of_lt (Nat.mul_pos hB (pow_pos hc _))
    have := Nat.mul_le_mul_left (2*U+1) h1
    dsimp [j]
    simp only [Nat.mul_one,← mul_assoc] at this
    omega
  have grow (i : I) : ‖(t:ℂ)-a i‖ < ‖(w:ℂ)-a i‖ := by
    have hl := norm_sub_norm_le (w:ℂ) (a i)
    have hu := norm_sub_le (t:ℂ) (a i)
    rw [Complex.norm_natCast] at hu hl
    have hj' : 2*(U:ℝ)<j := by exact_mod_cast hj
    have hw : (w:ℝ) = t+j := by simp [w]
    rw [hw] at hl
    linarith [ha i]
  have hg : c.natAbs < (g.eval (w:ℤ)).natAbs := by
    have hh := prod_lt_prod (s := univ) (fun i _ => hpos i) (fun i _ => (grow i).le)
      ⟨Classical.arbitrary I,mem_univ _,grow _⟩
    rw [← abs_eval g a h t,← abs_eval g a h w] at hh
    exact_mod_cast hh
  obtain ⟨k,hk⟩ := g.sub_dvd_eval_sub (w:ℤ) (t:ℤ)
  let q : ℤ := 1 + ((2*U+1 : ℕ):ℤ) * B * c * k
  have hjz : (j:ℤ) = ((2*U+1 : ℕ):ℤ)*B*c^2 := by simp [j]
  have hv : g.eval (w:ℤ) = c*q := by
    change g.eval (w:ℤ)-c = ((w:ℤ)-(t:ℤ))*k at hk
    have hw : (w:ℤ)-(t:ℤ) = j := by simp [w]
    rw [hw,hjz] at hk
    dsimp only [q]
    push_cast at hk ⊢
    linear_combination hk
  rw [hv,Int.natAbs_mul] at hg
  have hq : 1 < q.natAbs := by by_contra! hh; have := Nat.mul_le_mul_left c.natAbs hh; omega
  obtain ⟨p,hp,hpq⟩ := Nat.exists_prime_and_dvd (ne_of_gt hq)
  have hpz : (p:ℤ) ∣ q := Int.natAbs_dvd_natAbs.mp (by simpa using hpq)
  have havoid : ¬p ∣ B := by
    intro hdiv
    have hb : (p:ℤ) ∣ B := by exact_mod_cast hdiv
    have hx : (p:ℤ) ∣ ((2*U+1 : ℕ):ℤ) * B * c * k := by
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hb _) _) _
    have h1 : (p:ℤ) ∣ 1 := by simpa [q] using dvd_sub hpz hx
    have h2 := Int.natAbs_dvd_natAbs.mpr h1
    simp [hp.not_dvd_one] at h2
  have hroot : (g.map (Int.castRingHom (ZMod p))).IsRoot (w:ZMod p) := by
    unfold IsRoot
    rw [show (w:ZMod p) = Int.castRingHom (ZMod p) (w:ℤ) by simp]
    rw [eval_map_apply,hv]
    exact (CharP.intCast_eq_zero_iff (ZMod p) p _).mpr (dvd_mul_of_dvd_right hpz _)
  have hpval : p ≤ (g.eval (w:ℤ)).natAbs := by
    rw [hv,Int.natAbs_mul]
    exact (Nat.le_of_dvd (by omega) hpq).trans (Nat.le_mul_of_pos_left _ hc)
  have hct : c.natAbs ≤ (2*U+2)^(Fintype.card I) := by
    simpa only [t,show U+2+U = 2*U+2 by omega] using eval_bound g a h U ha t
  refine ⟨p,hpval.trans ((eval_bound g a h U ha w).trans ?_),hp,havoid,_,hroot⟩
  apply Nat.pow_le_pow_left
  change U+2+((2*U+1)*B*c.natAbs^2)+U ≤ _
  have hh := Nat.mul_le_mul_left ((2*U+1)*B) (Nat.pow_le_pow_left hct 2)
  omega

#print axioms bounded_prime_root
end Erdos478.EffectiveResolvent
