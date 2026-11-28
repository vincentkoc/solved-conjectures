import Erdos478DisjointGapFamilies
import Mathlib.Algebra.Polynomial.Taylor

/-! # Distinct translated factorial-gap polynomials -/

namespace Erdos478.LocalSpacing
open Polynomial Finset

/-- The endpoint is at offset `r` from the start of an interval and the
collision has positive index difference `k`. -/
noncomputable def translatedGap (R : Type*) [CommRing R] (r k : ℕ) : R[X] :=
  taylor (r : R) (descPochhammer R k-1)

theorem translated_degree (R : Type*) [CommRing R] [IsDomain R] (r : ℕ) {k : ℕ} (hk : 0<k) :
    (translatedGap R r k).IsMonicOfDegree k := by
  have h : (descPochhammer R k).IsMonicOfDegree k :=
    ⟨descPochhammer_natDegree R k,monic_descPochhammer R k⟩
  have a : (descPochhammer R k-1).IsMonicOfDegree k := by
    simpa only [sub_eq_add_neg] using h.add_right (q:=-(1:R[X])) (by simpa using hk)
  exact ⟨(natDegree_taylor ..).trans a.natDegree_eq,(leadingCoeff_taylor ..).trans a.monic⟩

theorem translated_irreducible (r : ℕ) {k : ℕ} (hk : 0<k) : Irreducible (translatedGap ℚ r k) :=
  (MulEquiv.irreducible_iff (f:=taylorEquiv (r:ℚ))).mpr (GapFamilies.irreducible_gap_rat hk)

private theorem different_shift {r s k l : ℕ} (hrs : r<s) (hl : 0<l) :
    translatedGap ℚ r k≠translatedGap ℚ s l := by
  intro h
  have eq := congrArg (eval (-(s:ℚ))) h
  simp only [translatedGap,taylor_eval,neg_add_cancel,eval_sub,eval_one,
    sub_left_inj] at eq
  have z := descPochhammer_eval_coe_nat_of_lt (R:=ℚ) (k:=0) hl
  simp only [Nat.cast_zero] at z
  rw [z,descPochhammer_eval_eq_prod_range] at eq
  apply (Finset.prod_ne_zero_iff.mpr ?_) eq
  intro j _
  have hq : (r:ℚ)<s := by exact_mod_cast hrs
  have hj : (0:ℚ)≤j := by positivity
  linarith

theorem translated_distinct {r s k l : ℕ} (hk : 0<k) (hl : 0<l) (h : (r,k)≠(s,l)) :
    translatedGap ℚ r k≠translatedGap ℚ s l := by
  rcases lt_trichotomy r s with hr|rfl|hr
  · exact different_shift hr hl
  · intro eq
    have d := congrArg natDegree eq
    rw [(translated_degree _ _ hk).natDegree_eq,(translated_degree _ _ hl).natDegree_eq] at d
    exact h (congrArg (Prod.mk _) d)
  · exact Ne.symm (different_shift hr hk)

theorem translated_coprime {r s k l : ℕ} (hk : 0<k) (hl : 0<l) (h : (r,k)≠(s,l)) :
    IsCoprime (translatedGap ℚ r k) (translatedGap ℚ s l) := by
  apply (translated_irreducible r hk).coprime_iff_not_dvd.mpr
  intro dv
  apply translated_distinct hk hl h
  exact eq_of_monic_of_associated (translated_degree _ _ hk).monic (translated_degree _ _ hl).monic
    ((translated_irreducible r hk).associated_of_dvd (translated_irreducible s hl) dv)

#print axioms translatedGap
#print axioms translated_degree
#print axioms translated_irreducible
#print axioms translated_distinct
#print axioms translated_coprime
end Erdos478.LocalSpacing
