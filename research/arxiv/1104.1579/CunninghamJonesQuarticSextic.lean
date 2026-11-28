import CunninghamJonesSexticDiscriminant
import CunninghamJonesFactorOrders
import CunninghamJonesPrimePowerDegrees

/-! Positive constant shifts of the fourth and sixth geometric sums. -/

namespace CunninghamChain
open Polynomial

private lemma sextic_coefficients {a b c d e f m : ℤ}
    (h₅ : c+a=1) (h₄ : d+a*c+b=1) (h₃ : e+a*d+b*c=1)
    (h₂ : f+a*e+b*d=1) (h₁ : a*f+b*e=1) (h₀ : b*f=m) : m=0 := by
  have h : (1-3*a)*b^2 + (4*a^3-3*a^2+2*a-1)*b +
      (1-a+a^2-a^3+a^4-a^5) = 0 := by
    linear_combination -h₁ + a*h₂ + (b-a^2)*h₃ + (a^3-2*a*b)*h₄ +
      (-a^4+3*a^2*b-b^2)*h₅
  rcases JonesSextic.remainder_pairs h with ⟨rfl,rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
    norm_num at h₅ h₄ h₃ h₂ h₁ h₀ <;> omega

private lemma quartic_coefficients {a b c d m : ℤ}
    (h₃ : c+a=1) (h₂ : d+a*c+b=1) (h₁ : a*d+b*c=1) (h₀ : b*d=m) :
    m=0 ∨ m=12 := by
  have hc : c=1-a := by linarith
  subst c
  have hb : b=1+a*(b-d) := by nlinarith
  have hd : d=1+(a-1)*(b-d) := by nlinarith
  have id : (2*a-1)*((2*a-1)-4*(b-d))=5 := by
    linear_combination -4*h₂ + 4*hb + 4*hd
  have hdiv : 2*a-1 ∣ (5:ℤ) := ⟨_,id.symm⟩
  have lim : (2*a-1).natAbs ≤ 5 :=
    Nat.le_of_dvd (by decide) (Int.natAbs_dvd_natAbs.mpr hdiv)
  have absbound : |2*a-1| ≤ 5 := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast lim
  have lower := (abs_le.mp absbound).1
  have upper := (abs_le.mp absbound).2
  have al : -2 ≤ a := by omega
  have au : a ≤ 3 := by omega
  clear id hdiv lim absbound lower upper hb hd
  interval_cases a <;> norm_num at h₂ h₁ <;> first
    | omega
    | have hb' : b=3 ∧ d=4 ∨ b=4 ∧ d=3 ∨ b=0 ∨ d=0 := by omega
      rcases hb' with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | rfl | rfl <;> norm_num at h₀ ⊢ <;> omega

private lemma quadratic_product_row {A B : ℤ[X]} (ha : A.Monic) (da : A.natDegree=2)
    (n : ℕ) :
    (if 2≤n then B.coeff (n-2) else 0) +
      A.coeff 1 * (if 1≤n then B.coeff (n-1) else 0) + A.coeff 0 * B.coeff n =
      (A*B).coeff n := by
  have top : A.coeff 2 = 1 := da ▸ ha.coeff_natDegree
  have shape : A = X^2 + C (A.coeff 1)*X + C (A.coeff 0) := by
    calc A = _ := A.as_sum_range_C_mul_X_pow
         _ = _ := by rw [da]; simp [Finset.sum_range_succ,top]; ring
  have shift : (X*B).coeff n = (if 1≤n then B.coeff (n-1) else 0) := by
    simpa only [pow_one] using (coeff_X_pow_mul' B 1 n)
  conv_rhs => rw [shape]
  simp only [add_mul,coeff_add,mul_assoc,coeff_C_mul,coeff_X_pow_mul',shift]

private lemma low_coefficient (m j n : ℕ) (hn : n ≤ j) :
    (jonesSumPolynomial m j).coeff n = if n=0 then (m:ℤ) else 1 := by
  cases n with
  | zero => simp [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow]
  | succ n =>
    have hi : n < j := by omega
    simp [jonesSumPolynomial,finsetSum_coeff,coeff_X_pow,Finset.mem_range,hi]

private lemma quadratic_split_sextic {A B : ℤ[X]} {m : ℕ}
    (ha : A.Monic) (hb : B.Monic) (da : A.natDegree=2) (db : B.natDegree=4)
    (he : A*B=jonesSumPolynomial m 6) : m=0 := by
  have row (n : ℕ) (hn : n ≤ 6) := (quadratic_product_row ha da (B:=B) n).trans
    ((congrArg (fun P : ℤ[X] => P.coeff n) he).trans (low_coefficient m 6 n hn))
  have top : B.coeff 4 = 1 := db ▸ hb.coeff_natDegree
  have zero : B.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h := sextic_coefficients (a:=A.coeff 1) (b:=A.coeff 0) (c:=B.coeff 3)
    (d:=B.coeff 2) (e:=B.coeff 1) (f:=B.coeff 0) (m:=(m:ℤ))
  suffices (m:ℤ)=0 by exact_mod_cast this
  apply h
  · simpa [top,zero] using row 5 (by decide)
  · simpa [top] using row 4 (by decide)
  · simpa using row 3 (by decide)
  · simpa using row 2 (by decide)
  · simpa using row 1 (by decide)
  · simpa using row 0 (by decide)

private lemma quadratic_split_quartic {A B : ℤ[X]} {m : ℕ}
    (ha : A.Monic) (hb : B.Monic) (da : A.natDegree=2) (db : B.natDegree=2)
    (he : A*B=jonesSumPolynomial m 4) : (m:ℤ)=0 ∨ (m:ℤ)=12 := by
  have row (n : ℕ) (hn : n ≤ 4) := (quadratic_product_row ha da (B:=B) n).trans
    ((congrArg (fun P : ℤ[X] => P.coeff n) he).trans (low_coefficient m 4 n hn))
  have top : B.coeff 2 = 1 := db ▸ hb.coeff_natDegree
  have zero : B.coeff 3 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  apply quartic_coefficients (a:=A.coeff 1) (b:=A.coeff 0) (c:=B.coeff 1) (d:=B.coeff 0)
  · simpa [top,zero] using row 3 (by decide)
  · simpa [top] using row 2 (by decide)
  · simpa using row 1 (by decide)
  · simpa using row 0 (by decide)

private lemma irreducible_small_even {m j : ℕ} (hm : 2 ≤ m) (hj : j=4 ∨ j=6)
    (noSplit : ∀ A B : ℤ[X], A.Monic → B.Monic → A.natDegree=2 →
      B.natDegree=j-2 → A*B=jonesSumPolynomial m j → False) :
    Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  obtain ⟨degree,monic⟩ := jonesSumPolynomial_shape m j
  have H := monic (by omega)
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast H.isPrimitive).mp
  apply H.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at degree; omega, ?_⟩
  intro A B ha hb he
  have sum : A.natDegree+B.natDegree=j := by
    rw [← natDegree_mul ha.ne_zero hb.ne_zero,he,degree]
  have parity : Odd (j+1) := by rcases hj with rfl | rfl <;> decide
  obtain ⟨u,hu⟩ := jones_factor_even_degree hm ha (he ▸ dvd_mul_right _ _) parity
  obtain ⟨v,hv⟩ := jones_factor_even_degree hm hb (he ▸ dvd_mul_left _ _) parity
  by_contra! bad
  have cases : A.natDegree=2 ∨ B.natDegree=2 := by omega
  rcases cases with h | h
  · exact noSplit A B ha hb h (by omega) he
  · exact noSplit B A hb ha h (by omega) ((mul_comm B A).trans he)

/-- Every sextic X⁶+X⁵+X⁴+X³+X²+X+m with positive integer constant m
is irreducible over the rationals. -/
theorem jones_sextic_irreducible {m : ℕ} (hm : 0 < m) :
    Irreducible ((jonesSumPolynomial m 6).map (Int.castRingHom ℚ)) := by
  by_cases h : m=1
  · subst m
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact jones_pred_prime_power_degree_irreducible (p:=7) (a:=1)
      (by decide) (by decide) (by norm_num) (by decide)
  · apply irreducible_small_even (by omega) (Or.inr rfl)
    intro A B ha hb da db prod
    exact (Nat.ne_of_gt hm) (quadratic_split_sextic ha hb da db prod)

/-- Among positive integer constants m, the unique reducible quartic
X⁴+X³+X²+X+m has m=12. -/
theorem jones_quartic_irreducible_iff {m : ℕ} (hm : 0 < m) :
    Irreducible ((jonesSumPolynomial m 4).map (Int.castRingHom ℚ)) ↔ m ≠ 12 := by
  constructor
  · intro irr heq
    subst m
    let A : ℤ[X] := X^2 + C 3*X + C 4
    let B : ℤ[X] := X^2 - C 2*X + C 3
    have da : A.natDegree=2 := by dsimp [A]; compute_degree <;> decide
    have db : B.natDegree=2 := by dsimp [B]; compute_degree <;> decide
    have ha : A.Monic := by dsimp [A]; monicity <;> decide
    have hb : B.Monic := by dsimp [B]; monicity <;> decide
    have prod : A*B=jonesSumPolynomial 12 4 := by
      norm_num [A,B,jonesSumPolynomial,Finset.sum_range_succ]; ring
    have H := (jonesSumPolynomial_shape 12 4).2 (by decide)
    have iz := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast H.isPrimitive).mpr irr
    have either := (H.irreducible_iff_natDegree.mp iz).2 A B ha hb prod
    omega
  · intro h
    by_cases h₁ : m=1
    · subst m
      let : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact jones_pred_prime_power_degree_irreducible (p:=5) (a:=1)
        (by decide) (by decide) (by norm_num) (by decide)
    · apply irreducible_small_even (by omega) (Or.inl rfl)
      intro A B ha hb da db prod
      rcases quadratic_split_quartic ha hb da db prod with hz | ht <;> omega

/-- Degree six in Jones's parameter family, with arbitrary positive parameter. -/
theorem jones_parameter_sextic {t : ℕ} (ht : 0 < t) :
    Irreducible ((jonesSumPolynomial (jonesConstant t) 6).map (Int.castRingHom ℚ)) := by
  apply jones_sextic_irreducible
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have h : 0 < 2^k := by positivity
  simp only [jonesConstant,pow_succ]
  omega

#print axioms jones_parameter_sextic
#print axioms jones_sextic_irreducible
#print axioms jones_quartic_irreducible_iff

end CunninghamChain
