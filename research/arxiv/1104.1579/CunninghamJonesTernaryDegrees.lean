import CunninghamJonesTernaryMultiplicity
import CunninghamJonesFourthPrimePowers

/-! The missing prime base three and mixed degrees at the fourth Jones parameter. -/

namespace CunninghamChain.JonesFourthDegrees
open Polynomial JonesMultiplicity
open scoped Polynomial

private lemma complementary_dvd {m j : ℕ} (hm : 3 ∣ m) {A B : ℤ[X]}
    (hab : A*B=jonesSumPolynomial m j) (hB : (B.coeff 0:ZMod 3)=0) :
    A.map (Int.castRingHom (ZMod 3)) ∣ X^j-1 := by
  let φ := Int.castRingHom (ZMod 3)
  let G : (ZMod 3)[X] := ∑ i ∈ Finset.range j,X^i
  have hz : φ (m:ℤ)=0 := by simpa [φ] using (ZMod.natCast_eq_zero_iff m 3).mpr hm
  have geom : (jonesSumPolynomial m j).map φ=X*G := by
    simp only [jonesSumPolynomial,Polynomial.map_add,map_C,Polynomial.map_sum,Polynomial.map_mul,
      Polynomial.map_pow,Polynomial.map_X,hz,C_0,zero_add,G,Finset.mul_sum,pow_succ']
  obtain ⟨b,hb⟩ := X_dvd_iff.mpr (show (B.map φ).coeff 0=0 by simpa [coeff_map,φ] using hB)
  rw [←hab,Polynomial.map_mul,hb] at geom
  have hG : A.map φ*b=G := by
    apply mul_left_cancel₀ (X_ne_zero : (X:(ZMod 3)[X])≠0)
    calc
      X*(A.map φ*b) = A.map φ*(X*b) := by ring
      _ = _ := geom
  exact (Dvd.intro _ hG).trans ⟨X-1,(geom_sum_mul X j).symm⟩

private lemma even_degree {m d : ℕ} (hm : 9 ∣ m) (hm' : ¬27 ∣ m) (hd : ¬3 ∣ d)
    (orders : ∀ q : ℕ, q.Prime → q ∣ d → 2 ∣ orderOf (3 : ZMod q)) (n : ℕ)
    {A B : ℤ[X]} (ha : A.Monic) (hb : B.Monic)
    (hab : A*B=jonesSumPolynomial m (3^(n+3)*d)) (hB : (B.coeff 0 : ZMod 3)=0) :
    Even A.natDegree := by
  let φ := Int.castRingHom (ZMod 3)
  let e := (A.map φ).rootMultiplicity 1
  have opts := jones_factor_ternary_multiplicity hm hm' hd n ha hb hab
  change e=0 ∨ e=3^(n+2)-1 ∨ e=2*3^(n+2) ∨ e=3*3^(n+2)-1 at opts
  have odd : Odd (3^(n+2):ℕ) := (show Odd (3:ℕ) by decide).pow
  have he : 2 ∣ e := by obtain ⟨k,hk⟩ := odd; rcases opts with h|h|h|h <;> omega
  obtain ⟨Q,hQ,away⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (A.map φ) (ha.map φ).ne_zero 1
  have hq0 : Q≠0 := by intro h; simp [h] at hQ; exact (ha.map φ).ne_zero hQ
  have dvd := complementary_dvd ((by decide : 3∣9).trans hm) hab hB
  have hQdvd : Q ∣ X^(3^(n+3)*d)-1 := (hQ ▸ dvd_mul_left ..).trans dvd
  have hpos : 0<d := Nat.pos_of_ne_zero fun h => hd (h ▸ dvd_zero _)
  have evenQ := factor_degree_multiple_of_orders (j:=3^(n+3)*d) (k:=2) (p:=3)
    (Nat.mul_pos (by positivity) hpos) (fun q hq h => by
      rcases hq.dvd_mul.mp h with h|h
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)
        rw [show ((3:ℕ):ZMod 3)=0 by decide,orderOf_zero]; exact dvd_zero _
      · exact orders q hq h) hQdvd (fun h => away (dvd_iff_isRoot.mpr h))
  have deg := congrArg natDegree hQ
  rw [ha.natDegree_map,natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hq0,
    natDegree_pow,natDegree_X_sub_C,mul_one] at deg
  change A.natDegree=e+Q.natDegree at deg
  exact even_iff_two_dvd.mpr (deg ▸ dvd_add he evenQ)

private lemma complementary_constant {m j v : ℕ} (hj : 0<j) (oddj : Odd j) (hv : 1<v)
    (h3 : 3 ∣ v) {A B : ℤ[X]} (ha : A.Monic) (hab : A*B=jonesSumPolynomial m j)
    (hb : B.coeff 0=v) (evenA : Even A.natDegree) : (A.coeff 0:ZMod 3)=1 := by
  have H := congrArg (ZMod.castHom h3 (ZMod 3)) (jones_factor_complementary_modulus hj hv ha hab hb)
  simp only [map_pow,map_one,map_intCast,(evenA.mul_right j).neg_one_pow,one_mul] at H
  have cases : ∀ x : ZMod 3, x=0 ∨ x=1 ∨ x= -1 := by decide
  rcases cases (A.coeff 0) with h|h|h
  · rw [h,zero_pow hj.ne'] at H; exact False.elim (zero_ne_one H)
  · exact h
  · rw [h,oddj.neg_one_pow] at H; exact False.elim ((by decide : (-1:ZMod 3)≠1) H)

/-- At constant 342 the fourth Jones polynomial is irreducible at 3^(n+3)d
when d is prime to 3 and every prime q dividing d gives 3 even order modulo q. -/
theorem jones_nine_mixed_ternary_degrees {d : ℕ} (hd : ¬3 ∣ d)
    (orders : ∀ q : ℕ, q.Prime → q ∣ d → 2 ∣ orderOf (3 : ZMod q)) (n : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) (3^(n+3)*d)).map (Int.castRingHom ℚ)) := by
  let j := 3^(n+3)*d
  have hp : 0<d := Nat.pos_of_ne_zero fun h => hd (h ▸ dvd_zero _)
  have hj : 0<j := Nat.mul_pos (by positivity) hp
  have oddD : Odd d := by
    apply Nat.not_even_iff_odd.mp
    intro h
    have bad := orders 2 Nat.prime_two (even_iff_two_dvd.mp h)
    rw [show (3:ZMod 2)=1 by decide,orderOf_one] at bad
    exact (by decide : ¬(2:ℕ)∣1) bad
  have oddj : Odd j := (show Odd (3^(n+3):ℕ) from (show Odd (3:ℕ) by decide).pow).mul oddD
  change Irreducible ((jonesSumPolynomial 342 j).map (Int.castRingHom ℚ))
  obtain ⟨deg,hmon⟩ := jonesSumPolynomial_shape 342 j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun e => by rw [e,natDegree_one] at deg; omega,?_⟩
  intro A B ha hb hab
  by_contra! nonconst
  have pos {P : ℤ[X]} (hP : P.Monic) (div : P ∣ jonesSumPolynomial 342 j)
      (hn : P.natDegree≠0) : 1<P.coeff 0 := by
    have h := jones_factor_constant_gt_one (by decide) hP div (Nat.pos_of_ne_zero hn)
    have hh := (jones_factor_constant_congruence (by decide) hj hP (Nat.pos_of_ne_zero hn) div).1
    omega
  have ac := pos ha (hab ▸ dvd_mul_right ..) nonconst.1
  have bc := pos hb (hab ▸ dvd_mul_left ..) nonconst.2
  have prod : A.coeff 0*B.coeff 0=342 := by
    simpa [mul_coeff_zero,jonesSumPolynomial,finsetSum_coeff,coeff_X_pow] using
      congrArg (fun P : ℤ[X] => P.coeff 0) hab
  have eliminate (P Q : ℤ[X]) (hP : P.Monic) (hQ : Q.Monic)
      (hPQ : P*Q=jonesSumPolynomial 342 j) (hc : 1<P.coeff 0) (hc' : 1<Q.coeff 0)
      (hprod : P.coeff 0*Q.coeff 0=342) (hdeg : Q.natDegree≠0) (h3 : (3:ℤ) ∣ Q.coeff 0) : False := by
    let v := (Q.coeff 0).toNat
    let u := (P.coeff 0).toNat
    have he : Q.coeff 0=(v:ℤ) := by dsimp [v]; omega
    have hu : P.coeff 0=(u:ℤ) := by dsimp [u]; omega
    have hv : 3∣v := Int.natCast_dvd_natCast.mp (he ▸ h3)
    have hdg := even_degree (by decide : 9∣342) (by decide) hd orders n hP hQ hPQ
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h3)
    have residue := complementary_constant hj oddj (by omega : 1<v) hv hP hPQ he hdg
    rw [hu] at residue
    have hur : u%3=1 := (ZMod.natCast_eq_natCast_iff' u 1 3).mp (by simpa using residue)
    rw [hu,he] at hprod
    have uv : u*v=342 := by exact_mod_cast hprod
    have hdu : u ∣ 342 := uv ▸ dvd_mul_right ..
    have tests : ∀ i : Fin 343, 1 < i.val → i.val∣342 → i.val%3=1 → i.val=19 := by decide +kernel
    have u19 := tests ⟨u,by have := Nat.le_of_dvd (by decide : 0<342) hdu; omega⟩ (show 1<u by omega) hdu hur
    change u=19 at u19
    have v18 : v=18 := by rw [u19] at uv; omega
    have H := (jones_factor_constant_congruence (by decide) hj hQ (Nat.pos_of_ne_zero hdeg)
      (hPQ ▸ dvd_mul_left ..)).2
    have H' : (18:ZMod 341)^(j+1)=1 := by simpa [he,v18] using H
    have ho : orderOf (18:ZMod 341)=30 := by
      have test : ∀ i : Fin 30, 0 < i.val → (18:ZMod 341)^i.val≠1 := by decide +kernel
      exact (orderOf_eq_iff (by decide : 0<30)).mpr ⟨by decide,fun i hi => test ⟨i,hi⟩⟩
    have div := ho ▸ orderOf_dvd_of_pow_eq_one H'
    have h3j : 3 ∣ j := (dvd_pow_self 3 (by omega : n+3≠0)).trans (dvd_mul_right ..)
    omega
  have hdprod : (3:ℤ) ∣ A.coeff 0*B.coeff 0 := prod ▸ (by decide : (3:ℤ) ∣ 342)
  rcases (show Prime (3:ℤ) by norm_num).dvd_mul.mp hdprod with h|h
  · exact eliminate B A hb ha ((mul_comm ..).trans hab) bc ac ((mul_comm ..).trans prod) nonconst.1 h
  · exact eliminate A B ha hb hab ac bc prod nonconst.2 h


/-- Each prime-power degree whose base is below 100000 satisfies the
predicted fourth-parameter classification, including powers of three. -/
theorem jones_nine_prime_power_iff {q : ℕ} (hq : q.Prime) (hsmall : q<100000) (b : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) (q^b)).map (Int.castRingHom ℚ)) ↔ q^b≠9 := by
  constructor
  · intro ir eq
    rw [eq] at ir
    have root := (jones_rational_root_iff 9 9 (by decide) (by decide) (by decide) (by decide) (-2)).mpr ⟨rfl,rfl⟩
    apply ir.not_isRoot_of_natDegree_ne_one _ root
    obtain ⟨deg,mon⟩ := jonesSumPolynomial_shape (jonesConstant 9) 9
    rw [(mon (by decide)).natDegree_map,deg]
    decide
  · intro h
    by_cases eq : q=3
    · subst q
      cases b with
      | zero => simpa using jones_nine_prime_power_degrees Nat.prime_two (by decide) (by decide) 0
      | succ b =>
        cases b with
        | zero => simpa using jones_nine_prime_degrees Nat.prime_three (by decide)
        | succ b =>
          cases b with
          | zero => exact False.elim (h rfl)
          | succ b =>
            simpa using jones_nine_mixed_ternary_degrees (d:=1) (by decide)
              (fun p hp hd => False.elim (hp.not_dvd_one hd)) b
    · exact jones_nine_prime_power_degrees hq hsmall eq b

/-- The orders at 7 and 17 have different powers of two. Both primes can
occur with unrestricted exponents in the same degree. -/
theorem jones_nine_ternary_seven_seventeen (n a b : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) (3^(n+3)*(7^a*17^b))).map (Int.castRingHom ℚ)) := by
  have h7 : Nat.Prime 7 := by decide
  have h17 : Nat.Prime 17 := by decide
  apply jones_nine_mixed_ternary_degrees
  · intro h
    rcases Nat.prime_three.dvd_mul.mp h with h|h
    · exact (by decide : ¬3∣7) (Nat.prime_three.dvd_of_dvd_pow h)
    · exact (by decide : ¬3∣17) (Nat.prime_three.dvd_of_dvd_pow h)
  · intro p hp h
    rcases hp.dvd_mul.mp h with h|h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp h7).mp (hp.dvd_of_dvd_pow h)
      exact prime_dvd_order_of_modular_power (a:=3) (b:=1) h7 Nat.prime_two (by decide) (by decide) (by decide)
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp h17).mp (hp.dvd_of_dvd_pow h)
      exact prime_dvd_order_of_modular_power (a:=1) (b:=4) h17 Nat.prime_two (by decide) (by decide) (by decide)

#print axioms jones_nine_prime_power_iff
#print axioms jones_nine_ternary_seven_seventeen

#print axioms jones_nine_mixed_ternary_degrees

end CunninghamChain.JonesFourthDegrees
