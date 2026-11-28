import CunninghamJonesFrobeniusFactors
import CunninghamJonesFactorOrders

/-! Irreducibility of Jones sums in degrees on which a Frobenius power
acts by inversion. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

/-- When p divides the other factor constant and j divides p^h+1, reduction
forces the constant of this factor to be one modulo p. -/
theorem jones_factor_frobenius {p m j h : ℕ} [Fact p.Prime] (hm : p ∣ m)
    (hj : ¬ p ∣ j) (hd : j ∣ p^h+1) {A B : ℤ[X]} (ha : A.Monic)
    (hab : A*B = jonesSumPolynomial m j) (hb : (B.coeff 0 : ZMod p) = 0) :
    (A.coeff 0 : ZMod p) = 1 := by
  let f := Int.castRingHom (ZMod p)
  have hm0 : f (m:ℤ) = 0 := by simpa [f] using (ZMod.natCast_eq_zero_iff m p).mpr hm
  have hj0 : (j : ZMod p) ≠ 0 := fun e => hj ((ZMod.natCast_eq_zero_iff j p).mp e)
  obtain ⟨b,hb'⟩ := X_dvd_iff.mpr (show (B.map f).coeff 0=0 by simpa [coeff_map,f] using hb)
  have hg := jones_geometric_map f m j
  rw [← hab, Polynomial.map_mul, hb', hm0] at hg
  have hc : (A.map f)*((X-1)*b) = X^j-1 := by
    apply mul_left_cancel₀ (X_ne_zero : (X : (ZMod p)[X]) ≠ 0)
    calc
      X*((A.map f)*((X-1)*b)) = (X-1)*(A.map f*(X*b)) := by ring
      _ = _ := hg
      _ = X*(X^j-1) := by simp; ring
  have hdvd : A.map f ∣ X^(p^h+1)-1 :=
    (Dvd.intro _ hc).trans (dvd_pow_sub_one_of_dvd hd)
  have hone : (A.map f).eval 1 ≠ 0 := by
    intro hz
    have hn := congrArg (fun D : ℤ[X] => (D.map f).eval 1) hab
    have hmz := (ZMod.natCast_eq_zero_iff m p).mpr hm
    simp [Polynomial.map_mul,hz,jonesSumPolynomial,eval_finsetSum,hmz] at hn
    exact hj0 hn.symm
  simpa [coeff_map,f] using frobenius_divisor_constant (ha.map f) hdvd hone

/-- When p divides one factor constant, its complementary factor constant divides m/p.
Excluding 1 modulo p among those divisors proves irreducibility. -/
theorem jones_irreducible_of_frobenius {p m j h : ℕ} (hp : p.Prime) (hm : 3 ≤ m)
    (hpm : p ∣ m) (hdeg : j ∣ p^h+1) (hh : 0<h)
    (hco : ∀ d : ℕ, d ∣ m/p → 1<d → d % p ≠ 1) :
    Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hj : 0<j := Nat.pos_of_dvd_of_pos hdeg (by omega)
  have hjp : ¬p ∣ j := by
    intro e
    have one := (Nat.dvd_add_right (dvd_pow_self p hh.ne')).mp (e.trans hdeg)
    exact hp.not_dvd_one one
  obtain ⟨hN,hmon⟩ := jonesSumPolynomial_shape m j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun e => by rw [e, natDegree_one] at hN; omega, ?_⟩
  intro A B ha hb hab
  by_contra! hnon
  have pos (D : ℤ[X]) (hD : D.Monic) (hne : D.natDegree ≠ 0)
      (hd : D ∣ jonesSumPolynomial m j) : 1 < D.coeff 0 := by
    have h₁ := jones_factor_constant_gt_one (by omega) hD hd (Nat.pos_of_ne_zero hne)
    have h₂ := (jones_factor_constant_congruence hm hj hD (Nat.pos_of_ne_zero hne) hd).1
    omega
  let u := (A.coeff 0).toNat
  let v := (B.coeff 0).toNat
  have hA := pos A ha hnon.1 (hab ▸ dvd_mul_right ..)
  have hB := pos B hb hnon.2 (hab ▸ dvd_mul_left ..)
  have hu : A.coeff 0 = (u:ℤ) := by dsimp [u]; omega
  have hv : B.coeff 0 = (v:ℤ) := by dsimp [v]; omega
  have uv : u*v=m := by
    have e := congrArg (fun D : ℤ[X] => D.coeff 0) hab
    simp [mul_coeff_zero,jonesSumPolynomial,finsetSum_coeff,coeff_X_pow,hu,hv] at e
    exact_mod_cast e
  have rule {a b : ℤ[X]} {s t : ℕ} (ha' : a.Monic) (hab' : a*b=jonesSumPolynomial m j)
      (hs : a.coeff 0=(s:ℤ)) (ht : b.coeff 0=(t:ℤ)) (hgt : 1<s) (he : s*t=m)
      (htp : p∣t) : False := by
    have z := (ZMod.natCast_eq_zero_iff t p).mpr htp
    have res := jones_factor_frobenius hpm hjp hdeg ha' hab'
      (by simpa [ht] using z)
    rw [hs,Int.cast_natCast] at res
    have eq : s ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff s 1 p).mp (by simpa using res)
    obtain ⟨k,hk⟩ := htp
    have hd : s ∣ m/p := by
      refine ⟨k,?_⟩
      rw [← he, hk, show s*(p*k)=p*(s*k) by ring, Nat.mul_div_cancel_left _ hp.pos]
    exact hco s hd hgt (by simpa [Nat.ModEq,Nat.mod_eq_of_lt hp.one_lt] using eq)
  rcases hp.dvd_mul.mp (uv ▸ hpm) with e | e
  · exact rule hb ((mul_comm _ _).trans hab) hv hu (by omega) ((Nat.mul_comm ..).trans uv) e
  · exact rule ha hab hu hv (by omega) uv e


/-- Inversion modulo an odd integer d lifts to every divisor of every power
of d. The geometric sum contributes a further factor d at each step. -/
private theorem lift_inversion {d a : ℕ} (hd : Odd d) (ha : d ∣ a+1) (r : ℕ) :
    d^r ∣ a^(d^r)+1 := by
  have hza : -(a : ZMod d)=1 := by
    have eq := (ZMod.natCast_eq_zero_iff (a+1) d).mpr ha
    push_cast at eq
    linear_combination -eq
  have base (k : ℕ) : (d:ℤ)^k ∣ (-(a:ℤ))^(d^k)-1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      let v := (-(a:ℤ))^(d^k)
      have hs : (d:ℤ) ∣ ∑ i ∈ Finset.range d, v^i := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).mp
        simp [v,hza]
      rw [pow_succ d k,pow_succ (d:ℤ) k,pow_mul,← mul_geom_sum]
      exact mul_dvd_mul ih hs
  have eq : (-(a:ℤ))^(d^r)-1 = -((a:ℤ)^(d^r)+1) := by rw [(show Odd (d^r) from hd.pow).neg_pow]; ring
  have hh := base r
  rw [eq,dvd_neg] at hh
  exact_mod_cast hh

/-- At the fourth Jones parameter m=342, every divisor of 19^h+1 with
positive h gives an irreducible polynomial. -/
theorem jones_nine_frobenius_degree {j h : ℕ} (hd : j ∣ 19^h+1) (hh : 0<h) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) j).map (Int.castRingHom ℚ)) := by
  change Irreducible ((jonesSumPolynomial 342 j).map _)
  apply jones_irreducible_of_frobenius (by decide : Nat.Prime 19) (by decide) (by decide) hd hh
  intro d hd' hgt
  have bound := Nat.le_of_dvd (by decide : 0<342/19) hd'
  norm_num at bound
  rw [Nat.mod_eq_of_lt (by omega : d<19)]
  omega

/-- A single inversion test for an odd d covers all degrees dividing
arbitrary powers of d, including degrees formed from different primes. -/
theorem jones_nine_frobenius_power_divisors {j d h r : ℕ} (ho : Odd d)
    (he : d ∣ 19^h+1) (hh : 0<h) (hd : j ∣ d^r) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) j).map (Int.castRingHom ℚ)) := by
  have hl := lift_inversion ho he r
  rw [←pow_mul] at hl
  exact jones_nine_frobenius_degree (hd.trans hl) (Nat.mul_pos hh (Nat.pow_pos ho.pos))

/-- The fourth parameter is irreducible throughout the mixed degree family
13^a·29^b. In particular, odd powers of 29 meet all three classes
29, 59, 89 modulo 90 that survived the complementary order sieve. -/
theorem jones_nine_thirteen_twentynine (a b : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) (13^a*29^b)).map (Int.castRingHom ℚ)) := by
  apply jones_nine_frobenius_power_divisors (d:=377) (h:=42) (r:=a+b)
    (by decide) (by decide) (by decide)
  refine ⟨13^b*29^a,?_⟩
  rw [show 377=13*29 by decide,mul_pow,pow_add,pow_add]
  ring

#print axioms jones_nine_frobenius_degree
#print axioms jones_nine_frobenius_power_divisors
#print axioms jones_nine_thirteen_twentynine

#print axioms jones_factor_frobenius
#print axioms jones_irreducible_of_frobenius

end CunninghamChain
