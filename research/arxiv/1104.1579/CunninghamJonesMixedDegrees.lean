import CunninghamJonesDyadicDegrees

/-! Irreducibility from the powers of two different primes in consecutive degrees. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

private theorem factor_degree_of_dyadic_divisor {m a j : ℕ} (hm : m%4=2) (hj : 0 < j)
    (hD : 2^a ∣ j) {A : ℤ[X]} (ha : A.Monic) (hd : A ∣ jonesSumPolynomial m j) :
    2^a ∣ A.natDegree := by
  obtain ⟨v,hv⟩ := hD
  have hv₀ : v≠0 := by rintro rfl; simp_all
  obtain ⟨r,d,ho,hf⟩ := Nat.exists_eq_two_pow_mul_odd hv₀
  have he : j=2^(a+r)*d := by rw [hv,hf,pow_add,mul_assoc]
  rw [he] at hd
  exact (pow_dvd_pow 2 (by omega : a ≤ a+r)).trans (jones_dyadic_factor_degree hm ho ha hd)

/-- The prime-power constraints at j and j+1 rule out both nonconstant factors. -/
theorem jones_mixed_degree_irreducible {q m a b d j : ℕ} [Fact q.Prime] (hq : Odd q)
    (hm : m%4=2) (hj : 0 < j) (hD : 2^a ∣ j) (he : j+1=q^b*d)
    (hp : q ∣ m-1) (hv : ¬q^2 ∣ m-1) (hd : ¬q ∣ d) (hs : ¬q^2 ∣ m+j)
    (hsize : j ≤ 2^a*q^b) : Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hdeg,hmon⟩ := jonesSumPolynomial_shape m j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun h => by rw [h,natDegree_one] at hdeg; omega,?_⟩
  intro A B ha hb eqn
  have hA := factor_degree_of_dyadic_divisor hm hj hD ha (eqn ▸ dvd_mul_right ..)
  have hB := factor_degree_of_dyadic_divisor hm hj hD hb (eqn ▸ dvd_mul_left ..)
  have hsum : A.natDegree+B.natDegree=j := by rwa [←eqn,natDegree_mul ha.ne_zero hb.ne_zero] at hdeg
  have cop := (hq.coprime_two_left.pow_left a).pow_right b
  have large {e : ℕ} (h₁ : 2^a ∣ e) (h₂ : q^b ∣ e) (hz : 0 < e) : j ≤ e :=
    hsize.trans (Nat.le_of_dvd hz (cop.mul_dvd_of_dvd_of_dvd h₁ h₂))
  rcases jones_predecessor_factor_degree (by omega : 1 ≤ m) hp hv hd hs he ha hb eqn with h|h
  · by_cases h₀ : A.natDegree=0
    · exact Or.inl h₀
    · have := large hA h (by omega); right; omega
  · by_cases h₀ : B.natDegree=0
    · exact Or.inr h₀
    · have := large hB h (by omega); left; omega

/-- For every coefficient in the criterion, arbitrarily large multipliers
coprime to q each give an entire arithmetic progression of exponents. -/
theorem jones_unbounded_mixed_multipliers {q m : ℕ} [Fact q.Prime] (hq : Odd q)
    (hm : m%4=2) (hp : q ∣ m-1) (hv : ¬q^2 ∣ m-1) (R : ℕ) :
    ∃ s L : ℕ, R < s ∧ 1 < s ∧ ¬q ∣ s ∧ 0 < L ∧ ∀ k : ℕ,
      Irreducible ((jonesSumPolynomial m (s*q^(L*(k+1)+1)-1)).map (Int.castRingHom ℚ)) := by
  have hq' := (Fact.out : q.Prime).two_le
  have hφ := Nat.totient_pos.mpr (by positivity : 0 < q^2)
  let a := (q^2).totient*(2*R+4)
  let D := 2^a
  have hD : 2*R+4 < D := by
    have hle : 2*R+4 ≤ a := by
      dsimp [a]; simpa using Nat.mul_le_mul_right (2*R+4) hφ
    exact hle.trans_lt Nat.lt_two_pow_self
  have ret : D ≡ 1 [MOD q^2] := by
    dsimp [D,a]; rw [pow_mul]
    simpa only [one_pow] using (Nat.ModEq.pow_totient (hq.coprime_two_left.pow_right 2)).pow (2*R+4)
  obtain ⟨z,hz⟩ := (Nat.modEq_iff_dvd' (by omega : 1 ≤ D)).mp ret.symm
  have hDz : D=1+q^2*z := by omega
  have hz₀ : 0 < z := by
    by_contra! e
    have hz' : z=0 := by omega
    rw [hz',mul_zero,add_zero] at hDz
    omega
  let s := 1+q*((q-1)*z)
  have hq₁ : q-1+1=q := by omega
  have hdiff : s+q*z = D := by dsimp [s]; rw [hDz]; nlinarith only [congrArg (fun n => q*z*n) hq₁]
  have hpos : 1 < s := by
    dsimp [s]
    have := Nat.mul_pos (by omega : 0<q) (Nat.mul_pos (by omega : 0<q-1) hz₀)
    omega
  have hsD : s < D := by
    have := Nat.mul_pos (by omega : 0<q) hz₀
    omega
  have hRs : R < s := by
    have hle := Nat.mul_le_mul_left (q*z) (show 1 ≤ q-1 by omega)
    dsimp [s] at *
    nlinarith only [hD,hdiff,hle]
  have hs : ¬q ∣ s := by
    intro hs
    exact (Fact.out : q.Prime).not_dvd_one
      ((Nat.dvd_add_iff_left (dvd_mul_right q ((q-1)*z))).mpr hs)
  have hid : s*q=1+(q-1)*D := by
    dsimp [s]; rw [hDz]; nlinarith only [hq₁]
  have hL := Nat.totient_pos.mpr (by omega : 0<D)
  refine ⟨s,D.totient,hRs,hpos,hs,hL,?_⟩
  intro k
  let b := D.totient*(k+1)+1
  let Q := q^b
  have hb : 2 ≤ b := by
    dsimp [b]
    have := Nat.mul_pos hL (show 0 < k+1 by omega)
    omega
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have modQ : Q ≡ q [MOD D] := by
    dsimp [Q,b]; rw [pow_succ,pow_mul]
    simpa only [one_pow,one_mul] using
      ((Nat.ModEq.pow_totient (hq.coprime_two_right.pow_right a)).pow (k+1)).mul_right q
  have hprod : 1 < s*Q := lt_of_lt_of_le hpos (Nat.le_mul_of_pos_right s hQ)
  have hj : 1 ≡ s*Q [MOD D] := by
    refine (modQ.mul_left s).trans ?_ |>.symm
    rw [hid]
    simp [Nat.ModEq]
  have hDdvd := (Nat.modEq_iff_dvd' (show 1 ≤ s*Q by omega)).mp hj
  have hsQ : q^2 ∣ s*Q := dvd_mul_of_dvd_right (pow_dvd_pow q hb) s
  have hsval : ¬q^2 ∣ m+(s*Q-1) := by
    have hm₀ : 1 ≤ m := by omega
    rw [show m+(s*Q-1)=(m-1)+s*Q by omega]
    exact fun e => hv ((Nat.dvd_add_iff_left hsQ).mpr e)
  apply jones_mixed_degree_irreducible (q:=q) (a:=a) (b:=b) (d:=s) (j:=s*Q-1)
    hq hm (by omega) hDdvd
    (by change s*Q-1+1=Q*s; rw [mul_comm Q s]; omega)
    hp hv hs hsval
  exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right Q hsD.le)

#print axioms jones_unbounded_mixed_multipliers

/-- One Cartesian family of Jones parameters and degrees with two distinct prime
divisors in j+1. Both indices range independently. -/
theorem jones_seven_mixed_family (u v : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant (42*u+5)) (3*7^(2*v+3)-1)).map
      (Int.castRingHom ℚ)) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let m := jonesConstant (42*u+5)
  let Q := 7^(2*v+3)
  have hpow : 2^(42*u+5) ≡ 32 [MOD 147] := by
    rw [pow_add,pow_mul]
    have h : 2^42 ≡ 1 [MOD 147] := by decide
    rw [show (2:ℕ)^5=32 by decide]
    simpa only [one_pow,one_mul] using (h.pow u).mul_right 32
  change 2^(42*u+5)%147=32 at hpow
  have hm : m=2*((2^(42*u+5)+1)/3) := rfl
  have h4 : m%4=2 := by
    have h₄ : 4 ∣ 2^(42*u+5) := ⟨2^(42*u+3),by rw [show 42*u+5=(42*u+3)+2 by omega,pow_add]; ring⟩
    have h₃ : 3 ∣ 2^(42*u+5)+1 := by omega
    omega
  have hm₄₉ : m%49=22 := by omega
  have hQ : Q ≡ 3 [MOD 4] := by
    have h : 7^2 ≡ 1 [MOD 4] := by decide
    change 7^(2*v+3) ≡ 3 [MOD 4]
    rw [pow_add,pow_mul]
    exact (show (7^2)^v*7^3 ≡ 7^3 [MOD 4] by simpa only [one_pow,one_mul] using (h.pow v).mul_right (7^3)).trans (by decide)
  change Q%4=3 at hQ
  have h₄₉ : 49 ∣ Q := by
    exact pow_dvd_pow 7 (by omega : 2 ≤ 2*v+3)
  have hpos : 0 < Q := by dsimp [Q]; positivity
  apply jones_mixed_degree_irreducible (m:=m) (j:=3*Q-1) (q:=7) (a:=2) (b:=2*v+3) (d:=3)
    (by decide) h4 (by omega) (by change 4 ∣ 3*Q-1; omega) (by change 3*Q-1+1=Q*3; omega)
    (by omega) (by change ¬49 ∣ m-1; omega) (by decide) (by change ¬49 ∣ m+(3*Q-1); omega)
  change 3*Q-1 ≤ 2^2*Q
  omega

#print axioms jones_mixed_degree_irreducible
#print axioms jones_seven_mixed_family

end CunninghamChain
