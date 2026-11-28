import CunninghamJonesOrderDegrees
import CunninghamJonesFactorOrders

/-! An irreducibility criterion from component degrees of reduced Jones
factors. It applies to composite degrees as well as prime powers. -/

namespace CunninghamChain
open Polynomial
open scoped Polynomial

/-- If p divides the constant of B, the reduction of the complementary
factor A divides the geometric sum 1+X+⋯+X^(j−1). Its component degrees
reflect the orders of p at primes dividing j. -/
theorem jones_complementary_factor_degree {p m j k : ℕ} [Fact p.Prime]
    (hj : 0 < j) (hm : p ∣ m) (hpj : ¬ p ∣ j)
    (orders : ∀ q : ℕ, q.Prime → q ∣ j → k ∣ orderOf (p : ZMod q))
    {A B : ℤ[X]} (ha : A.Monic) (hab : A*B=jonesSumPolynomial m j)
    (hb : (B.coeff 0 : ZMod p)=0) : k ∣ A.natDegree := by
  let f := Int.castRingHom (ZMod p)
  let G : (ZMod p)[X] := ∑ i ∈ Finset.range j, X^i
  have hm0 : f (m:ℤ)=0 := by simpa [f] using (ZMod.natCast_eq_zero_iff m p).mpr hm
  have geom : (jonesSumPolynomial m j).map f=X*G := by
    simp only [jonesSumPolynomial,Polynomial.map_add,map_C,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_X,hm0,C_0,zero_add,G,Finset.mul_sum,pow_succ']
  obtain ⟨b,hb'⟩ := X_dvd_iff.mpr (show (B.map f).coeff 0=0 by simpa [coeff_map,f] using hb)
  rw [←hab,Polynomial.map_mul,hb'] at geom
  have hG : A.map f*b=G := by
    apply mul_left_cancel₀ (X_ne_zero : (X:(ZMod p)[X])≠0)
    calc
      X*(A.map f*b) = A.map f*(X*b) := by ring
      _ = _ := geom
  have hgeom : G ∣ X^j-1 := ⟨X-1,(geom_sum_mul X j).symm⟩
  have h1 : (A.map f).eval 1 ≠ 0 := by
    intro z
    have he := congrArg (fun g : (ZMod p)[X] => g.eval 1) hG
    have he' : (j:ZMod p)=0 := by simpa [G,eval_finsetSum,z] using he.symm
    exact hpj ((ZMod.natCast_eq_zero_iff ..).mp he')
  simpa only [ha.natDegree_map] using
    factor_degree_multiple_of_orders hj orders ((Dvd.intro _ hG).trans hgeom) h1

/-- When all coefficient-prime and degree-prime pairs have a common order
divisor k which does not divide j, a nontrivial rational split is impossible. -/
theorem jones_irreducible_of_common_order {m j k : ℕ} (hm : 2 ≤ m) (hj : 0<j)
    (hc : m.Coprime j) (hk : ¬ k ∣ j)
    (orders : ∀ p : ℕ, p.Prime → p ∣ m → ∀ q : ℕ, q.Prime → q ∣ j →
      k ∣ orderOf (p : ZMod q)) :
    Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  obtain ⟨hN,hmon⟩ := jonesSumPolynomial_shape m j
  have mon := hmon hj
  apply (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp
  apply mon.irreducible_iff_natDegree.mpr
  refine ⟨fun e => by rw [e,natDegree_one] at hN; omega,?_⟩
  intro A B ha hb hab
  by_contra! nonconst
  have side {a b : ℤ[X]} (ha' : a.Monic) (hb' : b.Monic) (h : a*b=jonesSumPolynomial m j)
      (hd : b.natDegree≠0) : k ∣ a.natDegree := by
    have hsize := jones_factor_constant_gt_one hm hb' (h ▸ dvd_mul_left ..) (Nat.pos_of_ne_zero hd)
    obtain ⟨p,hp,hpb⟩ := Nat.exists_prime_and_dvd (by omega : (b.coeff 0).natAbs≠1)
    have eq : a.coeff 0 * b.coeff 0 = (m:ℤ) := by
      simpa [mul_coeff_zero,jonesSumPolynomial,finsetSum_coeff,coeff_X_pow] using
        congrArg (fun D : ℤ[X] => D.coeff 0) h
    have prod : (a.coeff 0).natAbs*(b.coeff 0).natAbs=m := by simpa [Int.natAbs_mul] using congrArg Int.natAbs eq
    have hpm : p ∣ m := prod ▸ dvd_mul_of_dvd_right hpb _
    have hpj : ¬p ∣ j := fun he => (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,hpm,he⟩) hc
    let : Fact p.Prime := ⟨hp⟩
    apply jones_complementary_factor_degree hj hpm hpj (orders p hp hpm) ha' h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hpb))
  have deg : A.natDegree+B.natDegree=j := by
    simpa only [ha.natDegree_mul hb,hN] using congrArg natDegree hab
  apply hk
  rw [←deg]
  exact dvd_add (side ha hb hab nonconst.2) (side hb ha ((mul_comm ..).trans hab) nonconst.1)


/-- Removing a prime-power factor of a known multiple of the group order
gives a modular exponentiation certificate for divisibility of the order. -/
theorem prime_dvd_order_of_modular_power {p q l a b : ℕ} (hq : q.Prime) (hl : l.Prime)
    (hp : ¬ q ∣ p) (hc : q-1 ∣ a*l^b) (ht : (p : ZMod q)^a ≠ 1) :
    l ∣ orderOf (p : ZMod q) := by
  let : Fact q.Prime := ⟨hq⟩
  have hn : (p:ZMod q) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hp
  have horder := (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hn)).trans hc
  by_contra bad
  have hp' := (hl.coprime_iff_not_dvd.mpr bad).symm.pow_right b
  exact ht (orderOf_dvd_iff_pow_eq_one.mp (hp'.dvd_mul_right.mp horder))

/-- For a safe prime q=2l+1, every power of q gives an irreducible Jones
sum when every prime factor of m is strictly between 1 and q−1. -/
theorem jones_safe_prime_power_degrees {m q l : ℕ} (hm : 2 ≤ m) (hq : q.Prime)
    (hl : l.Prime) (hs : q=2*l+1)
    (hsize : ∀ p : ℕ, p.Prime → p ∣ m → p+1<q) (b : ℕ) :
    Irreducible ((jonesSumPolynomial m (q^b)).map (Int.castRingHom ℚ)) := by
  have hqm : ¬q ∣ m := fun h => by have := hsize q hq h; omega
  have hlq : ¬l ∣ q := fun h => by
    have eq := (Nat.prime_dvd_prime_iff_eq hl hq).mp h
    omega
  apply jones_irreducible_of_common_order hm (Nat.pow_pos hq.pos)
    ((hq.coprime_iff_not_dvd.mpr hqm).symm.pow_right b)
    (fun h => hlq (hl.dvd_of_dvd_pow h))
  intro p hp hpm t ht htb
  have eq := (Nat.prime_dvd_prime_iff_eq ht hq).mp (ht.dvd_of_dvd_pow htb)
  subst t
  have lt := hsize p hp hpm
  have hqp : ¬q ∣ p := Nat.not_dvd_of_pos_of_lt hp.pos (by omega)
  apply prime_dvd_order_of_modular_power (a:=2) (b:=1) hq hl hqp
  · simp [hs]
  let : Fact q.Prime := ⟨hq⟩
  intro hone
  rcases sq_eq_one_iff.mp hone with he|he
  · have hnat := (ZMod.natCast_eq_natCast_iff' p 1 q).mp (by simpa using he)
    rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt hq.one_lt] at hnat
    exact hp.ne_one hnat
  · have hz : ((p+1:ℕ):ZMod q)=0 := by push_cast; rw [he,neg_add_cancel]
    exact (Nat.not_dvd_of_pos_of_lt (by omega) lt) ((ZMod.natCast_eq_zero_iff ..).mp hz)

#print axioms prime_dvd_order_of_modular_power
#print axioms jones_safe_prime_power_degrees

#print axioms jones_complementary_factor_degree
#print axioms jones_irreducible_of_common_order

end CunninghamChain
