import CunninghamJonesCommonOrder
import CunninghamJonesComplementaryOrders

/-! Prime-power degrees at the fourth parameter of Jones's conjecture. -/

namespace CunninghamChain.JonesFourthDegrees
open Polynomial
open scoped Polynomial

private def OrderWitness (q l b : ℕ) : Prop :=
  let v := l^b
  v ∣ q-1 ∧ ∀ p ∈ ([2,3,19] : List ℕ), npowBinRec ((q-1)/v) (p : ZMod q) ≠ 1

private instance (q l b : ℕ) : Decidable (OrderWitness q l b) := inferInstanceAs (Decidable (_ ∧ _))

/-- A composite candidate can be skipped. A prime candidate needs an order witness. -/
private def accepts (q : ℕ) : Bool :=
  q.minFac != q || (q-1).primeFactorsList.any fun l => decide (OrderWitness q l 1) || decide (OrderWitness q l 2)

-- Blocks keep each kernel evaluation small. They include every candidate below 100000.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem table_block (b : ℕ) (hb : b<27) :
    ∀ i : Fin 125, accepts (30*(125*b+i.val)+29) = true := by
  interval_cases b <;> decide +kernel

private lemma table (i : ℕ) (hi : i<3333) : accepts (30*i+29)=true := by
  have ht := table_block (i/125) (by omega) ⟨i%125, Nat.mod_lt _ (by decide)⟩
  simpa only [Fin.val_mk, Nat.div_add_mod] using ht

private theorem bin_pow {q : ℕ} (p : ZMod q) (n : ℕ) : npowBinRec n p=p^n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ,ih,pow_succ]

private lemma prime_factor_342 {p : ℕ} (hp : p.Prime) (hd : p ∣ 342) :
    p=2 ∨ p=3 ∨ p=19 := by
  change p ∣ 2*3^2*19 at hd
  rcases hp.dvd_mul.mp hd with hx|h
  · rcases hp.dvd_mul.mp hx with h|h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow h)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))

private lemma common_from_check {q l b p : ℕ} (hq : q.Prime) (hl : l.Prime)
    (hlarge : 19<q) (hc : OrderWitness q l b) (hp : p.Prime) (hpm : p ∣ 342) :
    l ∣ orderOf (p : ZMod q) := by
  have hmem : p ∈ [2,3,19] := by rcases prime_factor_342 hp hpm with h|h|h <;> simp [h]
  have hpq : p<q := by rcases prime_factor_342 hp hpm with h|h|h <;> omega
  apply prime_dvd_order_of_modular_power (a:=(q-1)/l^b) (b:=b) hq hl
    (Nat.not_dvd_of_pos_of_lt hp.pos hpq)
  · rw [Nat.div_mul_cancel hc.1]
  · simpa only [bin_pow] using hc.2 p hmem

private theorem power_from_accepts {q : ℕ} (hq : q.Prime) (hlarge : 19<q)
    (ha : accepts q = true) (n : ℕ) :
    Irreducible ((jonesSumPolynomial 342 (q^n)).map (Int.castRingHom ℚ)) := by
  simp only [accepts,hq.minFac_eq, bne_self_eq_false, Bool.false_or,List.any_eq_true,
    Bool.or_eq_true,decide_eq_true_eq] at ha
  obtain ⟨l,hm,hc⟩ := ha
  have hl := Nat.prime_of_mem_primeFactorsList hm
  have hdiv := Nat.dvd_of_mem_primeFactorsList hm
  have hsmall := Nat.le_of_dvd (show 0<q-1 by omega) hdiv
  have hqm : ¬q∣342 := by intro e; rcases prime_factor_342 hq e with e|e|e <;> omega
  apply jones_irreducible_of_common_order (by decide) (Nat.pow_pos hq.pos)
    ((hq.coprime_iff_not_dvd.mpr hqm).symm.pow_right n)
    (fun h => by have := (Nat.prime_dvd_prime_iff_eq hl hq).mp (hl.dvd_of_dvd_pow h); omega)
  intro p hp hpm t ht htd
  have eq := (Nat.prime_dvd_prime_iff_eq ht hq).mp (ht.dvd_of_dvd_pow htd)
  subst t
  rcases hc with h|h <;> exact common_from_check hq hl hlarge h hp hpm

private theorem neg_one_base (q n : ℕ) (h : 30 ∣ q^n+1) : q%30=29 := by
  let x : ZMod 30 := q
  have hn : x^n = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff (q^n+1) 30).mpr h
    push_cast at hz
    change (q : ZMod 30)^n = -1
    linear_combination hz
  have hf : ∀ y : ZMod 30, y^5=y := by decide
  have hor (i : ℕ) : x^(i+1)=x ∨ x^(i+1)=x^2 ∨ x^(i+1)=x^3 ∨ x^(i+1)=x^4 := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ x (i+1)]
      rcases ih with a|a|a|a <;> rw [a]
      · exact Or.inr (Or.inl (by ring))
      · exact Or.inr (Or.inr (Or.inl (by ring)))
      · exact Or.inr (Or.inr (Or.inr (by ring)))
      · exact Or.inl ((pow_succ x 4).symm.trans (hf x))
  have test : ∀ y : ZMod 30, (y= -1 ∨ y^2= -1 ∨ y^3= -1 ∨ y^4= -1) → y=29 := by decide
  have hx : x=29 := by
    cases n with
    | zero => exact False.elim ((by decide : (1 : ZMod 30) ≠ -1) (by simpa using hn))
    | succ i => apply test; simpa only [hn,eq_comm (a := (-1 : ZMod 30))] using hor i
  exact (ZMod.natCast_eq_natCast_iff' q 29 30).mp hx

/-- For the fourth parameter the exponent is unrestricted. Only the prime base is bounded. -/
theorem jones_nine_prime_power_degrees {q : ℕ} (hq : q.Prime) (hb : q<100000)
    (hne : q≠3) (n : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) (q^n)).map (Int.castRingHom ℚ)) := by
  change Irreducible ((jonesSumPolynomial 342 _).map (Int.castRingHom ℚ))
  by_contra hr
  rcases jones_nine_complementary_classes _ (Nat.pow_pos hq.pos) hr with he|he
  · have h3 : (q^n)%3=0 := by omega
    have h := Nat.prime_three.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h3)
    exact hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).mp h).symm
  · have hqmod := neg_one_base q n he
    have heq : 30*(q/30)+29=q := by omega
    have ht := table (q/30) (by omega)
    change accepts (30*(q/30)+29)=true at ht
    rw [heq] at ht
    exact hr (power_from_accepts hq (by omega) ht n)

/-- Every prime degree below the bound is irreducible, including degree three. -/
theorem jones_nine_prime_degrees {q : ℕ} (hq : q.Prime) (hb : q<100000) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) q).map (Int.castRingHom ℚ)) := by
  by_cases he : q=3
  · subst q
    by_contra h
    rcases jones_nine_complementary_classes 3 (by decide) h with e|e <;> revert e <;> decide
  · simpa using jones_nine_prime_power_degrees hq hb he 1

#print axioms jones_nine_prime_power_degrees
#print axioms jones_nine_prime_degrees

/-- The fourth Jones parameter is irreducible throughout a two-prime family of degrees. -/
theorem jones_nine_mixed_59_233 (a b : ℕ) :
    Irreducible ((jonesSumPolynomial (jonesConstant 9) (59^a * 233^b)).map (Int.castRingHom ℚ)) := by
  change Irreducible ((jonesSumPolynomial 342 _).map (Int.castRingHom ℚ))
  have hl : Nat.Prime 29 := by decide
  have hp59 : Nat.Prime 59 := by decide
  have hp233 : Nat.Prime 233 := by norm_num
  apply jones_irreducible_of_common_order (k:=29) (by decide) (by positivity)
    (((by decide : Nat.Coprime 342 59).pow_right a).mul_right ((by decide : Nat.Coprime 342 233).pow_right b))
  · intro h
    rcases hl.dvd_mul.mp h with h|h
    · exact (by decide : ¬29∣59) (hl.dvd_of_dvd_pow h)
    · exact (by decide : ¬29∣233) (hl.dvd_of_dvd_pow h)
  · intro p hp hpm t ht hd
    rcases ht.dvd_mul.mp hd with h|h
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq ht hp59).mp (ht.dvd_of_dvd_pow h)
      exact common_from_check hp59 hl (by decide) (by decide : OrderWitness 59 29 1) hp hpm
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq ht hp233).mp (ht.dvd_of_dvd_pow h)
      exact common_from_check hp233 hl (by decide) (by decide : OrderWitness 233 29 1) hp hpm

#print axioms jones_nine_mixed_59_233

end CunninghamChain.JonesFourthDegrees
