import research.arxiv.«1104.1579».CunninghamJonesComplementaryOrders
import Mathlib.NumberTheory.Multiplicity

/-! Degree divisibility for reducible Jones sums with a powered constant term. -/

namespace CunninghamChain

private lemma power_order_lift {a p k N : ℕ} (ha : 1 < a) (hp : p.Prime)
    (hc : a.Coprime p) (he : a^(2*N) ≡ 1 [MOD p^k]) :
    p^k ∣ (a^(2*(p-1))-1)*(2*N) := by
  have hpos (e : ℕ) : 1 ≤ a^e := Nat.one_le_pow _ _ (by omega)
  have hn : ¬p ∣ a := hp.coprime_iff_not_dvd.mp hc.symm
  by_cases htwo : p=2
  · subst p
    have hdiff : 2 ∣ a-1 := by omega
    have hd := (Nat.modEq_iff_dvd' (hpos _)).mp he.symm
    have hv := Nat.two_pow_sub_pow (y:=1) hdiff hn (even_two_mul N)
    simp only [one_pow] at hv
    have heq : (a+1)*(a-1)=a^2-1 := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.add_mul, Nat.one_mul, ←sq]
      omega
    norm_num
    rw [←heq,pow_dvd_iff_le_emultiplicity,emultiplicity_mul Nat.prime_two.prime,
      emultiplicity_mul Nat.prime_two.prime,←hv]
    exact (pow_dvd_iff_le_emultiplicity.mp hd).trans (le_self_add)
  · let X := a^(2*(p-1))
    have hf : a^(p-1) ≡ 1 [MOD p] := by simpa [Nat.totient_prime hp] using Nat.ModEq.pow_totient hc
    have hx : p ∣ X-1 := by
      apply (Nat.modEq_iff_dvd' (hpos _)).mp
      simpa [X,show 2*(p-1)=(p-1)*2 by omega,pow_mul] using (hf.pow 2).symm
    have hX : ¬p ∣ X := fun h => hn (hp.dvd_of_dvd_pow h)
    have hm : X^N ≡ 1 [MOD p^k] := by
      have hpow := he.pow (p-1)
      simpa only [X,←pow_mul,one_pow,show 2*N*(p-1)=2*(p-1)*N by ring] using hpow
    have hd := (Nat.modEq_iff_dvd' (Nat.one_le_pow N X (hpos _))).mp hm.symm
    have hv := Nat.emultiplicity_pow_sub_pow hp (hp.odd_of_ne_two htwo) hx hX N
    simp only [one_pow] at hv
    have hl : p^k ∣ (X-1)*N := by
      rw [pow_dvd_iff_le_emultiplicity,emultiplicity_mul hp.prime,←hv]
      exact pow_dvd_iff_le_emultiplicity.mp hd
    exact hl.trans (mul_dvd_mul_left _ (dvd_mul_left ..))

/-- A common multiple for the constants that occur in lifting complementary
factor orders. It depends only on the original base. -/
def jonesOrderMultiple (m : ℕ) : ℕ := 2 * (m^(2*m)).factorial

private lemma complementary_power_dvd {m a b h j p k : ℕ} (ha : 1<a) (hb : 1<b)
    (hab : a*b=m) (hp : p.Prime) (hk : 0<k) (hc : (a^h).Coprime (b^h))
    (hh : 0<h) (hd : p^k ∣ b^h) (hs : (((a^h : ℕ) : ZMod (b^h))^2)^j=1) :
    p^k ∣ jonesOrderMultiple m * h * j := by
  have hpb : p ∣ b := hp.dvd_of_dvd_pow ((dvd_pow_self p hk.ne').trans hd)
  have hca : a.Coprime b := (hc.of_dvd_left (dvd_pow_self a hh.ne')).of_dvd_right
    (dvd_pow_self b hh.ne')
  have hap : a.Coprime p := hca.of_dvd_right hpb
  have ham : a ≤ m := Nat.le_of_dvd (by rw [←hab]; positivity) (hab ▸ dvd_mul_right ..)
  have hpm : p ≤ m := Nat.le_of_dvd (by rw [←hab]; positivity) (hab ▸ hpb.trans (dvd_mul_left ..))
  have he : a^(2*(h*j)) ≡ 1 [MOD b^h] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa only [Nat.cast_pow,Nat.cast_one,←pow_mul,show h*2*j=2*(h*j) by ring] using hs
  have hl := power_order_lift ha hp hap (he.of_dvd hd)
  have small : a^(2*(p-1))-1 ∣ (m^(2*m)).factorial := by
    apply Nat.dvd_factorial
    · have := hp.two_le
      have := Nat.one_lt_pow (by omega : 2*(p-1) ≠ 0) ha
      omega
    · exact (Nat.sub_le _ _).trans ((Nat.pow_le_pow_left ham _).trans
        (Nat.pow_le_pow_right (by omega) (by omega)))
  refine hl.trans ?_
  simpa only [jonesOrderMultiple,mul_assoc,mul_left_comm,mul_comm] using
    mul_dvd_mul_right small (2*(h*j))

/-- Reducibility in degree j with coefficient m^h forces exponential divisibility
of the product h*j, uniformly over all positive exponents. -/
theorem jones_powered_coefficient_dvd {m h j : ℕ} (hm : 2 ≤ m) (hh : 0<h) (hj : 0<j)
    (hred : ¬Irreducible ((jonesSumPolynomial (m^h) j).map (Int.castRingHom ℚ))) :
    m^h ∣ jonesOrderMultiple m * h * j := by
  by_cases hm3 : 3 ≤ m^h
  · obtain ⟨u,v,hu,hv,huv,hc,h₁,h₂⟩ := jones_reducible_constant_split hm3 hj hred
    have unit {x y : ℕ} (hxy : x.Coprime y) : IsUnit (GCDMonoid.gcd x y) := by
      change IsUnit (x.gcd y)
      simp [hxy.gcd_eq_one]
    obtain ⟨a,rfl⟩ := exists_eq_pow_of_mul_eq_pow (unit hc) huv
    obtain ⟨b,rfl⟩ := exists_eq_pow_of_mul_eq_pow (unit hc.symm) ((Nat.mul_comm ..).trans huv)
    have hab : a*b=m := Nat.pow_left_injective hh.ne' (by simpa only [mul_pow] using huv)
    have gt (x : ℕ) (hx : 1 < x^h) : 1 < x := by
      by_contra! hn
      exact (not_lt_of_ge (show x^h ≤ 1 by simpa using Nat.pow_le_pow_left hn h)) hx
    apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
    intro p k hp hd
    rcases Nat.eq_zero_or_pos k with rfl|hk
    · simp
    have hs := (hc.isPrimePow_dvd_mul ((isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,rfl⟩)).mp (huv ▸ hd)
    rcases hs with hl|hr
    · exact complementary_power_dvd (gt _ hv) (gt _ hu) ((Nat.mul_comm ..).trans hab)
        hp hk hc.symm hh hl h₂
    · exact complementary_power_dvd (gt _ hu) (gt _ hv) hab hp hk hc hh hr h₁
  · have := Nat.one_lt_pow hh.ne' (show 1 < m by omega)
    rw [show m^h=2 by omega]
    exact ((dvd_mul_right 2 _).trans (dvd_mul_right _ h)).trans (dvd_mul_right _ j)

private lemma remove_exponent_factor {m C h j k : ℕ} (hm : 0 < m) (hC : 0 < C)
    (hh : 0<h) (hj : 0<j) (hd : m^h ∣ C*h*j) (hlarge : 2*(C+k) ≤ h) : m^k ∣ j := by
  apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ hm.ne') hj.ne').mp
  intro p hp
  have hv := (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ hm.ne')
    (by positivity)).mpr hd p hp
  simp only [Nat.factorization_mul (by positivity : C*h≠0) hj.ne',
    Nat.factorization_mul hC.ne' hh.ne',Finsupp.add_apply,Nat.factorization_pow,
    Finsupp.smul_apply,smul_eq_mul] at hv ⊢
  by_cases hz : m.factorization p=0
  · simp [hz]
  have half (n : ℕ) : 2*n ≤ 2^n := by
    cases n with
    | zero => decide
    | succ n =>
      have hn : n+1 ≤ 2^n := Nat.lt_two_pow_self
      simpa only [pow_succ, Nat.mul_comm 2 (n+1)] using Nat.mul_le_mul_right 2 hn
  have hhval : 2*h.factorization p ≤ h := (half _).trans
    ((Nat.pow_le_pow_left hp.two_le _).trans (Nat.ordProj_le p hh.ne'))
  have hcv := Nat.factorization_lt p hC.ne'
  have hdiff : C+h.factorization p ≤ h-k := by omega
  have hmul := Nat.mul_le_mul_left (h-k) (show 1 ≤ m.factorization p by omega)
  have heq : h-k+k=h := by omega
  have hsum := congrArg (fun x : ℕ => x*m.factorization p) heq
  simp only [Nat.add_mul] at hsum
  omega

/-- For every prescribed power of the base, all sufficiently large exceptional
degrees are multiples of that power, uniformly in the varying exponent. -/
theorem jones_powered_exceptional_degrees {m : ℕ} (hm : 2 ≤ m) (k : ℕ) :
    ∃ D : ℕ, ∀ j ≥ D, ∀ h : ℕ, 0<h →
      ¬Irreducible ((jonesSumPolynomial (m^h) j).map (Int.castRingHom ℚ)) → m^k ∣ j := by
  let H := 2*(jonesOrderMultiple m+k)
  let M := m^H
  let D := 4^(4+(M-1)^2+M^2)
  refine ⟨D,?_⟩
  intro j hD h hh hred
  have hj : 0<j := lt_of_lt_of_le (show 0<D by dsimp [D]; positivity) hD
  by_cases hlarge : H ≤ h
  · exact remove_exponent_factor (by omega) (by unfold jonesOrderMultiple; positivity)
      hh hj (jones_powered_coefficient_dvd hm hh hj hred) hlarge
  · have hM : m^h ≤ M := Nat.pow_le_pow_right (by omega) (by omega)
    have h₀ := Nat.pow_le_pow_left (Nat.sub_le_sub_right hM 1) 2
    have h₁ := Nat.pow_le_pow_left hM 2
    have hcut : 4^(4+(m^h-1)^2+(m^h)^2) ≤ D :=
      Nat.pow_le_pow_right (by decide) (by omega)
    exact (hred (jones_irreducible_of_large_degree _ _
      (Nat.one_lt_pow hh.ne' (by omega)) (by omega))).elim

#print axioms jones_powered_coefficient_dvd
#print axioms jones_powered_exceptional_degrees

end CunninghamChain
