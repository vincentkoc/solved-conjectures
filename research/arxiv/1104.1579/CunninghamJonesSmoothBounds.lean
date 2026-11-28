import CunninghamJonesPoweredDegrees
import Mathlib.Analysis.SpecificLimits.Normed

/-! Simultaneous Jones irreducibility for smooth coefficients with at most three prime divisors. -/

namespace CunninghamChain

/-- Removing from j all primes outside the permitted support keeps divisibility
by d; bounded local valuations then give a multiplier independent of j. -/
private lemma trim_smooth_divisor {B k d M j : ℕ} (hd : 0<d) (hM : 0<M) (hj : 0<j)
    (hs : ∀ p : ℕ, p.Prime → p ∣ d → p ≤ B)
    (small : ∀ p : ℕ, p.Prime → p ≤ B → ¬p^k ∣ j) (hdiv : d ∣ M*j) :
    d ∣ M*B.factorial^k := by
  have hfac : 0 < B.factorial^k := pow_pos (Nat.factorial_pos _) _
  apply (Nat.factorization_prime_le_iff_dvd hd.ne' (by positivity)).mp
  intro p hp
  by_cases hpd : p ∣ d
  · have hpb := hs p hp hpd
    have hlow := (hp.pow_dvd_iff_le_factorization hfac.ne').mp
      (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpb) k)
    have hjk : j.factorization p<k := by
      exact lt_of_not_ge (fun he => small p hp hpb ((hp.pow_dvd_iff_le_factorization hj.ne').mpr he))
    have hu := (Nat.factorization_prime_le_iff_dvd hd.ne' (by positivity)).mpr hdiv p hp
    simp only [Nat.factorization_mul hM.ne' hj.ne',Nat.factorization_mul hM.ne' hfac.ne',
      Finsupp.add_apply] at hu ⊢
    omega
  · have hz : d.factorization p=0 := Nat.factorization_eq_zero_of_not_dvd hpd
    simp [hz]

private lemma bounded_exponential {C r : ℕ} :
    ∃ A : ℕ, ∀ a ≥ A, C*a^r < 2^a := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt r (by norm_num : (1:ℝ)<2)
  have h := Filter.Tendsto.eventually_lt_const (by positivity : (0:ℝ)<1/((C:ℝ)+1)) ht
  obtain ⟨A,hA⟩ := Filter.eventually_atTop.mp h
  refine ⟨A,fun a ha => ?_⟩
  have hh := hA a ha
  have he := (div_lt_div_iff₀ (show 0<(2:ℝ)^a by positivity) (show 0<(C:ℝ)+1 by positivity)).mp hh
  have hc : (C:ℝ)*a^r < (2:ℝ)^a := by nlinarith [show 0 ≤ (a:ℝ)^r by positivity]
  exact_mod_cast hc

/-- Away from high small-prime powers in the degree, a unitary split with one
prime-power side has bounded product. The other side may have arbitrary exponents. -/
private theorem bounded_prime_side (B k : ℕ) :
    ∃ M : ℕ, ∀ {u v j : ℕ}, 1<u → 1<v → 0<j → IsPrimePow u → u.Coprime v →
      (∀ q : ℕ, q.Prime → q ∣ u*v → q ≤ B) →
      (∀ q : ℕ, q.Prime → q ≤ B → ¬q^k ∣ j) →
      ((u:ZMod v)^2)^j=1 → ((v:ZMod u)^2)^j=1 → u*v ≤ M := by
  let Y := B.factorial^k
  let C := jonesOrderMultiple B
  let e := 2*B
  have hY : 0<Y := pow_pos (Nat.factorial_pos _) _
  have hC : 0<C := by unfold C jonesOrderMultiple; positivity
  obtain ⟨A,hA⟩ := bounded_exponential (C:=2*Y*(C*Y)^e) (r:=e)
  refine ⟨B^A*(C*Y*A),?_⟩
  intro u v j hu hv hj hpp hc smooth small hs₁ hs₂
  obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hpa := dvd_pow_self p ha.ne'
  have hpB := smooth p hp (hpa.trans (dvd_mul_right ..))
  have hvB (q : ℕ) (hq : q.Prime) (hd : q ∣ v) : q ≤ B :=
    smooth q hq (hd.trans (dvd_mul_left ..))
  have hpv := hc.of_dvd_left hpa
  have he₁ : p^(2*(a*j)) ≡ 1 [MOD v] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa only [Nat.cast_pow,Nat.cast_one,←pow_mul,show a*2*j=2*(a*j) by ring] using hs₁
  have h₁ := jones_complementary_power_bound hp.one_lt hpB hpv hvB he₁
  have hvle : v ≤ C*Y*a := by
    have htrim := trim_smooth_divisor (Nat.zero_lt_of_lt hv) (Nat.mul_pos hC ha) hj hvB small h₁
    simpa only [Y,C,mul_assoc,mul_left_comm,mul_comm] using
      Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos hC ha) hY) htrim
  have he₂ : v^(2*j) ≡ 1 [MOD p^a] := by
    apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa only [Nat.cast_pow,Nat.cast_one,pow_mul] using hs₂
  let F := v^(2*(p-1))-1
  have hF : 0<F := by
    have := hp.two_le
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) hv)
  have h₂ : p^a ∣ (F*2)*j := by
    simpa [F,Nat.mul_assoc] using jones_power_order_lift hv hp hpv.symm he₂
  have htrim := trim_smooth_divisor (Nat.pow_pos hp.pos) (Nat.mul_pos hF (by decide)) hj
    (fun q hq hd => smooth q hq (hd.trans (dvd_mul_right ..))) small h₂
  have hpale := Nat.le_of_dvd (Nat.mul_pos (Nat.mul_pos hF (by decide)) hY) htrim
  have hfle : F ≤ (C*Y*a)^e := (Nat.sub_le _ _).trans
    ((Nat.pow_le_pow_left hvle _).trans (Nat.pow_le_pow_right (by positivity) (by dsimp [e]; omega)))
  have hle : 2^a ≤ (2*Y*(C*Y)^e)*a^e := calc
    _ ≤ p^a := Nat.pow_le_pow_left hp.two_le a
    _ ≤ F*2*Y := hpale
    _ ≤ (C*Y*a)^e*2*Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hfle)
    _ = _ := by rw [mul_pow (C*Y) a]; ring
  have halt : a<A := by by_contra! h; exact (hA a h).not_ge hle
  exact Nat.mul_le_mul ((Nat.pow_le_pow_left hpB _).trans
    (Nat.pow_le_pow_right (by have := hp.two_le; omega) halt.le))
    (hvle.trans (Nat.mul_le_mul_left _ halt.le))

private lemma degree_cutoff (K : ℕ) :
    ∃ D : ℕ, 0 < D ∧ ∀ j ≥ D, ∀ m ≥ 2, m ≤ K →
      Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) := by
  let D := 4^(4+(K-1)^2+K^2)
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro j hD m hm bound
  have h₀ := Nat.pow_le_pow_left (Nat.sub_le_sub_right bound 1) 2
  have h₁ := Nat.pow_le_pow_left bound 2
  have hcut : 4^(4+(m-1)^2+m^2) ≤ D := Nat.pow_le_pow_right (by decide) (by omega)
  exact jones_irreducible_of_large_degree _ _ hm (by omega)

/-- Among coefficients supported on at most three primes up to B, any sufficiently
large exceptional degree is divisible by a prescribed power of some prime up to B.
The coefficient exponents vary independently. -/
theorem jones_three_prime_exceptional_degrees (B k : ℕ) :
    ∃ D : ℕ, ∀ j ≥ D, ∀ m ≥ 2, m.primeFactors.card ≤ 3 →
      (∀ q : ℕ, q.Prime → q ∣ m → q ≤ B) →
      ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) →
      ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ p^k ∣ j := by
  obtain ⟨M,hM⟩ := bounded_prime_side B k
  let K := max M 2
  obtain ⟨D,hpos,hcut⟩ := degree_cutoff K
  refine ⟨D,?_⟩
  intro j hD m hm hcard hB hred
  have hj := hpos.trans_le hD
  by_contra! small
  have bound : m ≤ K := by
    by_cases hm₃ : 3 ≤ m
    · obtain ⟨u,v,hu,hv,huv,hc,hs₁,hs₂⟩ := jones_reducible_constant_split hm₃ hj hred
      have sizes : u.primeFactors.card + v.primeFactors.card ≤ 3 := by
        rw [←Finset.card_union_of_disjoint hc.disjoint_primeFactors,
          ←Nat.primeFactors_mul (by omega) (by omega),huv]
        exact hcard
      have side : IsPrimePow u ∨ IsPrimePow v := by
        by_contra! hn
        have h₁ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hu).mp hn.1
        have h₂ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hv).mp hn.2
        rw [←Finset.one_lt_card_iff_nontrivial] at h₁ h₂
        omega
      apply le_trans _ (le_max_left M 2)
      rcases side with h|h
      · exact huv ▸ hM hu hv hj h hc (huv ▸ hB) small hs₁ hs₂
      · have hvu := (Nat.mul_comm v u).trans huv
        exact hvu ▸ hM hv hu hj h hc.symm (hvu ▸ hB) small hs₂ hs₁
    · exact (show m=2 by omega) ▸ le_max_right M 2
  exact hred (hcut j hD m hm bound)

/-- Rational fixed-support specialization of Yu's valuation estimate. For
B-smooth v ≥ 2 the exponents in v^(2 B!) are bounded by 2 B! log₂ v. -/
def JonesPadicLogBound (B : ℕ) : Prop :=
  ∃ K : ℕ, ∀ v ≥ 2, (∀ q : ℕ, q.Prime → q ∣ v → q ≤ B) →
    ∀ p : ℕ, p.Prime → p ≤ B →
      (v^(2*B.factorial)-1).factorization p ≤ K*(1+Nat.log 2 (1+Nat.log 2 v))

/-- A fixed-support consequence of Yu's p-adic logarithmic forms estimate. Each
B-smooth divisor of v^(2 B!)−1 has size polynomial in log v for B-smooth v. -/
def JonesSmoothPartBound (B : ℕ) : Prop :=
  ∃ C : ℕ, ∀ v ≥ 2, (∀ p : ℕ, p.Prime → p ∣ v → p ≤ B) →
    ∀ d : ℕ, d ∣ v^(2*B.factorial)-1 → (∀ p : ℕ, p.Prime → p ∣ d → p ≤ B) →
      d ≤ C*(1+Nat.log 2 v)^C

/-- Multiplying the fixed-prime valuation bounds yields a bound polynomial in log v
for every smooth divisor, uniformly in v. -/
theorem JonesPadicLogBound.smoothPart {B : ℕ} (arith : JonesPadicLogBound B) :
    JonesSmoothPartBound B := by
  obtain ⟨K,hK⟩ := arith
  let C := B.factorial^K
  have hC : 0<C := pow_pos (Nat.factorial_pos _) _
  refine ⟨C,?_⟩
  intro v hv hsv d hd hsd
  let H := 1+Nat.log 2 v
  let e := K*(1+Nat.log 2 H)
  let F := v^(2*B.factorial)-1
  have hF : 0<F := Nat.sub_pos_of_lt (Nat.one_lt_pow (by positivity) hv)
  have hdpos := Nat.pos_of_dvd_of_pos hd hF
  have hfac : 0<B.factorial^e := pow_pos (Nat.factorial_pos _) _
  have hdiv : d ∣ B.factorial^e := by
    apply (Nat.factorization_prime_le_iff_dvd hdpos.ne' hfac.ne').mp
    intro p hp
    by_cases hpd : p ∣ d
    · have hpB := hsd p hp hpd
      have h₁ := (Nat.factorization_prime_le_iff_dvd hdpos.ne' hF.ne').mpr hd p hp
      have h₂ : F.factorization p ≤ e := hK v hv hsv p hp hpB
      exact (h₁.trans h₂).trans ((hp.pow_dvd_iff_le_factorization hfac.ne').mp
        (pow_dvd_pow_of_dvd (Nat.dvd_factorial hp.pos hpB) e))
    · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
  have hlog := Nat.pow_log_le_self 2 (show H ≠ 0 by dsimp [H]; omega)
  calc
    d ≤ B.factorial^e := Nat.le_of_dvd hfac hdiv
    _ = C * C^(Nat.log 2 H) := by rw [show e=K*(1+Nat.log 2 H) by rfl,pow_mul,pow_add,pow_one]
    _ ≤ C * (2^C)^(Nat.log 2 H) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
    _ = C * (2^(Nat.log 2 H))^C := by rw [←pow_mul, Nat.mul_comm C (Nat.log 2 H),pow_mul]
    _ ≤ C*H^C := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog _)

private lemma small_smooth_part {B : ℕ} (h : JonesSmoothPartBound B) (A : ℕ) :
    ∃ V : ℕ, ∀ v ≥ V, 2 ≤ v → (∀ p : ℕ, p.Prime → p ∣ v → p ≤ B) →
      ∀ d : ℕ, d ∣ v^(2*B.factorial)-1 → (∀ p : ℕ, p.Prime → p ∣ d → p ≤ B) → A*d < v := by
  obtain ⟨C,hC⟩ := h
  obtain ⟨K,hK⟩ := bounded_exponential (C:=A*C*2^C) (r:=C)
  refine ⟨2^(K+1),?_⟩
  intro v hv hv₂ hs d hd hpr
  let t := Nat.log 2 v
  have ht : K+1 ≤ t := Nat.le_log_of_pow_le (by decide) hv
  have hle := hC v hv₂ hs d hd hpr
  calc
    A*d ≤ A*(C*(1+t)^C) := Nat.mul_le_mul_left _ hle
    _ ≤ A*(C*(2*t)^C) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    _ = (A*C*2^C)*t^C := by rw [mul_pow]; ring
    _ < 2^t := hK _ (by omega)
    _ ≤ v := Nat.pow_log_le_self 2 (by omega)

private lemma larger_side_constant {B k : ℕ} (arith : JonesSmoothPartBound B) :
    ∃ M : ℕ, ∀ {u v j : ℕ}, 1<v → v ≤ u → 0<j → u.Coprime v →
      (∀ q : ℕ, q.Prime → q ∣ u*v → q ≤ B) →
      (∀ q : ℕ, q.Prime → q ≤ B → ¬q^k ∣ j) →
      ((v:ZMod u)^2)^j=1 → u*v ≤ M := by
  let L := 2*B.factorial
  let A := 2*B.factorial^k
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨V,hV⟩ := small_smooth_part arith A
  refine ⟨(V^L*A)*V,?_⟩
  intro u v j hv hu hj hc hpr small hmod
  have us (p : ℕ) (hp : p.Prime) (hd : p ∣ u) := hpr p hp (hd.trans (dvd_mul_right ..))
  have vs (p : ℕ) (hp : p.Prime) (hd : p ∣ v) := hpr p hp (hd.trans (dvd_mul_left ..))
  let F := v^L-1
  have hF : 0<F := Nat.sub_pos_of_lt (Nat.one_lt_pow (by dsimp [L]; positivity) hv)
  have hd : u ∣ F*(2*j) := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
    intro p e hp hpe
    rcases Nat.eq_zero_or_pos e with rfl|he
    · simp
    have hpu := (dvd_pow_self p he.ne').trans hpe
    have heq : v^(2*j) ≡ 1 [MOD u] := by
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      simpa only [Nat.cast_pow,Nat.cast_one,pow_mul] using hmod
    have hloc := jones_power_order_lift hv hp (hc.symm.of_dvd_right hpu) (heq.of_dvd hpe)
    have hexp : 2*(p-1) ∣ L := Nat.mul_dvd_mul_left _ (Nat.dvd_factorial (by have := hp.two_le; omega)
      (by have := us p hp hpu; omega))
    exact hloc.trans (mul_dvd_mul_right (Nat.pow_sub_one_dvd_pow_sub_one v hexp) _)
  have htrim := trim_smooth_divisor (by omega : 0<u) (Nat.mul_pos hF (by decide)) hj us small
    (show u ∣ (F*2)*j by simpa only [Nat.mul_assoc] using hd)
  have hfull : u ∣ F*A := by simpa only [A,Nat.mul_assoc] using htrim
  let d := u.gcd F
  have hsmall : u ≤ d*A :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ (by omega)) hA) (dvd_gcd_mul_of_dvd_mul hfull)
  have hvV : v<V := by
    by_contra! hl
    have hgap := hV v hl hv vs d (Nat.gcd_dvd_right ..)
      (fun p hp hpd => us p hp (hpd.trans (Nat.gcd_dvd_left ..)))
    rw [Nat.mul_comm A d] at hgap
    omega
  have bound := Nat.le_of_dvd (Nat.mul_pos hF hA) hfull
  exact Nat.mul_le_mul (bound.trans (Nat.mul_le_mul_right _ ((Nat.sub_le _ _).trans
    (Nat.pow_le_pow_left hvV.le L)))) hvV.le

/-- With the fixed-support smooth-part bound, all B-smooth coefficients admit
the same prime-power restriction on exceptional degrees. -/
theorem jones_smooth_exceptional_degrees {B : ℕ} (arith : JonesPadicLogBound B) (k : ℕ) :
    ∃ D : ℕ, ∀ j ≥ D, ∀ m ≥ 2, (∀ q : ℕ, q.Prime → q ∣ m → q ≤ B) →
      ¬Irreducible ((jonesSumPolynomial m j).map (Int.castRingHom ℚ)) →
      ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ p^k ∣ j := by
  obtain ⟨M,hM⟩ := larger_side_constant (k:=k) arith.smoothPart
  obtain ⟨D,hpos,hcut⟩ := degree_cutoff (max M 2)
  refine ⟨D,?_⟩
  intro j hD m hm hpr hred
  by_contra! small
  apply hred (hcut j hD m hm ?_)
  by_cases hm₃ : 3 ≤ m
  · obtain ⟨u,v,hu,hv,huv,hc,hs₁,hs₂⟩ := jones_reducible_constant_split hm₃ (hpos.trans_le hD) hred
    apply le_trans _ (le_max_left M 2)
    rcases le_total v u with h|h
    · exact huv ▸ hM hv h (hpos.trans_le hD) hc (huv ▸ hpr) small hs₂
    · have hvu := (Nat.mul_comm v u).trans huv
      exact hvu ▸ hM hu h (hpos.trans_le hD) hc.symm (hvu ▸ hpr) small hs₁
  · exact (show m=2 by omega) ▸ le_max_right M 2

#print axioms JonesPadicLogBound.smoothPart
#print axioms jones_smooth_exceptional_degrees
#print axioms jones_three_prime_exceptional_degrees

end CunninghamChain
