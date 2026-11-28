import CunninghamRationalRootDenominators
import CunninghamRootCoefficientArithmetic

/-! Complete rational-root classification at all prime-power coefficients. -/

namespace CunninghamChain.LinearRoots
open Polynomial

private lemma only_full_square {p e q b : ℕ} (hp : p.Prime) (hq : 2≤q)
    (h : p^e=q^2*b) (hc : q.Coprime b) : p^e=q^2 := by
  have dq : q ∣ p^e := h ▸ dvd_mul_of_dvd_left (by simp [pow_two]) _
  have db : b ∣ p^e := h ▸ dvd_mul_left _ _
  obtain ⟨i,_,hi⟩ := (Nat.dvd_prime_pow hp).mp dq
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow hp).mp db
  have hi0 : i≠0 := by rintro rfl; simp at hi; omega
  have hj0 : j=0 := by
    by_contra hn
    have d₁ : p∣q := hi ▸ dvd_pow_self _ hi0
    have d₂ : p∣b := hj ▸ dvd_pow_self _ hn
    exact hp.not_dvd_one ((show Nat.gcd q b=1 from hc) ▸ Nat.dvd_gcd d₁ d₂)
  simpa [hj,hj0] using h

private theorem endpoint_equation {d : ℤ} {n : ℕ} (hd : 2≤d.natAbs) (hn : 0<n) (k : Bool)
    (h : (d-1)^2=sign k*(d^n-1)) :
    (k=true ∧ n=1 ∧ d=2) ∨ (k=false ∧ n=3 ∧ d= -2) := by
  have d2 : d ∣ 2 := by
    obtain ⟨u,hu⟩ := dvd_pow_self d hn.ne'
    cases k
    · have e₁ : d^(n-1)=2-d := by
        apply mul_right_cancel₀ (show d≠0 by omega)
        rw [←pow_succ,show n-1+1=n by omega]
        simp only [sign,Bool.false_eq_true,if_false] at h
        linear_combination h
      have hn' : n-1≠0 := by
        intro he; rw [he,pow_zero] at e₁; omega
      obtain ⟨v,hv⟩ := dvd_pow_self d hn'
      exact ⟨v+1,by linear_combination hv-e₁⟩
    · refine ⟨u-d+2,?_⟩
      simp only [sign,if_true,one_mul] at h
      linear_combination h+hu
  have hdub : d.natAbs≤2 := Nat.le_of_dvd (by decide) (Int.natAbs_dvd_natAbs.mpr d2)
  have eqd : d=2 ∨ d= -2 := by omega
  rcases eqd with rfl|rfl <;> cases k
  · norm_num [sign] at h
    have hp : (0:ℤ)<2^n := by positivity
    omega
  · left
    refine ⟨rfl,?_,rfl⟩
    have e : (2:ℤ)^n=2 := by norm_num [sign] at h; omega
    exact Nat.pow_right_injective (a:=2) (by decide) (by exact_mod_cast (show (2:ℤ)^n=2^1 by simpa using e))
  · right
    refine ⟨rfl,?_,rfl⟩
    have e : (-2:ℤ)^n= -8 := by norm_num [sign] at h; omega
    have en := congrArg Int.natAbs e
    apply Nat.pow_right_injective (a:=2) (by decide)
    simpa only [Int.natAbs_pow,show (-2:ℤ).natAbs=2 by decide,show (-8:ℤ).natAbs=2^3 by decide] using en
  · have e : (-2:ℤ)^n=10 := by norm_num [sign] at h; omega
    have en : (2:ℕ)^n=10 := by simpa only [Int.natAbs_pow,show (-2:ℤ).natAbs=2 by decide,show (10:ℤ).natAbs=10 by decide] using congrArg Int.natAbs e
    by_cases h4 : 4≤n
    · have ge : (2:ℕ)^4≤2^n := Nat.pow_le_pow_right (by decide) h4
      omega
    · interval_cases n <;> norm_num at en

/-- Across both signs and all positive indices, prime powers have just two exceptional
rational roots, both at coefficient four. -/
theorem prime_power_rational_roots {p e n : ℕ} (hp : p.Prime) (hn : 0<n) (k : Bool) (x : ℚ) :
    (term k (p^e:ℕ) (-(p^e:ℕ):ℤ) n).IsRoot x ↔
      p^e=4 ∧ ((k=true ∧ n=1 ∧ x=1/2) ∨ (k=false ∧ n=3 ∧ x= -1/2)) := by
  constructor
  · intro h
    obtain ⟨d,hd,hx,he⟩ := (rational_root_iff_denominator k _ n (pow_pos hp.pos _) hn x).mp h
    obtain ⟨_,b,hb,hc⟩ := root_denominator_arithmetic hd hn (show (sign k)^2=1 by cases k <;> norm_num [sign]) he
    have heq := only_full_square hp hd hb hc
    have val : ((p^e:ℕ):ℤ)=d^2 := by exact_mod_cast (show ((p^e:ℕ):ℤ)=(d.natAbs:ℤ)^2 by exact_mod_cast heq).trans (Int.natAbs_sq d)
    have H : (d-1)^2=sign k*(d^n-1) := by
      apply mul_left_cancel₀ (pow_ne_zero 2 (show d≠0 by omega))
      rw [val] at he
      linear_combination he
    rcases endpoint_equation hd hn k H with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
    · exact ⟨heq,Or.inl ⟨rfl,rfl,by norm_num at hx ⊢; exact hx⟩⟩
    · exact ⟨heq,Or.inr ⟨rfl,rfl,by norm_num at hx ⊢; exact hx⟩⟩
  · rintro ⟨h,hk⟩
    rw [h]
    rcases hk with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> norm_num [IsRoot.def,term,polynomialTerm]

#print axioms prime_power_rational_roots

end CunninghamChain.LinearRoots
