import HosoyaSplitProjectiveRoots
import HosoyaInertProjectiveRoots

/-! Local root counts for every affine upper Fibonacci–Lucas index form. -/

namespace Arxiv.«2211.10788»

private def atRoot {p : ℕ} [Fact p.Prime] (a : ZMod p) (h : a^2=a+1) :
    QuadraticAlgebra (ZMod p) 1 1 →ₐ[ZMod p] ZMod p :=
  QuadraticAlgebra.lift ⟨a,by simpa [pow_two,add_comm] using h⟩

private lemma atRoot_apply {p : ℕ} [Fact p.Prime] {a : ZMod p} (h : a^2=a+1)
    (z : QuadraticAlgebra (ZMod p) 1 1) :
    atRoot a h z=z.re+z.im*a := by change z.re • (1:ZMod p)+z.im • a=_; simp

private lemma upper_at_root {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a^2=a+1) (r : ℕ) :
    atRoot a ha (upperIndexStart (ZMod p) r)=(3+a)*a^r := by
  induction r with
  | zero => simp [upperIndexStart,atRoot_apply,lucas_fibonacci_sum_zero,lucas_fibonacci_sum_one]; ring
  | succ r ih =>
    rw [pow_succ,←mul_assoc,←ih,atRoot_apply,atRoot_apply]
    simp only [upperIndexStart,show r+1+1=r+2 by omega,lucas_fibonacci_sum_recurrence,Nat.cast_add]
    linear_combination -(lucasFibonacciSum r : ZMod p)*ha

/-- At all ordinary primes the same quadratic coefficient decides between
no projective roots and exactly gcd(d,N), with N read off from p modulo five. -/
theorem upperProjectiveRootCount_ordinary {p : ℕ} [Fact p.Prime] (h5 : p≠5) (h11 : p≠11)
    (r d : ℕ) (hd : 0<d) :
    let N := if p%5=2 ∨ p%5=3 then p+1 else p-1
    let g := N.gcd d
    upperProjectiveRootCount p r d =
      if (upperIndexStart (ZMod p) r ^ (N/g)).im=0 then g else 0 := by
  dsimp only
  by_cases h : p%5=2 ∨ p%5=3
  · simp only [if_pos h]
    exact upperProjectiveRootCount_inert ((fibonacci_nonsplit_mod_five Fact.out h5).mpr h) r d
  · simp only [if_neg h]
    have hs := (fibonacci_nonsplit_mod_five Fact.out h5).not.mpr h
    push Not at hs
    obtain ⟨a,ha⟩ := hs
    have hₐ : a^2=a+1 := by simpa [add_comm] using ha
    let b := 1-a
    have hᵦ : b^2=b+1 := by dsimp [b]; linear_combination hₐ
    have hba : b≠a := by
      have he : (b-a)^2=5 := by dsimp [b]; linear_combination 4*hₐ
      intro hab
      have hz : (5:ZMod p)=0 := by simpa [hab] using he.symm
      exact h5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 5)).mp
        ((ZMod.natCast_eq_zero_iff ..).mp hz))
    let e := (p-1)/(p-1).gcd d
    let z := upperIndexStart (ZMod p) r ^ e
    have ev {s : ZMod p} (hs : s^2=s+1) :
        ((3+s)*s^r)^e=z.re+z.im*s := by
      rw [←upper_at_root hs,←map_pow,atRoot_apply]
    have crit : ((3+b)*b^r)^e=((3+a)*a^r)^e ↔ z.im=0 := by
      rw [ev hᵦ,ev hₐ,add_right_inj,mul_eq_mul_left_iff]
      simp [hba]
    rw [upperProjectiveRootCount_split h5 h11 hₐ r d hd]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact (h₂ (crit.mp h₁)).elim
    · exact (h₁ (crit.mpr h₂)).elim
    · rfl

#print axioms upperProjectiveRootCount_ordinary

/-- The affine polynomial loses exactly the root at infinity when p divides U(r). -/
theorem upperProjectiveRootCount_affine {p : ℕ} [Fact p.Prime] (r d : ℕ) :
    upperProjectiveRootCount p r d =
      (Finset.univ.filter fun x : ZMod p =>
        Polynomial.eval₂ (Int.castRingHom (ZMod p)) x (upperIndexPolynomial r d)=0).card +
      (if p ∣ lucasFibonacciSum r then 1 else 0) := by
  have inf (d r : ℕ) : upperIndexForm (1:ZMod p) 0 d r=(lucasFibonacciSum r : ZMod p) := by
    induction d generalizing r with
    | zero => rfl
    | succ d ih => simp [upperIndexForm,ih]
  have val (x : ZMod p) (d r : ℕ) :
      Polynomial.eval₂ (Int.castRingHom (ZMod p)) x (upperIndexPolynomial r d)=
        upperIndexForm x 1 d r := by
    let ev := Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) x
    change ev (upperIndexForm Polynomial.X (1:Polynomial ℤ) d r)=_
    induction d generalizing r with
    | zero => exact map_natCast ev _
    | succ d ih =>
      rw [upperIndexForm, map_add,map_mul,map_mul,ih,ih,upperIndexForm]
      simp [ev]
  unfold upperProjectiveRootCount
  rw [Finset.card_filter,univ_option,Finset.sum_insertNone,Finset.card_filter]
  simp only [upperIndexChart,inf,ZMod.natCast_eq_zero_iff,val]
  apply add_comm

#print axioms upperProjectiveRootCount_affine

end Arxiv.«2211.10788»
