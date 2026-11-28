import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-! Real coordinates of odd powers on the line 1 + 2c√d. -/

namespace Arxiv.«2211.10788».HosoyaOddNorm

private def block (d c T u v : ℤ) : Zsqrtd d :=
  ⟨1+4*T*c^2*u,4*T*c*v⟩

private lemma block_mul (d c T u v s t : ℤ) :
    block d c T u v * block d c T s t =
    block d c T (u+s+4*T*c^2*u*s+4*d*T*v*t) (v+t+4*T*c^2*(u*t+s*v)) := by
  ext <;> simp [block,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring

private lemma block_pow (d c T u v : ℤ) (n : ℕ) :
    ∃ r t : ℤ, (block d c T u v)^n=block d c T (n*u+2*r) t := by
  induction n with
  | zero => exact ⟨0,0,by ext <;> simp [block]⟩
  | succ n ih =>
    obtain ⟨r,t,he⟩ := ih
    rw [pow_succ,he,block_mul]
    refine ⟨r+2*T*c^2*(n*u+2*r)*u+2*d*T*t*v,t+v+4*T*c^2*((n*u+2*r)*v+u*t),?_⟩
    congr 1
    push_cast
    ring

private lemma dyadic_power (d c : ℤ) (hd : Odd d) (k : ℕ) :
    ∃ u v : ℤ, Odd u ∧ (⟨1,2*c⟩ : Zsqrtd d)^(2*2^k) = block d c (2^k) u v := by
  induction k with
  | zero =>
    refine ⟨d,1,hd,?_⟩
    ext <;> simp [sq,block,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring
  | succ k ih =>
    obtain ⟨u,v,hu,he⟩ := ih
    let T : ℤ := 2^k
    let q := T*c^2*u^2 + d*T*v^2
    refine ⟨u+2*q,(1+4*T*c^2*u)*v,hu.add_even (even_two_mul _),?_⟩
    rw [pow_succ (2:ℕ) k,←Nat.mul_assoc,pow_mul,he,sq]
    ext <;> simp [block,Zsqrtd.re_mul,Zsqrtd.im_mul,T,q,pow_succ] <;> ring

/-- In an odd quadratic order, an odd power above one of 1+2c√d can have
real coordinate one only on the rational axis. -/
theorem real_part_odd_power_eq_one {d c : ℤ} (hd : Odd d) {p : ℕ} (hp : Odd p) (hp₁ : 1<p)
    (he : ((⟨1,2*c⟩ : Zsqrtd d)^p).re=1) : c=0 := by
  obtain ⟨s,hs⟩ := hp
  obtain ⟨k,n,hn,hs'⟩ := Nat.exists_eq_two_pow_mul_odd (show s ≠ 0 by omega)
  obtain ⟨u,v,hu,hz⟩ := dyadic_power d c hd k
  obtain ⟨r,t,ht⟩ := block_pow d c (2^k) u v n
  have hN : p=(2*2^k)*n+1 := by rw [hs,hs']; ring
  rw [hN,pow_succ,pow_mul,hz,ht] at he
  change (1+4*(2:ℤ)^k*c^2*(n*u+2*r))*1+d*(4*2^k*c*t)*(2*c)=1 at he
  have hodd : Odd ((n:ℤ)*u+2*r+2*d*t) := by
    have hn' : Odd (n:ℤ) := by exact_mod_cast hn
    simpa only [mul_assoc] using ((hn'.mul hu).add_even (even_two_mul r)).add_even (even_two_mul (d*t))
  have hmul : 4*(2:ℤ)^k*c^2*((n:ℤ)*u+2*r+2*d*t)=0 := by linear_combination he
  rcases mul_eq_zero.mp hmul with h|h
  · have hpow : (2:ℤ)^k ≠ 0 := by positivity
    rcases mul_eq_zero.mp h with h|h
    · exact False.elim ((mul_ne_zero (by decide) hpow) h)
    · exact pow_eq_zero_iff (by decide) |>.mp h
  · obtain ⟨l,hl⟩ := hodd
    omega

#print axioms real_part_odd_power_eq_one

end Arxiv.«2211.10788».HosoyaOddNorm
