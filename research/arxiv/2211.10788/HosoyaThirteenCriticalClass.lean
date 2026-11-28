import HosoyaPrimePowerCollisions
import LucasFibonacciProgressionClosure

/-! At 13 a reduced prime-parameter class realizes the square-root concentration rate. -/

namespace Arxiv.«2211.10788».LocalPower
open CongruenceClosure ProgressionClosure

private def companion : ℕ → ℕ
  | 0 => 7
  | 1 => 6
  | n+2 => companion (n+1)+companion n

private theorem comp_coprime (n : ℕ) : (companion n).Coprime (companion (n+1)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (companion (n+1)).Coprime (companion (n+1)+companion n)
    simpa using ih.symm

private theorem comp_eq (n : ℕ) : (companion n:ℤ) = coordinate n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n hi hj =>
    change ((companion (n+1)+companion n:ℕ):ℤ)=_
    rw [Nat.cast_add,hi,hj]
    rw [coordinate_rec]

private theorem mod_thirteen (t : ℕ) : lucasFibonacciSum (23+364*t) ≡ 12 [MOD 13] := by
  have period (i : ℕ) : lucasFibonacciSum (i+28) ≡ lucasFibonacciSum i [MOD 13] := by
    induction i using Nat.twoStepInduction with
    | zero => decide +kernel
    | one => decide +kernel
    | more n h₀ h₁ =>
      rw [show n+2+28=n+28+2 by omega,lucas_fibonacci_sum_recurrence,lucas_fibonacci_sum_recurrence n]
      exact (show lucasFibonacciSum (n+28+1) ≡ lucasFibonacciSum (n+1) [MOD 13] by
        simpa [Nat.add_right_comm] using h₁).add h₀
  have base (u : ℕ) : lucasFibonacciSum (23+28*u) ≡ 12 [MOD 13] := by
    induction u with
    | zero => decide +kernel
    | succ u ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (period _).trans ih
  simpa [show 364*t=28*(13*t) by ring] using base (13*t)

private theorem common_value {h n m : ℕ} (hp : 0<h)
    (xn : 13^h∣companion (23+364*n)) (xm : 13^h∣companion (23+364*m)) :
    (lucasFibonacciSum (23+364*n):ℤ) ≡ lucasFibonacciSum (23+364*m) [ZMOD (13:ℤ)^(2*h)] := by
  let N := 13^(2*h)
  let i := 23+364*n
  let j := 23+364*m
  let A := lucasFibonacciSum i
  let B := lucasFibonacciSum j
  have pell (t : ℕ) : (companion (23+364*t):ℤ)^2 =
      5*(lucasFibonacciSum (23+364*t):ℤ)^2-44 := by
    rw [comp_eq]
    have eq := PrimeObstruction.upper_signed_pell (23+364*t)
    have odd : Odd (23+364*t) := ⟨11+182*t,by ring⟩
    change (2*(lucasFibonacciSum (23+364*t+1):ℤ)-lucasFibonacciSum (23+364*t))^2 = _
    rw [odd.neg_one_pow] at eq
    linarith only [eq]
  have z (t : ℕ) (hit : 13^h∣companion (23+364*t)) :
      5*(lucasFibonacciSum (23+364*t):ZMod N)^2=44 := by
    have dv : N∣companion (23+364*t)^2 := by
      change (13:ℕ)^(2*h) ∣ (companion (23+364*t))^2
      rw [Nat.mul_comm 2 h,pow_mul]
      exact pow_dvd_pow_of_dvd hit 2
    have zero := (ZMod.natCast_eq_zero_iff _ N).mpr dv
    have ident := congrArg (fun x : ℤ => (x:ZMod N)) (pell t)
    push_cast at ident zero
    linear_combination zero-ident
  have sum : ¬13∣A+B := by
    intro div
    have eq := (mod_thirteen n).add (mod_thirteen m)
    exact (by decide : ¬13∣12+12) (Nat.modEq_zero_iff_dvd.mp (eq.symm.trans (Nat.modEq_zero_iff_dvd.mpr div)))
  have unit : IsUnit (5*((A:ZMod N)+B)) := by
    have u₁ : IsUnit (5:ZMod N) := by
      exact (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=5) (by decide : Nat.Prime 13) (by omega : 0<2*h)).mpr (by decide)
    have u₂ := (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=A+B) (by decide : Nat.Prime 13) (by omega : 0<2*h)).mpr sum
    exact u₁.mul (by simpa using u₂)
  have eq : (5*((A:ZMod N)+B))*((A:ZMod N)-B)=0 := by
    change 5*((lucasFibonacciSum (23+364*n):ZMod N)+_)*(_-_)=0
    linear_combination z n xn-z m xm
  have same : (A:ZMod N)=(B:ZMod N) := sub_eq_zero.mp (unit.mul_right_inj.mp (eq.trans (mul_zero _).symm))
  have nn := (ZMod.natCast_eq_natCast_iff ..).mp same
  exact_mod_cast nn

/-- For every h the entire reduced class a mod 364·13^h gives a single
value modulo 13^(2h+4). Dirichlet supplies prime indices on that class. -/
theorem critical_thirteen (b : ℕ) :
    ∃ a<364*13^b, a.Coprime (364*13^b) ∧ ∀ t : ℕ,
      (lucasFibonacciSum (a+364*13^b*t):ℤ) ≡ lucasFibonacciSum a [ZMOD (13:ℤ)^(2*(b+2))] := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have fast : Nat.fib 364=Nat.fastFib 364 := (Nat.fastFib_eq 364).symm
  have hf : 169∣Nat.fib 364 := by rw [fast]; decide +kernel
  have sharp : ¬13*169∣Nat.fib 364 := by rw [fast]; decide +kernel
  obtain ⟨c,bound,all⟩ := fibonacci_recurrence_root_progression companion (fun _ => rfl) comp_coprime
    (s:=23) (by decide : 0<169) (by decide : 13*13∣169) (by decide +kernel) hf sharp b
  let a := 23+364*c
  have first : a.Coprime 364 := by dsimp [a]; simp; decide
  have second : a.Coprime 13 := first.coprime_dvd_right (by decide)
  refine ⟨a,by dsimp [a]; omega,first.mul_right (second.pow_right _),fun t => ?_⟩
  have atLevel (s : ℕ) : 13^(b+2)∣companion (23+364*(c+13^b*s)) := by simpa [pow_add] using all s
  have res := common_value (by omega : 0<b+2) (atLevel t) (by simpa using atLevel 0)
  simpa only [a,show 23+364*c+364*13^b*t = 23+364*(c+13^b*t) by ring] using res

#print axioms critical_thirteen

end Arxiv.«2211.10788».LocalPower
