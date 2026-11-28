import HosoyaPrimePowerCollisions
import HosoyaLucasShiftIdentities

/-! Exact differences between Hosoya values with an even midpoint step. -/

namespace Arxiv.«2211.10788».LocalPower

open CongruenceClosure

private abbrev V (n : ℕ) : ℤ := lucasFibonacciSum n

private lemma rec (n : ℕ) : V (n+2) = V (n+1)+V n := by
  exact_mod_cast lucas_fibonacci_sum_recurrence n

private lemma fib_shift (n j : ℕ) :
    V (n+j) = ((Nat.fib (j+1):ℤ)-Nat.fib j)*V n + Nat.fib j*V (n+1) := by
  have hh := ProgressionClosure.half_shift (n:ℤ) j
  rw [ProgressionClosure.lucas_cast,
    ← Nat.cast_add n j, show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by push_cast; rfl] at hh
  simp only [signed_nat] at hh
  change 2*V (n+j) = _*V n + _*(2*V (n+1)-V n) at hh
  linarith only [hh]

private lemma fib_determinant (n j : ℕ) :
    (Nat.fib (j+1):ℤ)*V (n+j) - Nat.fib j*V (n+j+1) = (-1:ℤ)^j*V n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show j+1+1=j+2 by omega,Nat.fib_add_two (n := j),
      show n+(j+1)+1=n+j+2 by omega,rec,pow_succ]
    push_cast
    rw [show n+(j+1)=n+j+1 by omega]
    linear_combination -ih

/-- Factoring a value difference about its midpoint gives the companion
coordinate there. The sign keeps the identity valid at odd half-steps. -/
theorem midpoint_difference (n j : ℕ) :
    V (n+2*j) - (-1:ℤ)^j*V n = Nat.fib j * coordinate (n+j) := by
  rw [show n+2*j=(n+j)+j by omega,fib_shift (n+j) j,← fib_determinant n j]
  unfold coordinate
  ring

#print axioms midpoint_difference

private lemma cancel_coordinate {p v c : ℕ} (hp : p.Prime) (hc : c ≠ 0)
    (hval : c.factorization p = v) (m x : ℕ) :
    p^(m+v) ∣ x*c ↔ p^m ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hx hc),
    hp.pow_dvd_iff_le_factorization hx,Nat.factorization_mul hx hc,Finsupp.add_apply,hval]
  omega

/-- On a branch where the midpoint coordinate has constant valuation v,
the normalized difference of two values has exactly the index divisibility. -/
theorem midpoint_class_congruence {p j a v s : ℕ} (hp : p.Prime) (hj : Even j)
    (ha : 2 ≤ a) (hf : p^a ∣ Nat.fib j) (hsharp : ¬p^(a+1) ∣ Nat.fib j)
    (hc : ∀ u : ℕ, (coordinate (s+j*u)).natAbs ≠ 0 ∧
      (coordinate (s+j*u)).natAbs.factorization p = v) (b n m : ℕ) :
    V (s+2*j*n) ≡ V (s+2*j*m) [ZMOD (p:ℤ)^(a+v+b)] ↔ n ≡ m [MOD p^b] := by
  let : Fact p.Prime := ⟨hp⟩
  have gap (n t : ℕ) : V (s+2*j*n) ≡ V (s+2*j*(n+t)) [ZMOD (p:ℤ)^(a+v+b)] ↔
      n ≡ n+t [MOD p^b] := by
    let J := j*t
    let i := s+2*j*n
    have hv := midpoint_difference i J
    rw [(hj.mul_right t).neg_one_pow,one_mul] at hv
    have hi : i+J = s+j*(2*n+t) := by dsimp [i,J]; ring
    have hstep : i+2*J = s+2*j*(n+t) := by dsimp [i,J]; ring
    rw [hi,hstep] at hv
    have hcrt := hc (2*n+t)
    have hF : p^(a+b) ∣ Nat.fib (j*t) ↔ p^b ∣ t := by
      let : NeZero (p^a) := ⟨pow_ne_zero _ hp.ne_zero⟩
      let : NeZero (p^b*p^a) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hp.ne_zero)⟩
      have rk := sharp_step_rank (p:=p) (m:=p^a) (j:=j)
        (by simpa [pow_two] using (pow_dvd_pow p ha)) hf (by simpa [pow_succ'] using hsharp) b
      have iff := fibonacciStepRank_dvd_iff (p^b*p^a) j t
      rw [rk,← pow_add,Nat.add_comm b a] at iff
      exact iff.symm
    rw [Int.modEq_iff_dvd,Nat.modEq_iff_dvd' (Nat.le_add_right n t),Nat.add_sub_cancel_left]
    change (p:ℤ)^(a+v+b) ∣ V (s+2*j*(n+t)) - V i ↔ _
    rw [hv,← Int.natAbs_dvd_natAbs,Int.natAbs_pow,Int.natAbs_natCast,Int.natAbs_mul,Int.natAbs_natCast,
      show a+v+b=a+b+v by omega]
    exact (cancel_coordinate hp hcrt.1 hcrt.2 (a+b) _).trans hF
  rcases le_total n m with h | h
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
    exact gap n t
  · obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le h
    exact ⟨fun h => ((gap m t).mp h.symm).symm,fun h => ((gap m t).mpr h.symm).symm⟩

#print axioms midpoint_class_congruence

/-- A normalized isometry on index classes fills the entire value class.
At each higher power every compatible target has exactly one index class. -/
theorem lift_class_of_isometry {p h : ℕ} (hp : 0 < p) (f : ℕ → ℤ)
    (iso : ∀ b n m : ℕ, f n ≡ f m [ZMOD (p:ℤ)^(h+b)] ↔ n ≡ m [MOD p^b])
    {y : ℤ} (hy : f 0 ≡ y [ZMOD (p:ℤ)^h]) (b : ℕ) :
    ∃ z < p^b, ∀ n : ℕ, f n ≡ y [ZMOD (p:ℤ)^(h+b)] ↔ n ≡ z [MOD p^b] := by
  classical
  let : NeZero (p^b) := ⟨pow_ne_zero _ hp.ne'⟩
  have any (n : ℕ) : (p:ℤ)^h ∣ f n - f 0 := Int.modEq_iff_dvd.mp (by
    simpa using (iso 0 0 n).mpr (by simp [Nat.ModEq,Nat.mod_one]))
  choose g hg using any
  obtain ⟨c,hc⟩ := Int.modEq_iff_dvd.mp hy
  have hg' (n : ℕ) : f n = f 0 + (p:ℤ)^h*g n := by linarith [hg n]
  have hys : y = f 0 + (p:ℤ)^h*c := by linarith only [hc]
  have law (a c : ℤ) : f 0 + (p:ℤ)^h*a ≡ f 0 + (p:ℤ)^h*c [ZMOD (p:ℤ)^(h+b)] ↔
      (a : ZMod (p^b)) = c := by
    rw [ZMod.intCast_eq_intCast_iff,Int.modEq_iff_dvd,Int.modEq_iff_dvd,Nat.cast_pow,pow_add,
      show f 0 + (p:ℤ)^h*c - (f 0 + (p:ℤ)^h*a) = (p:ℤ)^h*(c-a) by ring]
    exact mul_dvd_mul_iff_left (by positivity : (p:ℤ)^h ≠ 0)
  have eq (n m : ℕ) : (g n : ZMod (p^b)) = g m ↔ n ≡ m [MOD p^b] := by
    rw [←iso b n m,hg' n,hg' m,law]
  let F (w : ZMod (p^b)) : ZMod (p^b) := g w.val
  have hi : Function.Injective F := by
    intro u w huv
    have hh := (ZMod.natCast_eq_natCast_iff ..).mpr ((eq u.val w.val).mp huv)
    simpa using hh
  obtain ⟨w,hw⟩ := Finite.surjective_of_injective hi (c : ZMod (p^b))
  refine ⟨w.val,w.val_lt,fun n => ?_⟩
  rw [hg' n,hys,law,← eq n w.val]
  change (g n : ZMod (p^b)) = c ↔ (g n : ZMod (p^b)) = F w
  rw [hw]

#print axioms lift_class_of_isometry

private lemma state_returns (M : ℕ) [NeZero M] : ∃ T : ℕ, 0 < T ∧
    (Nat.fib T : ZMod M) = 0 ∧ (Nat.fib (T+1) : ZMod M) = 1 := by
  let f (x : ZMod M × ZMod M) := (x.2,x.1+x.2)
  have hi : Function.Injective f := by
    rintro ⟨a,b⟩ ⟨c,d⟩ he
    obtain ⟨rfl,h⟩ := Prod.mk.inj (show (b,a+b)=(d,c+d) from he)
    exact Prod.ext (add_right_cancel h) rfl
  have it (t : ℕ) : f^[t] (0,1) = ((Nat.fib t : ZMod M), (Nat.fib (t+1) : ZMod M)) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [f,Nat.fib_add_two,Nat.cast_add]
  obtain ⟨T,hT,hfix⟩ := hi.mem_periodicPts ((0,1) : ZMod M × ZMod M)
  have hpair := (it T).symm.trans hfix.eq
  have hf : (Nat.fib T : ZMod M) = 0 := congrArg Prod.fst hpair
  have hg : (Nat.fib (T+1) : ZMod M) = 1 := congrArg Prod.snd hpair
  exact ⟨T,hT,hf,hg⟩

/-- The first positive return of the Fibonacci state (0,1) modulo M. -/
def fibStatePeriod (M : ℕ) [NeZero M] : ℕ := Nat.find (state_returns M)

/-- A full Fibonacci state return fixes every companion coordinate and every
upper value, at every translate. -/
theorem midpoint_period (M : ℕ) [NeZero M] :
    let T := fibStatePeriod M
    0 < T ∧ M ∣ Nat.fib T ∧ ∀ n t : ℕ,
      (coordinate (n+T*t) : ZMod M) = coordinate n ∧
      (lucasFibonacciSum (n+T*t) : ZMod M) = lucasFibonacciSum n := by
  let T := fibStatePeriod M
  obtain ⟨hT,hf,hg⟩ := Nat.find_spec (state_returns M)
  change 0 < T at hT
  change (Nat.fib T : ZMod M) = 0 at hf
  change (Nat.fib (T+1) : ZMod M) = 1 at hg
  have term (n : ℕ) : (V (n+T) : ZMod M) = (V n : ZMod M) := by
    have eq := congrArg (fun z : ℤ => (z:ZMod M)) (fib_shift n T)
    push_cast at eq
    simpa [hf,hg] using eq
  have step (n : ℕ) : (coordinate (n+T):ZMod M) = coordinate n := by
    change ((2*V (n+T+1)-V (n+T):ℤ):ZMod M) = ((2*V (n+1)-V n:ℤ):ZMod M)
    rw [show n+T+1=n+1+T by omega]
    push_cast
    have term' (m : ℕ) : (lucasFibonacciSum (m+T):ZMod M) = lucasFibonacciSum m := by
      simpa only [V,Int.cast_natCast] using term m
    rw [term',term']
  refine ⟨hT,(ZMod.natCast_eq_zero_iff _ _).mp hf,fun n t => ?_⟩
  change (coordinate (n+T*t) : ZMod M) = coordinate n ∧
    (lucasFibonacciSum (n+T*t) : ZMod M) = lucasFibonacciSum n
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.mul_succ,← Nat.add_assoc,step]
    have ht := term (n+T*t)
    simp only [V,Int.cast_natCast] at ht
    rw [ht]
    exact ih

#print axioms midpoint_period

end Arxiv.«2211.10788».LocalPower
