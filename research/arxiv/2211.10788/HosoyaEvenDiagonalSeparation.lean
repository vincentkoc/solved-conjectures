import LucasFibonacciDiagonalUnion

/-! A split Fibonacci recurrence distinguishes even lower values modulo a prime. -/

namespace Arxiv.«2211.10788».PrimeObstruction

private lemma lower_step (n : ℕ) : lowerNeighborAtAddTwo (n+2) =
    lowerNeighborAtAddTwo n + lowerNeighborAtAddTwo (n+1) := by
  simp only [lowerNeighborAtAddTwo,Nat.fib_add_two]
  omega

private theorem signed_pell (f : ℕ → ℕ) (step : ∀ j, f (j+2)=f (j+1)+f j)
    (h0 : (f 1:ℤ)^2-f 0*f 1-(f 0:ℤ)^2=11) (n : ℕ) :
    (2*(f (n+1):ℤ)-f n)^2 = 5*(f n:ℤ)^2 + 44*(-1:ℤ)^n := by
  have H (j : ℕ) : (f (j+1):ℤ)^2 - f j*f (j+1) - (f j:ℤ)^2 = 11*(-1:ℤ)^j := by
    induction j with
    | zero => simpa using h0
    | succ j ih =>
      rw [show j.succ+1=j+2 by rfl,step,Nat.cast_add,pow_succ]
      linear_combination -ih
  linear_combination 4*(H n)

/-- The sign-specific Pell witness for every upper term. -/
theorem upper_signed_pell (n : ℕ) :
    (2*(lucasFibonacciSum (n+1):ℤ)-lucasFibonacciSum n)^2 =
      5*(lucasFibonacciSum n:ℤ)^2 + 44*(-1:ℤ)^n :=
  signed_pell _ lucas_fibonacci_sum_recurrence (by norm_num [lucas_fibonacci_sum_zero,lucas_fibonacci_sum_one]) n

/-- The positive discriminant of an even lower term is an integer square. -/
theorem even_lower_positive_square (j : ℕ) : IsSquare (5*(lowerNeighborAtAddTwo (2*j):ℤ)^2+44) := by
  have he := signed_pell _ (fun n => (lower_step n).trans (Nat.add_comm ..)) (by decide) (2*j)
  rw [pow_mul] at he
  refine ⟨2*(lowerNeighborAtAddTwo (2*j+1):ℤ)-lowerNeighborAtAddTwo (2*j),?_⟩
  simpa [pow_two] using he.symm

private theorem recurrence_formula {K : Type*} [Field K] (f : ℕ → ℕ)
    (step : ∀ n, f (n+2)=f n+f (n+1)) (D c d a b : K)
    (ha : a^2=a+1) (hb : b^2=b+1)
    (h0 : D*f 0=c+d) (h1 : D*f 1=c*a+d*b) (n : ℕ) :
    D*f n = c*a^n+d*b^n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa using h0
  | one => simpa using h1
  | more n h₀ h₁ =>
    rw [step,Nat.cast_add,mul_add,h₀,h₁,pow_add a n 2,pow_add b n 2,ha,hb,pow_succ,pow_succ]
    ring

private theorem square_sum_obstruction {K : Type*} [Field K] {c d t u : K}
    (htu : u≠0) (hn : ¬IsSquare (-1:K)) (h₁₁ : ¬IsSquare (11:K))
    (hcd : c*d= -11) (he : (t^2*u^2+1)*(c*t^2+d*u^2)=0) : False := by
  rcases mul_eq_zero.mp he with h|h
  · exact hn ⟨t*u,by linear_combination -h⟩
  · apply h₁₁
    refine ⟨c*t/u,?_⟩
    field_simp
    linear_combination -c*h + u^2*hcd

/-- If 5 is a square and −1 and 11 are nonsquares, no even upper index can coincide with
any even lower index modulo p. -/
theorem even_diagonals_disjoint {p : ℕ} (hp : p.Prime) (h₅ : IsSquare (5:ZMod p))
    (hm : ¬IsSquare (-1:ZMod p)) (h₁₁ : ¬IsSquare (11:ZMod p)) (i j : ℕ) :
    (lucasFibonacciSum (2*i):ZMod p) ≠ (lowerNeighborAtAddTwo (2*j):ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨h,hh⟩ := h₅
  have ht : (2:ZMod p)≠0 := by
    intro hz
    exact hm ⟨1,by linear_combination -hz⟩
  let a := (1+h)/2
  let b := (1-h)/2
  have ha : a^2=a+1 := by dsimp [a]; field_simp; linear_combination -hh
  have hb : b^2=b+1 := by dsimp [b]; field_simp; linear_combination -hh
  have hab : a*b= -1 := by dsimp [a,b]; field_simp; linear_combination hh
  have hs : a+b=1 := by dsimp [a,b]; field_simp; ring
  let c := 4-b
  let d := a-4
  have hcd : c*d= -11 := by dsimp [c,d]; linear_combination 4*hs-hab
  let D := a-b
  have upper := recurrence_formula lucasFibonacciSum (fun n => (lucas_fibonacci_sum_recurrence n).trans (Nat.add_comm ..)) D c d a b ha hb
    (by simp [lucas_fibonacci_sum_zero,D,c,d])
    (by simp [lucas_fibonacci_sum_one,D,c,d]; ring)
  have lower := recurrence_formula lowerNeighborAtAddTwo lower_step D (-d*a^2) (-c*b^2) a b ha hb
    (by rw [show lowerNeighborAtAddTwo 0=2 by decide,ha,hb]; push_cast
        dsimp [D,c,d]; linear_combination ha-hb)
    (by rw [show lowerNeighborAtAddTwo 1=5 by decide,ha,hb]; push_cast
        dsimp [D,c,d]; linear_combination (a-2)*ha-(b-2)*hb)
  have pair (n : ℕ) : a^(2*n)*b^(2*n)=1 := by rw [←mul_pow,hab,pow_mul]; simp
  have ha0 : a≠0 := by intro h; simp [h] at hab
  intro hit
  have he := (upper (2*i)).symm.trans ((congrArg (D*·) hit).trans (lower (2*j)))
  apply square_sum_obstruction (c:=c) (d:=d) (t:=a^i) (u:=a^(j+1)) (pow_ne_zero _ ha0) hm h₁₁ hcd
  have hbpow : b^2*b^(2*j) = b^(2*(j+1)) := by rw [←pow_add]; congr 1; omega
  have hapow : a^2*a^(2*j) = a^(2*(j+1)) := by rw [←pow_add]; congr 1; omega
  rw [mul_assoc,mul_assoc,hapow,hbpow] at he
  have e₁ := pair i
  have e₂ := pair (j+1)
  rw [show 2*i=i*2 by omega,pow_mul,pow_mul] at he e₁
  rw [show 2*(j+1)=(j+1)*2 by omega,pow_mul,pow_mul] at he e₂
  linear_combination (a^i)^2*(a^(j+1))^2*he - d*(a^(j+1))^2*e₁ - c*(a^i)^2*e₂

/-- The fourth nonsquare excludes the odd upper indices as well. -/
theorem even_lower_prime_obstruction {p : ℕ} (hp : p.Prime) (j : ℕ)
    (h₅ : IsSquare (5:ZMod p)) (hm : ¬IsSquare (-1:ZMod p)) (h₁₁ : ¬IsSquare (11:ZMod p))
    (hB : ¬IsSquare (5*(lowerNeighborAtAddTwo (2*j):ZMod p)^2-44)) (n : ℕ) :
    ¬lucasFibonacciSum n ≡ lowerNeighborAtAddTwo (2*j) [MOD p] := by
  intro hit
  have he := (ZMod.natCast_eq_natCast_iff ..).mpr hit
  rcases Nat.even_or_odd n with ⟨i,hi⟩|ho
  · rw [show n=2*i by omega] at he
    exact even_diagonals_disjoint hp h₅ hm h₁₁ i j he
  · have hh := upper_signed_pell n
    rw [ho.neg_one_pow] at hh
    have e := congrArg (fun z : ℤ => (z:ZMod p)) hh
    push_cast at e
    rw [he] at e
    exact hB ⟨2*(lucasFibonacciSum (n+1):ZMod p)-lowerNeighborAtAddTwo (2*j),by linear_combination -e⟩

#print axioms upper_signed_pell
#print axioms even_lower_positive_square
#print axioms even_diagonals_disjoint
#print axioms even_lower_prime_obstruction

end Arxiv.«2211.10788».PrimeObstruction
