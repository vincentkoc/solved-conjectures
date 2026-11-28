import LucasFibonacciDiagonalUnion

/-! Prime divisors specific to one member of a neighboring Hosoya pair. -/

namespace Arxiv.«2211.10788»

/-- X-coordinates in the three positive-k rows of Bennett and Ghadermarzi
obtained by reducing the exponent of seven modulo three. -/
def HosoyaSevenMordellRows : Prop :=
  (∀ X Y : ℤ, Y^2=X^3+1100 → X = -10 ∨ X=5 ∨ X=14 ∨ X=245) ∧
  (∀ X Y : ℤ, Y^2=X^3+53900 → X = -35 ∨ X = -10 ∨ X=14 ∨ X=70) ∧
  (∀ X Y : ℤ, Y^2=X^3+2641100 → X=245)

/-- All powers of seven, allowing exponent zero, on the union of the two diagonals. -/
theorem seven_power_on_hosoya_iff (rows : HosoyaSevenMordellRows) (k : ℕ) :
    ((∃ n, 7^k=lucasFibonacciSum n) ∨ IsLowerNeighborValue (7^k)) ↔
    k=0 ∨ k=1 ∨ k=3 := by
  constructor
  · intro h
    obtain ⟨x,hx⟩ := (either_diagonal_iff_pell _).mp h
    by_cases hk : k=0
    · exact Or.inl hk
    have he : (x:ℤ)^2=5*((7:ℤ)^k)^2+44 := by
      rcases hx with h | h
      · exact_mod_cast h
      · have hv := congrArg (Nat.castRingHom (ZMod 7)) h
        simp only [map_add,map_pow,map_mul,map_ofNat,Nat.coe_castRingHom] at hv
        have hz : (7:ZMod 7)=0 := by decide
        rw [hz,zero_pow hk] at hv
        exact False.elim ((by decide : ∀ z : ZMod 7, z^2+44 ≠ 5*0^2) _ hv)
    let j := k/3
    let a := (7:ℤ)^j
    have ha : 1 ≤ a := by dsimp [a]; exact one_le_pow₀ (by decide)
    have large (hj : 2 ≤ j) : 49 ≤ a := by
      exact (show (7:ℤ)^2 ≤ 7^j from pow_le_pow_right₀ (by decide) hj)
    have hr : k%3<3 := Nat.mod_lt _ (by decide)
    generalize ht : k%3 = t at hr
    interval_cases t
    · have hd : k=j*3 := by dsimp [j]; omega
      rw [hd,pow_mul] at he
      change (x:ℤ)^2=5*(a^3)^2+44 at he
      have hh := rows.1 (5*a^2) (5*x) (by linear_combination 25*he)
      by_cases hj : 2 ≤ j
      · have := large hj
        rcases hh with h|h|h|h <;> nlinarith [sq_nonneg (a-49)]
      · omega
    · have hd : k=j*3+1 := by dsimp [j]; omega
      rw [hd,pow_succ (7:ℤ) (j*3),pow_mul] at he
      change (x:ℤ)^2=5*(a^3*7)^2+44 at he
      have hh := rows.2.2 (245*a^2) (245*x) (by linear_combination 60025*he)
      by_cases hj : 1 ≤ j
      · have hh' : (7:ℤ) ≤ a := by
          simpa using (pow_le_pow_right₀ (by decide : (1:ℤ) ≤ 7) hj)
        nlinarith [sq_nonneg (a-7)]
      · omega
    · have hd : k=j*3+2 := by dsimp [j]; omega
      rw [hd,pow_add,pow_mul] at he
      change (x:ℤ)^2=5*(a^3*7^2)^2+44 at he
      have hh := rows.2.1 (245*a^2) (35*x) (by linear_combination 1225*he)
      rcases hh with h|h|h|h <;> nlinarith [sq_nonneg (a-1)]
  · rintro (rfl|rfl|rfl)
    · exact Or.inl ⟨0,by decide⟩
    · exact Or.inr (Or.inr ⟨2,by decide⟩)
    · exact Or.inr (Or.inr ⟨10,by decide⟩)

#print axioms seven_power_on_hosoya_iff


/-- A prime dividing both neighbors must be seven. -/
theorem shared_neighbor_prime {p m : ℕ} (hp : p.Prime)
    (hu : p ∣ lucasFibonacciSum (m+2)) (hl : p ∣ lowerNeighborAtAddTwo m) : p=7 := by
  have sum_eq : lowerNeighborAtAddTwo m + lucasFibonacciSum (m+2) = 7*Nat.fib (m+2) := by
    simp only [lowerNeighborAtAddTwo,lucasFibonacciSum,Nat.fib_add_two]; omega
  have hh := dvd_add hl hu
  rw [sum_eq] at hh
  rcases hp.dvd_mul.mp hh with h | h
  · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
  · have hu' : lucasFibonacciSum (m+2)=3*Nat.fib (m+2)+Nat.fib (m+2+1) := by
      simp only [lucasFibonacciSum,Nat.fib_add_two]; omega
    rw [hu'] at hu
    have hb := (Nat.dvd_add_right (dvd_mul_of_dvd_right h 3)).mp hu
    have hc := Nat.dvd_gcd h hb
    rw [(Nat.fib_coprime_fib_succ (m+2)).gcd_eq_one] at hc
    exact False.elim (hp.not_dvd_one hc)

private theorem upper_period_twenty_one (n : ℕ) :
    lucasFibonacciSum (n+16) ≡ lucasFibonacciSum n [MOD 21] := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [show n+2+16=n+16+2 by omega, lucas_fibonacci_sum_recurrence (n+16),
      lucas_fibonacci_sum_recurrence n]
    exact h₁.add h₀

/-- Seven is idempotent modulo 21, and the upper diagonal omits its residue. -/
theorem upper_ne_positive_seven_power (n k : ℕ) :
    lucasFibonacciSum n ≠ 7^(k+1) := by
  have never (i : ℕ) : lucasFibonacciSum i % 21 ≠ 7 := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases hi : i < 16
      · interval_cases i <;> decide
      · let j := i-16
        have he : i=j+16 := by dsimp [j]; omega
        have hl : j < i := by omega
        rw [he, (upper_period_twenty_one j : lucasFibonacciSum (j+16)%21=lucasFibonacciSum j%21)]
        exact ih j hl
  have idem : 7^(k+1)%21=7 := by
    induction k with
    | zero => decide
    | succ k ih => rw [pow_succ 7 (k+1),Nat.mul_mod,ih]
  intro h
  exact never n (h ▸ idem)

private theorem private_prime_of_not_seven {a b : ℕ} (ha : a≠0)
    (hs : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → p=7)
    (hpow : ∀ k : ℕ, a≠7^k) : ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ ¬p ∣ b := by
  by_contra! hn
  exact hpow _ (Nat.eq_prime_pow_of_unique_prime_dvd ha fun {p} hp hd => hs p hp hd (hn p hp hd))

theorem upper_has_private_neighbor_prime (m : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∣ lucasFibonacciSum (m+2) ∧ ¬p ∣ lowerNeighborAtAddTwo m := by
  have hf : 0 < Nat.fib (m+2) := Nat.fib_pos.mpr (by omega)
  have hu : 1 < lucasFibonacciSum (m+2) := by simp only [lucasFibonacciSum]; omega
  apply private_prime_of_not_seven (by omega) (fun _ hp => shared_neighbor_prime hp)
  rintro (_|k)
  · simp; omega
  · exact upper_ne_positive_seven_power _ _

theorem lower_has_private_neighbor_prime_iff (rows : HosoyaSevenMordellRows) (m : ℕ) :
    (∃ p : ℕ, p.Prime ∧ p ∣ lowerNeighborAtAddTwo m ∧ ¬p ∣ lucasFibonacciSum (m+2)) ↔
    m≠2 ∧ m≠10 := by
  have lower : StrictMono lowerNeighborAtAddTwo := by
    apply strictMono_nat_of_lt_succ
    intro i
    have h := Nat.fib_add_two_strictMono (Nat.lt_succ_self i)
    have h' := Nat.fib_mono (Nat.le_succ i)
    simp only [lowerNeighborAtAddTwo]
    change Nat.fib i ≤ Nat.fib (i+1) at h'
    change Nat.fib (i+2) < Nat.fib (i+1+2) at h
    omega
  constructor
  · rintro ⟨p,hp,hd,hn⟩
    constructor
    · rintro rfl
      exact hn (hd.trans (by decide))
    · rintro rfl
      change p ∣ 7^3 at hd
      have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp (hp.dvd_of_dvd_pow hd)
      subst p
      exact hn (by decide)
  · rintro ⟨h₂,h₁₀⟩
    have hf : 0 < Nat.fib (m+2) := Nat.fib_pos.mpr (by omega)
    have hl : 1 < lowerNeighborAtAddTwo m := by simp only [lowerNeighborAtAddTwo]; omega
    apply private_prime_of_not_seven (by omega) (fun _ hp hd hu => shared_neighbor_prime hp hu hd)
    intro k he
    have h := (seven_power_on_hosoya_iff rows k).mp (Or.inr (Or.inr ⟨m,he.symm⟩))
    rcases h with rfl|rfl|rfl
    · simp at he; omega
    · exact h₂ (lower.injective (he.trans (by decide)))
    · exact h₁₀ (lower.injective (he.trans (by decide)))

#print axioms shared_neighbor_prime
#print axioms upper_ne_positive_seven_power
#print axioms upper_has_private_neighbor_prime
#print axioms lower_has_private_neighbor_prime_iff

end Arxiv.«2211.10788»
