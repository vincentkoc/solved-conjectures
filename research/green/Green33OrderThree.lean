import Green33ReflectionRigidity

open Finset Green33Multiplicity Green33ReflectionRigidity
open scoped Pointwise

namespace Green33OrderThree

private def tr (x : ZMod 3) : ℤ := if x = 0 then 2 else -1

-- Center the input classes at the half of s in the quotient (which is −s).
private lemma trace_product (a b s : ZMod 3) :
    tr (a + s) * tr (b + s) = tr (a + b - s) + tr (a + (s - b) - s) := by
  decide +revert

private lemma trace_double (a s : ZMod 3) : tr (a + a - s) = tr (a + s) := by
  decide +revert

private lemma trace_orbit (a s : ZMod 3) :
    tr (a - s) + tr (a + 1 - s) + tr (a + (1 + 1) - s) = 0 := by
  decide +revert

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [DecidableEq G] in
private lemma total_trace (f : G →+ ZMod 3) (hf : Function.Surjective f) (s : G) :
    ∑ t, tr (f t - f s) = 0 := by
  obtain ⟨u, hu⟩ := hf 1
  let v (t : G) := tr (f t - f s)
  have shift (a : G) : ∑ t, v (t + a) = ∑ t, v t :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ fun _ => rfl
  have horbit (t : G) : v t + v (t + u) + v (t + (u + u)) = 0 := by
    simpa only [v, map_add, hu] using trace_orbit (f t) (f s)
  have h := sum_congr (s₁ := univ) rfl fun t _ => horbit t
  simp only [sum_add_distrib, shift, sum_const_zero] at h
  change ∑ t, v t = 0
  omega

omit [Fintype G] in
private lemma reflect_sum (A : Finset G) (s : G) (hs : reflectedPart A s = A) (w : G → ℤ) :
    ∑ b ∈ A, w (s - b) = ∑ b ∈ A, w b := by
  have mem (a : G) (ha : a ∈ A) : s - a ∈ A :=
    (mem_filter.mp (show a ∈ reflectedPart A s by rwa [hs])).2
  exact sum_bij' (fun b _ => s - b) (fun b _ => s - b) mem mem
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => rfl)

omit [AddCommGroup G] in
private lemma weight_fibers {α : Type*} (B : Finset α) (f : α → G) (w : G → ℤ) :
    ∑ s, (((B.filter fun a => f a = s).card : ℤ) * w s) = ∑ a ∈ B, w (f a) := by
  classical
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_mul, sum_filter]
  rw [sum_comm]
  simp

/-- An exact extremal two-basis in a group with an order-three quotient forces
4|A|−7 to be an integer square. -/
theorem square_of_quotient (A : Finset G) (hA : A + A = univ)
    (he : 2 * Fintype.card G = A.card ^ 2 + 2)
    (f : G →+ ZMod 3) (hf : Function.Surjective f) :
    ∃ z : ℤ, z ^ 2 = 4 * (A.card : ℤ) - 7 := by
  classical
  obtain ⟨s, hsym, hdiag, hoff⟩ := extremal_profile A hA he
  let v (t : G) := tr (f t - f s)
  let w (a : G) := tr (f a + f s)
  let S := ∑ a ∈ A, w a
  let U := ∑ p ∈ A ×ˢ A, v (p.1 + p.2)
  have hprod (a b : G) : w a * w b = v (a + b) + v (a + (s - b)) := by
    simpa only [v, w, map_add, map_sub] using trace_product (f a) (f b) (f s)
  have hdouble (a : G) : v (a + a) = w a := by
    simpa only [v, w, map_add] using trace_double (f a) (f s)
  have hrefl (a : G) : ∑ b ∈ A, v (a + (s - b)) = ∑ b ∈ A, v (a + b) :=
    reflect_sum A s hsym (fun b => v (a + b))
  have hsq : S ^ 2 = 2 * U := calc
    _ = ∑ a ∈ A, ∑ b ∈ A, w a * w b := by simp [S, sq, mul_sum, mul_comm]
    _ = 2 * U := by simp only [hprod, sum_add_distrib, hrefl, U, sum_product]; ring
  have hweight : ∑ t, ((reps A t : ℤ) + diagonalReps A t) * v t = U + S := by
    simp only [add_mul, sum_add_distrib, reps, diagonalReps, weight_fibers, hdouble, U, S]
  have hs : reps A s = A.card := by rw [← card_reflectedPart, hsym]
  have hv : v s = 2 := by simp [v, tr]
  have hp (t : G) : ((reps A t : ℤ) + diagonalReps A t) * v t =
      2 * v t + (if t = s then 2 * ((A.card : ℤ) - 2) else 0) := by
    by_cases ht : t = s
    · subst t
      rw [hs, hdiag, hv]
      simp
      ring
    · have h : (reps A t : ℤ) + diagonalReps A t = 2 := by exact_mod_cast hoff t ht
      simp [ht, h]
  have ht : ∑ t, v t = 0 := total_trace f hf s
  have hprofile := sum_congr (s₁ := univ) rfl fun t _ => hp t
  rw [hweight, sum_add_distrib, ← mul_sum, ht] at hprofile
  simp only [mul_zero, zero_add, sum_ite_eq', mem_univ, if_true] at hprofile
  exact ⟨S + 1, by nlinarith only [hsq, hprofile]⟩

/-- For a cyclic modulus divisible by three, reduction modulo three supplies the quotient. -/
theorem square_of_three_dvd (q : ℕ+) (h₃ : 3 ∣ (q : ℕ)) (A : Finset (ZMod q))
    (hA : A + A = univ) (he : 2 * (q : ℕ) = A.card ^ 2 + 2) :
    ∃ z : ℤ, z ^ 2 = 4 * (A.card : ℤ) - 7 :=
  square_of_quotient A hA (by rwa [ZMod.card]) (ZMod.castHom h₃ (ZMod 3)).toAddMonoidHom
    (ZMod.castHom_surjective h₃)

/-- A nonsquare discriminant rules out the smallest candidate basis size
when the cyclic modulus is extremal for that candidate. -/
theorem lt_card_of_nonsquare (q : ℕ+) (k : ℕ) (h₃ : 3 ∣ (q : ℕ))
    (he : 2 * (q : ℕ) = k ^ 2 + 2) (hn : ¬ ∃ z : ℤ, z ^ 2 = 4 * (k : ℤ) - 7)
    (A : Finset (ZMod q)) (hA : A + A = univ) : k < A.card := by
  have hord := order_bound A hA
  rw [ZMod.card, he] at hord
  by_contra! hle
  have hk : A.card = k := by
    apply Nat.le_antisymm hle
    by_contra! hlt
    have := Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)
    omega
  exact hn (hk ▸ square_of_three_dvd q h₃ A hA (hk ▸ he))

/-- At q = 2(15n+5)²+1, equality in the group order bound would force a
square congruent to 3 modulo 5. Every cyclic two-basis therefore has size > 30n+10. -/
theorem strict_size_progression (n : ℕ) (A : Finset (ZMod (2 * (15 * n + 5) ^ 2 + 1)))
    (hA : A + A = univ) : 30 * n + 10 < A.card := by
  let q : ℕ+ := ⟨2 * (15 * n + 5) ^ 2 + 1, by positivity⟩
  have he : 2 * (q : ℕ) = (30 * n + 10) ^ 2 + 2 := by
    change 2 * (2 * (15 * n + 5) ^ 2 + 1) = _
    ring
  have hd : 3 ∣ (q : ℕ) := ⟨150 * n ^ 2 + 100 * n + 17, by
    change 2 * (15 * n + 5) ^ 2 + 1 = _
    ring⟩
  refine lt_card_of_nonsquare q (30 * n + 10) hd he ?_ A hA
  rintro ⟨z,hz⟩
  have h₅ := congrArg (fun x : ℤ => (x : ZMod 5)) hz
  push_cast at h₅
  have hred : (z : ZMod 5)^2 = 3 := by
    simpa only [show (30 : ZMod 5) = 0 by decide, show (10 : ZMod 5) = 0 by decide,
      zero_mul, add_zero, mul_zero, zero_sub, show (-7 : ZMod 5) = 3 by decide] using h₅
  exact (show ∀ t : ZMod 5, t ^ 2 ≠ 3 by decide) _ hred

set_option maxRecDepth 4096 in
/-- Haanpää's Table 3 witness attains the order-three lower bound at modulus 51. -/
theorem minimum_mod_fifty_one :
    (∃ A : Finset (ZMod 51), A.card = 11 ∧ A + A = univ) ∧
    ∀ A : Finset (ZMod 51), A + A = univ → 11 ≤ A.card := by
  constructor
  · exact ⟨{0, 1, 3, 7, 10, 15, 18, 22, 24, 25, 38}, by decide⟩
  · intro A hA
    exact strict_size_progression 0 A hA

#print axioms square_of_quotient
#print axioms square_of_three_dvd
#print axioms lt_card_of_nonsquare
#print axioms strict_size_progression
#print axioms minimum_mod_fifty_one

end Green33OrderThree
