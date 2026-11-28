import LucasFibonacciProgressionClosure

/-! Recovering the index class of an actual forward term from congruence tests. -/

namespace Arxiv.«2211.10788».ProgressionClosure

open CongruenceClosure

private lemma upper_strict : StrictMono lucasFibonacciSum := fun _ _ h =>
  Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.fib_mono h.le)) (Nat.fib_add_two_strictMono h)

private lemma lower_strict : StrictMono lowerNeighborAtAddTwo := fun _ _ h =>
  Nat.add_lt_add_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (Nat.fib_add_two_strictMono h) (by decide))
    (Nat.fib_mono h.le)

/-- The only extra bilateral representation of any forward term is at indices 2 and −3. -/
theorem signed_upper_fiber (n : ℕ) (w : ℤ) :
    signed w = lucasFibonacciSum n ↔ w = n ∨ (n = 2 ∧ w = -3) := by
  constructor
  · intro hy
    obtain ⟨k,rfl | rfl⟩ := w.eq_nat_or_neg
    · rw [signed_nat] at hy
      exact Or.inl (by exact_mod_cast upper_strict.injective (Nat.cast_inj.mp hy))
    · rcases k with _ | _ | k
      · have he : lucasFibonacciSum n = lucasFibonacciSum 0 := by
          exact_mod_cast (show (lucasFibonacciSum n : ℤ) = 1 from hy.symm)
        simp [upper_strict.injective he]
      · have he : lucasFibonacciSum n = 3 := by exact_mod_cast (show (lucasFibonacciSum n : ℤ) = 3 from hy.symm)
        have := (both_diagonals_iff_five _).mp ⟨⟨n,rfl⟩,Or.inl he⟩
        omega
      · rw [signed_lower] at hy
        have hab := congrArg abs hy
        simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,Nat.abs_cast] at hab
        have eq : lucasFibonacciSum n = lowerNeighborAtAddTwo k := by exact_mod_cast hab.symm
        have five := (both_diagonals_iff_five _).mp ⟨⟨n,rfl⟩,Or.inr ⟨k,eq⟩⟩
        have hn := upper_strict.injective (show lucasFibonacciSum n = lucasFibonacciSum 2 from five)
        have hk := lower_strict.injective (show lowerNeighborAtAddTwo k = lowerNeighborAtAddTwo 1 from eq.symm.trans five)
        exact Or.inr ⟨hn,by subst k; decide⟩
  · rintro (rfl | ⟨rfl,rfl⟩)
    · exact signed_nat _
    · decide

/-- Forward values recover their index class. The prime five also survives in the class of −3. -/
theorem upper_index_class {d : ℕ} (hd : 0 < d) (r n : ℕ) :
    (∀ M > 0, ∃ t, Hit d r M (lucasFibonacciSum n) t) ↔
      (n:ℤ) ≡ r [ZMOD d] ∨ (n = 2 ∧ (-3:ℤ) ≡ r [ZMOD d]) := by
  rw [progression_local_global hd]
  constructor
  · rintro ⟨w,hw,hy⟩
    rcases (signed_upper_fiber n w).mp hy with rfl | ⟨h,rfl⟩
    · exact Or.inl hw
    · exact Or.inr ⟨h,hw⟩
  · rintro (h | ⟨rfl,h⟩)
    · exact ⟨n,h,signed_nat _⟩
    · exact ⟨-3,h,by decide⟩

#print axioms signed_upper_fiber
#print axioms upper_index_class

end Arxiv.«2211.10788».ProgressionClosure
