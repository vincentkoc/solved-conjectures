import Mathlib

/-! Coordinate slices for dense families in the binary cube. -/

open Finset
namespace Green50Downsets

/-- In any family of at least three binary marginal splits, either one can cover
this coordinate without losing product density, or omitting it gains a fixed factor
in every marginal on average. The entries are twice the probabilities of omission. -/
theorem choose_slices {r : ℕ} (hr : 3 ≤ r) (a : Fin r → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, a i ≤ 2) :
    (∃ b : Fin r → Bool, (∃ i, b i = false) ∧
      1 ≤ ∏ i, if b i then a i else 2 - a i) ∨ (3/2 : ℝ)^r ≤ ∏ i, a i := by
  classical
  by_cases h : ∃ i, a i ≤ 1
  · obtain ⟨i,hi⟩ := h
    refine Or.inl ⟨fun j => decide (1 < a j),⟨i,by simp [not_lt.mpr hi]⟩,?_⟩
    have hstep (j : Fin r) : 1 ≤ if decide (1 < a j) then a j else 2-a j := by
      by_cases h : 1 < a j <;> simp [h] <;> linarith
    simpa only [prod_const_one] using
      (prod_le_prod (s := (univ : Finset (Fin r))) (f := fun _ => (1 : ℝ))
        (fun _ _ => zero_le_one) (fun j _ => hstep j))
  push Not at h
  by_cases hh : ∀ i, 3/2 ≤ a i
  · right
    simpa only [prod_const, card_univ, Fintype.card_fin] using (prod_le_prod (s := (univ : Finset (Fin r)))
      (f := fun _ => (3/2 : ℝ)) (fun _ _ => by norm_num) (fun i _ => hh i))
  push Not at hh
  obtain ⟨j,hj⟩ := hh
  obtain ⟨i,_,hi⟩ := exists_min_image (univ : Finset (Fin r)) a ⟨j,mem_univ _⟩
  have hm : a i < 3/2 := (hi j (mem_univ _)).trans_lt hj
  let b (k : Fin r) := decide (k ≠ i)
  refine Or.inl ⟨b,⟨i,by simp [b]⟩,?_⟩
  let f (k : Fin r) := if b k then a k else 2-a k
  change 1 ≤ ∏ k, f k
  rw [← prod_erase_mul univ f (mem_univ i)]
  have hf : f i = 2-a i := by simp [f,b]
  rw [hf]
  have hprod : (a i)^(r-1) ≤ ∏ k ∈ univ.erase i, f k := by
    have := prod_le_prod (s := univ.erase i) (f := fun _ => a i) (g := f)
      (fun _ _ => ha i) (fun k hk => by simpa [f,b,ne_of_mem_erase hk] using hi k (mem_univ _))
    simpa using this
  have hpow : (a i)^2 ≤ (a i)^(r-1) := pow_le_pow_right₀ (h i).le (by omega)
  have hl : 1 ≤ (a i)^2 * (2-a i) := by
    have hq : 0 ≤ 1+a i-(a i)^2 := by
      nlinarith [mul_nonneg (show 0 ≤ 3/2-a i by linarith) (show 0 ≤ a i+1/2 by linarith [h i])]
    nlinarith [mul_nonneg (sub_nonneg.mpr (h i).le) hq]
  exact hl.trans (mul_le_mul_of_nonneg_right (hpow.trans hprod) (sub_nonneg.mpr (hb i)))

#print axioms choose_slices
abbrev Cube (n : ℕ) := Fin n → Fin 2
private def slice {n : ℕ} (A : Finset (Cube (n+1))) (b : Fin 2) : Finset (Cube n) :=
  univ.filter fun x => Fin.cons b x ∈ A

private theorem slice_card {n : ℕ} (A : Finset (Cube (n+1))) :
    (slice A 0).card + (slice A 1).card = A.card := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 2)
  have eqf (b : Fin 2) : (slice A b).card =
      ∑ x : Cube n, if e (b,x) ∈ A then 1 else 0 := by
    exact Finset.card_filter _ _
  rw [eqf,eqf,← Fin.sum_univ_two (fun b : Fin 2 => ∑ x : Cube n, if e (b,x) ∈ A then 1 else 0)]
  calc
    _ = ∑ p : Fin 2 × Cube n, if e p ∈ A then (1:ℕ) else 0 := (Fintype.sum_prod_type _).symm
    _ = ∑ y : Cube (n+1), if y ∈ A then (1:ℕ) else 0 := Equiv.sum_comp e (fun y => if y ∈ A then (1:ℕ) else 0)
    _ = _ := by simp

private def holes {r n : ℕ} (x : Fin r → Cube n) : ℕ :=
  (univ.filter fun j => ∀ i, x i j = 0).card

private theorem holes_cons {r n : ℕ} (b : Fin r → Fin 2) (y : Fin r → Cube n) :
    holes (fun i => Fin.cons (b i) (y i)) = (if ∀ i, b i = 0 then 1 else 0) + holes y := by
  simp only [holes,card_filter,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

end Green50Downsets
