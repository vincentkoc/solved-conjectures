import Green50Sharp

/-! # When iterated sums fill the affine span

We bound the density of a set admitting a long shortest word by applying the
diameter-two case of Kleitman's theorem to each binary fibre. See
`AFFINE-SPANNING-DIAMETER.md` for the source and the exact ten-summand threshold.
-/

open Finset

namespace Green50Diameter

open Green50Downsets (Cube slice slice_card)

private theorem dist_cons {n : ℕ} (a b : ZMod 2) (x y : Cube n) :
    hammingDist (Fin.cons a x : Cube (n + 1)) (Fin.cons b y : Cube (n + 1)) =
      (if a ≠ b then 1 else 0) + hammingDist x y := by
  simp [hammingDist, card_filter, Fin.sum_univ_succ]

private theorem triangle_even {n : ℕ} (x y z : Cube n) :
    Even (hammingDist x y + hammingDist y z + hammingDist x z) := by
  induction n with
  | zero => simp [hammingDist]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, ← Fin.cons_self_tail z]
    rw [dist_cons, dist_cons, dist_cons]
    have bit (a b c : ZMod 2) :
        Even ((if a ≠ b then 1 else 0 : ℕ) + (if b ≠ c then 1 else 0) +
          (if a ≠ c then 1 else 0)) := by decide +revert
    obtain ⟨i, hi⟩ := ih (Fin.tail x) (Fin.tail y) (Fin.tail z)
    obtain ⟨j, hj⟩ := bit (x 0) (y 0) (z 0)
    exact ⟨i + j, by omega⟩

private theorem pair_of_adjacent {n : ℕ} {x y z : Cube n} (hne : x ≠ y)
    (hxy : hammingDist x y ≤ 1) (hyz : hammingDist y z ≤ 1) (hxz : hammingDist x z ≤ 1) :
    z = x ∨ z = y := by
  by_contra! hn
  have hx := hammingDist_pos.mpr hne
  have hy := hammingDist_pos.mpr hn.2.symm
  have hz := hammingDist_pos.mpr hn.1.symm
  obtain ⟨k, hk⟩ := triangle_even x y z
  omega

-- Start at dimension three; paired complementary vertices are distance three.
private theorem dim_three : ∀ A : Finset (Cube 3),
    (∀ x ∈ A, ∀ y ∈ A, hammingDist x y ≤ 2) → A.card ≤ 4 := by
  decide +kernel
/-- Kleitman's diameter-two bound in a binary cube of dimension at least three. -/
theorem anticode {n : ℕ} (hn : 3 ≤ n) (A : Finset (Cube n))
    (hA : ∀ x ∈ A, ∀ y ∈ A, hammingDist x y ≤ 2) : A.card ≤ n + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction m with
  | zero => exact dim_three A hA
  | succ m ih =>
    let B := slice A 0
    let C := slice A 1
    have dist (a b : ZMod 2) {x y} (hx : x ∈ slice A a) (hy : y ∈ slice A b) :
        (if a ≠ b then 1 else 0) + hammingDist x y ≤ 2 := by
      rw [← dist_cons]
      exact hA _ (mem_filter.mp hx).2 _ (mem_filter.mp hy).2
    have mixed {x y} (hx : x ∈ B) (hy : y ∈ C) : hammingDist x y ≤ 1 := by
      have h := dist 0 1 hx hy
      norm_num at h
      omega
    have proj : ∀ x ∈ B ∪ C, ∀ y ∈ B ∪ C, hammingDist x y ≤ 2 := by
      intro x hx y hy
      rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
      · simpa using dist 0 0 hx hy
      · exact (mixed hx hy).trans (by decide)
      · rw [hammingDist_comm]; exact (mixed hy hx).trans (by decide)
      · simpa using dist 1 1 hx hy
    have cover (x) (hx : x ∈ B ∩ C) (z) (hz : z ∈ B ∪ C) : hammingDist x z ≤ 1 := by
      rcases mem_union.mp hz with hz | hz
      · rw [hammingDist_comm]; exact mixed hz (mem_inter.mp hx).2
      · exact mixed (mem_inter.mp hx).1 hz
    have hj := slice_card A
    have count := card_inter_add_card_union B C
    change B.card + C.card = A.card at hj
    by_cases small : (B ∩ C).card ≤ 1
    · have h₁ := ih (by omega) (B ∪ C) proj
      omega
    · obtain ⟨x, hx, y, hy, hne⟩ := one_lt_card.mp (lt_of_not_ge small)
      have hxy := mixed (mem_inter.mp hx).1 (mem_inter.mp hy).2
      have hs : B ∪ C ⊆ {x, y} := by
        intro z hz
        simpa using pair_of_adjacent hne hxy (cover _ hy _ hz) (cover _ hx _ hz)
      have h₁ := (card_le_card hs).trans card_le_two
      have h₂ : (B ∩ C).card ≤ (B ∪ C).card := card_le_card (fun _ hz =>
        mem_union_left _ (mem_inter.mp hz).1)
      omega

open scoped Pointwise
section
variable {G : Type*} [AddCommGroup G] [Module (ZMod 2) G] [DecidableEq G]
variable {k : ℕ} (v : Fin k → G)
private def evalWord (v : Fin k → G) (x : Cube k) : G := ∑ i, x i • v i

omit [Module (ZMod 2) G] in
private theorem sum_members {ι : Type*} (s : Finset ι) (w : ι → G) {A : Finset G}
    (h : ∀ i ∈ s, w i ∈ A) : ∑ i ∈ s, w i ∈ s.card • A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [card_insert_of_notMem hi, succ_nsmul, add_comm _ A, sum_insert hi]
    exact add_mem_add (h i (mem_insert_self ..)) (ih (fun j hj => h _ (mem_insert_of_mem hj)))

private theorem fibre_distance (A : Finset G) (hv : ∀ i, v i ∈ A)
    (hmin : ∀ m < k, ∑ i, v i ∉ m • A) {g : G} {x y : Cube k}
    (hx : g + evalWord v x ∈ A) (hy : g + evalWord v y ∈ A) :
    hammingDist x y ≤ 2 := by
  classical
  let S := univ.filter (fun i => x i = y i)
  have hself (u : G) : u + u = 0 := by
    rw [← two_smul (ZMod 2) u, show (2 : ZMod 2) = 0 by decide, zero_smul]
  have bit (a b : ZMod 2) : a + b = if a = b then 0 else 1 := by decide +revert
  have hrepr : (g + evalWord v x) + (g + evalWord v y) + (∑ i ∈ S, v i) = ∑ i, v i := by
    rw [show (g + evalWord v x) + (g + evalWord v y) = (g + g) + (evalWord v x + evalWord v y) by abel,
      hself, zero_add]
    dsimp [evalWord, S]
    rw [← sum_add_distrib, sum_filter]
    simp_rw [← add_smul, bit, ite_smul, zero_smul, one_smul]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    split <;> simp
  have hmem : ∑ i, v i ∈ (2 + S.card) • A := by
    rw [← hrepr, add_nsmul]
    apply add_mem_add _ (sum_members S v fun i _ => hv i)
    rw [two_nsmul]
    exact add_mem_add hx hy
  have hcount : hammingDist x y + S.card = k := by
    simpa [hammingDist, S] using (card_filter_add_card_filter_not
      (s := (univ : Finset (Fin k))) (fun i => x i ≠ y i))
  by_contra! h
  exact hmin _ (by omega) hmem
variable [Fintype G]

/-- A shortest word of length k forces density at most (k+1)/2^k. -/
theorem diameter_density (A : Finset G) (hk : 3 ≤ k) (hv : ∀ i, v i ∈ A)
    (hmin : ∀ m < k, ∑ i, v i ∉ m • A) :
    2 ^ k * A.card ≤ (k + 1) * Fintype.card G := by
  classical
  let F (g : G) := univ.filter (fun x : Cube k => g + evalWord v x ∈ A)
  have bound (g : G) : (F g).card ≤ k + 1 :=
    anticode hk _ (fun _ hx _ hy => fibre_distance v A hv hmin (mem_filter.mp hx).2 (mem_filter.mp hy).2)
  have count (x : Cube k) :
      ∑ g : G, (if g + evalWord v x ∈ A then 1 else 0 : ℕ) = A.card := by
    let e := Equiv.addRight (evalWord v x)
    change (∑ g, if e g ∈ A then 1 else 0 : ℕ) = _
    rw [Equiv.sum_comp e (fun y => if y ∈ A then (1 : ℕ) else 0)]
    simp
  have total : ∑ g, (F g).card = 2 ^ k * A.card := by
    simp only [F, card_filter]
    rw [sum_comm]
    simp [count, Cube, Fintype.card_pi]
  rw [← total]
  simpa [Nat.mul_comm] using sum_le_sum (s := (univ : Finset G)) (fun g _ => bound g)

/-- Above the spanning-diameter threshold the r-fold sumset stops growing. -/
theorem sum_stabilizes {r : ℕ} (hr : 2 ≤ r) (A : Finset G) (h₀ : 0 ∈ A)
    (hA : (r + 2) * Fintype.card G < 2 ^ (r + 1) * A.card) : (r + 1) • A = r • A := by
  apply Subset.antisymm _ (nsmul_subset_nsmul_right h₀ (by omega))
  intro x hx
  by_contra hn
  obtain ⟨w, hw⟩ := mem_nsmul.mp hx
  let f (i : Fin (r + 1)) : G := (w i).val
  have he : ∑ i, f i = x := by
    simpa only [List.sum_ofFn] using hw
  have hm (m) (hm : m < r + 1) : ∑ i, f i ∉ m • A := by
    rw [he]
    exact fun h => hn (nsmul_subset_nsmul_right h₀ (by omega) h)
  exact hA.not_ge (diameter_density f A (by omega) (fun i => (w i).property) hm)

omit [Fintype G] in
private theorem sum_eq_span {r : ℕ} (hr : 0 < r) (A : Finset G) (h₀ : 0 ∈ A)
    (hs : (r + 1) • A = r • A) :
    (↑(r • A) : Set G) = Submodule.span (ZMod 2) (A : Set G) := by
  classical
  have stable (j : ℕ) : (r + j) • A = r • A := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.add_succ, succ_nsmul, ih, ← succ_nsmul, hs]
  let W : Submodule (ZMod 2) G :=
    { carrier := (↑(r • A) : Set G)
      zero_mem' := zero_mem_nsmul h₀
      add_mem' := fun hx hy => by
        have he := add_mem_add hx hy
        rw [← add_nsmul, stable] at he
        exact he
      smul_mem' := fun c x hx => by
        rcases (show c = 0 ∨ c = 1 from by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr rfl) with rfl | rfl
        · rw [zero_smul]
          exact zero_mem_nsmul h₀
        · simpa only [one_smul] using hx }
  have hWA : (A : Set G) ⊆ W := by
    change A ⊆ r • A
    simpa only [one_nsmul] using (nsmul_subset_nsmul_right h₀ (show 1 ≤ r by omega))
  refine Set.Subset.antisymm ?_ ((Submodule.span_le).mpr hWA)
  intro x hx
  obtain ⟨w, hw⟩ := mem_nsmul.mp hx
  rw [← hw, List.sum_ofFn]
  exact (Submodule.span (ZMod 2) (A : Set G)).sum_mem (fun i _ => Submodule.subset_span (w i).property)

/-- Density measured inside the linear span suffices for a zero-based family. -/
theorem sum_eq_span_of_density {r : ℕ} (hr : 2 ≤ r) (A : Finset G) (h₀ : 0 ∈ A)
    (hA : (r + 2) * Nat.card (Submodule.span (ZMod 2) (A : Set G)) < 2 ^ (r + 1) * A.card) :
    (↑(r • A) : Set G) = Submodule.span (ZMod 2) (A : Set G) := by
  classical
  let W := Submodule.span (ZMod 2) (A : Set G)
  let B := A.subtype (· ∈ W)
  have inc (a) (ha : a ∈ A) : a ∈ W := Submodule.subset_span ha
  have hB : B.image W.subtype = A := by
    ext a
    constructor
    · rintro ha
      obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
      change z.val ∈ A
      simpa only [B, mem_subtype] using hz
    · intro ha
      exact mem_image.mpr ⟨⟨a, inc a ha⟩, by simpa [B] using ha, rfl⟩
  have hcard : B.card = A.card := by
    rw [← hB, card_image_of_injective _ W.subtype_injective]
  have zeroB : 0 ∈ B := by simpa [B] using h₀
  have hh := sum_stabilizes hr B zeroB (by simpa only [hcard, ← Nat.card_eq_fintype_card] using hA)
  apply sum_eq_span (by omega) A h₀
  have lift := congrArg (fun Z : Finset W => Z.image W.subtype) hh
  simpa only [image_nsmul, hB] using lift

/-- If A occupies more than 3/512 of its affine span, ten summands fill its direction space. -/
theorem tenfold_relative (A : Finset G) {a : G} (ha : a ∈ A)
    (hA : 3 * Nat.card (Submodule.span (ZMod 2) (↑(A + {a}) : Set G)) < 512 * A.card) :
    (↑((10 : ℕ) • A) : Set G) = Submodule.span (ZMod 2) (↑(A + {a}) : Set G) := by
  have hself : a + a = 0 := by
    rw [← two_smul (ZMod 2) a, show (2 : ZMod 2) = 0 by decide, zero_smul]
  have hb : 0 ∈ A + {a} := hself ▸ add_mem_add ha (mem_singleton_self a)
  have h := sum_eq_span_of_density (r := 10) (by norm_num) (A + {a}) hb (by
    rw [card_add_singleton]
    change 12 * Nat.card (Submodule.span (ZMod 2) (↑(A + {a}) : Set G)) < 2048 * A.card
    omega)
  have h₂ : (2 : ℕ) • a = 0 := by rwa [two_nsmul]
  have h₁₀ : (10 : ℕ) • a = 0 := by rw [show 10 = 5 * 2 by decide, mul_smul, h₂, smul_zero]
  simpa only [nsmul_add, nsmul_singleton, h₁₀, singleton_zero, add_zero] using h

end

/-- Green 50 with coefficient one whenever the density in the affine span exceeds 3/512. -/
theorem green_50_dense_span {n : ℕ} (A : Finset (Cube n)) {a : Cube n} (ha : a ∈ A)
    (hA : 3 * Nat.card (Submodule.span (ZMod 2) (↑(A + {a}) : Set (Cube n))) < 512 * A.card) :
    ∃ W : Submodule (ZMod 2) (Cube n),
      (W : Set (Cube n)) = (↑((10 : ℕ) • A) : Set (Cube n)) ∧
      (n : ℝ) - Real.logb 2 (1 / (A.dens : ℝ)) ≤ Module.finrank (ZMod 2) W := by
  classical
  let W := Submodule.span (ZMod 2) (↑(A + {a}) : Set (Cube n))
  refine ⟨W, (tenfold_relative A ha hA).symm, ?_⟩
  have hsize : (A + {a}).card ≤ Fintype.card W := by
    let B := A + {a}
    have inc (x) (hx : x ∈ B) : x ∈ W := Submodule.subset_span hx
    let f (x : B) : W := ⟨x.val, inc _ x.property⟩
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f
      (fun x y h => Subtype.ext (congrArg (fun z : W => (z : Cube n)) h))
  rw [card_add_singleton, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hsize
  have hs : (A.card : ℝ) ≤ 2 ^ Module.finrank (ZMod 2) W := by exact_mod_cast hsize
  have hcard : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr ⟨a, ha⟩
  have den : (A.dens : ℝ) = (A.card : ℝ) / 2 ^ n := by simp [Finset.dens, Cube, Fintype.card_pi]
  rw [den, one_div_div, sub_le_comm]
  apply (Real.le_logb_iff_rpow_le (by norm_num) (div_pos (by positivity) hcard)).mpr
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
  exact div_le_div_of_nonneg_left (by positivity) hcard hs

/-- The density threshold is attained by zero and the coordinate vectors. -/
theorem threshold_example (r : ℕ) :
    ∃ A : Finset (Cube (r + 1)), 0 ∈ A ∧ A.card = r + 2 ∧
      Submodule.span (ZMod 2) (A : Set (Cube (r + 1))) = ⊤ ∧
      r • A ≠ univ := by
  classical
  let e (i : Fin (r + 1)) : Cube (r + 1) := Pi.single i 1
  let A := insert (0 : Cube (r + 1)) (univ.image e)
  have ei (i : Fin (r + 1)) : e i ∈ A := mem_insert_of_mem (mem_image_of_mem _ (mem_univ _))
  have nz (i : Fin (r + 1)) : e i ≠ 0 := by
    intro h
    have := congrFun h i
    simp [e] at this
  have inj : Function.Injective e := by
    intro i j he
    by_contra h
    have h' := congrFun he i
    simp [e, Pi.single_eq_of_ne h] at h'
  have hcard : A.card = r + 2 := by
    dsimp [A]
    rw [card_insert_of_notMem (by simpa using (fun i => nz i)), card_image_of_injective _ inj]
    simp
  refine ⟨A, mem_insert_self .., hcard, ?_, ?_⟩
  · apply top_unique
    intro x _
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    have one : e i ∈ Submodule.span (ZMod 2) (A : Set (Cube (r + 1))) := Submodule.subset_span (ei i)
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) (x i) with h | h
    · simp [h]
    · simpa [h, e] using one
  · have sub : A ⊆ Green50Sharp.ball (r + 1) 1 := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · simp [Green50Sharp.ball, Green50Sharp.supp]
      obtain ⟨i, _, rfl⟩ := mem_image.mp hx
      apply mem_filter.mpr ⟨mem_univ _, ?_⟩
      have hs : Green50Sharp.supp (e i) ⊆ {i} := by
        intro j hj
        by_contra h
        have hji : j ≠ i := by simpa using h
        exact (mem_filter.mp hj).2 (by simp [e, Pi.single_eq_of_ne hji])
      simpa using card_le_card hs
    intro heq
    have cov : (0 : Cube (r + 1)) +ᵥ (↑(⊤ : Submodule (ZMod 2) (Cube (r + 1))) : Set (Cube (r + 1))) ⊆
        (↑(r • Green50Sharp.ball (r + 1) 1) : Set (Cube (r + 1))) := by
      intro x _
      apply nsmul_subset_nsmul_left sub
      rw [heq]
      exact mem_univ _
    have hd := Green50Sharp.ball_dimension _ _ cov
    simp [Cube] at hd

#print axioms anticode
#print axioms diameter_density
#print axioms sum_stabilizes
#print axioms sum_eq_span_of_density
#print axioms tenfold_relative
#print axioms green_50_dense_span
#print axioms threshold_example

end Green50Diameter
