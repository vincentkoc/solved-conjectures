import ThetaDiagonalModEight

/-! Products over unordered pairs of odd representatives for primes congruent to one modulo eight. -/

namespace Arxiv.«2501.03234».ThetaSixteen

open Finset
open ThetaDiagonal (U rep sign oddReps)

variable {p : ℕ} [Fact p.Prime]

private def oddLift (a : U p) : U p := if rep a % 2 = 1 then a else -a

private lemma neg_parity (hp : p % 2 = 1) (a : U p) :
    rep (-a) % 2 = 1 ↔ rep a % 2 ≠ 1 := by
  let : NeZero (a : ZMod p) := ⟨a.ne_zero⟩
  have h : rep (-a) = p - rep a := ZMod.val_neg_of_ne_zero (a : ZMod p)
  have hlt : rep a < p := ZMod.val_lt _
  rw [h]; omega

private lemma oddLift_neg (hp : p % 2 = 1) (a : U p) : oddLift (-a) = oddLift a := by
  simp only [oddLift, neg_parity hp, neg_neg]
  split_ifs <;> simp_all

private lemma oddLift_mem (hp : p % 2 = 1) (a : U p) : oddLift a ∈ oddReps p := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  unfold oddLift
  split_ifs with h
  · exact h
  · exact (neg_parity hp a).mpr h

private lemma oddLift_of_mem {a : U p} (ha : a ∈ oddReps p) : oddLift a = a :=
  if_pos (mem_filter.mp ha).2

private lemma oddLift_mul (hp : p % 2 = 1) (a b : U p) :
    oddLift (a * oddLift b) = oddLift (a * b) := by
  change oddLift (a * (if rep b % 2 = 1 then b else -b)) = _
  split_ifs <;> simp [mul_neg, oddLift_neg hp]

omit [Fact p.Prime] in
private lemma lift_sq (a : U p) : oddLift a * oddLift a = a * a := by
  unfold oddLift
  split_ifs <;> simp

private lemma sign_neg (hp : p % 2 = 1) (a : U p) : sign (-a) = -sign a := by
  simp only [sign, neg_parity hp]
  split_ifs <;> simp_all

private lemma sum_rotate (hp : p % 2 = 1) (u : U p) (f : U p → ℤ) :
    ∑ a ∈ oddReps p, f (oddLift (u * a)) = ∑ a ∈ oddReps p, f a := by
  apply sum_nbij' (fun a => oddLift (u * a)) (fun a => oddLift (u⁻¹ * a))
  · intros; apply oddLift_mem hp
  · intros; apply oddLift_mem hp
  · intro a ha
    rw [oddLift_mul hp, inv_mul_cancel_left, oddLift_of_mem ha]
  · intro a ha
    rw [oddLift_mul hp, mul_inv_cancel_left, oddLift_of_mem ha]
  · intros; rfl

private lemma diagonal_zero (hp : p % 8 = 1) :
    ∑ a ∈ oddReps p, sign (a * a) = 0 := by
  have hp2 : p % 2 = 1 := by omega
  obtain ⟨i, hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  let u : U p := Units.mk0 i hi0
  have hu : u * u = -1 := Units.ext (by simpa [u] using hi.symm)
  have hs := sum_rotate hp2 u (fun a => sign (a * a))
  simp_rw [lift_sq, show ∀ a : U p, u * a * (u * a) = -(a * a) by
    intro a; rw [mul_mul_mul_comm, hu, neg_one_mul], sign_neg hp2] at hs
  rw [sum_neg_distrib] at hs
  omega

private def edges {α : Type*} [LinearOrder α] (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter fun e => e.1 < e.2

private lemma edges_insert_max {α : Type*} [LinearOrder α] {s : Finset α} {a : α}
    (ha : ∀ x ∈ s, x < a) : edges (insert a s) = edges s ∪ (s ×ˢ {a}) := by
  ext ⟨x,y⟩
  simp only [edges, mem_filter, mem_product, mem_insert, mem_union, mem_singleton]
  grind

private lemma upper_triangle {α : Type*} [LinearOrder α] (s : Finset α) (f : α → α → ℤ)
    (hsym : ∀ a b, f a b = f b a) :
    ∑ a ∈ s, ∑ b ∈ s, f a b =
      ∑ a ∈ s, f a a + 2 * ∑ e ∈ edges s, f e.1 e.2 := by
  induction s using Finset.induction_on_max with
  | empty => simp [edges]
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax _ h)
    have hd : Disjoint (edges s) (s ×ˢ {a}) := by
      rw [disjoint_left]; rintro ⟨x,y⟩ he hg
      have hy := (mem_product.mp (mem_filter.mp he).1).2
      have hy' : y = a := mem_singleton.mp (mem_product.mp hg).2
      exact ha (hy' ▸ hy)
    simp only [sum_insert ha, sum_add_distrib, edges_insert_max hmax, sum_union hd,
      sum_product, sum_singleton]
    rw [ih]
    have he := sum_congr (s₁ := s) rfl (fun b _ => hsym b a)
    linarith

private lemma edge_products {α G : Type*} [LinearOrder α] [CommMonoid G] (s : Finset α)
    (f : α → G) : (∏ e ∈ edges s, f e.1 * f e.2) * (∏ x ∈ s, f x) =
      (∏ x ∈ s, f x)^s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp [edges]
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax _ h)
    have hd : Disjoint (edges s) (s ×ˢ {a}) := by
      rw [disjoint_left]; rintro ⟨x,y⟩ he hg
      have hy := (mem_product.mp (mem_filter.mp he).1).2
      have hy' : y = a := mem_singleton.mp (mem_product.mp hg).2
      exact ha (hy' ▸ hy)
    simp only [edges_insert_max hmax, prod_union hd, prod_product, prod_singleton,
      prod_mul_distrib, prod_const, card_singleton, pow_zero, one_mul, prod_insert ha, card_insert_of_notMem ha, mul_pow, pow_succ]
    calc
      _ = ((∏ e ∈ edges s, f e.1 * f e.2) * ∏ x ∈ s, f x) *
          ((f a)^s.card * f a) * ∏ x ∈ s, f x := by rw [prod_mul_distrib]; ac_rfl
      _ = _ := by rw [ih]; ac_rfl

private lemma edge_card {α : Type*} [LinearOrder α] (s : Finset α) :
    (s.card : ℤ)^2 = s.card + 2 * ((edges s).card : ℤ) := by
  simpa [sq] using upper_triangle s (fun _ _ => 1) (by simp)

private noncomputable local instance unitOrder : LinearOrder (U p) :=
  LinearOrder.lift' rep (fun _ _ h => Units.ext (ZMod.val_injective p h))

private lemma odd_eq_of_sq {a b : U p} (hp : p % 2 = 1)
    (ha : a ∈ oddReps p) (hb : b ∈ oddReps p) (h : a*a = b*b) : a = b := by
  have he : (a : ZMod p)^2 = (b : ZMod p)^2 := by
    simpa [sq] using congrArg Units.val h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with e | e
  · exact Units.ext e
  · have en : a = -b := Units.ext e
    have ho := (mem_filter.mp ha).2
    rw [en] at ho
    exact ((neg_parity hp b).mp ho (mem_filter.mp hb).2).elim

private lemma odd_roots (hp : p % 2 = 1) (c : U p) :
    (∑ a ∈ oddReps p, if a*a = c then (1 : ℤ) else 0) =
      if IsSquare (c : ZMod p) then 1 else 0 := by
  classical
  split_ifs with hs
  · obtain ⟨x,hx⟩ := hs
    have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at hx; exact c.ne_zero hx
    let a : U p := oddLift (Units.mk0 x hx0)
    have ha : a ∈ oddReps p := oddLift_mem hp _
    have hsq : a*a = c := by rw [show a*a = _ from lift_sq _]; exact Units.ext hx.symm
    have he (b : U p) (hb : b ∈ oddReps p) : b*b = c ↔ b = a := by
      constructor
      · intro e; exact odd_eq_of_sq hp hb ha (e.trans hsq.symm)
      · rintro rfl; exact hsq
    rw [sum_congr rfl (fun b hb => if_congr (he b hb) rfl rfl)]
    simp [ha]
  · apply sum_eq_zero
    intro b _
    rw [if_neg]
    intro h
    exact hs ⟨(b : ZMod p), congrArg Units.val h.symm⟩

private lemma lift_eq_iff (hp : p % 2 = 1) {c : U p} (hc : c ∈ oddReps p) (a : U p) :
    oddLift a = c ↔ a = c ∨ a = -c := by
  constructor
  · unfold oddLift; split_ifs
    · exact Or.inl
    · exact fun h => Or.inr (by simpa using congrArg Neg.neg h)
  · rintro (rfl | rfl)
    · exact oddLift_of_mem hc
    · rw [oddLift_neg hp, oddLift_of_mem hc]

private lemma root_fiber (hp : p % 8 = 1) {c : U p} (hc : c ∈ oddReps p) :
    (∑ a ∈ oddReps p, if oddLift (a*a) = c then (1 : ℤ) else 0) =
      if IsSquare (c : ZMod p) then 2 else 0 := by
  classical
  have hp2 : p % 2 = 1 := by omega
  have hne : c ≠ -c := by
    intro h
    have ho := (mem_filter.mp hc).2
    exact (neg_parity hp2 c).mp (h ▸ ho) ho
  have he (a : U p) :
      (if oddLift (a*a) = c then (1 : ℤ) else 0) =
      (if a*a = c then 1 else 0) + (if a*a = -c then 1 else 0) := by
    simp only [lift_eq_iff hp2 hc]
    split_ifs <;> grind
  simp_rw [he]
  rw [sum_add_distrib, odd_roots hp2, odd_roots hp2]
  have hn := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mpr (by omega)
  have hneg (x : ZMod p) (hx : IsSquare x) : IsSquare (-x) := by simpa using hn.mul hx
  have iffneg : IsSquare ((-c : U p) : ZMod p) ↔ IsSquare (c : ZMod p) :=
    ⟨fun h => by simpa using hneg _ h, hneg _⟩
  simp only [iffneg]
  split_ifs <;> norm_num

private lemma edge_fiber (hp : p % 8 = 1) {c : U p} (hc : c ∈ oddReps p) :
    ((edges (oddReps p)).filter fun e => oddLift (e.1*e.2) = c).card =
      p / 4 - (if IsSquare (c : ZMod p) then 1 else 0) := by
  classical
  have hp2 : p % 2 = 1 := by omega
  let f (a b : U p) : ℤ := if oddLift (a*b) = c then 1 else 0
  have h := upper_triangle (oddReps p) f (fun a b => by simp only [f, mul_comm a b])
  have hr (a : U p) : ∑ b ∈ oddReps p, f a b = 1 := by
    exact (sum_rotate hp2 a (fun x => if x = c then (1 : ℤ) else 0)).trans (by simp [hc])
  simp_rw [hr] at h
  simp only [f, sum_const, nsmul_eq_mul, mul_one, ThetaDiagonal.card_oddReps hp2,
    root_fiber hp hc, sum_boole] at h
  split_ifs at * <;> omega

/-- Product in the prime field of the odd least representatives that are quadratic nonresidues. -/
noncomputable def oddNonresidueProduct (p : ℕ) [Fact p.Prime] : ZMod p :=
  ∏ a ∈ oddReps p, if IsSquare (a : ZMod p) then 1 else (a : ZMod p)

private noncomputable def allProduct (p : ℕ) [Fact p.Prime] : ZMod p :=
  ∏ a ∈ oddReps p, (a : ZMod p)

private noncomputable def squareProduct (p : ℕ) [Fact p.Prime] : ZMod p :=
  ∏ a ∈ oddReps p, if IsSquare (a : ZMod p) then (a : ZMod p) else 1

private lemma product_partition : squareProduct p * oddNonresidueProduct p = allProduct p := by
  unfold squareProduct oddNonresidueProduct allProduct
  rw [← prod_mul_distrib]
  apply prod_congr rfl; intro a _
  split_ifs <;> simp

private lemma wilson_half (hp : p % 8 = 1) : allProduct p ^ 2 = -1 := by
  have hp2 : p % 2 = 1 := by omega
  have he := congrArg (Units.coeHom (ZMod p)) (FiniteField.prod_univ_units_id_eq_neg_one (K := ZMod p))
  rw [map_prod, ← prod_filter_mul_prod_filter_not univ (fun a : U p => rep a % 2 = 1)] at he
  have hs : (∏ a : U p with ¬rep a % 2 = 1, (a : ZMod p)) =
      ∏ a ∈ oddReps p, -(a : ZMod p) := by
    apply prod_nbij' (fun a => -a) (fun a => -a) <;> simp [oddReps, neg_parity hp2]
    intro a ha; have := neg_parity hp2 a; omega
  change allProduct p * (∏ a : U p with ¬rep a % 2 = 1, (a : ZMod p)) = -1 at he
  rw [hs, prod_neg, ThetaDiagonal.card_oddReps hp2,
    (show Even (p/2) from Nat.even_iff.mpr (by omega)).neg_one_pow, one_mul] at he
  exact (sq _).trans he

private lemma norm_product (hp : p % 8 = 1) :
    (∏ e ∈ edges (oddReps p), (oddLift (e.1*e.2) : ZMod p)) * squareProduct p =
      allProduct p ^ (p/4) := by
  classical
  let O := oddReps p
  let X := edges O
  have hm (e : U p × U p) (_ : e ∈ X) : oddLift (e.1*e.2) ∈ O :=
    oddLift_mem (by omega) _
  have he := prod_fiberwise_of_maps_to' hm (fun a : U p => (a : ZMod p))
  simp only [prod_const] at he
  change (∏ e ∈ X, (oddLift (e.1*e.2) : ZMod p)) * squareProduct p = _
  rw [← he, squareProduct, ← prod_mul_distrib, allProduct, ← prod_pow]
  apply prod_congr rfl; intro c hc
  rw [edge_fiber hp hc]
  split_ifs
  · have hpos : 1 ≤ p/4 := by have := (Fact.out : p.Prime).two_le; omega
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  · simp

private lemma lift_factor (a : U p) :
    (a : ZMod p) = (sign a : ZMod p) * (oddLift a : ZMod p) := by
  unfold sign oddLift
  split_ifs <;> simp

private noncomputable def negCount (p : ℕ) [Fact p.Prime] : ℕ :=
  ((edges (oddReps p)).filter fun e => sign (e.1*e.2) = -1).card

private lemma sign_count_product :
    (∏ e ∈ edges (oddReps p), (sign (e.1 * e.2) : ZMod p)) =
      (-1 : ZMod p) ^ negCount p := by
  unfold negCount
  rw [← prod_const (b := (-1 : ZMod p)), prod_filter]
  apply prod_congr rfl; intro e _
  unfold sign
  split_ifs <;> norm_num at *

private lemma odd_product_sign (hp : p % 8 = 1) :
    oddNonresidueProduct p = (-1 : ZMod p)^(p/8 + negCount p) := by
  let O := oddReps p
  let X := edges O
  let P := allProduct p
  let Z := ∏ e ∈ X, (oddLift (e.1*e.2) : ZMod p)
  let E : ZMod p := (-1)^(negCount p)
  have hp2 : p % 2 = 1 := by omega
  have raw := edge_products O (fun a : U p => (a : ZMod p))
  have hh : (∏ e ∈ X, (e.1 : ZMod p) * (e.2 : ZMod p)) = E * Z := by
    change (∏ e ∈ X, (((e.1*e.2 : U p)) : ZMod p)) = _
    conv_lhs => arg 2; intro e; rw [lift_factor]
    rw [prod_mul_distrib, sign_count_product]
  change (∏ e ∈ X, (e.1 : ZMod p) * (e.2 : ZMod p)) * P = P^(oddReps p).card at raw
  rw [hh, ThetaDiagonal.card_oddReps hp2] at raw
  have hnorm : Z * squareProduct p = P^(p/4) := norm_product hp
  have hhalf : p/2 = p/4 + p/4 := by omega
  have heq : P^(p/4) * (E * oddNonresidueProduct p) = P^(p/4) * P^(p/4) := by
    calc
      _ = E * Z * (squareProduct p * oddNonresidueProduct p) := by rw [← hnorm]; ac_rfl
      _ = _ := by rw [product_partition, raw, hhalf, pow_add]
  have hP : P ≠ 0 := prod_ne_zero_iff.mpr (fun a _ => a.ne_zero)
  have hcancel := mul_left_cancel₀ (pow_ne_zero _ hP) heq
  have hp4 : p/4 = 2*(p/8) := by omega
  rw [hp4, pow_mul, show P^2 = -1 from wilson_half hp] at hcancel
  have hE : E * E = 1 := by
    change (-1 : ZMod p)^_ * (-1)^_ = 1
    rw [← mul_pow]; simp
  rw [pow_add]
  change oddNonresidueProduct p = (-1)^(p/8) * E
  rw [← hcancel]
  calc _ = (E * E) * oddNonresidueProduct p := by rw [hE, one_mul]
       _ = _ := by ac_rfl
private lemma S_residue_parity (hp : p % 8 = 1) :
    S p ≡ 8 * ((p / 8 + negCount p : ℕ) : ℤ) [ZMOD 16] := by
  have hp2 : p % 2 = 1 := by omega
  have hS := ThetaDiagonal.S_eq_odd_square (p := p) hp2
  have htri := upper_triangle (oddReps p) (fun a b => sign (b*a)) (fun a b => by rw [mul_comm])
  rw [htri, diagonal_zero hp, zero_add] at hS
  have hs (e : U p × U p) : sign (e.2*e.1) =
      1 - 2 * (if sign (e.1*e.2) = -1 then 1 else 0 : ℤ) := by
    rw [mul_comm e.2]; unfold sign; split_ifs <;> norm_num at *
  simp_rw [hs] at hS
  rw [sum_sub_distrib, ← mul_sum] at hS
  simp only [sum_const, nsmul_eq_mul, mul_one, sum_boole] at hS
  change S p = 2 * (2 * (((edges (oddReps p)).card : ℤ) - 2 * (negCount p : ℤ))) at hS
  have hcard := edge_card (oddReps p)
  rw [ThetaDiagonal.card_oddReps hp2,
    show ((p/2 : ℕ) : ℤ) = 4 * ((p/8 : ℕ) : ℤ) by omega] at hcard
  have h : S p = 32 * ((p/8 : ℕ) : ℤ)^2 - 8 * (p/8 : ℕ) - 8 * (negCount p : ℤ) := by
    nlinarith only [hS, hcard]
  rw [h, Nat.cast_add]
  unfold Int.ModEq
  omega

private lemma neg_unit_distinct (hp : p % 2 = 1) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have hu : (-1 : U p) = 1 := Units.ext h
  have hneg := neg_parity hp (1 : U p)
  rw [hu] at hneg
  tauto

/-- Exact residue in the remaining prime class, classified by the product of the odd nonresidues. -/
theorem S_mod_sixteen (hp : p % 8 = 1) :
    S p ≡ (if oddNonresidueProduct p = -1 then 8 else 0) [ZMOD 16] := by
  have hS := S_residue_parity hp
  have hQ := odd_product_sign hp
  rw [neg_one_pow_eq_pow_mod_two] at hQ
  rcases Nat.mod_two_eq_zero_or_one (p / 8 + negCount p) with he | he
  · rw [he, pow_zero] at hQ
    rw [hQ, if_neg (Ne.symm (neg_unit_distinct (by omega)))]
    unfold Int.ModEq at *; omega
  · rw [he, pow_one] at hQ
    rw [if_pos hQ]
    unfold Int.ModEq at *; omega

/-- The odd-nonresidue product can take only the two square roots of unity. -/
theorem oddNonresidueProduct_eq_one_or_neg_one (hp : p % 8 = 1) :
    oddNonresidueProduct p = 1 ∨ oddNonresidueProduct p = -1 := by
  rw [odd_product_sign hp, neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (p / 8 + negCount p) with he | he <;> simp [he]

/-- A negative product certifies nonvanishing of the original theta sum. -/
theorem S_ne_zero_of_oddNonresidueProduct (hp : p % 8 = 1)
    (h : oddNonresidueProduct p = -1) : S p ≠ 0 := by
  have hs := S_mod_sixteen hp
  rw [if_pos h] at hs
  unfold Int.ModEq at hs
  omega

end Arxiv.«2501.03234».ThetaSixteen

#print axioms Arxiv.«2501.03234».ThetaSixteen.S_mod_sixteen
#print axioms Arxiv.«2501.03234».ThetaSixteen.oddNonresidueProduct_eq_one_or_neg_one
#print axioms Arxiv.«2501.03234».ThetaSixteen.S_ne_zero_of_oddNonresidueProduct
