import Erdos722HarmonicQuadruples
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Direct products of Steiner quadruple systems

Four points form a product block when their projections to each factor are
either four distinct points of a block or two equal pairs. See A. Rosa,
*Combinatorial Design Theory — Notes*, the product construction for SQSs.
-/

namespace Erdos722.QuadrupleProduct

open Finset
open scoped Multiset

variable {V W : Type*} [DecidableEq V]

private def valid (H : Finset (Finset V)) (m : Multiset V) : Prop :=
  m.toFinset ∈ H ∨ ∀ x, Even (m.count x)

private def four (a b c d : V) : Multiset V := a ::ₘ b ::ₘ c ::ₘ d ::ₘ 0

private theorem repeated {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) (x y z : V) :
    valid H (four x x y z) ↔ y = z := by
  have small : ({x, y, z} : Finset V) ∉ H := fun h ↦ by
    have hc := hH.1 _ h
    have hb : ({x, y, z} : Finset V).card ≤ 3 := card_le_three
    omega
  simp only [valid, four, Multiset.toFinset_cons, Multiset.toFinset_zero, insert_empty_eq,
    insert_idem, small, false_or]
  constructor
  · intro h
    by_contra hy
    have := h y
    simp only [Nat.even_iff, Multiset.count_cons, Multiset.count_zero, if_neg hy] at this
    split_ifs at this
  · rintro rfl a
    simp only [Nat.even_iff, Multiset.count_cons, Multiset.count_zero]
    split_ifs <;> decide

private theorem unique_coordinate {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4)
    (a b c : V) : ∃! w, valid H (four a b c w) := by
  by_cases hab : a = b
  · subst b
    simpa only [repeated hH] using (show ∃! w, c = w from ⟨c, rfl, fun w h ↦ h.symm⟩)
  by_cases hac : a = c
  · subst c
    have perm (w : V) : four a b a w = four a a b w := by
      simp only [four, ← Multiset.singleton_add]
      ac_rfl
    simp_rw [perm, repeated hH]
    exact ⟨b, rfl, fun w h ↦ h.symm⟩
  by_cases hbc : b = c
  · subst c
    have perm (w : V) : four a b b w = four b b a w := by
      simp only [four, ← Multiset.singleton_add]
      ac_rfl
    simp_rw [perm, repeated hH]
    exact ⟨a, rfl, fun w h ↦ h.symm⟩
  let S : Finset V := {a, b, c}
  have hs : S.card = 3 := card_eq_three.mpr ⟨a,b,c,hab,hac,hbc,rfl⟩
  have toFin (w : V) : (four a b c w).toFinset = insert w S := by
    ext v
    simp [four, S, or_comm, or_left_comm]
  have valid_iff (w : V) : valid H (four a b c w) ↔ insert w S ∈ H := by
    rw [valid, toFin]
    refine or_iff_left (fun h ↦ ?_)
    by_cases hw : w = a
    · have := h b
      simp [four, hbc, Ne.symm hab, hw] at this
    · have := h a
      simp [four, hab, hac, Ne.symm hw] at this
  obtain ⟨B, ⟨hB, hSB⟩, uniq⟩ := hH.2 S hs
  obtain ⟨w, _, hw⟩ := exists_eq_insert_iff.mpr ⟨hSB, by rw [hs, hH.1 _ hB]⟩
  have fresh {x : V} (hx : insert x S ∈ H) : x ∉ S := by
    intro hmem
    rw [insert_eq_of_mem hmem] at hx
    have := hH.1 _ hx
    omega
  have hwB : insert w S ∈ H := hw ▸ hB
  refine ⟨w, (valid_iff w).mpr hwB, ?_⟩
  intro v hv
  have hvB := (valid_iff v).mp hv
  have hi := (uniq (insert v S) ⟨hvB, subset_insert _ _⟩).trans hw.symm
  have hmem : v ∈ insert w S := hi ▸ mem_insert_self v S
  exact (mem_insert.mp hmem).resolve_right (fresh hvB)

private theorem mapped_quad {A D : Type*} [DecidableEq A] (f : A → D) {a b c w : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hw : w ∉ ({a,b,c} : Finset A)) :
    ((insert w {a,b,c} : Finset A).val.map f) = four (f a) (f b) (f c) (f w) := by
  rw [insert_val_of_notMem hw, insert_val_of_notMem (show a ∉ ({b,c} : Finset A) by simp [hab,hac]),
    insert_val_of_notMem (show b ∉ ({c} : Finset A) by simp [hbc])]
  simp only [singleton_val, four, ← Multiset.singleton_add]
  ac_rfl

private theorem first_duplicate {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) (a b c : V) :
    valid H (four a b c a) ↔ b = c := by
  convert repeated hH a b c using 2
  simp only [four, ← Multiset.singleton_add]
  ac_rfl

private theorem second_duplicate {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) (a b c : V) :
    valid H (four a b c b) ↔ a = c := by
  convert repeated hH b a c using 2
  simp only [four, ← Multiset.singleton_add]
  ac_rfl

private theorem third_duplicate {H : Finset (Finset V)} (hH : H.IsBlockDesign 3 4) (a b c : V) :
    valid H (four a b c c) ↔ a = b := by
  convert repeated hH c a b using 2
  simp only [four, ← Multiset.singleton_add]
  ac_rfl

variable {X : Type*} [DecidableEq W] [Fintype X]

/-- Project a proposed four-set to each factor, retaining multiplicities. -/
noncomputable def blocks (H : Finset (Finset V)) (G : Finset (Finset W)) (e : X ≃ V × W) :
    Finset (Finset X) := by
  classical
  exact univ.filter fun B ↦ B.card = 4 ∧ valid H (B.val.map fun x ↦ (e x).1) ∧
    valid G (B.val.map fun x ↦ (e x).2)

/-- Two Steiner quadruple systems give a Steiner quadruple system on the
Cartesian product, transported to any equivalent finite ground set. -/
theorem blocks_isBlockDesign {H : Finset (Finset V)} {G : Finset (Finset W)}
    (hH : H.IsBlockDesign 3 4) (hG : G.IsBlockDesign 3 4) (e : X ≃ V × W) :
    (blocks H G e).IsBlockDesign 3 4 := by
  classical
  let f := fun x : X ↦ (e x).1
  let g := fun x : X ↦ (e x).2
  have memB (B : Finset X) : B ∈ blocks H G e ↔ B.card = 4 ∧
      valid H (B.val.map f) ∧ valid G (B.val.map g) := by simp [blocks, f, g]
  refine ⟨fun B hB ↦ ((memB B).mp hB).1, ?_⟩
  intro S hS
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp hS
  obtain ⟨u,hu,uu⟩ := unique_coordinate hH (f a) (f b) (f c)
  obtain ⟨v,hv,uv⟩ := unique_coordinate hG (g a) (g b) (g c)
  let w := e.symm (u,v)
  have fw : f w = u := by simp [w,f]
  have gw : g w = v := by simp [w,g]
  have extp {i j : X} (hf : f i = f j) (hg : g i = g j) : i = j :=
    e.injective (Prod.ext hf hg)
  have fresh : w ∉ ({a,b,c} : Finset X) := by
    simp only [mem_insert, mem_singleton]
    rintro (h | h | h)
    · replace hu := (first_duplicate hH _ _ _).mp ((h ▸ fw.symm) ▸ hu)
      replace hv := (first_duplicate hG _ _ _).mp ((h ▸ gw.symm) ▸ hv)
      exact hbc (extp hu hv)
    · replace hu := (second_duplicate hH _ _ _).mp ((h ▸ fw.symm) ▸ hu)
      replace hv := (second_duplicate hG _ _ _).mp ((h ▸ gw.symm) ▸ hv)
      exact hac (extp hu hv)
    · replace hu := (third_duplicate hH _ _ _).mp ((h ▸ fw.symm) ▸ hu)
      replace hv := (third_duplicate hG _ _ _).mp ((h ▸ gw.symm) ▸ hv)
      exact hab (extp hu hv)
  refine ⟨insert w {a,b,c}, ⟨(memB _).mpr ⟨by rw [card_insert_of_notMem fresh,hS], ?_, ?_⟩,
    subset_insert _ _⟩, ?_⟩
  · rwa [mapped_quad f hab hac hbc fresh, fw]
  · rwa [mapped_quad g hab hac hbc fresh, gw]
  · rintro B ⟨hB, hs⟩
    obtain ⟨hb4, b1, b2⟩ := (memB _).mp hB
    obtain ⟨z,hz,rfl⟩ := exists_eq_insert_iff.mpr ⟨hs, by rw [hS,hb4]⟩
    rw [mapped_quad f hab hac hbc hz] at b1
    rw [mapped_quad g hab hac hbc hz] at b2
    rw [extp ((uu _ b1).trans fw.symm) ((uv _ b2).trans gw.symm)]

/-- The spectrum of orders of Steiner quadruple systems is multiplicatively closed. -/
theorem exists_product {m n : ℕ} {H : Finset (Finset (Fin m))} {G : Finset (Finset (Fin n))}
    (hH : H.IsBlockDesign 3 4) (hG : G.IsBlockDesign 3 4) :
    ∃ B : Finset (Finset (Fin (m * n))), B.IsBlockDesign 3 4 :=
  ⟨_, blocks_isBlockDesign hH hG finProdFinEquiv.symm⟩

/-- Powers of ten above the order 100 lie outside both the binary and the
ternary projective quadruple-system parameter families. -/
theorem ten_power_new_orders (d : ℕ) (hd : 3 ≤ d) :
    (∀ i : ℕ, 10 ^ d ≠ 2 ^ i) ∧ (∀ i : ℕ, 10 ^ d ≠ 3 ^ i + 1) := by
  have h5 : 5 ∣ (10 : ℕ) ^ d := dvd_pow (by decide : 5 ∣ (10 : ℕ)) (by omega)
  have h8 : 8 ∣ (10 : ℕ) ^ d :=
    (show 8 ∣ (10 : ℕ) ^ 3 by decide).trans (pow_dvd_pow 10 hd)
  constructor
  · intro i he
    rw [he] at h5
    have := (by decide : Nat.Prime 5).dvd_of_dvd_pow h5
    omega
  · intro i he
    have residue (j : ℕ) : 3 ^ j % 8 = 1 ∨ 3 ^ j % 8 = 3 := by
      induction j with
      | zero => decide
      | succ j ih =>
        rw [pow_succ, Nat.mul_mod]
        rcases ih with h | h <;> rw [h] <;> decide
    rw [he] at h8
    rcases residue i with h | h <;> omega

/-- Iterating the product on the order-ten harmonic system gives all positive powers of ten. -/
theorem exists_ten_power (d : ℕ) : ∃ H : Finset (Finset (Fin (10 ^ (d + 1)))), H.IsBlockDesign 3 4 := by
  have seed : ∃ H : Finset (Finset (Fin 10)), H.IsBlockDesign 3 4 := by
    exact Erdos722.Harmonic.exists_ternary_quadruple_design 2 (by decide)
  induction d with
  | zero => simpa using seed
  | succ d ih =>
    obtain ⟨H,hH⟩ := ih
    obtain ⟨G,hG⟩ := seed
    rw [pow_succ (10 : ℕ) (d + 1)]
    exact exists_product hH hG

/-- Arbitrarily large orders outside both previously constructed order families
carry Steiner quadruple systems. -/
theorem arbitrarily_large_mixed_orders (N : ℕ) :
    ∃ n > N, (∀ i : ℕ, n ≠ 2 ^ i) ∧ (∀ i : ℕ, n ≠ 3 ^ i + 1) ∧
      ∃ H : Finset (Finset (Fin n)), H.IsBlockDesign 3 4 := by
  obtain ⟨h2,h3⟩ := ten_power_new_orders (N + 3) (by omega)
  have := Nat.lt_pow_self (n := N + 3) (by decide : 1 < (10 : ℕ))
  exact ⟨10 ^ (N + 3), by omega, h2, h3, exists_ten_power (N + 2)⟩

#print axioms blocks_isBlockDesign
#print axioms exists_product
#print axioms ten_power_new_orders
#print axioms exists_ten_power
#print axioms arbitrarily_large_mixed_orders

end Erdos722.QuadrupleProduct
