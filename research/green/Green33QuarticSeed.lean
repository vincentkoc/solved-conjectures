import Green33ApproximateCovers
import Green33DivisibleOrder

/-! An eighteen-label strict cover of the cyclic group of order 130. -/

open Finset Filter Green33StrictReduction Green33MaximalOrders
open scoped Pointwise Topology

namespace Green33QuarticSeed

/-- Scaling a row of a character graph transports distinct witnesses. -/
theorem character_rows {F K : Type*} [Field F] [Field K] (χ : F →*₀ K)
    (h : ∀ z : K, ∃ a b : F, a ≠ b ∧ a + b = 1 ∧ χ a + χ b = z)
    {s : F} (hs : s ≠ 0) (z : K) :
    ∃ a b : F, a ≠ b ∧ a + b = s ∧ χ a + χ b = z := by
  obtain ⟨a, b, hab, hr, hz⟩ := h (z / χ s)
  refine ⟨s*a, s*b, fun e => hab (mul_left_cancel₀ hs e), ?_, ?_⟩
  · rw [← mul_add, hr, mul_one]
  · rw [map_mul, map_mul, ← mul_add, hz, mul_div_cancel₀ _ (by simpa using hs : χ s ≠ 0)]

/-- Put the character graph in the even layer and the whole vertical axis in
the odd layer. The character and the additive group of its codomain each
require just the indicated strict row coverage. -/
theorem index_two_cover {F K : Type*} [Field F] [Field K] [Fintype F] [Fintype K]
    [DecidableEq F] [DecidableEq K] (χ : F →*₀ K)
    (h : ∀ z : K, ∃ a b : F, a ≠ b ∧ a+b=1 ∧ χ a+χ b=z)
    (hv : ∀ z : K, ∃ u v : K, u ≠ v ∧ u+v=z) :
    let B := (univ : Finset F).image (fun a => ((0 : ZMod 2), a, χ a))
    let O := (univ : Finset K).image (fun v => ((1 : ZMod 2), (0 : F), v))
    StrictCover (B ∪ O) := by
  intro B O
  have hb (a : F) : ((0 : ZMod 2), a, χ a) ∈ B ∪ O :=
    mem_union_left _ (mem_image_of_mem _ (mem_univ a))
  have ho (v : K) : ((1 : ZMod 2), (0 : F), v) ∈ B ∪ O :=
    mem_union_right _ (mem_image_of_mem _ (mem_univ v))
  rintro ⟨e,s,z⟩
  fin_cases e
  · by_cases hs : s = 0
    · subst s
      obtain ⟨u,v,huv,hz⟩ := hv z
      exact ⟨_,ho u,_,ho v,fun eq => huv (congrArg (fun p => p.2.2) eq),
        Prod.ext (by change (1+1 : ZMod 2) = 0; decide) (Prod.ext (zero_add _) hz)⟩
    · obtain ⟨a,b,hab,hs',hz⟩ := character_rows χ h hs z
      exact ⟨_,hb a,_,hb b,fun eq => hab (congrArg (fun p => p.2.1) eq),
        Prod.ext (by change (0+0 : ZMod 2) = 0; decide) (Prod.ext hs' hz)⟩
  · exact ⟨_,hb s,_,ho (z-χ s),fun eq => (by decide : (0 : ZMod 2) ≠ 1) (congrArg Prod.fst eq),
      Prod.ext (by change (0+1 : ZMod 2) = 1; decide)
        (Prod.ext (add_zero _) (by change χ s + (z-χ s) = z; abel))⟩

private def values : Fin 13 → ZMod 5 := ![0,1,3,1,4,3,3,2,2,1,4,2,4]

private instance : Fact (Nat.Prime 13) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The quartic character determined by sending the generator 2 to 3. -/
def quartic : ZMod 13 →*₀ ZMod 5 where
  toFun x := values ⟨x.val, x.val_lt⟩
  map_zero' := by decide
  map_one' := by decide
  map_mul' := by decide +revert

/-- The strict graph sum covers all five colors at every nonzero row. -/
theorem quartic_rows {s : ZMod 13} (hs : s ≠ 0) (z : ZMod 5) :
    ∃ a b : ZMod 13, a ≠ b ∧ a + b = s ∧ quartic a + quartic b = z :=
  character_rows quartic (by decide +kernel) hs z

/-- The even character graph and the five odd multiples of thirteen. -/
def seed : Finset (ZMod 130) :=
  {0,2,8,13,14,32,36,39,56,65,74,91,94,98,116,117,122,128}

set_option maxRecDepth 16384 in
theorem seed_structure (x : ZMod 130) :
    x ∈ seed ↔ (x.val % 2 = 0 ∧ ((x.val / 2 : ℕ) : ZMod 5) = quartic (x.val / 2 : ℕ)) ∨
      (x.val % 2 = 1 ∧ 13 ∣ x.val) := by decide +revert

theorem seed_card : seed.card = 18 := by decide +kernel

/-- The affine image is zero adjoined to the connection set in Lewis,
Table 5 (degree 17). Odd degree adds the involution to the signed generators. -/
theorem lewis_seed : seed.image (fun x => 9*x+65) =
    ({0,65,1,-1,7,-7,26,-26,37,-37,47,-47,49,-49,52,-52,61,-61} : Finset (ZMod 130)) := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem seed_strict : StrictCover seed := by
  change ∀ z : ZMod 130, ∃ a ∈ seed, ∃ b ∈ seed, a ≠ b ∧ a+b=z
  decide +kernel

/-- The exact finite charged certificate has zero missing residues. -/
theorem order_constant_lower : (65 / 162 : ℝ) ≤ orderConstant := by
  have hall : Green33ApproximateCovers.strictSums seed = univ :=
    eq_univ_of_forall fun z => Green33ApproximateCovers.mem_strictSums.mpr (seed_strict z)
  have h := Green33ApproximateCovers.finite_certificate (M := (130 : ℕ+)) seed
  change (130:ℝ) ≤ orderConstant * ((seed.card:ℝ) +
    2 * Real.sqrt (Green33ApproximateCovers.strictSums seed)ᶜ.card)^2 at h
  rw [hall, seed_card] at h
  norm_num at h ⊢
  linarith

/-- On an arithmetic progression of widths p the orders 130p(p−1) have
strict covers of exactly the specified size, for any fixed divisor D. -/
theorem lifted_family (D : ℕ+) :
    ∃ s C : ℕ, 0 < s ∧ ∀ l : ℕ, C + 2 ≤ s*l →
      ∃ N : ℕ+, N.val = 130*(s*l)*(s*l-1) ∧ D.val ∣ N.val ∧
        ∃ A : Finset (ZMod N), StrictCover A ∧ A.card = 18*(s*l+C) := by
  classical
  obtain ⟨s,C,hs,_,H⟩ := Green33DivisibleOrder.divisible_seed_lifts
    (M := (130 : ℕ+)) seed_strict D
  refine ⟨s,C,hs,?_⟩
  intro l hl
  obtain ⟨N,hN,hD,B,hB,hk⟩ := H l (by omega)
  change N.val = 130*(s*l)*(s*l-1) at hN
  change B.card ≤ seed.card*(s*l+C) at hk
  rw [seed_card] at hk
  have hp : 18*(s*l+C) ≤ N.val := by
    rw [hN]
    have hw := Nat.mul_le_mul_left (130*(s*l)) (show 1 ≤ s*l-1 by omega)
    omega
  obtain ⟨A,hBA,_,hA⟩ := exists_subsuperset_card_eq (subset_univ B) hk
    (show 18*(s*l+C) ≤ (univ : Finset (ZMod N)).card by simpa [ZMod.card] using hp)
  refine ⟨N,hN,hD,A,?_,hA⟩
  intro z
  obtain ⟨a,ha,b,hb,hab,he⟩ := hB z
  exact ⟨a,hBA ha,b,hBA hb,hab,he⟩

/-- Arbitrarily large multiples of each prescribed divisor attain the new
constant with strict representations and the absolute tolerance in Green 33. -/
theorem frequently_strict (D : ℕ+) (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ+ in atTop, D.val ∣ N.val ∧ ∃ A : Finset (ZMod N), StrictCover A ∧
      |(A.card : ℝ) / Real.sqrt N - 18 / Real.sqrt 130| < ε := by
  obtain ⟨s,C,hs,H⟩ := lifted_family D
  apply frequently_atTop.mpr
  intro R
  let c := 18 / Real.sqrt 130
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_gt (c * (C+1:ℝ) / ε)
  let l := J + C + R.val + 2
  let p := s*l
  let q := p-1
  have hl : l ≤ p := by simpa [p] using Nat.mul_le_mul_right l hs
  have hpc : C+2 ≤ p := by dsimp [l] at hl; omega
  have hpq : q+1 = p := by dsimp [q]; omega
  have hq : 0 < q := by omega
  have hJq : J ≤ q := by dsimp [l] at hl; omega
  obtain ⟨N,hN,hD,A,hA,hk⟩ := H l hpc
  change N.val = 130*p*q at hN
  change A.card = 18*(p+C) at hk
  have hRN : R.val ≤ N.val := by
    rw [hN]
    have := Nat.mul_le_mul_left (130*p) hq
    dsimp [l] at hl
    omega
  refine ⟨N,hRN,hD,A,hA,?_⟩
  have hpr : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hqr : 0 < (q:ℝ) := by exact_mod_cast hq
  have heq : (q:ℝ)+1 = p := by exact_mod_cast hpq
  have hNr : (N:ℝ) = 130*p*q := by exact_mod_cast hN
  have hkr : (A.card:ℝ) = 18*((p:ℝ)+C) := by exact_mod_cast hk
  have hsq : Real.sqrt N = Real.sqrt 130 * Real.sqrt ((p:ℝ)*q) := by
    rw [hNr, mul_assoc, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 130)]
  have hlow : (q:ℝ) ≤ Real.sqrt ((p:ℝ)*q) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hhigh : Real.sqrt ((p:ℝ)*q) ≤ p := (Real.sqrt_le_iff).mpr ⟨hpr.le, by nlinarith⟩
  have hscale : c * Real.sqrt 130 = 18 := div_mul_cancel₀ _ (by positivity)
  have hroot : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast N.pos)
  have hsmall : c*((C:ℝ)+1) < ε*q :=
    (div_lt_iff₀ hε).mp (hJ.trans_le (by exact_mod_cast hJq)) |>.trans_eq (mul_comm _ _)
  apply abs_lt.mpr
  constructor
  · have hh : c ≤ (A.card:ℝ) / Real.sqrt N := by
      apply (le_div_iff₀ hroot).mpr
      rw [hsq, ← mul_assoc, hscale, hkr]
      linarith [Nat.cast_nonneg (α := ℝ) C]
    change -ε < (A.card:ℝ) / Real.sqrt N - c
    linarith
  · have hh : (A.card:ℝ) / Real.sqrt N < c + ε := by
      apply (div_lt_iff₀ hroot).mpr
      rw [hkr, hsq, ← mul_assoc]
      have hb : 0 < (c+ε)*Real.sqrt 130 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hlow hb.le
      have hsc : 18*((C:ℝ)+1) < ε*Real.sqrt 130*q := by
        have h := mul_lt_mul_of_pos_right hsmall (show 0 < Real.sqrt 130 by positivity)
        nlinarith only [h, hscale, mul_assoc c ((C:ℝ)+1) (Real.sqrt 130),
          show c*((C:ℝ)+1)*Real.sqrt 130 = 18*((C:ℝ)+1) by
            rw [mul_right_comm, hscale]]
      rw [add_mul, hscale] at hmul ⊢
      nlinarith only [hmul,hsc,heq]
    change (A.card:ℝ) / Real.sqrt N - c < ε
    linarith

/-- The ordinary-basis statement uses the upstream quantifiers. -/
theorem frequently_cyclic_basis (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ N : ℕ+ in atTop, ∃ A : Finset (ZMod N), A+A=univ ∧
      |(A.card:ℝ)/Real.sqrt N - 18/Real.sqrt 130| < ε :=
  (frequently_strict 1 ε hε).mono fun _ ⟨_,A,hA,hr⟩ => ⟨A,
    eq_univ_of_forall fun z => by
      obtain ⟨a,ha,b,hb,_,he⟩ := hA z
      exact mem_add.mpr ⟨a,ha,b,hb,he⟩, hr⟩

#print axioms character_rows
#print axioms index_two_cover
#print axioms quartic_rows
#print axioms seed_structure
#print axioms seed_card
#print axioms lewis_seed
#print axioms seed_strict
#print axioms order_constant_lower
#print axioms lifted_family
#print axioms frequently_strict
#print axioms frequently_cyclic_basis

end Green33QuarticSeed
