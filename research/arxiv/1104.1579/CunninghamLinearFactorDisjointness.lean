import CunninghamRepeatedRootSeeds

/-! A sharp finite test for disjoint factors in the two positive-index Jones chains. -/

namespace CunninghamChain.SharedFactors
open Polynomial LinearRoots

/-- Every two distinct signed positive indices have coprime rational polynomials. -/
def DisjointTerms (a b : ℤ) : Prop :=
  ∀ k l m n, 0 < m → 0 < n → (k≠l ∨ m≠n) → IsCoprime (term k a b m) (term l a b n)

/-- The same condition restricted to the first N positive indices of each sign. -/
def DisjointThrough (N : ℕ) (a b : ℤ) : Prop :=
  ∀ k l m n, 0 < m → m ≤ N → 0 < n → n ≤ N →
    (k≠l ∨ m≠n) → IsCoprime (term k a b m) (term l a b n)

private lemma fails_through_seven {a b : ℤ} (ha : 0 < a) (hex : ExceptionalSeed a b) :
    ¬DisjointThrough 7 a b := by
  intro h
  have shared {k : Bool} {m n d : ℕ} (hd : 0 < d) (hm : 0 < m) (hn : m<n) (h7 : n ≤ 7)
      (h₁ : cyclotomic d ℚ ∣ term k a b m) (h₂ : cyclotomic d ℚ ∣ term k a b n) : False :=
    (cyclotomic.irreducible_rat hd).not_isUnit
      ((h k k m n hm (by omega) (by omega) h7 (Or.inr hn.ne)).isUnit_of_dvd' h₁ h₂)
  have opposite {k : Bool} {m n : ℕ} {z : ℂ} (hm : 0 < m) (hn : m<n) (h7 : n ≤ 7)
      (row : CollisionRow k a b m n z) : False := by
    obtain ⟨h₁,h₂⟩ := row.roots
    have cop := h k (!k) m n hm (by omega) (by omega) h7 (Or.inr hn.ne)
    exact (aeval_ne_zero_of_isCoprime cop z).elim (· h₁) (· h₂)
  rcases hex with h₀|h₀|h₀|h₀|h₀|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · apply shared (k:=true) (m:=2) (n:=4) (d:=2) (by decide) (by decide) (by decide) (by decide)
    all_goals apply (linear_cyclotomic_endpoints ..).2.mpr; norm_num [sign]; omega
  · apply shared (k:=true) (m:=1) (n:=3) (d:=2) (by decide) (by decide) (by decide) (by decide)
    all_goals apply (linear_cyclotomic_endpoints ..).2.mpr; norm_num [sign]; omega
  · apply shared (k:=false) (m:=1) (n:=3) (d:=2) (by decide) (by decide) (by decide) (by decide)
    all_goals apply (linear_cyclotomic_endpoints ..).2.mpr; norm_num [sign]; omega
  · apply opposite (k:=false) (m:=1) (n:=2) (z:= -(1/2:ℂ)) (by decide) (by decide) (by decide)
    exact Or.inl ⟨rfl,rfl,by simpa [sign] using h₀,by norm_num⟩
  · apply opposite (k:=true) (m:=1) (n:=2) (z:= -(1/2:ℂ)) (by decide) (by decide) (by decide)
    exact Or.inl ⟨rfl,rfl,by simpa [sign] using h₀,by norm_num⟩
  · apply shared (k:=true) (m:=1) (n:=7) (d:=6) (by decide) (by decide) (by decide) (by decide)
    all_goals apply (higher_cyclotomic_iff ha _ _ (by decide)).mpr; decide
  · apply opposite (k:=false) (m:=2) (n:=3) (z:=(-1+Complex.I)/2) (by decide) (by decide) (by decide)
    refine Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl,rfl,rfl,?_⟩))
    linear_combination Complex.I_sq / 2

/-- For all positive-leading integral linear seeds, five lines and two isolated seeds are the
complete obstruction to pairwise coprimality at all positive signed indices. -/
theorem disjoint_terms_iff {a b : ℤ} (ha : 0 < a) :
    DisjointTerms a b ↔ ¬ExceptionalSeed a b := by
  constructor
  · intro h hex
    exact fails_through_seven ha hex (fun k l m n hm _ hn _ hne => h k l m n hm hn hne)
  · intro h k l m n hm hn hne
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ ..).mpr
    intro z
    by_contra! bad
    exact h (exceptional_of_shared_root ha hm hn hne bad.1 bad.2)

/-- Checking the first seven positive terms for both signs decides whether any factor ever repeats. -/
theorem disjoint_terms_iff_seven {a b : ℤ} (ha : 0 < a) :
    DisjointTerms a b ↔ DisjointThrough 7 a b :=
  ⟨fun h k l m n hm _ hn _ hne => h k l m n hm hn hne,
   fun h => (disjoint_terms_iff ha).mpr fun hex => fails_through_seven ha hex h⟩

/-- In particular no factor ever repeats between distinct positive iterates of the balanced seed. -/
theorem balanced_terms_disjoint {a : ℤ} (ha : 2 ≤ a) : DisjointTerms a (-a) := by
  rw [disjoint_terms_iff (by omega)]
  unfold ExceptionalSeed
  omega

/-- The cutoff is sharp: X−1 has no repeat through index six, then Φ₆ occurs again at seven. -/
theorem seven_is_sharp : DisjointThrough 6 1 (-1) ∧ ¬DisjointThrough 7 1 (-1) := by
  constructor
  · intro k l m n hm hm6 hn hn6 hne
    apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ ℂ ..).mpr
    intro z
    by_contra! bad
    by_cases hu : OffUnity z
    · rcases off_unity_rows (by decide : (0:ℤ)<1) hm hn hne hu bad.1 bad.2 with h|h <;>
        have := h.exceptional <;> norm_num at this
    unfold OffUnity at hu
    push Not at hu
    obtain ⟨D,hD,hpow⟩ := hu
    let t := orderOf z
    have ht : 0 < t := Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one hpow) hD
    have hz : IsPrimitiveRoot z t := IsPrimitiveRoot.orderOf z
    have cls (c : Bool) (j : ℕ) (hpos : 0 < j) (hle : j ≤ 6)
        (hroot : aeval z (term c 1 (-1) j)=0) : c=true ∧ j=1 := by
      have hdiv := (primitive_dvd ht hz _).mpr hroot
      by_cases h : t=1
      · rw [h] at hdiv
        have e := (linear_cyclotomic_endpoints ..).1.mp hdiv
        cases c <;> norm_num [sign] at e <;> omega
      by_cases h' : t=2
      · rw [h'] at hdiv
        have e := (linear_cyclotomic_endpoints ..).2.mp hdiv
        split_ifs at e; cases c <;> norm_num [sign] at e
      have e := (higher_cyclotomic_iff (by decide : (0:ℤ)<1) j t (by omega)).mp hdiv
      norm_num at e
      exact ⟨e.1,by omega⟩
    obtain ⟨rfl,rfl⟩ := cls k m hm hm6 bad.1
    obtain ⟨rfl,rfl⟩ := cls l n hn hn6 bad.2
    simp at hne
  · exact fails_through_seven (by decide) (by unfold ExceptionalSeed; decide)

#print axioms seven_is_sharp
#print axioms disjoint_terms_iff
#print axioms disjoint_terms_iff_seven
#print axioms balanced_terms_disjoint

end CunninghamChain.SharedFactors
