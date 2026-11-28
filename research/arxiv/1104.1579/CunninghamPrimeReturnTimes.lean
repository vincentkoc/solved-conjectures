import CunninghamReturnProgressions
import CunninghamReturnDifferences
import Mathlib.Data.Fintype.Pigeonhole

/-! Recurring exact first-return times to a prime along the two Cunningham
recurrences, from Maynard’s affine prime-cluster theorem. -/

namespace CunninghamChain.PrimeReturns
open Finset

/-- Qualitative fixed-family consequence of Maynard, *Dense clusters of primes
in subsets*, Theorem 3.4, with interval length x. The slopes can be different. -/
def MaynardAffineClusters : Prop :=
  ∀ m : ℕ, ∃ K : ℕ, ∀ (A : Finset ℕ) (a c : ℕ → ℕ), K ≤ A.card →
    (∀ i ∈ A, 0 < a i) → (∀ i ∈ A, ∀ j ∈ A, i ≠ j → a i*c j ≠ a j*c i) →
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ i ∈ A, ¬p ∣ a i*n+c i) →
    ∀ X : ℕ, ∃ n ≥ X, m ≤ (A.filter (fun i => Nat.Prime (a i*n+c i))).card

/-- Every sufficiently large set of allowed positions contains a fixed pattern
of at least m prime sites attained by infinitely many centers. All unlisted
positions up to D are composite at each such center. -/
theorem recurring_exact_patterns (h : MaynardAffineClusters) (m : ℕ) :
    ∃ K : ℕ, ∀ (first : Bool) (A : Finset ℕ) (D : ℕ), K ≤ A.card → (∀ i ∈ A, i≤D) →
      ∃ U ⊆ A, m ≤ U.card ∧
        {x : ℕ | 3 ≤ x ∧ ∀ i ≤ D, (orbitValue first x i).Prime ↔ i ∈ U}.Infinite := by
  classical
  obtain ⟨K,hK⟩ := h m
  refine ⟨K,?_⟩
  intro first A D hcard hD
  obtain ⟨W,B,hW,hB,hmask,hadm⟩ := composite_mask first A D hD
  let a (i : ℕ) := 2^i*W
  let c (i : ℕ) := orbitValue first B i
  have he (n i : ℕ) : a i*n+c i=orbitValue first (W*n+B) i :=
    (affine_orbit first (by omega) W n i).symm
  have hx := hK A a c hcard (fun i _ => Nat.mul_pos (by positivity) hW)
    (fun _ _ _ _ hne => affine_nondegenerate first (by omega) hW hne) (by simpa only [he] using hadm)
  choose t ht hm using hx
  let pat (X : ℕ) : ↥A.powerset :=
    ⟨A.filter fun i => (a i*t X+c i).Prime,mem_powerset.mpr (filter_subset ..)⟩
  obtain ⟨U,hfib⟩ := Finite.exists_infinite_fiber pat
  have hfreq : (pat ⁻¹' {U}).Infinite := Set.infinite_coe_iff.mp hfib
  have hpat {X : ℕ} (hh : X ∈ pat ⁻¹' {U}) :
      (A.filter (fun i => (a i*t X+c i).Prime)) = U.val :=
    congrArg Subtype.val (show pat X=U from hh)
  obtain ⟨X,hX⟩ := hfreq.nonempty
  refine ⟨U.val,mem_powerset.mp U.property,hpat hX ▸ hm X,Set.infinite_of_forall_exists_gt ?_⟩
  intro Z
  obtain ⟨z,hz,hlarge⟩ := Set.infinite_iff_exists_gt.mp hfreq (Z+3)
  have hct := Nat.le_mul_of_pos_left (t z) hW
  have htz := ht z
  refine ⟨W*t z+B,⟨by omega,?_⟩,by omega⟩
  intro i hle
  rw [← hpat hz,mem_filter,he]
  exact ⟨fun hi => ⟨by by_contra hnot; exact hmask (t z) i hle hnot hi,hi⟩,And.right⟩

/-- The next prime after the prime seed occurs for the first time at d. -/
def IsPrimeReturn (first : Bool) (p d : ℕ) : Prop :=
  let term := if first then firstKindTerm else secondKindTerm
  0<d ∧ p.Prime ∧ (term p d).Prime ∧ ∀ e, 0<e → e<d → ¬(term p e).Prime

def recurringReturns (first : Bool) : Set ℕ :=
  {d | {p : ℕ | IsPrimeReturn first p d}.Infinite}

/-- Every sufficiently large finite set of positions contains a positive
difference that occurs as an exact prime-return time for infinitely many seeds. -/
theorem recurring_returns_meet_differences (h : MaynardAffineClusters) :
    ∃ K : ℕ, ∀ first : Bool, MeetsDifferences (recurringReturns first) K := by
  classical
  obtain ⟨K,hK⟩ := recurring_exact_patterns h 2
  refine ⟨K,?_⟩
  intro first A hA
  let D := A.sup id
  have hD (i : ℕ) (hi : i ∈ A) : i ≤ D := le_sup (f := id) hi
  obtain ⟨U,hUA,hU,hcent⟩ := hK first A D hA hD
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp hU
  have hpair : ∃ i ∈ U, ∃ j ∈ U, i<j := by
    rcases lt_or_gt_of_ne hab with hh | hh
    · exact ⟨a,ha,b,hb,hh⟩
    · exact ⟨b,hb,a,ha,hh⟩
  obtain ⟨i,hi,j₀,hj₀,hij₀⟩ := hpair
  let V := U.filter (i < ·)
  have hne : V.Nonempty := ⟨j₀,mem_filter.mpr ⟨hj₀,hij₀⟩⟩
  let j := V.min' hne
  obtain ⟨hj,hij⟩ := mem_filter.mp (V.min'_mem hne)
  change j ∈ U at hj
  change i<j at hij
  refine ⟨i,hUA hi,j,hUA hj,hij,Set.infinite_of_forall_exists_gt ?_⟩
  intro Z
  obtain ⟨x,⟨hx,hxU⟩,hxZ⟩ := Set.infinite_iff_exists_gt.mp hcent (Z+1)
  have hval := Nat.le_mul_of_pos_left x (by positivity : 0 < 2^i)
  refine ⟨orbitValue first x i,?_,?_⟩
  · refine ⟨by omega,(hxU i (hD _ (hUA hi))).mpr hi,?_,?_⟩
    · rw [orbit_restart first (by omega),Nat.add_sub_of_le hij.le]
      exact (hxU j (hD _ (hUA hj))).mpr hj
    · intro e he hed hepr
      rw [orbit_restart first (by omega)] at hepr
      have hmid := (hxU (i+e) (by have := hD _ (hUA hj); omega)).mp hepr
      have hm := V.min'_le (i+e) (mem_filter.mpr ⟨hmid,by omega⟩)
      change j ≤ i+e at hm
      omega
  · cases first <;> simp only [orbitValue, Bool.false_eq_true, if_false, if_true] <;> omega

/-- For each recurrence the spacings attained as exact prime returns for
infinitely many seeds have bounded gaps as a subset of the natural numbers. -/
theorem bounded_gaps_of_recurring_prime_returns (h : MaynardAffineClusters) :
    ∀ first : Bool, ∃ D : ℕ, ∀ n, ∃ d ∈ recurringReturns first, n ≤ d ∧ d ≤ n+D := by
  obtain ⟨_,hh⟩ := recurring_returns_meet_differences h
  exact fun first => bounded_gaps_of_meetsDifferences (hh first)

#print axioms recurring_exact_patterns
#print axioms recurring_returns_meet_differences
#print axioms bounded_gaps_of_recurring_prime_returns

/-- One spacing works on each recurrence, also after multiplication by any
member of a prescribed finite set of positive scales. The witnessing prime
seeds for different signs or scales can be different. -/
def commonSpacings (E : Finset ℕ) : Set ℕ :=
  {d | ∀ s ∈ E, ∀ first : Bool, s*d ∈ recurringReturns first}

theorem common_spacings_meet_differences (h : MaynardAffineClusters) (E : Finset ℕ)
    (hpos : ∀ s ∈ E, 0<s) : ∃ M, MeetsDifferences (commonSpacings E) M := by
  classical
  obtain ⟨K,hK⟩ := recurring_returns_meet_differences h
  obtain ⟨L,hL⟩ := meetsDifferences_inter (hK true) (hK false)
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨K,fun A ha => ?_⟩
    obtain ⟨i,hi,j,hj,hij,_⟩ := hK true A ha
    exact ⟨i,hi,j,hj,hij,by simp [commonSpacings]⟩
  | insert s E hs ih =>
    obtain ⟨M,hM⟩ := ih (fun t ht => hpos t (mem_insert_of_mem ht))
    have hscaled := meetsDifferences_dilate hL (hpos s (mem_insert_self ..))
    obtain ⟨P,hP⟩ := meetsDifferences_inter hscaled hM
    refine ⟨P,fun A ha => ?_⟩
    obtain ⟨i,hi,j,hj,hij,hd⟩ := hP A ha
    refine ⟨i,hi,j,hj,hij,?_⟩
    intro t ht first
    rcases mem_insert.mp ht with rfl | ht
    · cases first
      · exact hd.1.2
      · exact hd.1.1
    · exact hd.2 t ht first

theorem bounded_gaps_of_common_spacings (h : MaynardAffineClusters) (E : Finset ℕ)
    (hpos : ∀ s ∈ E, 0<s) :
    ∃ D : ℕ, ∀ n, ∃ d ∈ commonSpacings E, n ≤ d ∧ d ≤ n+D := by
  obtain ⟨_,hM⟩ := common_spacings_meet_differences h E hpos
  exact bounded_gaps_of_meetsDifferences hM

#print axioms common_spacings_meet_differences
#print axioms bounded_gaps_of_common_spacings

end CunninghamChain.PrimeReturns
