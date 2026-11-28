import Green51SeventeenProfiles
import Green51SeventeenCompletions
import Green51SeventeenWitness

/-! # Completions at seventeen labels in eleven binary dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51ShortenedColumns Green51ExtensionFibres Green51ShortenedCompletions Green51WeightTransform
open scoped Classical Pointwise

namespace Green51SeventeenSpectrum
local notation "F" => ZMod 2
local notation "V" => Cube 11

/-- All ten-element subsets whose labels sum to zero. -/
def tens (A : Finset V) := (A.powersetCard 10).filter fun U => syndrome U = 0

private theorem present {A : Finset V} (size : A.card = 17)
    (avoid : ¬FlatAt A 0) (ten : tens A = ∅) : Nonempty (Presentation A) := by
  apply presentation_of_four (by omega) (by omega) avoid
  intro T sub even sum
  have free (U : Finset V) (us : U ⊆ A) (sz : U.card = 4 ∨ U.card = 6) : syndrome U ≠ 0 :=
    fun z => avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨U,us,sz,z⟩))
  have high := card_le_card sub
  have two : T.card ≠ 2 := by
    intro h;obtain ⟨a,b,ne,rfl⟩ := card_eq_two.mp h
    change (∑ x ∈ {a,b},x) = 0 at sum
    rw [sum_pair ne] at sum
    exact ne (add_right_cancel (sum.trans (ZModModule.add_self b).symm))
  have six : T.card ≠ 6 := fun h => free T sub (Or.inr h) sum
  have miss : T.card ≠ 10 := by
    intro h
    have hit : T ∈ tens A := mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,h⟩,sum⟩
    simp [ten] at hit
  have nofourteen : T.card ≠ 14 := fun h => Green51MissingLabel.forbidden (Or.inl h) (fun U hU => free U (hU.trans sub)) sum
  omega

private theorem pool_count {n : ℕ} (len : n = 17) (C : Submodule F (Cube n))
    (rank : n-12 ≤ Module.finrank F C)
    (allowed : ∀ c : C, (supp c.val).card ∈ ({0,8,12,16}:Finset ℕ)) :
    ((Green51ShortenedProfiles.multiplicity C 16=0 ∧ (triples C).card=15) ∨
     (Green51ShortenedProfiles.multiplicity C 16=1 ∧ (triples C).card=0)) ∧
    (pool C).card=896 := by
  subst n
  have al (c : C) := allowed c
  simp only [mem_insert,mem_singleton] at al
  have dist (c : C) (nz : c ≠ 0) : 8 ≤ (supp c.val).card := by
    have diff : (supp c.val).card ≠ 0 := by
      intro h
      apply nz
      apply Subtype.ext;funext i
      by_contra! ne
      have hit : i ∈ supp c.val := mem_filter.mpr ⟨mem_univ _,ne⟩
      rw [card_eq_zero.mp h] at hit
      exact notMem_empty _ hit
    have choices := al c
    omega
  have noTen : Green51ShortenedProfiles.multiplicity C 10 = 0 := by
    rw [Green51ShortenedProfiles.multiplicity,card_eq_zero,eq_empty_iff_forall_notMem]
    intro c h
    have e := (mem_filter.mp h).2
    have choices := al c
    omega
  obtain ⟨_,profile⟩ := Green51SeventeenProfiles.profiles C rank (fun x => by have h:=al x;omega) dist
  have tr : Green51SeventeenProfiles.dualCount C {3} = (triples C).card := by
    simp only [Green51SeventeenProfiles.dualCount,triples,mem_singleton]
  have po : Green51SeventeenProfiles.dualCount C {3,7,11,15} = (pool C).card := by
    unfold Green51SeventeenProfiles.dualCount pool
    congr 1
    apply filter_congr;intro z _
    have up := (supp z).card_le_univ
    rw [Fintype.card_fin] at up
    simp only [mem_insert,mem_singleton];omega
  rw [noTen,tr,po] at profile
  simp only [mem_insert,mem_singleton,Prod.mk.injEq] at profile
  omega

/-- A ten-relation prevents any extension. With no ten-relation there
are thirteen or twenty-eight one-label extensions, according as a
sixteen-relation is absent or present. -/
theorem extensions {A : Finset V} (size : A.card = 17) (avoid : ¬FlatAt A 0) :
    (holes A).card = if (tens A).Nonempty then 0 else if (sixteens A).Nonempty then 28 else 13 := by
  classical
  by_cases t : (tens A).Nonempty
  · rw [if_pos t,card_eq_zero,eq_empty_iff_forall_notMem]
    obtain ⟨T,ht⟩ := t
    obtain ⟨hT,z⟩ := mem_filter.mp ht
    obtain ⟨sub,ts⟩ := mem_powersetCard.mp hT
    intro v hv
    obtain ⟨fresh,good⟩ := (mem_filter.mp hv).2
    have next := card_insert_of_notMem fresh
    exact Green51ResidualPacking.no_ten (by omega : 18 ≤ (insert v A).card) good
      (sub.trans (subset_insert ..)) ts z
  · rw [if_neg t]
    obtain ⟨D⟩ := present size avoid (not_nonempty_iff_eq_empty.mp t)
    obtain ⟨p,q⟩ := pool_count size D.P.ker (le_of_eq D.rank.symm) D.allowed
    have count := hole_count_from_seventeen (by omega : 17 ≤ A.card) avoid D
    rw [sixteen_count D] at p
    have exponent : A.card - 12 = 5 := by omega
    rw [q,Module.card_eq_pow_finrank (K:=F),D.rank,exponent,ZMod.card] at count
    norm_num at count
    by_cases existsSixteen : (sixteens A).Nonempty
    · rw [if_pos existsSixteen]
      have := card_pos.mpr existsSixteen
      omega
    · rw [if_neg existsSixteen]
      have null := not_nonempty_iff_eq_empty.mp existsSixteen
      rw [null,card_empty] at p
      omega

private theorem sixteen_mono {A B T : Finset V} (ab : A ⊆ B) (t : T ∈ sixteens A) :
    T ∈ sixteens B := by
  obtain ⟨s,z⟩ := mem_filter.mp t
  obtain ⟨ta,n⟩ := mem_powersetCard.mp s
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨ta.trans ab,n⟩,z⟩

private theorem no_ten_below {A B : Finset V} (ab : A ⊆ B) (large : 18 ≤ B.card)
    (good : ¬FlatAt B 0) : ¬(tens A).Nonempty := by
  rintro ⟨T,t⟩
  obtain ⟨s,z⟩ := mem_filter.mp t
  obtain ⟨ta,n⟩ := mem_powersetCard.mp s
  exact Green51ResidualPacking.no_ten large good (ta.trans ab) n z

/-- In the original ambient space there are zero, two or eight maximal-size
completions, distinguished by zero-sum sets of ten and sixteen labels. -/
theorem completion_number {A : Finset V} (size : A.card = 17) (avoid : ¬FlatAt A 0) :
    (completions A).card =
      if (tens A).Nonempty then 0 else if (sixteens A).Nonempty then 8 else 2 := by
  classical
  have more := extensions size avoid
  by_cases t : (tens A).Nonempty
  · rw [if_pos t,card_eq_zero,eq_empty_iff_forall_notMem]
    intro B h
    obtain ⟨ab,sz,good⟩ := (mem_filter.mp h).2
    exact no_ten_below ab (by omega) good t
  rw [if_neg t] at more ⊢
  by_cases s : (sixteens A).Nonempty
  · rw [if_pos s] at more ⊢
    obtain ⟨S,hS⟩ := s
    have two (v : V) (hv : v ∈ holes A) : (completions (insert v A)).card = 2 := by
      obtain ⟨fresh,good⟩ := (mem_filter.mp hv).2
      have next := card_insert_of_notMem fresh
      have size18 : (insert v A).card = 18 := by omega
      have pos := card_pos.mpr (show (sixteens (insert v A)).Nonempty from
        ⟨S,sixteen_mono (subset_insert ..) hS⟩)
      have upper := (extension_counts (by omega : 18 ≤ (insert v A).card) (by omega) good).2 size18
      rw [completion_count (by omega : 18 ≤ (insert v A).card) (by omega) good,if_pos size18]
      omega
    have flags := completion_flags A
    have count : (∑ v∈holes A,(completions (insert v A)).card) = (holes A).card*2 := by
      calc
        _ = ∑ _v∈holes A,(2:ℕ) := sum_congr rfl two
        _ = _ := by simp
    rw [size,count,more] at flags
    omega
  · rw [if_neg s] at more ⊢
    exact Green51SeventeenCompletions.two_of_thirteen size more

/-- Each of the three completion counts is attained by a seventeen-label
set with no linear three-space in its double. -/
theorem realized :
    ∀ k ∈ ({0,2,8}:Finset ℕ), ∃ A : Finset V,
      A.card = 17 ∧ ¬FlatAt A 0 ∧ (completions A).card=k := by
  classical
  intro k hk
  simp only [mem_insert,mem_singleton] at hk
  obtain ⟨one,two⟩ := Green51ShortenedFlatCounts.both_types
  rcases hk with rfl|rfl|rfl
  · obtain ⟨sz,avoid,maximal⟩ := Green51SeventeenWitness.maximal
    refine ⟨_,sz,avoid,card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr ?_)⟩
    intro B h
    obtain ⟨sub,bs,good⟩ := (mem_filter.mp h).2
    exact good (maximal B (lt_of_le_of_ne sub (fun e => by rw [e] at sz;omega)))
  · obtain ⟨B,bs,good,count⟩ := one
    have cb := completion_count (by omega : 18 ≤ B.card) (by omega) good
    rw [if_pos bs,count] at cb
    obtain ⟨A,ab,sz⟩ := exists_subset_card_eq (show 17 ≤ B.card by omega)
    have avoid := fun h => good (Green51ElevenColumns.flat_mono ab h)
    have light : ¬(sixteens A).Nonempty := by
      rintro ⟨S,s⟩
      have pos := card_pos.mpr (show (sixteens B).Nonempty from ⟨S,sixteen_mono ab s⟩)
      omega
    exact ⟨A,sz,avoid,by rw [completion_number sz avoid,if_neg (no_ten_below ab (by omega) good),if_neg light]⟩
  · obtain ⟨B,bs,good,count⟩ := two
    have cb := completion_count (by omega : 18 ≤ B.card) (by omega) good
    rw [if_pos bs,count] at cb
    obtain ⟨S,hS⟩ := card_pos.mp (show 0 < (sixteens B).card by omega)
    obtain ⟨mem,z⟩ := mem_filter.mp hS
    obtain ⟨sb,ss⟩ := mem_powersetCard.mp mem
    obtain ⟨A,sa,ab,sz⟩ := exists_subsuperset_card_eq sb (show S.card ≤ 17 by omega) (show 17 ≤ B.card by omega)
    have avoid := fun h => good (Green51ElevenColumns.flat_mono ab h)
    have heavy : (sixteens A).Nonempty := ⟨S,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sa,ss⟩,z⟩⟩
    exact ⟨A,sz,avoid,by rw [completion_number sz avoid,if_neg (no_ten_below ab (by omega) good),if_pos heavy]⟩

end Green51SeventeenSpectrum
#print axioms Green51SeventeenSpectrum.extensions
#print axioms Green51SeventeenSpectrum.completion_number
#print axioms Green51SeventeenSpectrum.realized
