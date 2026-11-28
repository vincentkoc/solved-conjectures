import Green51TenDimensions
/-! # Equality in odd-subset packing -/
open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise symmDiff
namespace Green51PerfectColumns
local notation "F" => ZMod 2
local notation "V" => Cube 11
def oddSets (A:Finset V) := A.powersetCard 1 ∪ A.powersetCard 3
def syndrome (S:Finset V) := ∑x∈S,x

theorem perfect_odd {A:Finset V} (size:A.card=24) (inj:Set.InjOn syndrome ↑(oddSets A)) :
    ∀v:V,∃! S:Finset V,S∈oddSets A ∧ syndrome S=v := by
  classical
  have dis : Disjoint (A.powersetCard 1) (A.powersetCard 3) := by
    rw [disjoint_left]; intro s h1 h3
    have h := (mem_powersetCard.mp h1).2.symm.trans (mem_powersetCard.mp h3).2
    omega
  have count : ((oddSets A).image syndrome).card=(univ:Finset V).card := by
    rw [card_image_iff.mpr inj,oddSets,card_union_of_disjoint dis,card_powersetCard,
        card_powersetCard,size]
    decide +kernel
  have full := eq_of_subset_of_card_le (subset_univ _) count.ge
  intro v
  obtain ⟨S,mem,eq⟩ := mem_image.mp (full ▸ mem_univ v : v∈(oddSets A).image syndrome)
  exact ⟨S,⟨mem,eq⟩,fun R ⟨hr,rv⟩ => inj hr mem (rv.trans eq.symm)⟩

theorem octads {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (inj:Set.InjOn syndrome ↑(oddSets A)) (T:Finset V) (sub:T⊆A) (five:T.card=5) :
    ∃! O:Finset V, O⊆A ∧ O.card=8 ∧ syndrome O=0 ∧ T⊆O := by
  classical
  obtain ⟨U,⟨hu,equal⟩,unique⟩ := perfect_odd size inj (syndrome T)
  have member : U⊆A ∧ (U.card=1 ∨ U.card=3) := by
    rcases mem_union.mp hu with h|h
    · exact ⟨(mem_powersetCard.mp h).1,Or.inl (mem_powersetCard.mp h).2⟩
    · exact ⟨(mem_powersetCard.mp h).1,Or.inr (mem_powersetCard.mp h).2⟩
  let I := T∩U
  have it : I⊆T := inter_subset_left
  have iu : I⊆U := inter_subset_right
  let D := T\I ∪ U\I
  have dis : Disjoint (T\I) (U\I) := by
    rw [disjoint_left]; intro x h g
    exact (mem_sdiff.mp h).2 (mem_inter.mpr ⟨(mem_sdiff.mp h).1,(mem_sdiff.mp g).1⟩)
  have dsub : D⊆A := union_subset ((sdiff_subset).trans sub) ((sdiff_subset).trans member.1)
  have exp : D.card=(T.card-I.card)+(U.card-I.card) := by
    rw [show D=T\I ∪ U\I from rfl,card_union_of_disjoint dis,
      card_sdiff_of_subset it,card_sdiff_of_subset iu]
  have same : (∑x∈T\I,x)=(∑x∈U\I,x) := add_right_cancel
    ((sum_sdiff it (f:=id)).trans (equal.symm.trans (sum_sdiff iu (f:=id)).symm))
  have zero : syndrome D=0 := by rw [syndrome,show D=T\I ∪ U\I from rfl,sum_union dis,same,ZModModule.add_self]
  have ni := card_le_card iu
  have small (h:D.card=4 ∨ D.card=6) : False := avoid ((flat_zero A).mpr
    ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨D,dsub,h,zero⟩))
  have two : D.card≠2 := by
    intro h; obtain ⟨a,b,ne,eq⟩ := card_eq_two.mp h
    rw [syndrome,eq,sum_pair ne] at zero
    exact ne (add_right_cancel (zero.trans (ZModModule.add_self b).symm))
  have small₄ : D.card≠4 := fun h => small (Or.inl h)
  have small₆ : D.card≠6 := fun h => small (Or.inr h)
  have len := member.2
  have empty : I.card=0 := by omega
  have eight : D.card=8 := by omega
  have form : D=T∪U := by simp [D,card_eq_zero.mp empty]
  have incl : T⊆D := form ▸ subset_union_left
  refine ⟨D,⟨dsub,eight,zero,incl⟩,?_⟩
  rintro O ⟨oa,sz,h,inside⟩
  have count : (O\T).card=3 := by rw [card_sdiff_of_subset inside,sz,five]
  have sum := sum_sdiff inside (f:=id)
  have eq : syndrome (O\T)=syndrome T := add_right_cancel
    ((sum.trans h).trans (ZModModule.add_self (syndrome T)).symm)
  have key := unique (O\T) ⟨mem_union_right _ (mem_powersetCard.mpr ⟨sdiff_subset.trans oa,count⟩),eq⟩
  rw [form,←key,union_comm,sdiff_union_of_subset inside]

def octadFamily (A:Finset V) := (A.powersetCard 8).filter (fun O => syndrome O=0)

/-- The zero-sum octads of every extremal avoiding double form a Steiner system
on its twenty-four labels. -/
theorem unique_octad {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (T:Finset V) (sub:T⊆A) (five:T.card=5) :
    ∃! O:Finset V,O∈octadFamily A ∧ T⊆O := by
  have inj : Set.InjOn syndrome ↑(oddSets A) := Green51SparseDimensions.odd_sum_inj A
    (by omega) (fun h => avoid ((flat_zero A).mpr h))
  simpa [octadFamily,mem_powersetCard,and_assoc] using octads size avoid inj T sub five

theorem flags {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (I:Finset V) (ia:I⊆A) (hi:I.card≤5) :
    (8-I.card).choose (5-I.card)*((octadFamily A).filter (I⊆·)).card=
      (24-I.card).choose (5-I.card) := by
  classical
  let H := (octadFamily A).filter (I⊆·)
  let P (B:Finset V) := (B.powersetCard 5).filter (I⊆·)
  have union : H.biUnion P=P A := by
    ext T
    constructor
    · intro ht
      obtain ⟨O,ho,ht⟩ := mem_biUnion.mp ht
      have oa := (mem_powersetCard.mp (mem_filter.mp (mem_filter.mp ho).1).1).1
      obtain ⟨t,inc⟩ := mem_filter.mp ht
      obtain ⟨sub,five⟩ := mem_powersetCard.mp t
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub.trans oa,five⟩,inc⟩
    · intro ht
      obtain ⟨t,inc⟩ := mem_filter.mp ht
      obtain ⟨sub,five⟩ := mem_powersetCard.mp t
      obtain ⟨O,⟨ho,contained⟩,_⟩ := unique_octad size avoid T sub five
      exact mem_biUnion.mpr ⟨O,mem_filter.mpr ⟨ho,inc.trans contained⟩,
        mem_filter.mpr ⟨mem_powersetCard.mpr ⟨contained,five⟩,inc⟩⟩
  have dis : (H:Set (Finset V)).PairwiseDisjoint P := by
    intro B hb C hc ne
    apply Finset.disjoint_left.mpr
    intro T tB tC
    obtain ⟨tb,sz⟩ := mem_powersetCard.mp (mem_filter.mp tB).1
    have tc := (mem_powersetCard.mp (mem_filter.mp tC).1).1
    have hB := (mem_filter.mp hb).1
    have hC := (mem_filter.mp hc).1
    have ba := (mem_powersetCard.mp (mem_filter.mp hB).1).1
    exact ne ((unique_octad size avoid T (tb.trans ba) sz).unique ⟨hB,tb⟩ ⟨hC,tc⟩)
  have count := congrArg card union
  rw [card_biUnion dis,show (P A).card=_ from card_filter_powersetCard_subset I A 5 ia hi,size] at count
  rw [←count]
  calc
    _ = ∑ _O∈H,(8-I.card).choose (5-I.card) := by simp [H,Nat.mul_comm]
    _ = _ := by
      apply sum_congr rfl
      intro O ho
      obtain ⟨h,sub⟩ := mem_filter.mp ho
      have eight := (mem_powersetCard.mp (mem_filter.mp h).1).2
      symm
      simpa only [P,eight] using card_filter_powersetCard_subset I O 5 sub hi

/-- Each label lies in 253 of the 759 octads. -/
theorem octads_through_label {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    {x:V} (hx:x∈A) : ((octadFamily A).filter (x∈·)).card=253 := by
  have h:=flags size avoid {x} (singleton_subset_iff.mpr hx) (by simp)
  simp only [card_singleton,singleton_subset_iff] at h
  change 35*((octadFamily A).filter (x∈·)).card=8855 at h
  omega

/-- There are exactly 759 octads. -/
theorem octad_count {A:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0) :
    (octadFamily A).card=759 := by
  have eq:=flags size avoid ∅ (empty_subset _) (by simp)
  simp only [card_empty,Nat.sub_zero,empty_subset,filter_true] at eq
  change 56*(octadFamily A).card=42504 at eq
  omega

end Green51PerfectColumns
#print axioms Green51PerfectColumns.unique_octad
#print axioms Green51PerfectColumns.flags
#print axioms Green51PerfectColumns.octad_count
#print axioms Green51PerfectColumns.octads_through_label
