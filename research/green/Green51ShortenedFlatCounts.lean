import Green51ShortenedCompletions

/-! # Affine three-space counts and both eighteen-label cases -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51ShortenedCompletions Green51WitnessIncidence
open scoped Classical Pointwise
namespace Green51ShortenedFlatCounts
local notation "V" => Cube 11

private theorem complement_zero {B T:Finset V} (sub:T⊆B) (zero:syndrome B=0) (z:syndrome T=0) :
    syndrome (B\T)=0 := by
  have h:=sum_sdiff sub (f:=id)
  change syndrome (B\T)+syndrome T=syndrome B at h
  simpa only [z,zero,add_zero] using h

/-- Every sixteen-label zero sum supports exactly fifteen flats in the total
count, throughout the completion range. -/
theorem flat_count {A:Finset V} (lo:18≤A.card) (hi:A.card≤24) (avoid:¬FlatAt A 0) :
    (family A).ncard=(sixteens A).card*15 := by
  classical
  have pos:0<(completions A).card:=by rw [completion_count lo hi avoid];split <;> omega
  obtain ⟨B,hB⟩:=card_pos.mp pos
  obtain ⟨sub,sz,good⟩:=(mem_filter.mp hB).2
  let U:=B\A
  have back:B\U=A:=Finset.sdiff_sdiff_eq_self sub
  have z:=full_sum sz good
  have t:=deleted_flat_count (U:=U) sz good sdiff_subset
  rw [back] at t
  rw [t]
  congr 1
  apply card_bij (fun O _=>B\O)
  · intro O h
    obtain ⟨oct,uo⟩:=mem_filter.mp h
    obtain ⟨mem,oz⟩:=mem_filter.mp oct
    obtain ⟨ob,os⟩:=mem_powersetCard.mp mem
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,by rw [card_sdiff_of_subset ob,sz,os]⟩,complement_zero ob z oz⟩
    intro x hx;by_contra absent
    exact (mem_sdiff.mp hx).2 (uo (mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1,absent⟩))
  · intro O h R k eq
    have ob:O⊆B:=(mem_powersetCard.mp (mem_filter.mp (mem_filter.mp h).1).1).1
    have rb:R⊆B:=(mem_powersetCard.mp (mem_filter.mp (mem_filter.mp k).1).1).1
    simpa only [Finset.sdiff_sdiff_eq_self ob,Finset.sdiff_sdiff_eq_self rb] using congrArg (B\·) eq
  · intro T h
    obtain ⟨mem,tz⟩:=mem_filter.mp h
    obtain ⟨ta,ts⟩:=mem_powersetCard.mp mem
    have tb:=ta.trans sub
    refine ⟨B\T,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sdiff_subset,by
      rw [card_sdiff_of_subset tb,sz,ts]⟩,complement_zero tb z tz⟩,?_⟩,?_⟩
    · intro x hx;obtain ⟨xb,xa⟩:=mem_sdiff.mp hx
      exact mem_sdiff.mpr ⟨xb,fun xt=>xa (ta xt)⟩
    · exact Finset.sdiff_sdiff_eq_self tb

/-- The affine-flat count depends only on cardinality from 19 through 24. -/
theorem nineteen_to_twenty_four {A:Finset V} (lo:19≤A.card) (hi:A.card≤24) (avoid:¬FlatAt A 0) :
    (family A).ncard=15*Green51DeletedLabels.multiplicity (24-A.card) := by
  obtain ⟨B,⟨sub,sz,good⟩,_⟩:=unique_completion lo hi avoid
  let U:=B\A
  have count:U.card=24-A.card:=(card_sdiff_of_subset sub).trans (by rw [sz])
  have back:B\U=A:=Finset.sdiff_sdiff_eq_self sub
  have h:=Green51DeletedLabels.flat_count_of_at_most_five_deletions (U:=U) sz good sdiff_subset (by omega)
  rwa [count,back] at h

/-- At eighteen labels the two completion counts correspond to zero and
fifteen affine flats. Both alternatives occur. -/
theorem eighteen_cases (A:Finset V) (sz:A.card=18) (avoid:¬FlatAt A 0) :
    ((completions A).card=1 ∧ (family A).ncard=0) ∨
    ((completions A).card=2 ∧ (family A).ncard=15) := by
  have small:=(extension_counts (by omega : 18≤A.card) (by omega) avoid).2 sz
  have n:=completion_count (by omega : 18≤A.card) (by omega) avoid
  rw [if_pos sz] at n
  have f:=flat_count (by omega : 18≤A.card) (by omega) avoid
  omega

/-- There are avoiding eighteen-label examples of each completion type. -/
theorem both_types :
    (∃ A:Finset V,A.card=18 ∧ ¬FlatAt A 0 ∧ (completions A).card=1) ∧
    (∃ A:Finset V,A.card=18 ∧ ¬FlatAt A 0 ∧ (completions A).card=2) := by
  classical
  let E:=Green51GolayWitnesses.shortened
  have es:E.card=18:=Green51GolayWitnesses.sizes.2
  have neg:¬FlatAt E 0:=fun h=>Green51GolayWitnesses.no_affine ⟨0,h⟩
  constructor
  · refine ⟨E,es,neg,?_⟩
    have none:sixteens E=∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro T hit
      obtain ⟨mem,tz⟩:=mem_filter.mp hit
      obtain ⟨te,sz⟩:=mem_powersetCard.mp mem
      obtain ⟨p,flat⟩:=Green51ElevenRelations.affine_of_sixteen_sum T sz tz
      exact Green51GolayWitnesses.no_affine ⟨p,Green51ElevenColumns.flat_mono te flat⟩
    rw [completion_count (by omega : 18≤E.card) (by omega) neg,if_pos es,none,card_empty]
  · let B:=Green51GolayWitnesses.full
    have bs:B.card=24:=Green51GolayWitnesses.sizes.1
    have ba:¬FlatAt B 0:=Green51GolayWitnesses.no_linear
    obtain ⟨T,tb,ts⟩:=exists_subset_card_eq (s:=B) (show 5≤B.card by omega)
    obtain ⟨O,⟨oct,_⟩,_⟩:=unique_octad bs ba T tb ts
    obtain ⟨mem,oz⟩:=mem_filter.mp oct
    obtain ⟨ob,os⟩:=mem_powersetCard.mp mem
    have sixteen:(B\O).card=16:=by rw [card_sdiff_of_subset ob,bs,os]
    obtain ⟨A,sub,ab,sz⟩:=exists_subsuperset_card_eq (sdiff_subset : B\O⊆B)
      (show (B\O).card≤18 by omega) (show 18≤B.card by omega)
    have avoid:¬FlatAt A 0:=fun h=>ba (Green51ElevenColumns.flat_mono ab h)
    have hit:B\O∈sixteens A:=mem_filter.mpr ⟨mem_powersetCard.mpr ⟨sub,sixteen⟩,complement_zero ob (full_sum bs ba) oz⟩
    have pos:=card_pos.mpr ⟨_,hit⟩
    have small:=(extension_counts (by omega : 18≤A.card) (by omega) avoid).2 sz
    refine ⟨A,sz,avoid,?_⟩
    rw [completion_count (by omega : 18≤A.card) (by omega) avoid,if_pos sz]
    omega

end Green51ShortenedFlatCounts
#print axioms Green51ShortenedFlatCounts.flat_count
#print axioms Green51ShortenedFlatCounts.nineteen_to_twenty_four
#print axioms Green51ShortenedFlatCounts.eighteen_cases
#print axioms Green51ShortenedFlatCounts.both_types
