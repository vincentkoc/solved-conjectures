import Green51OctadParity
import Green51FourSpaceProjection

/-! # Zero-sum octads and the affine spans of their complements -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise symmDiff
namespace Green51PerfectColumns
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem symmDiff_card (S T:Finset V) :
    (S∆T).card+2*(S∩T).card=S.card+T.card := by
  have dis : Disjoint (S\T) (T\S) := by
    apply disjoint_left.mpr
    intro x hx ht
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp ht).1
  rw [Finset.symmDiff_def,card_union_of_disjoint dis]
  have u := card_sdiff_add_card_inter S T
  have v := card_sdiff_add_card_inter T S
  rw [inter_comm T S] at v
  omega

/-- Strip an octad meeting a relation in at least five coordinates. Induction
shows that every even relation meets every octad in an even number of labels. -/
theorem relation_even {A O:Finset V} (size:A.card=24) (avoid:¬FlatAt A 0)
    (ho:O∈octadFamily A) (T:Finset V) (sub:T⊆A) (even:2∣T.card) (zero:syndrome T=0) :
    2∣(T∩O).card := by
  induction h:T.card using Nat.strong_induction_on generalizing T with
  | h n ih =>
    by_cases empty:T.card=0
    · simp [card_eq_zero.mp empty]
    have two : T.card≠2 := by
      intro k; obtain ⟨x,y,ne,eq⟩:=card_eq_two.mp k
      rw [syndrome,eq,sum_pair ne] at zero
      exact ne (add_right_cancel (zero.trans (ZModModule.add_self y).symm))
    have small : ¬(T.card=4 ∨ T.card=6) := fun sz => avoid ((flat_zero A).mpr
      ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,sz,zero⟩))
    obtain ⟨S,st,five⟩ := exists_subset_card_eq (show 5≤T.card by omega)
    obtain ⟨U,⟨hu,su⟩,_⟩ := unique_octad size avoid S (st.trans sub) five
    obtain ⟨hU,usum⟩ := mem_filter.mp hu
    obtain ⟨ua,sz⟩ := mem_powersetCard.mp hU
    have common := card_le_card (subset_inter st su)
    have eq := symmDiff_card T U
    have lower : (T∆U).card<n := by omega
    have dsub : T∆U⊆A := by
      intro x hx
      rcases mem_symmDiff.mp hx with m|m
      · exact sub m.1
      · exact ua m.1
    have dz : syndrome (T∆U)=0 := by
      have e := Green51FourSpace.subset_sum_add id T U
      change syndrome (T∆U)=syndrome T+syndrome U at e
      rw [e,zero,usum,add_zero]
    have de : 2∣(T∆U).card := by omega
    have step := ih _ lower (T∆U) dsub de dz rfl
    have dist : (T∆U)∩O=(T∩O)∆(U∩O) := by
      ext x; simp only [mem_inter,mem_symmDiff];tauto
    rw [dist] at step
    have calcSize := symmDiff_card (T∩O) (U∩O)
    have uo := octad_even size avoid ho hu
    omega

theorem outside_span {A O:Finset V} (sub:O⊆A) (non:O.Nonempty)
    (orth : ∀ T⊆A, 2∣T.card → syndrome T=0 → 2∣(T∩O).card) :
    Submodule.span F ((fun x:V => ((1:F),x)) '' ((A\O:Finset V):Set V))≠⊤ := by
  classical
  intro top
  obtain ⟨x,hx⟩ := non
  let v : V → F × V := fun a=> (1,a)
  have mem : v x∈Submodule.span F (v '' ((A\O:Finset V):Set V)) := top ▸ Submodule.mem_top
  obtain ⟨T,ts,sum⟩ := (Green51FourSpace.span_iff_subset_sum v (A\O) (v x)).mp mem
  have off : x∉T := fun h => (mem_sdiff.mp (ts h)).2 hx
  have fst := congrArg Prod.fst sum
  have even : 2∣(insert x T).card := by
    rw [card_insert_of_notMem off]
    have zero : ((T.card+1:ℕ):F)=0 := by
      have one : (T.card:F)=1 := by simpa [Prod.fst_sum,v] using fst
      rw [Nat.cast_add,Nat.cast_one,one];decide
    exact (ZMod.natCast_eq_zero_iff _ _).mp zero
  have cut := orth (insert x T) (insert_subset (sub hx) (ts.trans sdiff_subset)) even (by
    rw [syndrome,sum_insert off]
    have eq := congrArg Prod.snd sum
    simp only [Prod.snd_sum,v] at eq
    rw [eq,ZModModule.add_self])
  have cross : (insert x T)∩O={x} := by
    ext y
    constructor
    · intro h
      rcases mem_insert.mp (mem_inter.mp h).1 with eq|ht
      · exact mem_singleton.mpr eq
      · exact ((mem_sdiff.mp (ts ht)).2 (mem_inter.mp h).2).elim
    · rintro h; have := mem_singleton.mp h; subst y; exact mem_inter.mpr ⟨mem_insert_self ..,hx⟩
  rw [cross,card_singleton] at cut
  omega


end Green51PerfectColumns
#print axioms Green51PerfectColumns.relation_even
#print axioms Green51PerfectColumns.outside_span
