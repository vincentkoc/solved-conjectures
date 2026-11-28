import Green51MissingLabel
import Green51ElevenThresholds

/-! # Ten-label circuits and distance-eight column sets -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open scoped Classical Pointwise symmDiff
namespace Green51ResidualPacking
local notation "F" => ZMod 2
local notation "V" => Cube 11
private def col (x:V) : F×V := (1,x)
private def aug (T:Finset V) : F×V :=∑x∈T,col x

private theorem aug_zero {T:Finset V} : aug T=0 ↔ 2∣T.card ∧ syndrome T=0 := by
  have fst:(aug T).1=(T.card:F) := by simp [aug,col,Prod.fst_sum]
  have snd:(aug T).2=syndrome T := by simp [aug,col,syndrome,Prod.snd_sum]
  constructor
  · intro z
    refine ⟨(ZMod.natCast_eq_zero_iff ..).mp ?_,?_⟩
    · rw [←fst,z];rfl
    · rw [←snd,z];rfl
  · rintro ⟨e,z⟩
    exact Prod.ext (fst.trans ((ZMod.natCast_eq_zero_iff ..).mpr e)) (snd.trans z)

private theorem small {A T:Finset V} (high:5≤A.card) (avoid:¬FlatAt A 0) (sub:T⊆A)
    (short:T.card≤7) (zero:aug T=0) : T=∅ := by
  obtain ⟨even,z⟩:=aug_zero.mp zero
  have two:T.card≠2 := by
    intro n;obtain ⟨x,y,ne,eq⟩:=card_eq_two.mp n
    rw [syndrome,eq,sum_pair ne] at z
    exact ne (add_right_cancel (z.trans (ZModModule.add_self y).symm))
  have bad:¬(T.card=4 ∨ T.card=6) := fun sz=>avoid ((flat_zero A).mpr
    ((Green51SparseDimensions.linear_three_iff A high).mpr ⟨T,sub,sz,z⟩))
  exact card_eq_zero.mp (by omega)

private theorem flip {T S:Finset V} (st:S⊆T) (sum:aug T=0) :
    aug (T\S)=aug S := by
  have h:=sum_sdiff st (f:=col)
  change aug (T\S)+aug S=aug T at h
  exact add_right_cancel (h.trans (sum.trans (ZModModule.add_self (aug S)).symm))

private theorem diff_sub {S R T:Finset V} (s:S⊆T) (r:R⊆T) : S∆R⊆T := by
  intro x hx
  rcases mem_symmDiff.mp hx with h|h
  · exact s h.1
  · exact r h.1

/-- A zero-sum ten-set leaves room for at most seven further labels. -/
theorem no_ten {A T:Finset V} (hi:18≤A.card) (avoid:¬FlatAt A 0)
    (ta:T⊆A) (sz:T.card=10) : syndrome T≠0 := by
  classical
  intro zero
  have sum:aug T=0:=aug_zero.mpr ⟨by omega,zero⟩
  obtain ⟨t,ht⟩:=card_pos.mp (show 0<T.card by omega)
  let X:=(T.erase t).powerset
  let Y:=insert (∅:Finset V) ((A\T).powersetCard 1)
  have emptyout:(∅:Finset V)∉(A\T).powersetCard 1:=by simp
  have yc:Y.card=A.card-10+1 := by
    rw [show Y.card=((A\T).powersetCard 1).card+1 from card_insert_of_notMem emptyout,
      card_powersetCard,card_sdiff_of_subset ta,sz,Nat.choose_one_right]
  have xc:X.card=512 := by
    dsimp [X]
    rw [card_powerset,card_erase_of_mem ht,sz];decide
  have out {B:Finset V} (h:B∈Y): B⊆A\T ∧ B.card≤1 := by
    rcases mem_insert.mp h with rfl|hb
    · simp
    · obtain ⟨sub,n⟩:=mem_powersetCard.mp hb;exact ⟨sub,n.le⟩
  have compress {R:Finset V} (rt:R⊆T) :
      ∃S⊆T,S.card≤5 ∧ aug S=aug R := by
    by_cases low:R.card≤5
    · exact ⟨R,rt,low,rfl⟩
    · exact ⟨T\R,sdiff_subset,by rw [card_sdiff_of_subset rt,sz];omega,flip rt sum⟩
  let enc (p:Finset V × Finset V):=aug p.1+aug p.2
  have inject:Set.InjOn enc ↑(X×ˢY) := by
    rintro ⟨I,J⟩ hp ⟨K,L⟩ hq eq
    obtain ⟨hx,hy⟩:=mem_product.mp hp
    obtain ⟨hk,hl⟩:=mem_product.mp hq
    have i:=mem_powerset.mp hx
    have k:=mem_powerset.mp hk
    have dx:=diff_sub i k
    have rt: I∆K⊆T := dx.trans (erase_subset t T)
    obtain ⟨S,st,sc,rep⟩:=compress rt
    have j:=out hy
    have l:=out hl
    have et:=diff_sub j.1 l.1
    have ds:Disjoint S (J∆L) := disjoint_left.mpr fun _ hs he=>(mem_sdiff.mp (et he)).2 (st hs)
    have bc:(J∆L).card≤2 := by
      have h:=card_le_card (diff_sub (subset_union_left (s₂:=L)) (subset_union_right (s₁:=J)))
      have u:=card_union_le J L
      have jc:J.card≤1:=j.2
      have lc:L.card≤1:=l.2
      omega
    have az:aug (S∪(J∆L))=0 := by
      change aug I+aug J=aug K+aug L at eq
      change (∑x∈S∪(J∆L),col x)=0
      rw [sum_union ds]
      change aug S+aug (J∆L)=0
      rw [rep,show aug (I∆K)=aug I+aug K from Green51FourSpace.subset_sum_add col I K,
        show aug (J∆L)=aug J+aug L from Green51FourSpace.subset_sum_add col J L,
        add_add_add_comm,eq,ZModModule.add_self]
    have empty:=small (by omega) avoid (union_subset (st.trans ta) (et.trans sdiff_subset))
      (by rw [card_union_of_disjoint ds];omega) az
    obtain ⟨se,e⟩:=union_eq_empty.mp empty
    have jl:=symmDiff_eq_empty.mp e
    have iz:aug (I∆K)=0 := rep.symm.trans (by simp [se,aug])
    have same:I∆K=∅ := by
      by_cases low:(I∆K).card≤7
      · exact small (by omega) avoid (rt.trans ta) low iz
      · have cs:=card_sdiff_of_subset rt
        have co:=small (by omega) avoid (sdiff_subset.trans ta) (by omega) ((flip rt sum).trans iz)
        have mem:t∈T\(I∆K) := mem_sdiff.mpr ⟨ht,fun m => notMem_erase t T (dx m)⟩
        exact False.elim (notMem_empty t (co ▸ mem))
    exact Prod.ext (symmDiff_eq_empty.mp same) jl
  have bound:=(X×ˢY).card_le_card_of_injOn (t:=(univ:Finset (F×V))) enc (fun _ _=>mem_univ _) inject
  rw [card_product,xc,yc,card_univ,show Fintype.card (F×V)=4096 by simp [Cube,ZMod.card]] at bound
  omega

/-- At size eighteen and above, every even zero-sum subset has size divisible by four. -/
theorem four_divisibility {A:Finset V} (hi:18≤A.card) (avoid:¬FlatAt A 0)
    {T:Finset V} (ta:T⊆A) (even:2∣T.card) (sum:syndrome T=0) : 4∣T.card := by
  have free (R:Finset V) (ra:R⊆A) (sz:R.card=4 ∨ R.card=6) : syndrome R≠0 := fun z=>
    avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨R,ra,sz,z⟩))
  have max:¬25≤A.card := fun big=>avoid (((Green51ElevenThresholds.linear_iff 25).mpr (by decide)) A big)
  have top:=card_le_card ta
  have few:T.card≤7 → T.card=0:=fun h=>card_eq_zero.mpr (small (by omega) avoid ta h (aug_zero.mpr ⟨even,sum⟩))
  have ten:T.card≠10:=fun n=>no_ten hi avoid ta n sum
  have banned:¬(T.card=14 ∨ T.card=18 ∨ T.card=20 ∨ T.card=22) :=
    fun n=>Green51MissingLabel.forbidden n (fun R r=>free R (r.trans ta)) sum
  omega

end Green51ResidualPacking
#print axioms Green51ResidualPacking.no_ten

#print axioms Green51ResidualPacking.four_divisibility
