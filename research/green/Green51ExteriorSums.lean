import Green51TenDimensions

/-! # Odd sums in disjoint parts of a flat-free configuration -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise
namespace Green51ExteriorSums
local notation "F" => ZMod 2
variable {G:Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem odd_set {B:Finset G} {a b c:G} (ha:a∈B) (hb:b∈B) (hc:c∈B) :
    ∃T⊆B,(T.card=1 ∨ T.card=3) ∧ ∑x∈T,x=a+b+c := by
  classical
  by_cases ab:a=b
  · subst b;exact ⟨{c},by simpa using hc,Or.inl (card_singleton _),by simp [ZModModule.add_self]⟩
  by_cases ac:a=c
  · subst c;exact ⟨{b},by simpa using hb,Or.inl (card_singleton _),by
      rw [add_right_comm,ZModModule.add_self,zero_add,sum_singleton]⟩
  by_cases bc:b=c
  · subst c;exact ⟨{a},by simpa using ha,Or.inl (card_singleton _),by simp [add_assoc,ZModModule.add_self]⟩
  refine ⟨{a,b,c},?_,Or.inr (by simp [ab,ac,bc]),?_⟩
  · intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl <;> assumption
  · simp [ab,ac,bc,add_assoc]

theorem disjoint_odd {A B C:Finset G} (size:5≤A.card) (avoid:¬∃p,FlatAt A p)
    (inB:B⊆A) (inC:C⊆A) (dis:Disjoint B C) {a b c x y z:G}
    (ha:a∈B) (hb:b∈B) (hc:c∈B) (hx:x∈C) (hy:y∈C) (hz:z∈C) : a+b+c≠x+y+z := by
  intro eq
  obtain ⟨T,bt,ts,st⟩ := odd_set ha hb hc
  obtain ⟨U,cu,us,su⟩ := odd_set hx hy hz
  have mem {T:Finset G} (sub:T⊆A) (sz:T.card=1 ∨ T.card=3) :
      T∈A.powersetCard 1∪A.powersetCard 3 :=
    sz.elim (fun s=>mem_union_left _ (mem_powersetCard.mpr ⟨sub,s⟩))
      (fun s=>mem_union_right _ (mem_powersetCard.mpr ⟨sub,s⟩))
  have same := Green51SparseDimensions.odd_sum_inj A size (fun h=>avoid ⟨0,(flat_zero A).mpr h⟩)
    (mem (bt.trans inB) ts) (mem (cu.trans inC) us) (st.trans (eq.trans su.symm))
  obtain ⟨v,hv⟩ := card_pos.mp (show 0<T.card by omega)
  exact disjoint_left.mp dis (bt hv) (cu (same ▸ hv))

end Green51ExteriorSums
#print axioms Green51ExteriorSums.disjoint_odd
