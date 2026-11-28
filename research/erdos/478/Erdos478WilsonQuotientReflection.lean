import Erdos478CosetVisitBounds
import Erdos478ReflectedParityValues

/-! # Two disjoint sets of quotient roots under Wilson reflection -/

namespace Erdos478.QuotientSpacing
open Finset ReturnConcentration
open scoped Classical
noncomputable section

/-- Reflecting a gap changes its quotient by the sign of the gap. -/
theorem reflected_quotient {p : ℕ} (hp : p.Prime) (i k : ℕ) (up : i+k<p) :
    quotient p (p-1-(i+k)) (p-1-i)=(-1:ZMod p)^k*quotient p i (i+k) := by
  let : Fact p.Prime := ⟨hp⟩
  have left := ParityProducts.reflected_factorials (p:=p) i (by omega)
  have right := ParityProducts.reflected_factorials (p:=p) (i+k) up
  have base : (i.factorial : ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff,hp.dvd_factorial]; omega
  have reflected : ((p-1-(i+k)).factorial : ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff,hp.dvd_factorial]; omega
  have signs : (-1:ZMod p)^k*(-1:ZMod p)^(i+k+1)=(-1:ZMod p)^(i+1) := by
    rw [show i+k+1=i+1+k by omega,pow_add]
    calc
      _ = (-1:ZMod p)^(i+1)*(-1:ZMod p)^(k+k) := by rw [pow_add]; ring
      _ = _ := by rw [(show Even (k+k) from ⟨k,rfl⟩).neg_one_pow,mul_one]
  unfold quotient
  field_simp
  linear_combination left - (-1:ZMod p)^k * right - signs

/-- No two selected factorials have either of the two possible Wilson products. -/
def avoidsWilson (p : ℕ) (A : Finset ℕ) : Prop := ∀ i ∈ A, ∀ j ∈ A,
    (i.factorial : ZMod p)*j.factorial ≠ 1 ∧ (i.factorial : ZMod p)*j.factorial ≠ -1

theorem doubled_capacity {p : ℕ} (hp : p.Prime) (A : Finset ℕ) (fits : A ⊆ Ico 1 p)
    (sep : avoidsWilson p A) (D : Finset (ZMod p)) (cover : adjacentQuotients p A ⊆ D)
    (neg : ∀ u∈D,-u∈D) (k : ℕ) :
    2*((links A).filter (fun e => e.2-e.1=k)).card ≤ D.card*k := by
  let : Fact p.Prime := ⟨hp⟩
  let E := (links A).filter (fun e => e.2-e.1=k)
  let f (e : ℕ × ℕ) := p-1-e.2
  have data {e : ℕ × ℕ} (h : e∈E) : e.1∈A ∧ e.2∈A ∧ e.1<e.2 ∧ e.1+k=e.2 := by
    obtain ⟨he,gap⟩ := mem_filter.mp h
    obtain ⟨l,r,lt⟩ := links_mem he
    exact ⟨l,r,lt,by omega⟩
  by_cases hn : E.Nonempty
  · obtain ⟨q,hq⟩ := hn
    have hk : 0<k := by have h := data hq; omega
    have top : p-1∉A := by
      intro mem
      have h := (sep _ mem _ mem).1
      simp [ZMod.wilsons_lemma] at h
    have ends {e : ℕ × ℕ} (he : e∈E) : 1≤e.1 ∧ e.2<p-1 := by
      obtain ⟨l,r,_,_⟩ := data he
      have h := (mem_Ico.mp (fits r)).2
      have ne : e.2≠p-1 := fun eq => top (eq ▸ r)
      exact ⟨(mem_Ico.mp (fits l)).1,by omega⟩
    have start {e : ℕ × ℕ} (h : e∈E) : e.1∈quotientStarts p k D := by
      obtain ⟨lo,up⟩ := ends h
      have gap := (data h).2.2.2
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨lo,by omega⟩,gap ▸ cover (mem_image_of_mem _ (mem_filter.mp h).1)⟩
    have reflect {e : ℕ × ℕ} (h : e∈E) : f e∈quotientStarts p k D := by
      obtain ⟨lo,up⟩ := ends h
      have gap := (data h).2.2.2
      have rv := reflected_quotient hp e.1 k (by omega)
      have qe := (mem_filter.mp (start h)).2
      have endeq : f e+k=p-1-e.1 := by dsimp [f]; omega
      apply mem_filter.mpr
      refine ⟨mem_Ico.mpr ⟨by dsimp [f]; omega,by dsimp [f]; omega⟩,?_⟩
      rw [endeq,show f e=p-1-(e.1+k) by rw [gap],rv]
      rcases Nat.even_or_odd k with he|ho
      · simpa only [he.neg_one_pow,one_mul] using qe
      · simpa only [ho.neg_one_pow,neg_one_mul] using neg _ qe
    have leftInj : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) (↑E : Set (ℕ × ℕ)) := by
      intro e he s hs eq
      exact Prod.ext eq (by have a := (data he).2.2.2; have b := (data hs).2.2.2; omega)
    have rightInj : Set.InjOn f E := by
      intro e he s hs eq
      have a := (data he).2.2.2
      have b := (data hs).2.2.2
      have ea := (ends he).2
      have eb := (ends hs).2
      dsimp [f] at eq
      exact Prod.ext (by omega) (by omega)
    have dis : Disjoint (E.image Prod.fst) (E.image f) := by
      apply disjoint_left.mpr
      intro x hx hy
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hy
      obtain ⟨e,he,eq⟩ := mem_image.mp hx
      have both := sep s.2 (data hs).2.1 (f s) (eq ▸ (data he).1)
      have r := ParityProducts.reflected_factorials (p:=p) s.2 (by have b := ends hs; omega)
      change (s.2.factorial : ZMod p)*(f s).factorial=_ at r
      rcases Nat.even_or_odd (s.2+1) with even|odd
      · exact both.1 (r.trans even.neg_one_pow)
      · exact both.2 (r.trans odd.neg_one_pow)
    have sub : E.image Prod.fst ∪ E.image f ⊆ quotientStarts p k D :=
      union_subset (image_subset_iff.mpr fun _ h => start h) (image_subset_iff.mpr fun _ h => reflect h)
    have count := (card_le_card sub).trans (quotient_capacity hp hk D)
    rw [card_union_of_disjoint dis,card_image_of_injOn leftInj,card_image_of_injOn rightInj] at count
    simpa only [two_mul] using count
  · have eq : E=∅ := not_nonempty_iff_eq_empty.mp hn
    change 2*E.card≤_
    simp [eq]

theorem reflected_bound {p : ℕ} (hp : p.Prime) (A : Finset ℕ) (fits : A⊆Ico 1 p)
    (sep : avoidsWilson p A) (D : Finset (ZMod p)) (cover : adjacentQuotients p A ⊆ D)
    (neg : ∀ u∈D,-u∈D) : 16*(A.card-1)^3≤9*D.card*(width A)^2 := by
  by_cases hn : (links A).Nonempty
  · have nonempty : D.Nonempty := (hn.image _).mono cover
    simpa only [links_card,links_sum] using
      packing (links A) (fun e => e.2-e.1) D.card 2 (card_pos.mpr nonempty) (by decide)
        (fun e he => Nat.sub_pos_of_lt (links_mem he).2.2) (doubled_capacity hp A fits sep D cover neg)
  · have z := (links_card A).symm.trans (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn))
    simp [z]

#print axioms reflected_quotient
#print axioms avoidsWilson
#print axioms doubled_capacity
#print axioms reflected_bound
end
end Erdos478.QuotientSpacing
