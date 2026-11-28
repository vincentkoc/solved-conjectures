import Erdos722CyclotomicStarter
import Erdos722CyclotomicMultipliers
import Erdos722QuartetSeeds

/-!
# Developing a cyclotomic starter

Take the multiples of a starter by one representative of each pair of
opposites in the subgroup. Their ordered differences cover all nonzero
field elements. Equality of the two cardinalities makes the coverage unique.
-/

namespace Erdos722.Cyclotomy
open Finset Quartet
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

theorem twice_choose (k : ℕ) : k.choose 2*2=k*(k-1) := by
  rw [Nat.choose_two_right,Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self k)]

private theorem develop_cover {b k : ℕ} (f : Fin b → Fin k → F)
    (hf : ∀ l, Function.Injective (f l))
    (cover : ∀ d : Fˣ, ∃ l i j, f l i-f l j=(d:F))
    (size : b*(k*(k-1))=Fintype.card F-1) : Has (·=k) (Fintype.card F) := by
  classical
  let P := (univ : Finset (Fin k)).offDiag
  have hc : Fintype.card (Fin b × P) = Fintype.card Fˣ := by
    simpa only [Fintype.card_prod,Fintype.card_coe,P,offDiag_card,card_univ,Fintype.card_fin,Nat.mul_sub_one,Fintype.card_units] using size
  let val (t : Fin b × P) : Fˣ := Units.mk0 (f t.1 t.2.1.1-f t.1 t.2.1.2)
    (sub_ne_zero.mpr ((hf t.1).ne (mem_offDiag.mp t.2.2).2.2))
  have onto : Function.Surjective val := by
    intro d
    obtain ⟨l,i,j,h⟩ := cover d
    have ne : i≠j := fun e => d.ne_zero (by rw [← h,e,sub_self])
    exact ⟨(l,⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,ne⟩⟩),Units.ext h⟩
  have inj := ((Fintype.bijective_iff_surjective_and_card val).mpr ⟨onto,hc⟩).1
  apply Seeds.development f hf
  intro d hd
  obtain ⟨t,ht⟩ := onto (Units.mk0 d hd)
  refine ⟨(t.1,t.2.1),congrArg Units.val ht,?_⟩
  rintro ⟨l,i,j⟩ h
  change f l i-f l j=d at h
  have ne : i≠j := fun e => hd (by rw [← h,e,sub_self])
  let u : Fin b × P := (l,⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,ne⟩⟩)
  have eq : u=t := inj ((show val u=Units.mk0 d hd from Units.ext h).trans ht.symm)
  exact congrArg (fun x : Fin b × P => (x.1,x.2.1)) eq

theorem develop_starter {k : ℕ} (H : Subgroup Fˣ) (hm : H.index = k.choose 2)
    (hneg : (-1:Fˣ)∈H) (hchar : (-1:F)≠1)
    (f : Fin k → F) (hf : Function.Injective f)
    (hr : ∀ c : Fˣ ⧸ H, ∃ i j : Fin k, i<j ∧ f j-f i ∈ colorSet H c) :
    Has (·=k) (Fintype.card F) := by
  classical
  obtain ⟨R,hR,hcover⟩ := half_multipliers H hneg hchar
  let e := (R.equivFinOfCardEq rfl).symm
  let starters (l : Fin R.card) (i : Fin k) : F := ((e l).1:F)*f i
  apply develop_cover starters (fun l _ _ h => hf (mul_left_cancel₀ (e l).1.ne_zero h)) _ ?_
  · intro d
    obtain ⟨i,j,_,hij⟩ := hr (d : Fˣ ⧸ H)
    obtain ⟨v,hv,hc⟩ := mem_color.mp hij
    let u := d/v
    have hu : u∈H := QuotientGroup.eq_iff_div_mem.mp hc.symm
    have hmul : (u:F)*(f j-f i)=(d:F) := by
      rw [← hv]; change ((d/v*v:Fˣ):F)=(d:F); simp
    rcases hcover u hu with h|h
    · obtain ⟨l,hl⟩ := e.surjective ⟨u,h⟩
      exact ⟨l,j,i,by simpa [starters,hl,mul_sub] using hmul⟩
    · obtain ⟨l,hl⟩ := e.surjective ⟨-u,h⟩
      refine ⟨l,i,j,?_⟩
      dsimp [starters]
      rw [hl]
      rw [← hmul]
      change (-(u:F))*f i-(-(u:F))*f j=(u:F)*(f j-f i)
      ring
  · calc
      _ = H.index*(2*R.card) := by rw [hm,← twice_choose k]; ring
      _ = Fintype.card F-1 := by rw [hR,H.index_mul_card,Nat.card_units,Nat.card_eq_fintype_card]

#print axioms twice_choose
#print axioms develop_starter

end Erdos722.Cyclotomy
