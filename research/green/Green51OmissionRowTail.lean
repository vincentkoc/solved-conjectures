import Green51ActiveRowPresentations
import Green51OmissionRowCharge

/-! # A logarithmic cutoff for the number of occupied rows of a stable class -/
namespace Green51FrameIsomorphisms
open Finset
open scoped Classical

theorem many_active_presentations_rare {Q H I : Type*} [Finite Q] [Fintype I]
    [AddCommGroup H] [Module Green53ParityThreshold.F H] [FiniteDimensional Green53ParityThreshold.F H]
    {h B : ℕ} (large : 10 ≤ h) (cut : 64*(Nat.log 2 h+2) ≤ B) (A : Q → I → Finset H)
    (total : ∀ q,∑ i,(A q i).card=h) (many : ∀ q,B ≤ (occupiedRows (A q)).card)
    (separate : ∀ p q,WordMatch (A p) (A q) → p=q) :
    2^(B*h/8)*Nat.card Q ≤ universalDefectNumber h := by
  classical
  have occupied_le (q : Q) : (occupiedRows (A q)).card ≤ h := by
    have bound : (∑ _ : occupiedRows (A q),1) ≤ (∑ i : occupiedRows (A q), (A q i).card) :=
      sum_le_sum (fun i _ => card_pos.mpr (mem_filter.mp i.property).2)
    simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one,Nat.cast_id,occupied_sum,total] using bound
  let tag (q : Q) : Fin (h+1) := ⟨(occupiedRows (A q)).card,Nat.lt_succ_of_le (occupied_le q)⟩
  let D (i : Fin (h+1)) := {q : Q // tag q=i}
  let code (q : Q) : Σ i : Fin (h+1),D i := ⟨tag q,⟨q,rfl⟩⟩
  have inj : Function.Injective code := fun _ _ eq => congrArg (fun z => z.2.val) eq
  have number := Nat.card_le_card_of_injective code inj
  rw [Nat.card_sigma] at number
  let weight := (h+1)*2^(B*h/8)
  have each (i : Fin (h+1)) : weight*Nat.card (D i) ≤ universalDefectNumber h := by
    by_cases hi : B ≤ i.val
    · have hb := count_distinguished_presentations h i.val (fun z : D i => A z.val)
          (fun z => total z.val) (fun z => congrArg Fin.val z.property)
          (fun p q w => Subtype.ext (separate p.val q.val w))
      have bpow : i.val^(h-i.val) ≤ h^(h-i.val) := Nat.pow_le_pow_left (Nat.le_of_lt_succ i.isLt) _
      have weak := hb.trans (Nat.mul_le_mul_right _ (bpow.trans (Nat.le_mul_of_pos_left _ (by positivity : 0<2^h))))
      have bound := dyadic_row_charge large (Nat.le_of_lt_succ i.isLt) (cut.trans hi) weak
      exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide : 0<2) (Nat.div_le_div_right (Nat.mul_le_mul_right h hi))))).trans bound
    · have empty : IsEmpty (D i) := ⟨fun z => hi ((many z.val).trans_eq (congrArg Fin.val z.property))⟩
      simp
  have total : weight*Nat.card Q ≤ (h+1)*universalDefectNumber h := by
    calc
      _ ≤ weight * ∑ i, Nat.card (D i) := Nat.mul_le_mul_left _ number
      _ = ∑ i, weight*Nat.card (D i) := Finset.mul_sum _ _ _
      _ ≤ ∑ _ : Fin (h+1), universalDefectNumber h := sum_le_sum fun i _ => each i
      _ = _ := by simp
  change ((h+1)*2^(B*h/8))*Nat.card Q ≤ _ at total
  rw [Nat.mul_assoc] at total
  exact Nat.le_of_mul_le_mul_left total (Nat.succ_pos _)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.many_active_presentations_rare
