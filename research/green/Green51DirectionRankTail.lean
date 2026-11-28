import Green51FixedRankRows
import Green51DirectionRankBudget

/-! # Concentration of the intrinsic direction rank around half the number of sites -/
namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical

theorem far_rank_presentations_rare {Q H I : Type*} [Finite Q] [Fintype I] [AddCommGroup H]
    [Module F H] [FiniteDimensional F H] {h D : ℕ} (large : 10≤h)
    (gap : 64*h*(Nat.log 2 h+2)≤D^2) (A : Q → I → Finset H) (total : ∀ q,∑ i,(A q i).card=h)
    (far : ∀ q, 2*Module.finrank F (rowDirectionSpace (A q))+D≤h ∨
      h+D≤2*Module.finrank F (rowDirectionSpace (A q)))
    (separate : ∀ p q,WordMatch (A p) (A q) → p=q) :
    2^(D^2/8)*Nat.card Q ≤ universalDefectNumber h := by
  classical
  let b (q : Q) := (occupiedRows (A q)).card
  let d (q : Q) := Module.finrank F (rowDirectionSpace (A q))
  have cap (q : Q) : d q+b q≤h := (intrinsic_rank_cap (A q)).trans_eq (total q)
  let K := Fin (h+1) × Fin (h+1)
  let tag (q : Q) : K :=
    (⟨b q,Nat.lt_succ_of_le ((Nat.le_add_left _ _).trans (cap q))⟩,
     ⟨d q,Nat.lt_succ_of_le ((Nat.le_add_right _ _).trans (cap q))⟩)
  let Z (i : K) := {q : Q // tag q=i}
  let code (q : Q) : Σ i : K,Z i := ⟨tag q,⟨q,rfl⟩⟩
  have inj : Function.Injective code := fun _ _ eq => congrArg (fun v => v.2.val) eq
  have cnt := Nat.card_le_card_of_injective code inj
  rw [Nat.card_sigma] at cnt
  let w := (h+1)^2*2^(D^2/8)
  have each (i : K) : w*Nat.card (Z i) ≤ universalDefectNumber h := by
    by_cases empty : IsEmpty (Z i)
    · simp
    have z : Z i := Classical.choice (not_isEmpty_iff.mp empty)
    let k := i.1.val
    let r := i.2.val
    have bk (x : Z i) : b x.val=k := congrArg (fun j : K => j.1.val) x.property
    have dr (x : Z i) : d x.val=r := congrArg (fun j : K => j.2.val) x.property
    have room : r+k≤h := (dr z ▸ bk z ▸ cap z.val)
    have hfar : 2*r+D≤h ∨ h+D≤2*r := dr z ▸ far z.val
    have bnd := count_ambient_at_rank h k r (by omega) (fun x : Z i => A x.val)
      (fun x => total x.val) bk dr (fun p q eq => Subtype.ext (separate _ _ eq))
    have kp : k^(h-k) ≤ h^h := (Nat.pow_le_pow_left (show k≤h by omega) _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))
    have ex : (h-k-r)*r+(h-k-r) ≤ r*(h-r)+h := by
      rw [Nat.mul_comm (h-k-r) r]
      exact Nat.add_le_add (Nat.mul_le_mul_left r (Nat.sub_le_sub_right (Nat.sub_le h k) r))
        ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
    exact direction_rank_charge large (by omega) hfar gap
      (bnd.trans (Nat.mul_le_mul kp (Nat.pow_le_pow_right (by decide) ex)))
  have sum : w*Nat.card Q ≤ (h+1)^2*universalDefectNumber h := by
    calc
      _ ≤ w * ∑ i, Nat.card (Z i) := Nat.mul_le_mul_left _ cnt
      _ = ∑ i,w*Nat.card (Z i) := Finset.mul_sum _ _ _
      _ ≤ ∑ _ : K, universalDefectNumber h := sum_le_sum fun i _ => each i
      _ = _ := by simp [K,pow_two,Nat.mul_assoc]
  change ((h+1)^2*2^(D^2/8))*Nat.card Q ≤ _ at sum
  rw [Nat.mul_assoc] at sum
  exact Nat.le_of_mul_le_mul_left sum (by positivity)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.far_rank_presentations_rare
