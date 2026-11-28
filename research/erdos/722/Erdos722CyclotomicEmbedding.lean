import Erdos722CyclotomicShifts

/-!
# Choosing points with prescribed difference classes

At the start of step `t` each unused point has at least `q/C^t`
candidates. A union bound gives a pivot that preserves this estimate for
each remaining point at the next step.
-/

namespace Erdos722.Cyclotomy
open Finset
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]

/-- Size and multiplicative invariance needed for the shift estimate. -/
structure ClassBounds (D : Finset F) (C : ℕ) : Prop where
  size : 2*Fintype.card F ≤ C*D.card
  slopes : ∃ U : Finset F, U.card=D.card ∧
    ∀ a ∈ U, ∀ S : Finset F, ∀ b, hits D S a b = hits D S 1 b

private noncomputable def bad (C : ℕ) (D S : Finset F) : Finset F :=
  univ.filter fun b => C*(neighbors D S b).card < S.card

private theorem bad_card {C w : ℕ} {D S : Finset F} (h : ClassBounds D C)
    (hS : Fintype.card F ≤ S.card*w) :
    (bad C D S).card ≤ 4*C^2*w := by
  let q := Fintype.card F
  obtain ⟨U,hU,hstable⟩ := h.slopes
  have hb := sparse_shifts D S U (bad C D S) hU (fun a ha => hstable a ha S) (by
    intro b hb
    have hN := (mem_filter.mp hb).2
    calc
      _ ≤ C*D.card*(neighbors D S b).card := Nat.mul_le_mul_right _ h.size
      _ = D.card*(C*(neighbors D S b).card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hN.le)
  have hq : q ≤ C*D.card := (show q ≤ 2*q by omega).trans h.size
  have hprod : q^3 ≤ (C*D.card)^2*(S.card*w) := by
    rw [pow_succ q 2]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hq 2) hS
  apply Nat.le_of_mul_le_mul_right (c := q^3) _ (by dsimp [q]; positivity)
  calc
    _ ≤ (bad C D S).card*((C*D.card)^2*(S.card*w)) := Nat.mul_le_mul_left _ hprod
    _ = ((bad C D S).card*D.card^2*S.card)*(C^2*w) := by ring
    _ ≤ (4*q^3)*(C^2*w) := Nat.mul_le_mul_right _ hb
    _ = _ := by ring

private theorem choose_from {C k : ℕ} (hC : 0<C)
    (hbig : k*(4*C^2*C^k)*C^k < Fintype.card F) (r : ℕ) :
    ∀ (t : ℕ), t+r=k → ∀ (D : Fin r → Fin r → Finset F) (S : Fin r → Finset F),
    (∀ i j, i<j → ClassBounds (D i j) C) →
    (∀ i, Fintype.card F ≤ (S i).card*C^t) →
    ∃ f : Fin r → F, (∀ i, f i ∈ S i) ∧ ∀ i j, i<j → f j-f i ∈ D i j := by
  induction r with
  | zero =>
    intro t he D S hc hs
    exact ⟨Fin.elim0,(fun i => i.elim0),(fun i => i.elim0)⟩
  | succ r ih =>
    intro t he D S hc hs
    have hpow := Nat.pow_le_pow_right hC (show t≤k by omega)
    let B (j : Fin r) := bad C (D 0 j.succ) (S j.succ)
    have hB (j : Fin r) : (B j).card ≤ 4*C^2*C^k :=
      bad_card (hc _ _ (Fin.succ_pos _)) ((hs _).trans (Nat.mul_le_mul_left _ hpow))
    have hu : (univ.biUnion B).card ≤ k*(4*C^2*C^k) := calc
      _ ≤ ∑ j : Fin r, (B j).card := card_biUnion_le
      _ ≤ ∑ _j : Fin r, 4*C^2*C^k := sum_le_sum (fun j _ => hB j)
      _ = r*(4*C^2*C^k) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    have hpiv : (univ.biUnion B).card < (S 0).card := by
      by_contra! hn
      exact (not_lt_of_ge ((hs 0).trans (Nat.mul_le_mul (hn.trans hu) hpow))) hbig
    obtain ⟨x,hx,hout⟩ := exists_mem_notMem_of_card_lt_card hpiv
    let S' (j : Fin r) := neighbors (D 0 j.succ) (S j.succ) x
    have hxgood (j : Fin r) : (S j.succ).card ≤ C*(S' j).card := by
      apply le_of_not_gt
      intro hh
      exact hout (mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨mem_univ _,hh⟩⟩)
    obtain ⟨g,hg,hd⟩ := ih (t+1) (by omega) (fun i j => D i.succ j.succ) S'
      (fun i j hij => hc _ _ (Fin.succ_lt_succ_iff.mpr hij)) (fun j => (hs _).trans (calc
        _ ≤ (C*(S' j).card)*C^t := Nat.mul_le_mul_right _ (hxgood j)
        _ = (S' j).card*C^(t+1) := by rw [pow_succ]; ring))
    refine ⟨Fin.cons x g,?_,?_⟩
    · exact Fin.cases hx (fun i => (mem_filter.mp (hg i)).1)
    · intro i
      refine Fin.cases ?_ (fun a => ?_) i
      · exact Fin.cases (by simp) (fun j _ => (mem_filter.mp (hg j)).2)
      · exact Fin.cases (by simp) (fun b hab => hd a b (Fin.succ_lt_succ_iff.mp hab))

/-- Realize every prescribed list of difference classes on a sufficiently
large finite field. Only pairs `i<j` impose a condition. -/
theorem prescribed_differences {C k : ℕ} (hC : 0<C)
    (hbig : k*(4*C^2*C^k)*C^k < Fintype.card F) (D : Fin k → Fin k → Finset F)
    (hc : ∀ i j, i<j → ClassBounds (D i j) C) :
    ∃ f : Fin k → F, ∀ i j, i<j → f j-f i ∈ D i j := by
  obtain ⟨f,_,h⟩ := choose_from hC hbig k 0 (by omega) D (fun _ => univ) hc (by simp)
  exact ⟨f,h⟩

#print axioms prescribed_differences

end Erdos722.Cyclotomy
