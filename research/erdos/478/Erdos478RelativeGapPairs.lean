import Erdos478NormalPrimeRootAction
import Erdos478RootlessPrimeGaps

/-! # Simultaneous control of two factorial-gap roots and an auxiliary action -/

namespace Erdos478.BinaryGap
open Polynomial Function
noncomputable section

/-- A prime-to-l auxiliary quotient can be fixed pointwise while moving
any ordered pair of distinct gap roots to any other. -/
theorem relative_gap_pair {l : ℕ} (hl : l.Prime) (h : broad l) (hl3 : 3<l)
    (K : Type*) [Field K] [Algebra ℚ K] [Normal ℚ K]
    [Fact (((rationalGap l).map (algebraMap ℚ K)).Splits)]
    {B : Type*} [Group B] [Finite B] (φ : (K ≃ₐ[ℚ] K) →* B) (hB : ¬l ∣ Nat.card B)
    {a b c d : (rationalGap l).rootSet K} (hab : a≠b) (hcd : c≠d) :
    ∃ τ : K ≃ₐ[ℚ] K, φ τ=1 ∧ τ (a:K)=(c:K) ∧ τ (b:K)=(d:K) := by
  classical
  let : Fact l.Prime := ⟨hl⟩
  let F := rationalGap l
  have irr : Irreducible F := GapFamilies.irreducible_gap_rat hl.pos
  have degree : F.natDegree=l := by
    change (descPochhammer ℚ l-1).natDegree=l
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa [descPochhammer_natDegree] using hl.pos),
      descPochhammer_natDegree]
  obtain ⟨σ,hfix,hpow⟩ := broad_derangement hl h hl3
  let e := Gal.rootsEquivRoots F K
  have fixed (x : F.rootSet K) : Gal.galActionHom F K σ x≠x := by
    intro hx
    have eq : e (σ • e.symm x) = x := hx
    have eq' := e.injective (eq.trans (e.apply_symm_apply x).symm)
    exact hfix (e.symm x) (congrArg Subtype.val eq')
  have size : Fintype.card (F.rootSet K)=l :=
    (card_rootSet_eq_natDegree irr.separable (Fact.out : (F.map (algebraMap ℚ K)).Splits)).trans degree
  have hd : l ∣ Nat.card F.Gal := degree ▸ Gal.prime_degree_dvd_card irr (degree ▸ hl)
  let ρ := Gal.galActionHom F K
  have hi := Gal.galActionHom_injective F K
  obtain ⟨τ,ht,ha,hb⟩ := PrimeDifferences.kernel_pair_transitive (Gal.restrict F K)
    (Gal.restrict_surjective F K) φ ρ hi size hd hB
    (PrimeDifferences.nonaffine_of_derangement ρ hi fixed hpow) hab hcd
  exact ⟨τ,ht,(Gal.galActionHom_restrict F K τ a).symm.trans (congrArg Subtype.val ha),
    (Gal.galActionHom_restrict F K τ b).symm.trans (congrArg Subtype.val hb)⟩

#print axioms relative_gap_pair
end
end Erdos478.BinaryGap
