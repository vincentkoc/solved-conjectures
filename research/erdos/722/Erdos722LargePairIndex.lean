import Erdos722IntegralPairRelations
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Nat.ModEq

/-!
# Pair designs at large index

Taking the quotient by the block incidence map gives signed multiplicities.
A uniform increase of the block multiplicities supplies nonnegative weights
for every sufficiently large index satisfying the pair counting conditions.
-/

namespace Erdos722.PairLattice
open Finset
variable {α : Type*} [DecidableEq α]

/-- Signed multiplicities on k-subsets give the requested index on the pairs of any
admissible subset, and index zero on all other pairs. -/
theorem signed_pairs [Fintype α] {k : ℕ} (hk : 2≤k) (hv : k+2≤Fintype.card α)
    (V : Finset α) (l : ℕ) (h₁ : k-1 ∣ l*(V.card-1)) (h₂ : k.choose 2 ∣ l*V.card.choose 2) :
    ∃ w : Finset α → ℤ, ∀ e : Finset α, e.card=2 →
      (∑ B∈(univ : Finset α).powersetCard k, if e⊆B then w B else 0) =
        if e⊆V then (l : ℤ) else 0 := by
  classical
  let blocks := (univ : Finset α).powersetCard k
  let unit (e : Finset α) : Finset α → ℤ := Pi.single e 1
  let vec (B : Finset α) := ∑ e∈B.powersetCard 2, unit e
  let inc : (Finset α → ℤ) →+ (Finset α → ℤ) := {
    toFun := fun w => ∑ B∈blocks, w B • vec B
    map_zero' := by simp
    map_add' := by intro v w; simp only [Pi.add_apply,add_zsmul,sum_add_distrib] }
  let q := QuotientAddGroup.mk' inc.range
  have hzero (B : Finset α) (hB : B.card=k) : (∑ e∈B.powersetCard 2, q (unit e))=0 := by
    rw [← map_sum]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    refine AddMonoidHom.mem_range.mpr ⟨Pi.single B 1,?_⟩
    change (∑ D∈blocks, (Pi.single B 1 : Finset α → ℤ) D • vec D)=vec B
    rw [sum_eq_single B]
    · simp
    · intro D _ hd; simp [hd]
    · intro h; exact (h (mem_powersetCard.mpr ⟨subset_univ _,hB⟩)).elim
  have hvq := scaled_pair_sum_zero hk hv (fun e => q (unit e)) hzero V l h₁ h₂
  rw [← map_sum,← map_nsmul] at hvq
  obtain ⟨w,hw⟩ := AddMonoidHom.mem_range.mp ((QuotientAddGroup.eq_zero_iff _).mp hvq)
  have eval (B e : Finset α) (he : e.card=2) : vec B e = if e⊆B then 1 else 0 := by
    dsimp only [vec,unit]
    rw [Finset.sum_apply,sum_pi_single]
    simp [he]
  refine ⟨w,?_⟩
  intro e he
  have h := congrFun hw e
  change (∑ B∈blocks, w B • vec B) e = (l • vec V) e at h
  rw [Finset.sum_apply,Pi.smul_apply,eval V e he] at h
  have htarget : l • (if e⊆V then (1:ℤ) else 0) = if e⊆V then (l:ℤ) else 0 := by split <;> simp
  rw [htarget] at h
  refine Eq.trans (sum_congr rfl (fun B _ => ?_)) h
  change (if e⊆B then w B else 0) = w B • vec B e
  rw [eval B e he]
  split <;> simp

#print axioms signed_pairs

/-- With the point and block sizes fixed, every sufficiently large index
satisfying the two counting conditions admits nonnegative block multiplicities. -/
theorem eventual_index [Fintype α] {k : ℕ} (hk : 2≤k) (hv : k+2≤Fintype.card α) :
    ∃ L, ∀ l≥L, k-1 ∣ l*(Fintype.card α-1) → k.choose 2 ∣ l*(Fintype.card α).choose 2 →
      ∃ w : Finset α → ℕ, ∀ e : Finset α, e.card=2 →
        (∑ B∈((univ : Finset α).powersetCard k).filter (e ⊆ ·), w B)=l := by
  classical
  let v := Fintype.card α
  let blocks := (univ : Finset α).powersetCard k
  let C := (v-2).choose (k-2)
  let d := (k-1)*k.choose 2
  let period := C*d
  have hcpos : 0<C := Nat.choose_pos (by dsimp [v]; omega)
  have hkp : 0<k.choose 2 := Nat.choose_pos hk
  have hd : 0<d := Nat.mul_pos (by omega) hkp
  have hp : 0<period := Nat.mul_pos hcpos hd
  let admissible (l : ℕ) := k-1 ∣ l*(v-1) ∧ k.choose 2 ∣ l*v.choose 2
  have hs (r : ℕ) : ∃ w : Finset α → ℤ, admissible r → ∀ e : Finset α, e.card=2 →
      (∑ B∈blocks.filter (e ⊆ ·), w B)=(r:ℤ) := by
    by_cases h : admissible r
    · obtain ⟨w,hw⟩ := signed_pairs hk hv (univ : Finset α) r (by simpa [v] using h.1)
        (by simpa [v] using h.2)
      exact ⟨w,fun _ e he => by simpa [blocks,sum_filter] using hw e he⟩
    · exact ⟨0,fun hr => (h hr).elim⟩
  choose w hw using hs
  let mass r := ∑ B∈blocks, (w r B).natAbs
  let M := ∑ r∈range period, mass r
  refine ⟨M*period,?_⟩
  intro l hl h₁ h₂
  let r := l%period
  let t := (l/period)*d
  have hmod := Nat.mod_modEq l period
  have hp₁ : k-1 ∣ period := (dvd_mul_right (k-1) (k.choose 2)).trans (dvd_mul_left _ C)
  have hp₂ : k.choose 2 ∣ period := (dvd_mul_left (k.choose 2) (k-1)).trans (dvd_mul_left _ C)
  have hr : admissible r := ⟨((hmod.mul_right (v-1)).dvd_iff hp₁).mpr h₁,
    ((hmod.mul_right (v.choose 2)).dvd_iff hp₂).mpr h₂⟩
  have ht : M≤t := ((Nat.le_div_iff_mul_le hp).mpr hl).trans (Nat.le_mul_of_pos_right _ hd)
  have hn (B : Finset α) (hB : B∈blocks) : 0≤ w r B + (t:ℤ) := by
    have h₁ : (w r B).natAbs ≤ mass r := single_le_sum (f:=fun B => (w r B).natAbs) (fun _ _ => Nat.zero_le _) hB
    have h₂ : mass r≤M := single_le_sum (f:=mass) (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.mod_lt l hp))
    have h₃ : -w r B ≤ ((w r B).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      exact neg_le_abs _
    omega
  refine ⟨fun B => (w r B + (t:ℤ)).toNat,?_⟩
  intro e he
  let through := blocks.filter (e ⊆ ·)
  have hc : through.card=C := by
    simpa [through,blocks,C,v,he] using
      card_filter_powersetCard_subset e (univ : Finset α) k (subset_univ _) (by omega)
  have eq : r+C*t=l := by
    change l%period+C*((l/period)*d)=l
    rw [show C*((l/period)*d)=period*(l/period) by dsimp [period]; ring]
    exact Nat.mod_add_div l period
  apply Int.ofNat_inj.mp
  push_cast
  calc
    _ = ∑ B∈through, (w r B+(t:ℤ)) := by
      apply sum_congr rfl
      intro B hB
      exact Int.toNat_of_nonneg (hn B (mem_filter.mp hB).1)
    _ = (r:ℤ)+(C:ℤ)*t := by rw [sum_add_distrib,hw r hr e he,sum_const,hc]; simp
    _ = _ := by exact_mod_cast eq

#print axioms eventual_index
end Erdos722.PairLattice
