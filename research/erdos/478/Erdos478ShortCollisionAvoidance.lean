import Erdos478IntegerGapObservables

/-! # Simultaneously avoiding every short factorial collision -/

namespace Erdos478.FirstCollision
open Polynomial Finset Filter Topology BinaryGap FrobeniusCounts GapDensity GapSieve
open SplittingDensity NumberField Ideal MulAction
open scoped Classical
noncomputable section

def NoShort (p K : ℕ) : Prop := ∀ k, 0<k → k≤K → ¬HasGap p k
def First (p l : ℕ) : Prop := 0<l ∧ HasGap p l ∧ ∀ k, 0<k → k<l → ¬HasGap p k

theorem no_gap_one {p : ℕ} (hp : p.Prime) : ¬HasGap p 1 := by
  rintro ⟨j,hj,_,he⟩
  obtain ⟨lo,hi⟩ := mem_Ico.mp hj
  let : Fact p.Prime := ⟨hp⟩
  have hn : (j.factorial : ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff,hp.dvd_factorial]
    exact hi.not_ge
  have eq := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr he
  rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,add_mul,one_mul] at eq
  have hj0 : (j:ZMod p)=0 := (mul_eq_zero.mp (by linear_combination -eq : (j:ZMod p)*j.factorial=0)).resolve_right hn
  exact (Nat.not_dvd_of_pos_of_lt lo hi) ((ZMod.natCast_eq_zero_iff j p).mp hj0)

def short (K : ℕ) := Icc 2 K
def zeroCounts {s : Finset ℕ} (a : s → ℕ) : Prop := ∀ i, a i=0
def survival (K : ℕ) := density (short K) zeroCounts

theorem noShort_iff {p : ℕ} (hp : p.Prime) (K : ℕ) :
    NoShort p K ↔ zeroCounts (s:=short K) (fun i => (endpoints i.val p).card) := by
  constructor
  · intro h i
    have ⟨lo,hi⟩ := mem_Icc.mp i.prop
    have := h i.val (by omega) hi
    simpa [ConditionalGaps.hasGap_iff] using this
  · intro h k lo hi
    by_cases h₁ : k=1
    · simpa [h₁] using no_gap_one hp
    · have hz : (endpoints k p).card=0 := h ⟨k,mem_Icc.mpr ⟨by omega,hi⟩⟩
      simp [ConditionalGaps.hasGap_iff,hz]

theorem survival_limit (pit : DegreeOnePrimeIdealTheorem) (K : ℕ) :
    Tendsto (fun X => fraction X (fun p => NoShort p K)) atTop (𝓝 (survival K)) :=
  density_limit pit _ (fun _ hk => (mem_Icc.mp hk).1) _ _ 0 (fun _ _ hp => noShort_iff hp K)

attribute [local instance] Int.ideal_span_isMaximal_of_prime

/-- One Frobenius lift above two is a simultaneous derangement in every degree
at least two. The prime may ramify in the common field. -/
theorem simultaneous_zero (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ g : Aut K, ∀ k, 2≤k → fixedGap K k g=0 := by
  let P : Ideal ℤ := span {(2:ℤ)}
  let : P.IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨J,hJ,hcomp⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S:=𝓞 K) P
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))]; exact bot_le)
  let : J.IsMaximal := hJ
  let : J.LiesOver P := ⟨hcomp.symm⟩
  obtain ⟨g,_,hfix⟩ := binary_frobenius_lift K J
  refine ⟨g,fun k hk => ?_⟩
  let : IsEmpty (fixedBy (GapRoots K k) g) :=
    ⟨fun x => fixes_no_gap_root hk J g hfix x.val (congrArg Subtype.val (mem_fixedBy.mp x.prop))⟩
  exact Nat.card_of_isEmpty

theorem zero_density_lower (s : Finset ℕ) (hs : ∀ k∈s, 2≤k) :
    ((∏ k∈s, k.factorial : ℕ) : ℝ)⁻¹ ≤ density s zeroCounts := by
  classical
  let K := FieldOf s
  let : NumberField K := ⟨⟩
  let : IsGalois ℚ K := { to_isSeparable := inferInstance, to_normal := SplittingField.instNormal _ }
  obtain ⟨g,hg⟩ := simultaneous_zero K
  let w (h : Aut K) : ℝ := if zeroCounts (s:=s) (fun i => fixedGap K i.val h) then 1 else 0
  have wg : w g=1 := if_pos (show zeroCounts (s:=s) (fun i => fixedGap K i.val g) from fun i => hg i.val (hs i i.prop))
  have sum : 1≤∑ h, w h := wg ▸ Finset.single_le_sum (f:=w)
    (fun h _ => by dsimp [w]; split_ifs <;> norm_num) (mem_univ g)
  have pos (k) (hk : k∈s) := (by decide : 0<2).trans_le (hs k hk)
  have bound := density_lower_bound (by decide : 0<1) s pos
  simp only [Nat.totient_one,one_mul] at bound
  apply bound.trans
  change (Module.finrank ℚ K : ℝ)⁻¹ ≤ (∑ h, w h)/Fintype.card (Aut K)
  rw [← IsGalois.card_aut_eq_finrank ℚ K,Nat.card_eq_fintype_card,← one_div]
  exact div_le_div_of_nonneg_right sum (Nat.cast_nonneg _)

theorem survival_lower (K : ℕ) : ((∏ k∈Icc 2 K, k.factorial : ℕ) : ℝ)⁻¹ ≤ survival K :=
  zero_density_lower _ (fun _ hk => (mem_Icc.mp hk).1)

theorem survival_pos (K : ℕ) : 0<survival K :=
  lt_of_lt_of_le (inv_pos.mpr (Nat.cast_pos.mpr (prod_pos fun k _ => Nat.factorial_pos k))) (survival_lower K)

#print axioms NoShort
#print axioms First
#print axioms no_gap_one
#print axioms short
#print axioms zeroCounts
#print axioms survival
#print axioms noShort_iff
#print axioms survival_limit
#print axioms simultaneous_zero
#print axioms zero_density_lower
#print axioms survival_lower
#print axioms survival_pos
end
end Erdos478.FirstCollision
