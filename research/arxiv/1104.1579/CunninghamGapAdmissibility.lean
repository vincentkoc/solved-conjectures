import CunninghamPairedExactMean
import CunninghamPairedLocalTest

/-! The nonzero coefficients of the gap mean are decided by the finite paired-prefix test. -/

namespace CunninghamChain.GapMean

open Finset PairedRough

private lemma unit_residue (q k : ℕ) [NeZero q] (s : ℤ) (x : ZMod q) :
    x∈accepted s k q ↔ ∀ i<k, (2:ZMod q)^i*x+(s:ZMod q)*(2^i-1)≠0 := by
  classical
  simp only [accepted,mem_filter,mem_univ,true_and]
  change (∀ f∈(range k).image (form s), _) ↔ _
  simp [form]

private theorem factor_test (k l h q : ℕ) (hp : q.Prime) :
    factor k l q (h+2:ℕ) ≠ 0 ↔ ∃ x : ZMod q, avoids (h+2) k l q x := by
  classical
  let : Fact q.Prime := ⟨hp⟩
  have qr : (1:ℝ)<q := by exact_mod_cast hp.one_lt
  have z : 0<1-1/(q:ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr qr)
  have zp : (1-1/(q:ℝ))^(-((k+l:ℕ):ℤ))≠0 := (zpow_pos z _).ne'
  simp only [factor,dif_pos hp,pairFactor,mul_ne_zero_iff,div_ne_zero_iff,
    Nat.cast_ne_zero,←Nat.pos_iff_ne_zero,hp.pos,and_true,pairCount,card_pos,Finset.Nonempty]
  rw [and_iff_right zp]
  apply exists_congr
  intro x
  rw [mem_filter,unit_residue,unit_residue]
  unfold avoids
  push_cast
  constructor
  · rintro ⟨a,b⟩
    refine ⟨fun i hi e => a i hi ?_,fun i hi e => b i hi ?_⟩
    · linear_combination e
    · linear_combination e
  · rintro ⟨a,b⟩
    refine ⟨fun i hi e => a i hi ?_,fun i hi e => b i hi ?_⟩
    · linear_combination e
    · linear_combination e

/-- The coefficient is positive precisely when the reduced residue test
passes for every prime through k+l. This classification is unconditional. -/
theorem series_pos_iff_local {k l : ℕ} (hk : 0<k) (hl : 0<l) (h : ℕ) :
    0 < series k l h ↔ localTest (h+2) k l := by
  let Z := stop k l h
  have cpos := (chainConstant_spec (show 0<k+l by omega)).1
  have wn : 0≤weight k l Z h := weight_nonneg ..
  constructor
  · intro yes q mem
    have hp := Nat.prime_of_mem_primesLE mem
    apply (factor_test k l h q hp).mp
    intro zero
    have bound := (Nat.mem_primesLE.mp mem).1
    have mem' : q∈Z.primesBelow := by
      apply Nat.mem_primesBelow.mpr
      refine ⟨?_,hp⟩
      have low : threshold (k+l)≤Z := le_max_left ..
      unfold threshold at low
      have := Nat.zero_le (2^(k+l+2))
      omega
    have wz : weight k l Z h=0 := prod_eq_zero mem' (by change ratio k l q h=0; unfold ratio; rw [zero,zero_div])
    change 0<weight k l Z h*chainConstant (k+l) at yes
    rw [wz,zero_mul] at yes
    exact yes.false
  · intro pass
    apply mul_pos _ cpos
    apply lt_of_le_of_ne wn
    apply Ne.symm
    apply prod_ne_zero_iff.mpr
    intro q mem
    have hp := Nat.prime_of_mem_primesBelow mem
    exact div_ne_zero ((factor_test k l h q hp).mpr ((localTest_iff_all hk hl).mp pass q hp)) (single_pos _ _ hp).ne'

#print axioms series_pos_iff_local

end CunninghamChain.GapMean
