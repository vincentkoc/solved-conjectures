import ThetaOrderProjection

/-! A negative maximal-order cubic contribution at p = 241. -/
namespace Arxiv.«2501.03234».ThetaOrderExample
open Finset Complex DirichletCharacter ThetaFourier ThetaPointwiseCubic ThetaPointwiseParity ThetaOrderProjection
noncomputable section
set_option maxRecDepth 32000
private instance : Fact (Nat.Prime 241) := ⟨by norm_num⟩

private def g : (ZMod 241)ˣ := Units.mk0 (7:ZMod 241) (by decide)

private lemma g_order : orderOf g = 240 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · apply Units.ext; decide
  · intro l hl hd
    rw [show 240=2^4*3*5 by decide] at hd
    rcases hl.dvd_mul.mp hd with h|h
    · rcases hl.dvd_mul.mp h with h|h
      · have := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h)
        subst l; decide
      · have := (Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 3)).mp h
        subst l; decide
    · have := (Nat.prime_dvd_prime_iff_eq hl (by decide : Nat.Prime 5)).mp h
      subst l; decide

private def raw (p t : ℕ) := ∑ i∈range (p/2),∑ j∈range (p/2),
  if (t*(2*i+1)*(2*j+1)%p)%2=1 then 1 else 0

private lemma raw_eq {p : ℕ} [Fact p.Prime] (hp : p%2=1) (t : ℕ) :
    rotated p (t:ZMod p)=raw p t := by
  unfold rotated raw
  rw [←sum_progression hp]
  apply sum_congr rfl; intro i _
  rw [←sum_progression hp]
  apply sum_congr rfl; intro j _
  simp only [odds,mem_filter,mem_univ,true_and,←Nat.cast_mul,ZMod.val_natCast]

private def sample (d q : ℕ) := ∑ i∈range q,raw 241 (7^(d*i)%241)

private lemma sample_projection (d q : ℕ) (hd : d*q=240) :
    (240:ℂ)*(sample d q:ℂ) = (q:ℂ)*∑ χ : DirichletCharacter ℂ 241 with orderOf χ∣d,cubic χ := by
  have hg : orderOf g = Nat.card (ZMod 241)ˣ := by rw [g_order,Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient,Nat.totient_prime (Fact.out : Nat.Prime 241)]
  have H := projection g hg d q (hd.trans g_order.symm)
  rw [Nat.totient_prime (Fact.out : Nat.Prime 241)] at H
  change (240:ℂ)*_=_ at H
  rw [←H]; congr 1
  unfold sample
  push_cast
  apply sum_congr rfl; intro i _
  have hh : ((7^(d*i)%241:ℕ):ZMod 241)=(g:ZMod 241)^(d*i) := by
    simp [g,ZMod.natCast_mod]
  rw [←hh,raw_eq (by decide)]

/-- Kernel-verified row counts reused across the fifteen rotations. -/
private def rowTable : List ℕ :=
  [
    0, 120, 60, 80, 60, 72, 60, 69, 60, 66, 60, 65, 60, 63, 59, 64, 56, 63,
    60, 63, 60, 65, 65, 65, 60, 62, 59, 62, 59, 62, 60, 61, 60, 61, 57, 61,
    60, 57, 57, 61, 60, 60, 59, 61, 59, 62, 59, 60, 48, 60, 60, 61, 61, 60,
    60, 61, 61, 61, 60, 60, 60, 60, 61, 61, 60, 61, 61, 60, 61, 69, 61, 61,
    60, 59, 59, 62, 59, 60, 57, 60, 40, 60, 64, 60, 61, 57, 61, 60, 61, 61,
    60, 60, 59, 59, 60, 59, 60, 64, 60, 61, 60, 61, 59, 61, 61, 61, 58, 54,
    58, 61, 61, 59, 59, 60, 59, 61, 58, 61, 60, 60, 60, 60, 60, 60, 59, 62,
    59, 61, 60, 61, 61, 59, 59, 62, 66, 62, 59, 59, 59, 61, 59, 60, 59, 60,
    56, 60, 61, 60, 61, 61, 60, 60, 59, 59, 60, 59, 63, 59, 60, 56, 60, 80,
    60, 63, 60, 61, 58, 61, 61, 60, 59, 59, 51, 59, 60, 59, 59, 60, 59, 59,
    60, 60, 60, 60, 59, 59, 59, 60, 60, 59, 59, 60, 60, 72, 60, 61, 58, 61,
    59, 61, 60, 60, 59, 63, 63, 60, 59, 63, 59, 60, 59, 60, 58, 61, 58, 61,
    58, 60, 55, 55, 55, 60, 57, 60, 57, 64, 56, 61, 57, 60, 55, 60, 54, 60,
    51, 60, 48, 60, 40, 60, 0
  ]

private def rowCount (r : ℕ) : ℕ := ∑ j∈range 120, if (r*(2*j+1)%241)%2=1 then 1 else 0

private lemma rows_checked : ∀ r : Fin 241, rowCount r.val = rowTable.getD r.val 0 := by decide

private def fast (d q : ℕ) : ℕ := ∑ i∈range q,∑ a∈range 120,
  rowTable.getD ((7^(d*i)%241*(2*a+1))%241) 0

set_option maxHeartbeats 800000 in
private lemma fast_eq (d q : ℕ) : sample d q=fast d q := by
  unfold sample fast
  apply sum_congr rfl; intro i _
  unfold raw
  change ∑ a∈range 120,_ = _
  apply sum_congr rfl; intro a _
  let r := 7^(d*i)%241*(2*a+1)
  have h := rows_checked ⟨r%241,Nat.mod_lt _ (by decide)⟩
  change (∑ j∈range 120, if (r*(2*j+1)%241)%2=1 then 1 else 0) = rowTable.getD (r%241) 0
  rw [←h]
  unfold rowCount
  apply sum_congr rfl; intro j _
  simp only [Nat.mod_mul_mod]

private lemma sample_one : sample 240 1=7404 := by rw [fast_eq]; decide

private lemma sample_three : sample 80 3=22128 := by rw [fast_eq]; decide
private lemma sample_five : sample 48 5=36364 := by rw [fast_eq]; decide
private lemma sample_fifteen : sample 16 15=108560 := by rw [fast_eq]; decide

/-- The full-order cubic sum is negative although 241 is one modulo eight. -/
theorem maximal_packet :
    (∑ χ : DirichletCharacter ℂ 241 with orderOf χ=240,cubic χ)=(-1792:ℂ) := by
  classical
  have h1 := sample_projection 240 1 (by decide)
  have h3 := sample_projection 80 3 (by decide)
  have h5 := sample_projection 48 5 (by decide)
  have h15 := sample_projection 16 15 (by decide)
  rw [sample_one] at h1
  rw [sample_three] at h3
  rw [sample_five] at h5
  rw [sample_fifteen] at h15
  calc
    _ = (∑ χ : DirichletCharacter ℂ 241 with orderOf χ∣240,cubic χ)
        -(∑ χ : DirichletCharacter ℂ 241 with orderOf χ∣80,cubic χ)
        -(∑ χ : DirichletCharacter ℂ 241 with orderOf χ∣48,cubic χ)
        +(∑ χ : DirichletCharacter ℂ 241 with orderOf χ∣16,cubic χ) := by
      simp only [sum_filter,←sum_sub_distrib,←sum_add_distrib]
      apply sum_congr rfl; intro χ _
      by_cases hχ : χ=1
      · subst χ; norm_num
      have hd : orderOf χ ∣ 240 := by
        have hcard : Fintype.card (DirichletCharacter ℂ 241)=240 := by
          simpa only [Nat.card_eq_fintype_card,Nat.totient_prime (Fact.out : Nat.Prime 241)] using
            (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 241)
        exact hcard ▸ orderOf_dvd_card
      by_cases hh : orderOf χ ∣ 120
      · have hz := cubic_zero (p:=241) (by decide) hχ hh
        simp [hz]
      · have H : ∀ d : Fin 241, d.val ∣ 240 → ¬ d.val ∣ 120 →
            d.val=16 ∨ d.val=48 ∨ d.val=80 ∨ d.val=240 := by decide
        have hl := Nat.le_of_dvd (by decide : 0<240) hd
        rcases H ⟨orderOf χ,by omega⟩ hd hh with h|h|h|h <;>
          change orderOf χ=_ at h <;> norm_num [h]
    _ = _ := by linear_combination -h1+h3/3+h5/5-h15/15

/-- Thus the maximal-order terms contribute −448/15 to S(241). -/
theorem scaled_maximal_packet :
    (4/(240:ℝ))*((∑ χ : DirichletCharacter ℂ 241 with orderOf χ=240,cubic χ).re) = -448/15 := by
  rw [maximal_packet]; norm_num

theorem original_value : S 241 = 816 := by
  have hr : rotated 241 (1:ZMod 241) = 7404 := by
    have h := raw_eq (p:=241) (by decide) 1
    simpa only [Nat.cast_one] using h.trans (by simpa [sample] using sample_one)
  have ht : triples (odds 241)=(rotated 241 1:ℂ) := by
    simp only [triples,rotated,one_mul,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have h := S_trip (p:=241) (by decide)
  rw [ht,hr,card_odds (by decide)] at h
  norm_num at h
  exact_mod_cast h

#print axioms original_value
#print axioms maximal_packet
#print axioms scaled_maximal_packet
end
end Arxiv.«2501.03234».ThetaOrderExample
