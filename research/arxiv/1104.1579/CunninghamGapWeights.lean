import CunninghamGapCollisions

/-! Beyond the internal resultants the normalized paired product changes only
at prime divisors of the cross-resultant. -/

namespace CunninghamChain.GapMean

open Finset BatemanHornConjecture

def threshold (m : ℕ) := 2^(m+2)+2*m+3

noncomputable def ratio (k l q h : ℕ) : ℝ :=
  factor k l q (h+2:ℕ) / singleFactor (k+l) q

noncomputable def weight (k l Y h : ℕ) := ∏ q ∈ Y.primesBelow, ratio k l q h

theorem single_pos (m q : ℕ) (hp : q.Prime) : 0 < singleFactor m q := by
  let : Fact q.Prime := ⟨hp⟩
  have hq : (1:ℝ)<q := by exact_mod_cast hp.one_lt
  have nz : 0<1-1/(q:ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr hq)
  have ok : (-1:ZMod q)∈ accepted 1 m q := by
    simp only [accepted,mem_filter,mem_univ,true_and]
    intro f hf
    change f∈(range m).image (form 1) at hf
    obtain ⟨j,_,rfl⟩ := mem_image.mp hf
    have ev : ((form 1 j).map (Int.castRingHom (ZMod q))).eval (-1) = -1 := by simp [form]; ring
    rw [ev]; exact neg_ne_zero.mpr one_ne_zero
  have card := accepted_card 1 m q
  have pos := Finset.card_pos.mpr ⟨_,ok⟩
  have lt : (OmegaP (chainForms 1 m) q : ℝ)<q := by exact_mod_cast (show OmegaP (chainForms 1 m) q<q by omega)
  exact mul_pos (zpow_pos nz _) (sub_pos.mpr ((div_lt_one (by linarith)).mpr lt))

theorem product_single (m Y : ℕ) :
    (∏ q ∈ Y.primesBelow, singleFactor m q)=BatemanHornPartialProduct (chainForms 1 m) Y := by
  simp only [singleFactor,BatemanHornPartialProduct,chainForms_count]

theorem pairProduct_eq_weight (k l Y h : ℕ) :
    pairProduct k l Y (h+2) = weight k l Y h * BatemanHornPartialProduct (chainForms 1 (k+l)) Y := by
  rw [←product_single,weight,←prod_mul_distrib]
  apply prod_congr rfl
  intro q hq
  exact (div_mul_cancel₀ _ (single_pos _ _ (Nat.prime_of_mem_primesBelow hq)).ne').symm

theorem weight_nonneg (k l Y h : ℕ) : 0≤weight k l Y h := by
  apply prod_nonneg
  intro q hq
  have hp := Nat.prime_of_mem_primesBelow hq
  let : Fact q.Prime := ⟨hp⟩
  have h : (1:ℝ)<q := by exact_mod_cast hp.one_lt
  have z : 0<1-1/(q:ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr h)
  apply div_nonneg _ (single_pos _ _ hp).le
  simp only [factor,dif_pos hp,pairFactor]
  positivity

/-- The extra factor is 1 unless two sites collide. Even then its logarithmic
cost is at most twice the number of sites divided by the testing prime. -/
theorem ratio_bounds {k l q : ℕ} (hp : q.Prime) (large : threshold (k+l)≤q) (h : ℕ) :
    1≤ratio k l q h ∧ ratio k l q h ≤ 1+2*(k+l:ℕ)/((q:ℕ):ℝ) ∧
      (¬q∣exceptionalProduct k l h → ratio k l q h=1) := by
  let : Fact q.Prime := ⟨hp⟩
  let m := k+l
  change 2^(m+2)+2*m+3≤q at large
  have non := Nat.zero_le (2^(m+2))
  have two : 2<q := by omega
  have high : 2^m<q := by
    have hh := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_right m 2)
    change 2^(m+2)+2*m+3≤q at large
    omega
  have size : 2*m<q := by change 2^(m+2)+2*m+3≤q at large; omega
  obtain ⟨c,cm,supp,count⟩ := pairCount_excess (k:=k) (l:=l) two high h
  let n := pairCount (accepted 1 k q) (accepted (-1) l q) (h+2:ℕ)
  have countR : (n:ℝ)+m=q+(c:ℝ) := by exact_mod_cast count
  have grow : (2:ℝ)*m<q := by exact_mod_cast size
  have qr : (1:ℝ)<q := by exact_mod_cast hp.one_lt
  have qm : 0<(q:ℝ)-m := by linarith
  have z : 0<1-1/(q:ℝ) := sub_pos.mpr ((div_lt_one (by linarith)).mpr qr)
  have roots : OmegaP (chainForms 1 (k+l)) q=k+l := stable_roots two high
  have val : ratio k l q h = 1+(c:ℝ)/(q-m) := by
    simp only [ratio,factor,dif_pos hp,pairFactor,singleFactor,roots]
    change (_*((n:ℝ)/q))/(_*(1-(m:ℝ)/q))=_
    rw [mul_div_mul_left _ _ (zpow_pos z (-(m:ℤ))).ne']
    field_simp
    linear_combination countR
  have cr : (c:ℝ) ≤ m := by exact_mod_cast cm
  rw [val]
  refine ⟨by linarith [div_nonneg (Nat.cast_nonneg (α:=ℝ) c) qm.le],?_,fun no => by rw [show c=0 from Classical.not_not.mp (fun nc => no (supp nc))]; simp⟩
  suffices bound : (c:ℝ)/(q-m) ≤ 2*m/q by exact add_le_add_right bound 1
  rw [div_le_div_iff₀ qm (by linarith)]
  calc
    (c:ℝ)*q ≤ (m:ℝ)*q := mul_le_mul_of_nonneg_right cr (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) m) (sub_nonneg.mpr grow.le)]

#print axioms single_pos
#print axioms product_single
#print axioms pairProduct_eq_weight
#print axioms weight_nonneg
#print axioms ratio_bounds

end CunninghamChain.GapMean
