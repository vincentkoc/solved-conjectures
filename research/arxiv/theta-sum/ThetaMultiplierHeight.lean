import ThetaResonantPrefix
import ThetaShortParity

/-! The two frequencies in the odd-prefix identity admit small signed representatives
after multiplication by four. -/
namespace Arxiv.«2501.03234».ThetaMultiplierHeight
open Finset Real ThetaShortFrequencies ThetaResonantPrefix ThetaResonantBlock
open ThetaReciprocalParity ThetaReciprocalPrefixes
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem near_mono {t : ZMod p} {A B : ℕ} (hAB : A≤B) : near A t → near B t :=
  fun ⟨j,hj,h⟩ => ⟨j,hj.trans hAB,h⟩

theorem near_mul {t : ZMod p} {T : ℕ} (d : ℕ) (h : near T t) : near (d*T) ((d:ZMod p)*t) := by
  obtain ⟨j,hj,h|h⟩ := h
  · exact ⟨d*j,Nat.mul_le_mul_left d hj,Or.inl (by rw [h,Nat.cast_mul])⟩
  · exact ⟨d*j,Nat.mul_le_mul_left d hj,Or.inr (by rw [h,Nat.cast_mul,mul_neg])⟩

theorem heights (hp : p%2=1) {k i T : ℕ} (hk : k<stop p i) {t : ZMod p}
    (ht : near T t) :
    let c := denom p k/2*t
    near (8*2^i*T) (4*c) ∧ near (8*2^i*T) (4*(c/2)) := by
  have hk' := hk.trans_le (min_le_right ..)
  rw [pow_succ] at hk'
  let d := 2*k+1
  have hd : 2*d ≤ 8*2^i := by dsimp [d];omega
  have hd' : d ≤ 8*2^i := by omega
  have htwo := (ThetaFourier.two_unit hp).ne_zero
  change near _ (4*((d:ZMod p)/2*t)) ∧ near _ (4*((d:ZMod p)/2*t/2))
  constructor
  · have heq : 4*((d:ZMod p)/2*t)=((2*d:ℕ):ZMod p)*t := by push_cast;field_simp;ring
    rw [heq]
    exact near_mono (Nat.mul_le_mul_right T hd) (near_mul _ ht)
  · have heq : 4*((d:ZMod p)/2*t/2)=(d:ZMod p)*t := by field_simp;ring
    rw [heq]
    exact near_mono (Nat.mul_le_mul_right T hd') (near_mul _ ht)

theorem prefix_transfer_at (hp : p%2=1) {i a n : ℕ} (ha : 2^i ≤ a) (han : a+n ≤ 2^(i+1))
    (hm : a+n ≤ p/2) {E : ℝ}
    {Q : ZMod p → Prop} (he : ∀ N : ℕ, 2^i ≤ N → N ≤ 4*2^i → N<p → ∀ c : ZMod p,c≠0 → Q c → ‖recipSum N c‖ ≤ E)
    (c : ZMod p) (hc : c≠0) (hq : Q c) (hq₂ : Q (c/2)) :
    ‖∑ j∈range n,ZMod.stdAddChar (c/denom p (a+j))‖ ≤ 4*E := by
  have h₂ : (2:ZMod p)≠0 := (ThetaFourier.two_unit hp).ne_zero
  have hpow : 2^(i+1)=2^i*2 := pow_succ ..
  have hodd (T : ℕ) (hlo : 2^i ≤ T) (hhi : T ≤ a+n) :
      ‖∑ j∈range T,ZMod.stdAddChar (c/denom p j)‖ ≤ E+E := by
    rw [odd_sum]
    exact (norm_sub_le ..).trans (add_le_add (he _ (by omega) (by omega) (by omega) _ hc hq)
      (he _ hlo (by omega) (by omega) _ (div_ne_zero hc h₂) hq₂))
  have h := sum_range_add (fun j => ZMod.stdAddChar (c/denom p j)) a n
  have h' : (∑ j∈range n,ZMod.stdAddChar (c/denom p (a+j))) =
      (∑ j∈range (a+n),ZMod.stdAddChar (c/denom p j)) -
      ∑ j∈range a,ZMod.stdAddChar (c/denom p j) := by rw [h]; abel
  rw [h']
  apply (norm_sub_le ..).trans
  linarith only [hodd (a+n) (by omega) le_rfl,hodd a ha (by omega)]

#print axioms heights
#print axioms prefix_transfer_at
end
end Arxiv.«2501.03234».ThetaMultiplierHeight
