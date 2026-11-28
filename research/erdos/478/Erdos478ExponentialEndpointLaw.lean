import Erdos478GaussianGapTail

/-! # Exponential exceptional-prime estimates for a proportional factorial gap window -/

namespace Erdos478.GapTail
open Finset Filter Topology BinaryGap GapBands GapSieve GapDensity FrobeniusBands BandWeights
open scoped Classical
noncomputable section

/-- The endpoint threshold and the missing-residue bound refer to the same
canonical factorial image. The prime-counting cutoff may depend on the window. -/
theorem proportional_of_inputs (pit : DegreeOnePrimeIdealTheorem) (input : countingInput broad (1/3))
    {H : ℕ → ℕ} {L b A : ℝ} (hL : 1<L) (hw : Tendsto (fun K : ℕ => (H K:ℝ)/K) atTop (𝓝 L))
    (hb : b<(L-1)/3) (hA : A<((L-1)/3-b)^2/(2*((L-1)/3))) :
    ∀ᶠ K : ℕ in atTop, ∀ᶠ X : ℕ in atTop, 1-Real.exp (-A*K/Real.log K)<fraction X (fun p =>
      let D := ⌈b*K/Real.log K⌉₊
      D≤(joined (family K (H K)) p).card ∧ ((Ico 1 p).image (fun n => n.factorial%p)).card+D≤p-1) := by
  let c := (L-1)/3
  let m (K : ℕ) : ℝ := (family K (H K)).card
  let w := Proportional.scale
  have hc : 0<c := by dsimp [c]; linarith
  have mass : Tendsto (fun K => m K*w K) atTop (𝓝 c) := by
    rw [show c=(1/3)*(L-1) by dsimp [c]; ring]
    simpa only [m,w,family_card,Proportional.scale,mul_div_assoc] using length_asymptotic input hL hw
  have conc := ((mass.sub (tendsto_const_nhds (x:=b))).pow 2).div
    ((tendsto_const_nhds (x:=(2:ℝ))).mul mass) (mul_ne_zero (by norm_num) hc.ne')
  filter_upwards [conc.eventually_const_lt hA,mass.eventually_const_lt hb,mass.eventually_const_lt hc,
    eventually_ge_atTop 3] with K hrate hmid hpos hK
  let s := family K (H K)
  have logpos : 0<Real.log K := Real.log_pos (by exact_mod_cast (show 1<K by omega))
  have wp : 0<w K := div_pos logpos (by exact_mod_cast (show 0<K by omega))
  have mp : 0<m K := pos_of_mul_pos_left hpos wp.le
  let δ := (m K*w K-b)/(m K*w K)
  have hd : 0≤δ := div_nonneg (sub_nonneg.mpr hmid.le) hpos.le
  have th : (1-δ)*s.card=b*K/Real.log K := by
    change (1-δ)*m K=_
    dsimp only [δ,w,Proportional.scale]
    field_simp [mp.ne',logpos.ne',show (K:ℝ)≠0 by positivity]
    ring
  have exponent : -δ^2*s.card/2 < -A*K/Real.log K := by
    change -δ^2*m K/2 < _
    have eq : δ^2*m K/2*w K=(m K*w K-b)^2/(2*(m K*w K)) := by
      dsimp only [δ]
      field_simp [mp.ne',wp.ne']
    have less : A/w K < δ^2*m K/2 := (div_lt_iff₀ wp).mpr (eq ▸ hrate)
    have factor : A/w K=A*K/Real.log K := by
      dsimp [w,Proportional.scale]
      field_simp [logpos.ne',show (K:ℝ)≠0 by positivity]
    rw [factor] at less
    simpa only [neg_mul,neg_div] using neg_lt_neg less
  let small := Real.exp (-δ^2*s.card/2)
  let target := Real.exp (-A*K/Real.log K)
  have slack : 0<target-small := sub_pos.mpr (Real.exp_lt_exp.mpr exponent)
  have good : ∀ i∈s, broad i.val ∧ 3 < i.val := by
    intro i hi
    obtain ⟨hk,_,broad_i⟩ := family_mem.mp hi
    exact ⟨broad_i,by omega⟩
  filter_upwards [finite_lower_tail pit s good hd slack,eventually_ge_atTop 2] with X hx hX
  change fraction X _<small+(target-small) at hx
  rw [add_sub_cancel] at hx
  apply (sub_lt_sub_left hx 1).trans_le
  apply Proportional.fraction_lower hX
  intro p hn
  have he := le_of_not_gt hn
  rw [th] at he
  have hd' := Nat.ceil_le.mpr he
  exact ⟨hd',(Nat.add_le_add_left hd' _).trans (joined_deficit s p)⟩

#print axioms proportional_of_inputs
end
end Erdos478.GapTail
