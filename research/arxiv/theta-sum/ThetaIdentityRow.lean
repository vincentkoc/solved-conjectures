import ThetaRowCorrelations

/-! A uniform positive reciprocal-row contribution in the identity residue class. -/
namespace Arxiv.«2501.03234».ThetaIdentityRow
open Finset ThetaRowCorrelations ThetaCotangentTriangle
noncomputable section

private theorem half_pos {d w : ℕ} (hd : 1<d) (hw : w≤d) : 0≤wave 1 d w := by
  unfold wave
  split_ifs with h
  · have hlt : w<d := lt_of_le_of_ne hw (fun he => by
      rw [he] at h; have hc := h.2.2.2; rw [Nat.coprime_self] at hc; omega)
    simp only [reciprocalSign,Nat.cast_one,ZMod.inv_one,mul_one,ZMod.val_natCast_of_lt hlt,
      h.2.2.1,if_true]; decide
  · rfl

private theorem initial {d : ℕ} (hd : 1<d) (ho : Odd d) : wave 1 d 1=1 := by
  simp [wave,reciprocalSign,Nat.odd_iff.mp ho,ZMod.val_one'' (by omega : d≠1)]

theorem prefix_pos (d : ℕ) (hd : 1<d) (N : ℕ) : 0≤∑ i∈range N,(wave 1 d (i+1):ℝ) := by
  let v (j : ℕ) : ℝ := wave 1 d j
  have hz : v 0=0 := by simp [v,wave]
  have href (j : ℕ) (hj : j≤2*d) : v (2*d-j) = -v j := by dsimp only [v]; exact_mod_cast wave_reflect hd 1 hj
  have hcycle := ThetaUniformWindows.reflect_period v hz href
  change 0≤∑ i∈range N,v (i+1)
  induction N using Nat.strong_induction_on with
  | h N ih =>
    by_cases hbig : 2*d≤N
    · let K := N-2*d
      have he : N=2*d+K := by dsimp [K]; omega
      have hi := ih K (by dsimp [K]; omega)
      conv_rhs => rw [he,sum_range_add,hcycle,zero_add]
      simpa only [v,Nat.add_assoc,wave_period] using hi
    · by_cases hsmall : N≤d
      · apply sum_nonneg; intro i hi
        dsimp only [v]; exact_mod_cast half_pos hd (show i+1≤d by have := mem_range.mp hi; omega)
      · have hrest : ∑ i∈Ico N (2*d),v (i+1)≤0 := by
          apply sum_nonpos; intro i hi
          obtain ⟨hil,hih⟩ := mem_Ico.mp hi
          have hr := href (2*d-(i+1)) (by omega)
          rw [show 2*d-(2*d-(i+1))=i+1 by omega] at hr
          rw [hr]; apply neg_nonpos.mpr
          dsimp only [v]; exact_mod_cast half_pos hd (show 2*d-(i+1)≤d by omega)
        have H := sum_range_add_sum_Ico (fun i => v (i+1)) (by omega : N≤2*d)
        rw [hcycle] at H; linarith

/-- Every positive window in an odd identity row contributes at least a half. -/
theorem lower {d : ℕ} (hd : 1<d) (ho : Odd d) {K : ℕ} (hk : 0<K) : 1/2≤row d K 1 := by
  let A (k : ℕ) : ℝ := ∑ i∈range k,(wave 1 d (i+1):ℝ)
  have ha (k : ℕ) : 0≤A k  := prefix_pos d hd k
  have h (k : ℕ) : 1/2+A (k+2)/(k+2:ℕ)≤row d (k+2) 1 := by
    induction k with
    | zero =>
      norm_num [row,A,sum_range_succ,initial hd ho]
      <;> ring_nf <;> rfl
    | succ k ih =>
      have hpos : 0<((k+2:ℕ):ℝ) := by positivity
      have hs : A (k+2)/((k+3:ℕ):ℝ) ≤ A (k+2)/((k+2:ℕ):ℝ) :=
        div_le_div_of_nonneg_left (ha _) hpos (by push_cast; linarith)
      have hA : A (k+3)=A (k+2)+(wave 1 d (k+2+1):ℝ) := by dsimp only [A]; rw [sum_range_succ]
      change _≤row d (k+2+1) 1
      rw [row,sum_range_succ]
      change _≤row d (k+2) 1+_
      change 1/2+A (k+3)/(k+3:ℕ)≤_
      rw [hA,add_div]
      push_cast at ih hs ⊢
      have eq : (k:ℝ)+2+1=k+3 := by ring
      rw [eq,div_eq_inv_mul (wave 1 d (k+2+1):ℝ)]
      linarith
  rcases K with _|K
  · omega
  cases K with
  | zero => norm_num [row,initial hd ho]
  | succ k => exact (le_add_of_nonneg_right (div_nonneg (ha _) (Nat.cast_nonneg _))).trans (h k)

#print axioms lower
end
end Arxiv.«2501.03234».ThetaIdentityRow
