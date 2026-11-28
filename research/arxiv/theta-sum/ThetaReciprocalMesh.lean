import ThetaInteriorResonance

/-! A fixed sparse length grid for detecting a large initial reciprocal sum. -/
namespace Arxiv.«2501.03234».ThetaReciprocalMesh
open Finset Filter Real ThetaReciprocalPrefixes ThetaReciprocalResonance ThetaResonanceScales
noncomputable section

def stride (M i : ℕ) := max 1 (2^i/M)
def grid (p M : ℕ) : Finset ℕ :=
  (range (Nat.log 2 p+1)).biUnion (fun i => (range (4*M)).image (fun j => j*stride M i))

theorem card (p M : ℕ) : (grid p M).card ≤ (Nat.log 2 p+1)*(4*M) := calc
  _ ≤ ∑ i∈range (Nat.log 2 p+1),((range (4*M)).image (fun j => j*stride M i)).card := card_biUnion_le
  _ ≤ ∑ _i∈range (Nat.log 2 p+1),(range (4*M)).card := sum_le_sum (fun _ _ => card_image_le)
  _ = _ := by simp

/-- Rounding down retains the length up to relative error 1/M. -/
theorem approximate {p M N : ℕ} (hp : N≤p) (hN : 0<N) (hM : 0<M) :
    ∃ n∈grid p M, n≤N ∧ M*(N-n)≤N := by
  let i := Nat.log 2 N
  let d := 2^i
  let s := stride M i
  let k := N/s
  have h₁ : d≤N := Nat.pow_log_le_self 2 hN.ne'
  have h₂ : N<2*d := by simpa [d,i,pow_succ,Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1<2) N
  have hs : 0<s := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)
  have hdiv : d/M≤ s := le_max_right ..
  have hnext : d<(d/M+1)*M := by
    have hh := Nat.mod_lt d hM
    have he := Nat.mod_add_div d M
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (d/M) M]
    omega
  have hbound : d<2*s*M := hnext.trans_le (Nat.mul_le_mul_right M (by omega))
  have hk : k<4*M := (Nat.div_lt_iff_lt_mul hs).mpr (h₂.trans_le (by
    have h := Nat.mul_le_mul_left 2 hbound.le
    exact h.trans_eq (by ring)))
  have hn : k*s≤N := Nat.div_mul_le_self N s
  refine ⟨k*s,mem_biUnion.mpr ⟨i,mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hp)),
    mem_image.mpr ⟨k,mem_range.mpr hk,rfl⟩⟩,hn,?_⟩
  by_cases h : d/M≤1
  · have h1 : s=1 := max_eq_left h
    simp [k,h1]
  · have h1 : s=d/M := max_eq_right (by omega : 1≤d/M)
    have he := Nat.mod_add_div N s
    have hr := Nat.mod_lt N hs
    have hd : N-k*s≤ s := by dsimp [k];rw [Nat.mul_comm (N/s) s];omega
    exact ((Nat.mul_le_mul_left M hd).trans (by
      rw [h1,Nat.mul_comm]
      exact Nat.div_mul_le_self d M)).trans h₁

theorem prefix_change {p : ℕ} [Fact p.Prime] (a : ZMod p) (n k : ℕ) :
    ‖recipSum (n+k) a-recipSum n a‖≤k := by
  unfold recipSum
  rw [sum_range_add,add_sub_cancel_left]
  apply (norm_sum_le ..).trans
  simp only [ZMod.stdAddChar_apply,Circle.norm_coe,sum_const,card_range,nsmul_eq_mul,mul_one,le_refl]

def resolution (p : ℕ) : ℕ := ⌈1073741824*log (p:ℝ)*log (log p)⌉₊

/-- The rounded witness uses the same additive multiplier as the original one. -/
theorem detect {p N : ℕ} [Fact p.Prime] {a : ZMod p} (hNp : N≤p)
    (hlog : 1≤log (log (N:ℝ))) (hN : 1<(N:ℝ)) (h : signal N a) :
    ∃ n∈grid p (resolution p), n≤N ∧ resolution p*(N-n)≤N ∧
      4*(n:ℝ)<resolution p*‖recipSum n a‖ := by
  let M := resolution p
  have hnpos : 0<(N:ℝ) := by linarith
  have hl := Real.log_pos hN
  have hd : 0< log (log (N:ℝ)) := by linarith
  have hNp' : (N:ℝ)≤p := by exact_mod_cast hNp
  have hL := log_le_log hnpos hNp'
  have hD := log_le_log hl hL
  have hmul := mul_le_mul hL hD hd.le (hl.le.trans hL)
  have hM : (1073741824:ℝ)*log (N:ℝ)*log (log N) ≤ M := by
    apply le_trans _ (Nat.le_ceil _)
    linarith only [hmul]
  have hMp : 0<(M:ℝ) := lt_of_lt_of_le (by positivity) hM
  obtain ⟨n,hgrid,hn,hgap⟩ := approximate hNp (by exact_mod_cast hnpos) (Nat.cast_pos.mp hMp)
  refine ⟨n,hgrid,hn,hgap,?_⟩
  have hs := (div_lt_iff₀ (by positivity : 0<(134217728:ℝ)*log (N:ℝ)*log (log N))).mp h
  have ht := prefix_change a n (N-n)
  rw [Nat.add_sub_of_le hn,Nat.cast_sub hn] at ht
  have htri := norm_le_norm_add_norm_sub' (recipSum N a) (recipSum n a)
  have hdiff : ‖recipSum N a‖≤‖recipSum n a‖+((N:ℝ)-n) := htri.trans (add_le_add_right ht _)
  have hgap' : (M:ℝ)*((N:ℝ)-n)≤N := by
    have h' := (Nat.cast_le (α:=ℝ)).mpr hgap
    simpa only [Nat.cast_mul,Nat.cast_sub hn] using h'
  change 4*(n:ℝ)<(M:ℝ)*‖recipSum n a‖
  nlinarith only [hs,hgap',mul_le_mul_of_nonneg_left hdiff hMp.le,
    mul_le_mul_of_nonneg_right hM (norm_nonneg (recipSum N a)),
    show (n:ℝ)≤N by exact_mod_cast hn,hnpos]

#print axioms card
#print axioms approximate
#print axioms prefix_change
#print axioms detect
end
end Arxiv.«2501.03234».ThetaReciprocalMesh
