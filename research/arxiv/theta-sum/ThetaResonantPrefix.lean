import ThetaResonantBlock
import ThetaReciprocalPrefixes

/-! A large dyadic cotangent block forces a long ordinary reciprocal exponential sum. -/
namespace Arxiv.«2501.03234».ThetaResonantPrefix
open Finset Real ThetaShortReciprocalBlocks ThetaResonantBlock ThetaReciprocalParity
open ThetaReciprocalPrefixes ThetaReciprocalCutoff
noncomputable section
variable {p : ℕ} [Fact p.Prime]

private lemma long_sign {i : ℕ} (htile : (p:ℝ)/1024 < |tile p i|) :
    ∃ k<stop p i, ∃ a, 2^i ≤ a ∧ a ≤ stop p i ∧ ∃ n ≤ stop p i-a,
      (2:ℝ)^i/(4096*((i:ℝ)+1)) < |∑ j∈range n, sgn p (a+j) k| := by
  by_contra! h
  have hle := tile_bound (show 0 ≤ (2:ℝ)^i/(4096*((i:ℝ)+1)) by positivity) h
  have hid : 4*(p:ℝ)*((i:ℝ)+1)*((2:ℝ)^i/(4096*((i:ℝ)+1)))/(2:ℝ)^i=(p:ℝ)/1024 := by
    have hi : 0<(i:ℝ)+1 := by positivity
    field_simp
    ring
  linarith

private lemma prefix_transfer (hp : p%2=1) {i a n : ℕ} (ha : 2^i ≤ a) (han : a+n ≤ 2^(i+1))
    (hm : a+n ≤ p/2) {E : ℝ}
    (he : ∀ N : ℕ, 2^i ≤ N → N ≤ 4*2^i → N<p → ∀ c : ZMod p,c≠0 → ‖recipSum N c‖ ≤ E)
    (c : ZMod p) (hc : c≠0) :
    ‖∑ j∈range n,ZMod.stdAddChar (c/denom p (a+j))‖ ≤ 4*E := by
  have h₂ : (2:ZMod p)≠0 := (ThetaFourier.two_unit hp).ne_zero
  have hpow : 2^(i+1)=2^i*2 := pow_succ ..
  have hodd (T : ℕ) (hlo : 2^i ≤ T) (hhi : T ≤ a+n) :
      ‖∑ j∈range T,ZMod.stdAddChar (c/denom p j)‖ ≤ E+E := by
    rw [odd_sum]
    exact (norm_sub_le ..).trans (add_le_add (he _ (by omega) (by omega) (by omega) _ hc)
      (he _ hlo (by omega) (by omega) _ (div_ne_zero hc h₂)))
  have h := sum_range_add (fun j => ZMod.stdAddChar (c/denom p j)) a n
  have h' : (∑ j∈range n,ZMod.stdAddChar (c/denom p (a+j))) =
      (∑ j∈range (a+n),ZMod.stdAddChar (c/denom p j)) -
      ∑ j∈range a,ZMod.stdAddChar (c/denom p j) := by rw [h]; abel
  rw [h']
  apply (norm_sub_le ..).trans
  linarith only [hodd (a+n) (by omega) le_rfl,hodd a ha (by omega)]

private lemma smoothed_contra (hp : p%2=1) {i k a n : ℕ} (hk : k<stop p i)
    (ha : 2^i ≤ a) (han : a+n ≤ stop p i) (hfit : 65536*(i+1) ≤ p/2)
    (hd : (2:ℝ)^i/(4096*((i:ℝ)+1)) < |∑ j∈range n,sgn p (a+j) k|) :
    ∃ N : ℕ,2^i ≤ N ∧ N ≤ 4*2^i ∧ N<p ∧ ∃ c : ZMod p,c≠0 ∧
      (2:ℝ)^i/(262144*((i:ℝ)+1)*((harmonic (65536*(i+1)):ℝ)+2)) < ‖recipSum N c‖ := by
  by_contra! contra
  let H := 65536*(i+1)
  let L := p/H
  let I := (i:ℝ)+1
  let J := (2:ℝ)^i
  let V := (harmonic H:ℝ)+2
  have hi : 0<I := by dsimp [I]; positivity
  have hj : 0<J := by dsimp [J]; positivity
  have hH : 2 ≤ H := by dsimp [H]; omega
  have hL : 0<L := Nat.div_pos (by omega) (by omega)
  have hH' : 0<(H:ℝ) := by exact_mod_cast (show 0<H by omega)
  have hL' : 0<(L:ℝ) := by exact_mod_cast hL
  have hV : 0<V := by
    have h := harmonic_pos (by omega : H≠0)
    dsimp [V]
    positivity [show 0<(harmonic H:ℝ) by exact_mod_cast h]
  have hp' : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hprod : L*H ≤ p := Nat.div_mul_le_self p H
  have hLp : p/2+L ≤ p := by
    have h := Nat.mul_le_mul_left L hH
    omega
  have hR : (p:ℝ)/((H:ℝ)*L) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (show p ≤ 2*(H*L) by
      have he := Nat.div_add_mod p H
      change H*L+p%H=p at he
      have hmod := Nat.mod_lt p (show 0<H by omega)
      have hh := Nat.mul_le_mul_left H (show 1 ≤ L by omega)
      omega)
  have hm := han.trans (min_le_left ..)
  have he := han.trans (min_le_right ..)
  have hE : 0 ≤ 4*(J/(262144*I*V)) := mul_nonneg (by norm_num) (div_nonneg hj.le (mul_nonneg (mul_nonneg (by norm_num) hi.le) hV.le))
  have hsign := block_signs hp (hk.trans_le (min_le_left ..)) hm hL hLp
    (show 0<H by omega) hfit hE
    (prefix_transfer hp ha he hm contra)
  have hn : (n:ℝ) ≤ 2*J := by
    dsimp [J]
    exact_mod_cast (show n ≤ 2*2^i by rw [pow_succ] at he;omega)
  have hcast : (L:ℝ)*H ≤ p := by exact_mod_cast hprod
  have hHI : (H:ℝ)=65536*I := by dsimp [H,I]; push_cast; ring
  have h1 : 2*(n:ℝ)*L/p ≤ 4*J/(65536*I) := by
    rw [←hHI]
    apply (div_le_div_iff₀ hp' hH').mpr
    nlinarith only [mul_le_mul_of_nonneg_right hn (mul_nonneg hL'.le hH'.le),
      mul_le_mul_of_nonneg_left hcast hj.le]
  have hsum : (harmonic H:ℝ)+(p:ℝ)/(H*L) ≤ V := by
    change (harmonic H:ℝ)+(p:ℝ)/(H*L) ≤ (harmonic H:ℝ)+2
    linarith only [hR]
  have h2 : 4*((harmonic H:ℝ)+(p:ℝ)/(H*L))*(4*(J/(262144*I*V))) ≤ J/(16384*I) := by
    calc
      _ ≤ 4*V*(4*(J/(262144*I*V))) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hE
      _ = _ := by field_simp; ring
  have h3 : 4*J/(65536*I)+J/(16384*I) ≤ J/(4096*I) := by field_simp; linarith
  change J/(4096*I) < _ at hd
  linarith only [hsign,hd,h1,h2,h3]

theorem resonant_prefix (hp : p%2=1) {i : ℕ} (hfit : 65536*(i+1) ≤ p/2)
    (htile : (p:ℝ)/1024 < |tile p i|) :
    (2:ℝ)^i ≤ 4096*((i:ℝ)+1)*discrepancy p ∧
    ∃ N : ℕ,2^i ≤ N ∧ N ≤ 4*2^i ∧ N<p ∧ ∃ c : ZMod p,c≠0 ∧
      (2:ℝ)^i/(262144*((i:ℝ)+1)*((harmonic (65536*(i+1)):ℝ)+2)) < ‖recipSum N c‖ := by
  obtain ⟨k,hk,a,ha,ha',n,hn,H⟩ := long_sign htile
  have han : a+n ≤ stop p i := by omega
  refine ⟨?_,smoothed_contra hp hk ha han hfit H⟩
  have hpr := (Fact.out : p.Prime).pos
  have hk' := hk.trans_le (min_le_left (p/2) (2^(i+1)))
  have ha' := han.trans (min_le_left (p/2) (2^(i+1)))
  have hv : ((2*k+1 : ℕ) : ZMod p)≠0 := by
    intro h
    have h' := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at h'
    omega
  have h := reciprocal_interval hp (2*a+1) (2*k+1) n hv (by omega)
    (by intro j hj; constructor <;> omega)
  push_cast at h
  simp only [sgn,show ∀ j : ℕ, 2*(a+j)+1=2*a+1+2*j by intro j; omega] at H
  have hh := (div_lt_iff₀ (by positivity)).mp (H.trans_le h)
  linarith

#print axioms resonant_prefix
end
end Arxiv.«2501.03234».ThetaResonantPrefix
