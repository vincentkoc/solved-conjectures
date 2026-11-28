import ThetaMultiplierHeight

/-! A large dyadic level forces a short reciprocal sum with a small multiplier. -/
namespace Arxiv.«2501.03234».ThetaLowMultiplierLevel
open Finset Real ThetaShortFrequencies ThetaShortReciprocalBlocks ThetaResonantBlock
open ThetaReciprocalParity ThetaReciprocalPrefixes ThetaReciprocalCutoff
open ThetaResonantPrefix ThetaMultiplierHeight
noncomputable section
variable {p : ℕ} [Fact p.Prime]

def cutoff (i : ℕ) := 4*(65536*(i+1))^2

private lemma at_level (hp : p%2=1) {i k a n : ℕ} (hk : k<stop p i)
    (ha : 2^i ≤ a) (han : a+n ≤ stop p i) (hfit : cutoff i ≤ p/2)
    (hd : (2:ℝ)^i/(4096*((i:ℝ)+1)) < |∑ j∈range n,sgn p (a+j) k|) :
    ∃ N : ℕ,2^i ≤ N ∧ N ≤ 4*2^i ∧ N<p ∧ ∃ c : ZMod p,c≠0 ∧ near (8*2^i*cutoff i) (4*c) ∧
      (2:ℝ)^i/(262144*((i:ℝ)+1)*((harmonic (65536*(i+1)):ℝ)+2)) < ‖recipSum N c‖ := by
  by_contra! contra
  let H := 65536*(i+1)
  let T := cutoff i
  have hT : T=4*H^2 := rfl
  have hfitH : H ≤ p/2 := by change 4*H^2 ≤ p/2 at hfit; nlinarith only [hfit,Nat.le_self_pow (by decide : 2≠0) H]
  let L := p/H
  let I := (i:ℝ)+1
  let J := (2:ℝ)^i
  let V := (harmonic H:ℝ)+2
  have hi : 0<I := by dsimp [I]; positivity
  have hj : 0<J := by dsimp [J]; positivity
  have hH : 2 ≤ H := by dsimp [H]; omega
  have hT₀ : 0<T := by rw [hT];positivity
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
  have hsign := ThetaShortParity.block hp (hk.trans_le (min_le_left ..)) hm hL hLp
    (show 0<H by omega) hfitH hT₀ hfit hE (by
      intro t ht hnear
      have hbase : denom p k≠0 := by
        intro h
        have heq := congrArg ZMod.val h
        have hpk := hk.trans_le (min_le_left ..)
        change (((2*k+1:ℕ):ZMod p).val)=_ at heq
        rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at heq
        omega
      have hc := mul_ne_zero (div_ne_zero hbase (ThetaFourier.two_unit hp).ne_zero) ht
      have hh := heights hp hk hnear
      exact prefix_transfer_at hp ha he hm contra _ hc hh.1 hh.2)
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
  have htail : 4*((p:ℝ)/(T*L))*n ≤ 4*J/(65536*I) := by
    rw [←hHI]
    have ht' : (T:ℝ)=4*(H:ℝ)^2 := by exact_mod_cast hT
    have hT' : 0<(T:ℝ) := by exact_mod_cast hT₀
    have hpH := (div_le_iff₀ (mul_pos hH' hL')).mp hR
    have hr : (p:ℝ)/(T*L) ≤ 1/(2*H) := by
      apply (div_le_div_iff₀ (mul_pos hT' hL') (by positivity)).mpr
      rw [ht']
      nlinarith only [mul_le_mul_of_nonneg_right hpH hH'.le]
    calc
      _ ≤ 4*(1/(2*(H:ℝ)))*(2*J) := mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num)) hn
        (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 : 4*J/(65536*I)+J/(16384*I)+4*J/(65536*I) ≤ J/(4096*I) := by field_simp; linarith
  change J/(4096*I) < _ at hd
  linarith only [hsign,hd,h1,h2,htail,h3]

theorem short_prefix (hp : p%2=1) {i : ℕ} (hfit : cutoff i≤p/2)
    (hb : (p:ℝ)/1024 < |tile p i|) :
    ∃ N : ℕ,2^i ≤ N ∧ N ≤ 4*2^i ∧ N<p ∧ ∃ c : ZMod p,c≠0 ∧
      near (8*2^i*cutoff i) (4*c) ∧
      (2:ℝ)^i/(262144*((i:ℝ)+1)*((harmonic (65536*(i+1)):ℝ)+2)) < ‖recipSum N c‖ := by
  obtain ⟨k,hk,a,ha,_,n,hn,h⟩ := long_sign hb
  exact at_level hp hk ha (by omega) hfit h

#print axioms short_prefix
end
end Arxiv.«2501.03234».ThetaLowMultiplierLevel
