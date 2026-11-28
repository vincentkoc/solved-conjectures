import ThetaResonantPrefix

/-! Counting separated levels that carry large reciprocal sums. -/
namespace Arxiv.«2501.03234».ThetaResonantCount
open Finset Real ThetaResonantBlock ThetaShortReciprocalBlocks ThetaDyadicDiscrepancy
open ThetaReciprocalParity ThetaReciprocalPrefixes
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem peak (hp : p%2=1) {i t : ℕ} (hi : i<t) (ht : 2 ≤ t) (htp : t ≤ p/2)
    {K A : ℝ} (hK : 1 ≤ K) (hA : 1 ≤ A) (hKA : ((harmonic t:ℝ)+2)*K ≤ A*sqrt A)
    (hb : PrefixBound p K) : |tile p i| ≤ 2064*(p:ℝ)*A := by
  let I := (i:ℝ)+1
  let J := (2:ℝ)^i
  have hI : 0<I := by dsimp [I]; positivity
  have hJ : 0<J := by dsimp [J]; positivity
  rcases le_total I A with hl|hl
  · apply (trivial_tile i).trans
    change 8*(p:ℝ)*I ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg p), mul_nonneg (Nat.cast_nonneg p) (show 0 ≤ A by linarith)]
  let L := p/t
  have hL : 0<L := Nat.div_pos (by omega) (by omega)
  have hLp : p/2+L ≤ p := by
    have h := Nat.div_mul_le_self p t
    have hh : L*2 ≤ L*t := Nat.mul_le_mul_left _ ht
    change L*t ≤ p at h
    omega
  have ht₀ : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hp₀ : (0:ℝ)<p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hL₀ : (0:ℝ)<L := by exact_mod_cast hL
  have hprod : (L:ℝ)*t ≤ p := by exact_mod_cast Nat.div_mul_le_self p t
  have hquo : (p:ℝ)/((t:ℝ)*L) ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (show p ≤ 2*(t*L) by
      have hr := Nat.mod_lt p (show 0<t by omega)
      have h := Nat.div_add_mod p t
      change t*L+p%t=p at h
      have hmul := Nat.mul_le_mul_left t (show 1 ≤ L by omega)
      omega)
  let V := (harmonic t:ℝ)+2
  have hV : 0<V := by
    have h : (0:ℝ)<harmonic t := by exact_mod_cast harmonic_pos (by omega : t≠0)
    dsimp [V]; linarith
  let D := 4*J/t+512*V*K*J/(I*sqrt I)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htile := tile_bound (p:=p) (i:=i) hD (by
    intro k hk a ha ha' n hn
    have han : a+n ≤ stop p i := by omega
    have hm := han.trans (min_le_left ..)
    have htop := han.trans (min_le_right ..)
    have hn' : (n:ℝ) ≤ 2*J := by dsimp [J]; exact_mod_cast (show n ≤ 2*2^i by rw [pow_succ] at htop;omega)
    have bound := block_signs hp (hk.trans_le (min_le_left ..)) hm hL hLp
      (show 0<t by omega) htp (show 0 ≤ 128*K*J/(I*sqrt I) by positivity)
      (fun c hc => odd_interval hK hb hp ha htop hm hc)
    apply bound.trans
    apply add_le_add
    · apply (div_le_div_iff₀ hp₀ ht₀).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hn' (mul_nonneg hL₀.le ht₀.le),
        mul_le_mul_of_nonneg_left hprod hJ.le]
    · calc
        _ ≤ 4*V*(128*K*J/(I*sqrt I)) := by dsimp [V];gcongr
        _ = _ := by ring)
  apply htile.trans
  have he : 4*(p:ℝ)*I*D/J = 16*p*(I/t)+2048*p*(V*K/sqrt I) := by
    dsimp [D]; field_simp;ring
  change 4*(p:ℝ)*I*D/J ≤ _
  rw [he]
  have hIt : I/(t:ℝ) ≤ 1 := (div_le_one ht₀).mpr (by dsimp [I]; exact_mod_cast hi)
  have hR : V*K/sqrt I ≤ A := (div_le_iff₀ (sqrt_pos.mpr hI)).mpr
    (hKA.trans (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hl) (by linarith)))
  nlinarith only [mul_le_mul_of_nonneg_left hIt hp₀.le,mul_le_mul_of_nonneg_left hR hp₀.le,
    mul_le_mul_of_nonneg_left hA hp₀.le]

def levels (p s t : ℕ) [Fact p.Prime] := (Ico s t).filter (fun i => (p:ℝ)/1024 < |tile p i|)

theorem count {s t : ℕ} {A : ℝ} (hA : 0<A) (ht : p/2 ≤ 2^t) (hs : s ≤ t)
    (hsmall : 8192*s^2 ≤ t) (hbad : (p:ℝ)*t/256 ≤ |block p 0 (p/2)|)
    (cap : ∀ i<t, |tile p i| ≤ 2064*(p:ℝ)*A) :
    (t:ℝ)/(2097152*A) ≤ (levels p s t).card := by
  classical
  have he := tiled (p:=p) (p/2) t
  rw [min_eq_left ht] at he
  change (∑ i∈range t,tile p i)=_ at he
  rw [←he] at hbad
  have hsum := hbad.trans (abs_sum_le_sum_abs ..)
  rw [←sum_range_add_sum_Ico (fun i => |tile p i|) hs] at hsum
  have hlow : ∑ i∈range s,|tile p i| ≤ 8*(p:ℝ)*(s:ℝ)^2 := by
    calc
      _ ≤ ∑ _i∈range s,8*(p:ℝ)*s := by
        apply sum_le_sum; intro i hi; apply (trivial_tile i).trans
        gcongr; exact_mod_cast mem_range.mp hi
      _ = _ := by simp; ring
  let P := fun i => (p:ℝ)/1024 < |tile p i|
  have heq := sum_filter_add_sum_filter_not (Ico s t) P (fun i => |tile p i|)
  have hhi := sum_le_sum (s:=levels p s t) (fun i hi => cap i (mem_Ico.mp (mem_filter.mp hi).1).2)
  simp only [sum_const,nsmul_eq_mul] at hhi
  have hlo := sum_le_sum (s:=(Ico s t).filter (fun i => ¬P i))
    (fun i hi => le_of_not_gt (mem_filter.mp hi).2)
  simp only [sum_const,nsmul_eq_mul] at hlo
  have hcard : (((Ico s t).filter (fun i => ¬P i)).card:ℝ) ≤ t := by
    exact_mod_cast (card_filter_le ..).trans ((Nat.card_Ico ..).le.trans (Nat.sub_le ..))
  have hs' : 8192*(s:ℝ)^2 ≤ t := by exact_mod_cast hsmall
  have hp₀ : 0<(p:ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  change (∑ i∈levels p s t,|tile p i|)+_= _ at heq
  apply (div_le_iff₀ (by positivity)).mpr
  apply le_of_mul_le_mul_left _ hp₀
  have hnon : 0 ≤ ((levels p s t).card:ℝ)*(p:ℝ)*A := by positivity
  nlinarith only [hsum,heq,hlow,hhi,hlo,mul_le_mul_of_nonneg_left hs' hp₀.le,
    mul_le_mul_of_nonneg_right hcard (show 0 ≤ (p:ℝ)/1024 by positivity),hnon]

#print axioms peak
#print axioms count
end
end Arxiv.«2501.03234».ThetaResonantCount
