import ThetaReciprocalPrefixes
import ThetaDyadicDiscrepancy

/-! Pointwise control of the original theta triangle by ordinary short reciprocal sums. -/

namespace Arxiv.«2501.03234».ThetaShortSumTransfer
open Finset Real ThetaReciprocalPrefixes ThetaReciprocalParity ThetaShortReciprocalBlocks
variable {p : ℕ} [Fact p.Prime]

private lemma twice_le_exp (t : ℕ) : 2*t ≤ 2^t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rcases t with _|t
    · decide
    rw [pow_succ]
    omega

theorem triangle {K : ℝ} (hK : 1≤K) (hb : PrefixBound p K) (hp : p%2=1)
    {t : ℕ} (ht : 2≤t) (ht₁ : p/2≤2^t) (ht₂ : t≤p/2) :
    |block p 0 (p/2)| ≤ 4*(p:ℝ)*(4*t+1024*((harmonic t:ℝ)+2)*K*sqrt t) := by
  let L := p/t
  have hL : 0<L := Nat.div_pos (by omega) (by omega)
  have hLp : p/2+L≤p := by
    have h := Nat.div_mul_le_self p t
    have hh : L*2≤L*t := Nat.mul_le_mul_left _ ht
    change L*t≤p at h
    omega
  have ht₀ : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hp₀ : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hL₀ : (0:ℝ)<L := by exact_mod_cast hL
  have hprod : (L:ℝ)*t ≤ p := by exact_mod_cast Nat.div_mul_le_self p t
  have hquo : (p:ℝ)/((t:ℝ)*L)≤2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (show p≤2*(t*L) by
      have hr := Nat.mod_lt p (show 0<t by omega)
      have h := Nat.div_add_mod p t
      change t*L+p%t=p at h
      have hmul := Nat.mul_le_mul_left t (show 1≤L by omega)
      omega)
  let A := 4/(t:ℝ)
  let B := 512*((harmonic t:ℝ)+2)*K
  have hhh : 0≤(harmonic t:ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have htri := ThetaDyadicDiscrepancy.dyadic (p:=p) hA hB t ht₁
  have hblock := htri (by
    intro i hi k hk a ha ha' n hn
    let V := (i:ℝ)+1
    let D := V*sqrt V
    let P := (2:ℝ)^i
    have hP : 0<P := by dsimp [P]; positivity
    have hD : 0<D := by dsimp [D,V]; positivity
    have han : a+n ≤ min (p/2) (2^(i+1)) := by omega
    obtain ⟨hm,htop⟩ := le_min_iff.mp han
    have hn' : (n:ℝ)≤2*P := by
      dsimp [P]
      exact_mod_cast (show n≤2*2^i by rw [pow_succ] at htop; omega)
    have bound := block_signs hp (lt_of_lt_of_le hk (min_le_left ..)) hm hL hLp
      (show 0<t by omega) ht₂ (show 0≤128*K*P/D by positivity)
      (fun c hc => odd_interval hK hb hp ha htop hm hc)
    apply bound.trans
    have firstPart : 2*(n:ℝ)*L/p ≤ P*A := by
      dsimp [A]
      apply (div_le_iff₀ hp₀).mpr
      calc
        _ ≤ 4*P*L := by nlinarith [mul_le_mul_of_nonneg_right hn' hL₀.le]
        _ ≤ P*(4/t)*p := by
          field_simp
          nlinarith [mul_le_mul_of_nonneg_left hprod hP.le]
    change _ ≤ P*(A+B/D)
    have secondPart : 4*((harmonic t:ℝ)+(p:ℝ)/(t*L))*(128*K*P/D) ≤ P*(B/D) := by
      calc
        _ ≤ 4*((harmonic t:ℝ)+2)*(128*K*P/D) := by gcongr
        _ = _ := by dsimp [B]; ring
    linarith only [firstPart,secondPart, mul_add P A (B/D)])
  apply hblock.trans_eq
  dsimp [A,B]
  field_simp
  ring

theorem original_transfer : ∃ C : ℝ,0<C ∧ ∀ p : ℕ,[Fact p.Prime] → p%2=1 → 4≤p →
    ∀ K : ℝ, 1≤K → PrefixBound p K →
    let t := Nat.log 2 p
    |(S p:ℝ)| ≤ C*p + 2*(p:ℝ)*harmonic (p/2) + (p:ℝ)*log p/2 +
      4*(p:ℝ)*(4*t+1024*((harmonic t:ℝ)+2)*K*sqrt t) := by
  obtain ⟨C,hC,h⟩ := triangle_approx
  refine ⟨C,hC,?_⟩
  intro p _ hp hp₄ K hK hb
  let t := Nat.log 2 p
  have ht : 2≤t := (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : p≠0)).2 hp₄
  have h := h p hp
  have he := Nat.lt_pow_succ_log_self (by decide : 1<2) p
  change p<2^(t+1) at he
  rw [pow_succ] at he
  have hf := Nat.pow_log_le_self 2 (by omega : p≠0)
  have hle := (twice_le_exp t).trans hf
  have hb' := triangle hK hb hp ht (by omega) (by omega)
  have hlog : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast (show 1≤p by omega))
  have hterm : 0≤(p:ℝ)*log p/2 := by positivity
  dsimp only
  rw [abs_le] at h hb' ⊢
  constructor <;> linarith [h.1,h.2,hb'.1,hb'.2]

#print axioms triangle
#print axioms original_transfer
end Arxiv.«2501.03234».ThetaShortSumTransfer
