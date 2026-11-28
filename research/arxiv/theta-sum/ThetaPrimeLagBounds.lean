import ThetaPositiveLag
import ThetaPeriodicCorrelationWitness

/-! Positive lag mass and fourth-order energy at the average prime-spacing
scale, measured for the genuine signed residual after fixed-period subtraction. -/
namespace Arxiv.«2501.03234».ThetaPrimeLagBounds
open Real Filter Finset ThetaPositiveLag ThetaSlidingCorrelation ThetaCharacterPrimeMeans
open ThetaPeriodicCorrelationWitness ThetaNaturalPrimeMeans ThetaPeriodMeans
noncomputable section

def cut (X : ℕ) (g : ℕ → ℝ) (n : ℕ) := if n∈Nat.primesLE X then g n else 0
def corr (X d : ℕ) (g : ℕ → ℝ) := ∑ p∈(Nat.primesLE X).filter (fun p => p+d∈Nat.primesLE X),
  g p*g (p+d)

theorem cut_lag (X d : ℕ) (g : ℕ → ℝ) : lag (X+1) d (cut X g)=corr X d g := by
  classical
  simp only [lag,cut,ite_mul,zero_mul,mul_ite,mul_zero,←sum_filter,corr]
  congr 1;ext p;simp only [mem_filter,mem_range]
  have h : p∈Nat.primesLE X → p<X+1 := fun hp => Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1
  tauto

private theorem finite {c x l B w D A n k : ℝ} (hc : 0<c) (hx : 0<x) (hl : 0<l) (_hn : 0≤n)
    (hk : 0≤k) (hD : 0≤D) (hA : 0≤A) (hw : c*x≤|w| * l)
    (hd : D*l≤B*x) (hsize : 6*B*l≤c^2*k) (hspan : n≤3*x)
    (h : k*w^2≤n*(D+2*A)) : c^2*x*k≤12*A*l^2 := by
  have hs := pow_le_pow_left₀ (mul_nonneg hc.le hx.le) hw 2
  rw [mul_pow,mul_pow,sq_abs] at hs
  have h₁ := mul_le_mul_of_nonneg_right hs hk
  have h₂ := mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_right hspan (by positivity))) (sq_nonneg l)
  have h₃ := mul_le_mul_of_nonneg_right hd (show 0≤3*x*l by positivity)
  have h₄ := mul_le_mul_of_nonneg_right hsize (sq_nonneg x)
  apply (mul_le_mul_iff_right₀ hx).mp
  nlinarith only [h₁,h₂,h₃,h₄]

def Scales (q : ℕ) (c : ℝ) (g : ℕ → ℝ) := ∃ K : ℝ,0<K ∧
  ∀ᶠ X : ℕ in atTop,∀ L : ℕ, K*log X≤L → q*L≤X →
    c*X*L≤(∑ k∈offsets L,max 0 (corr X (q*k) g))*(log X)^2

theorem of_witness {q : ℕ} {c B : ℝ} (hc : 0<c) (hB : 0<B) {g v : ℕ → ℝ}
    (hv : ∀ n,|v n|≤1) (hper : ∀ n j,v (n+q*j)=v n)
    (hh : ∀ᶠ X : ℕ in atTop,c*X≤|(∑ p∈Nat.primesLE X,v p*g p)| * log X)
    (hd : ∀ᶠ X : ℕ in atTop,(∑ p∈Nat.primesLE X,(g p)^2)*log X≤B*X) :
    Scales q (c^2/12) g := by
  refine ⟨6*B/c^2,by positivity,?_⟩
  filter_upwards [hh,hd,eventually_ge_atTop (2:ℕ)] with X hw hD hx
  intro L hL hqL
  have hX : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hl := log_pos (show (1:ℝ)<X by exact_mod_cast hx)
  have hL' : 0<L := by exact_mod_cast (show 0<(L:ℝ) from (show 0<6*B/c^2*log X by positivity).trans_le hL)
  let f := cut X g
  have hzero : ∀ n≥X+1,f n=0 := by
    intro n hn;simp [f,cut,show n∉Nat.primesLE X by intro h;have := (Nat.mem_primesLE.mp h).1;omega]
  have htop : (∑ n∈range (X+1),v n*f n)=∑ p∈Nat.primesLE X,v p*g p := by
    dsimp only [f,cut];rw [show (∑ n∈range (X+1),v n*(if n∈Nat.primesLE X then g n else 0))=
      ∑ n∈(range (X+1)).filter (fun n => n∈Nat.primesLE X),v n*g n by
        simp only [mul_ite,mul_zero,sum_filter]]
    congr 1;ext p;simp only [mem_filter,mem_range,and_iff_right_iff_imp];intro h;exact Nat.lt_succ_of_le (Nat.mem_primesLE.mp h).1
  have hdiag : lag (X+1) 0 f=∑ p∈Nat.primesLE X,(g p)^2 := by
    simp only [f,cut_lag,corr,add_zero,filter_mem_eq_inter,inter_self,sq]
  have h := positive hL' f v hzero hv hper
  rw [htop,hdiag] at h
  have hs : 6*B*log X≤c^2*L := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<c^2)] at hL;linarith only [hL]
  have hh' := finite hc hX hl (Nat.cast_nonneg (X+1+q*L)) (Nat.cast_nonneg L)
    (sum_nonneg (fun _ _ => sq_nonneg _)) (sum_nonneg (fun _ _ => le_max_left _ _)) hw hD hs
    (show ((X+1+q*L:ℕ):ℝ)≤3*X by exact_mod_cast (show X+1+q*L≤3*X by omega)) h
  simp only [f,cut_lag] at hh'
  linarith only [hh']

theorem scales {m : ℕ} [NeZero m] (hAP : ProgressionMangoldt) :
    ∃ q : ℕ,m<q ∧ q.Prime ∧ q%4=3 ∧ ∃ c : ℝ,0<c ∧ ∀ g : ℕ → ℝ,OnMod m g →
      Scales q c (fun p => residual p-g p) := by
  obtain ⟨q,hq,hpr,hq₃,v,hv,hper,c,hc,hh⟩ := witness hAP m
  refine ⟨q,hq,hpr,hq₃,c^2/12,by positivity,?_⟩
  intro g hg
  obtain ⟨B,hB,hd⟩ := second hAP hg
  exact of_witness hc hB hv hper (hh g hg) hd

#print axioms scales
end
end Arxiv.«2501.03234».ThetaPrimeLagBounds
