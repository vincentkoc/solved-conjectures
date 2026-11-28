import ThetaPrimeConcentration
import ThetaSievedWindows

/-! Uniform concentration for the canonical theta residual over the primes. -/
namespace Arxiv.«2501.03234».ThetaSievedConcentration

open Finset ThetaPrimeDensity ThetaReciprocalInversion ThetaDenominatorTails
open ThetaRowCorrelations ThetaReciprocalBlocks

private noncomputable def err (p : ℕ) : ℝ := |(S p:ℝ)/p-Real.log p/2|
private noncomputable def weight (T : ℕ) : ℝ := (T:ℝ)^(1/128:ℝ)
private lemma weight_pos {T : ℕ} (hT : 1≤T) : 0<weight T :=
  Real.rpow_pos_of_pos (by exact_mod_cast hT) _
private lemma weight_mono {T N : ℕ} (h : T≤N) : weight T≤weight N :=
  Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) (by norm_num)
private lemma weight_sq (T : ℕ) : weight T*weight T=(T:ℝ)^(1/64:ℝ) := by
  unfold weight; rw [←Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by norm_num) (by norm_num)]
  norm_num
private lemma log_le_weight (N : ℕ) : Real.log N≤128*weight N := by
  dsimp [weight]; linarith only [Real.log_natCast_le_rpow_div N (by norm_num : (0:ℝ)<1/128)]
private lemma weight_le_sieve {T : ℕ} (hT : 1≤T) : weight T≤denominatorWeight T^2 := by
  unfold weight denominatorWeight; rw [←Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT) (by norm_num)

private lemma high_split {T N Y p : ℕ} (hTN : T≤N) (hNY : N≤Y)
    (L : ℕ → ℕ) (hL : L 1=0) (hc : ∀ d∈Icc 1 Y,p.Coprime d) :
    windowExtension (above T L) Y p=windowExtension (above N L) Y p+
      (low N L (fun d => if T<d then commonWeight Y d else 0) p:ℂ) := by
  have hzero : above T L 1=0 := by simp [above,hL]
  have hs := window_split hNY (above T L) hzero hc
  have hfun : above N (above T L)=above N L := by
    funext d; by_cases hd : d≤N
    · simp [above,hd]
    · simp [above,hd,show ¬d≤T from fun h => hd (h.trans hTN)]
  have hlow : low N (above T L) (commonWeight Y) p=
      low N L (fun d => if T<d then commonWeight Y d else 0) p := by
    unfold low; apply sum_congr rfl; intro d _
    by_cases hd : d≤T
    · simp [above,hd,not_lt.mpr hd,row]
    · simp [above,hd,lt_of_not_ge hd]
  rw [hfun,hlow] at hs; linear_combination hs

private lemma band : ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0≤B ∧ ∀ {N T : ℕ}, 2≤N → 1≤T → T≤N →
    ∀ s : Finset ℕ, (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64 ∧ A*(1+Real.log T)^2≤err p) →
      (s.card:ℝ)*(Real.log N*weight T)≤B*(N:ℝ)^64 := by
  obtain ⟨C,hC,h⟩ := ThetaPrimeMeanSquare.scale_window_control
  obtain ⟨D,hD,hsmall⟩ := small_rows_bound
  obtain ⟨W,hW,hhigh⟩ := cut_variance
  obtain ⟨U,hU,hsieve⟩ := ThetaSievedWindows.tail_prime_band
  let Z := ∑' g : ℕ,((g:ℝ)^2)⁻¹
  have hZ : 0≤Z := tsum_nonneg (fun _ => by positivity)
  let c := 8/Real.pi^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨C+c*(D+1),by positivity,2*(128*W+U*Z^2),by positivity,?_⟩
  intro N T hN hT hTN s hs
  obtain ⟨L,hL,ctrl⟩ := h N hN
  let Y := 2*N^52
  have hNY : N≤Y := by dsimp [Y]; have := Nat.le_self_pow (by decide : 52≠0) N; omega
  let F := windowExtension (above N L) Y
  let M := low N L (fun d => if T<d then commonWeight Y d else 0)
  have hpoint (p) (hp : p∈s) : 1≤2*(‖F p‖^2+(M p)^2) := by
    obtain ⟨hpr,hlo,hhi,hbad⟩ := hs p hp
    have hy := cutoff_inside hN hlo
    have hcop (d : ℕ) (hd : d∈Icc 1 Y) : p.Coprime d := hpr.coprime_iff_not_dvd.mpr
      (fun hh => ((mem_Icc.mp hd).2.trans_lt hy).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 hh))
    have hsplit := high_split hTN hNY L hL hcop
    have hn : ‖windowExtension L Y p‖≤D*(1+Real.log T)^2+(‖F p‖+|M p|) := by
      have hh := norm_add_le (windowExtension L Y p-windowExtension (above T L) Y p)
        (windowExtension (above T L) Y p)
      rw [sub_add_cancel] at hh
      apply hh.trans (add_le_add (hsmall hT L hL hcop) ?_)
      rw [hsplit]; simpa [F,M,Complex.norm_real,Real.norm_eq_abs] using
        (norm_add_le (F p) ((M p:ℝ):ℂ))
    have hu := ctrl p hpr hlo hhi
    change err p≤C+c*‖windowExtension L Y p‖ at hu
    have hV : 1≤(1+Real.log T)^2 := one_le_pow₀ (by linarith [Real.log_nonneg (show 1≤(T:ℝ) by exact_mod_cast hT)])
    have hb : 1≤‖F p‖+|M p| := by
      by_contra! he
      nlinarith only [hu,hbad,mul_le_mul_of_nonneg_left hn hc.le,mul_lt_mul_of_pos_left he hc,
        mul_le_mul_of_nonneg_left hV hC.le,mul_le_mul_of_nonneg_left hV hc.le]
    nlinarith only [pow_le_pow_left₀ zero_le_one hb 2,sq_nonneg (‖F p‖-|M p|),sq_abs (M p)]
  have hsum := sum_le_sum hpoint
  simp only [sum_const,nsmul_eq_mul,mul_one,←mul_sum,sum_add_distrib] at hsum
  let x := (N:ℝ)^64
  have hx : 0≤x := by dsimp [x]; positivity
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hw := weight_pos hT
  have hn := weight_pos (show 1≤N by omega)
  have hh : (∑ p∈s,‖F p‖^2)*(Real.log N*weight T)≤128*W*x := by
    have hsub : s⊆range (N^64+1) := fun p hp => mem_range.mpr (Nat.lt_succ_of_le (hs p hp).2.2.1)
    have H : (∑ p∈s,‖F p‖^2)≤W*x/(weight N*weight N) := by
      rw [weight_sq]; exact (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
        (hhigh (show 1≤N by omega) (above N L) (fun d hd => if_pos hd) N (by omega))
    have hb := (le_div_iff₀ (mul_pos hn hn)).mp H
    have hc' := mul_le_mul (log_le_weight N) (weight_mono hTN) hw.le (by positivity)
    calc
      _ ≤ (∑ p∈s,‖F p‖^2)*(128*weight N*weight N) :=
        mul_le_mul_of_nonneg_left hc' (sum_nonneg (fun _ _ => sq_nonneg _))
      _ ≤ _ := by linarith only [hb]
  have hm : (∑ p∈s,(M p)^2)*(Real.log N*weight T)≤U*Z^2*x := by
    have H := hsieve N T hN hT L (commonWeight Y) Z hZ
      (fun d _ => by rw [abs_of_nonneg (commonWeight_bounds _ d).1]; exact (commonWeight_bounds _ d).2) s (by
        intro p hp; obtain ⟨hpr,hlo,hhi,_⟩ := hs p hp
        have := cutoff_inside hN hlo; exact ⟨hpr,hNY.trans_lt this,hhi⟩)
    change (∑ p∈s,(M p)^2)≤U*(Z/denominatorWeight T)^2*x/Real.log N at H
    have hd : 0<denominatorWeight T := Real.rpow_pos_of_pos (by exact_mod_cast hT) _
    rw [div_pow,←mul_div_assoc,div_mul_eq_mul_div] at H
    have H' := (le_div_iff₀ (sq_pos_of_pos hd)).mp ((le_div_iff₀ hl).mp H)
    have hnon : 0≤(∑ p∈s,(M p)^2)*Real.log N := mul_nonneg (sum_nonneg (fun _ _ => sq_nonneg _)) hl.le
    rw [←mul_assoc]; exact (mul_le_mul_of_nonneg_left (weight_le_sieve hT) hnon).trans H'
  nlinarith only [mul_le_mul_of_nonneg_right hsum (mul_nonneg hl.le hw.le),hh,hm]

private lemma entry {P : ℕ → Prop} {X p : ℕ} : p∈primeSet P X ↔ p≤X ∧ p.Prime ∧ P p := by
  classical simp only [primeSet,mem_filter,Nat.mem_primesLE,and_assoc]

private lemma scales : ∃ A : ℝ, 0<A ∧ ∃ C : ℝ, 0<C ∧ ∀ {N T : ℕ}, 2≤N → 1≤T →
    ((primeSet (fun p => A*(1+Real.log T)^2≤err p) (N^64)).card:ℝ)*(Real.log N*weight T)
      ≤ C*(N:ℝ)^64 := by
  classical
  obtain ⟨a,ha,b,hb,H⟩ := band
  obtain ⟨d,hd,e,he,G⟩ := ThetaPrimeConcentration.cutoff_count
  let A := max a d
  refine ⟨A,ha.trans_le (le_max_left ..),128*e+b,by positivity,?_⟩
  intro N T hN hT
  let E := primeSet (fun p => A*(1+Real.log T)^2≤err p)
  have hh {s : ℝ} (hs : s≤A) {p} (hp : A*(1+Real.log T)^2≤err p) :
      s*(1+Real.log T)^2≤err p := (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans hp
  have global (X) : ((E X).card:ℝ)*(weight T*weight T)≤e*X := by
    let D := primeSet (fun p => d*(1+Real.log T)^2≤err p) X
    have hs : E X⊆D := by
      intro p hp; obtain ⟨hpx,pr,he'⟩ := entry.mp hp
      exact entry.mpr ⟨hpx,pr,hh (le_max_right ..) he'⟩
    have g : (D.card:ℝ)≤e*X/(T:ℝ)^(1/64:ℝ) := G T hT X
    rw [←weight_sq] at g
    exact (le_div_iff₀ (mul_pos (weight_pos hT) (weight_pos hT))).mp
      ((show ((E X).card:ℝ)≤D.card by exact_mod_cast card_le_card hs).trans g)
  have wt := weight_pos hT
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  change ((E (N^64)).card:ℝ)*(Real.log N*weight T)≤_
  by_cases hTN : T≤N
  · let Q := (E (N^64)).filter (fun p => N^56≤p)
    have hc : E (N^64)⊆E (N^56)∪Q := by
      intro p hp
      by_cases h : N^56≤p
      · exact mem_union_right _ (mem_filter.mpr ⟨hp,h⟩)
      · obtain ⟨_,pr,hh⟩ := entry.mp hp
        exact mem_union_left _ (entry.mpr ⟨(lt_of_not_ge h).le,pr,hh⟩)
    have hcard : ((E (N^64)).card:ℝ)≤((E (N^56)).card:ℝ)+Q.card := by
      exact_mod_cast (card_le_card hc).trans (card_union_le ..)
    have hQ := H hN hT hTN Q (by
      intro p hp; obtain ⟨hp,lo⟩ := mem_filter.mp hp
      obtain ⟨hi,pr,herr⟩ := entry.mp hp
      exact ⟨pr,lo,hi,hh (le_max_left ..) herr⟩)
    have hw : 1≤weight T := Real.one_le_rpow (by exact_mod_cast hT) (by norm_num)
    have hlo := global (N^56)
    push_cast at hlo
    have h₁ : ((E (N^56)).card:ℝ)*weight T≤e*(N:ℝ)^56 := by
      have hs := le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg (E (N^56)).card) wt.le) hw
      rw [mul_assoc] at hs; exact hs.trans hlo
    have hlog : Real.log N≤128*(N:ℝ)^8 := by
      apply (log_le_weight N).trans (mul_le_mul_of_nonneg_left _ (by norm_num))
      unfold weight; rw [←Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (show 1≤N by omega)
      · norm_num
    have hsmall := mul_le_mul h₁ hlog hl.le (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hcard (mul_nonneg hl.le wt.le),hsmall,hQ]
  · have hlog : Real.log N≤128*weight T := (log_le_weight N).trans
      (mul_le_mul_of_nonneg_left (weight_mono (le_of_not_ge hTN)) (by norm_num))
    have hglobal := global (N^64)
    push_cast at hglobal
    have hmul := mul_le_mul_of_nonneg_left hlog (mul_nonneg (Nat.cast_nonneg (E (N^64)).card) wt.le)
    nlinarith only [hmul,hglobal,mul_nonneg hb (show 0≤(N:ℝ)^64 by positivity)]

open Filter
private lemma cutoff_prime : ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ {T : ℕ}, 1≤T → ∀ X : ℕ, 2≤X →
    ((primeSet (fun p => A*(1+Real.log T)^2≤err p) X).card:ℝ) ≤ B*Nat.primeCounting X/weight T := by
  classical
  obtain ⟨A,hA,C,hC,H⟩ := scales
  let E T := primeSet (fun p => A*(1+Real.log T)^2≤err p)
  have mono (T : ℕ) : Monotone (E T) := by
    intro u v huv p hp
    obtain ⟨hpu,pr,hh⟩ := entry.mp hp
    exact entry.mpr ⟨hpu.trans huv,pr,hh⟩
  let b := Real.log 2/2
  have hb : 0<b := by dsimp [b]; positivity
  let d := 64*C*2^64/b
  have hd : 0<d := by dsimp [d]; positivity
  have eventual : ∀ᶠ X : ℕ in atTop, ∀ {T : ℕ}, 1≤T →
      ((E T X).card:ℝ)*weight T≤d*Nat.primeCounting X := by
    filter_upwards [eventually_ge_atTop 2,prime_count_lower] with X hX hc
    intro T hT
    let r := Nat.nthRoot 64 X
    let N := r+1
    have hr : 1≤r := (Nat.le_nthRoot_iff (by decide : (64:ℕ)≠0)).mpr (by simpa using (show 1≤X by omega))
    have hN : 2≤N := by dsimp [N]; omega
    have hL : X<N^64 := Nat.lt_pow_nthRoot_add_one (by decide) X
    have hnr : N^64≤2^64*X := calc
      _ ≤ (2*r)^64 := Nat.pow_le_pow_left (by dsimp [N]; omega) _
      _ = _ := Nat.mul_pow ..
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (Or.inl (by decide)))
    have hsize : (N:ℝ)^64≤(2:ℝ)^64*X := by exact_mod_cast hnr
    have hx : (1:ℝ)<X := by exact_mod_cast hX
    have hl : 0<Real.log X := Real.log_pos hx
    have hlog := Real.log_le_log (by linarith : (0:ℝ)<X) (show (X:ℝ)≤(N:ℝ)^64 by exact_mod_cast hL.le)
    rw [Real.log_pow] at hlog
    have hcard : ((E T X).card:ℝ)≤(E T (N^64)).card := by exact_mod_cast card_le_card (mono T hL.le)
    have h₁ := mul_le_mul_of_nonneg_right hcard (mul_nonneg (Real.log_pos (by exact_mod_cast hN : (1:ℝ)<N)).le (weight_pos hT).le)
    have h₂ := mul_le_mul_of_nonneg_left hlog (mul_nonneg (Nat.cast_nonneg (E T X).card) (weight_pos hT).le)
    have h₃ := h₁.trans (H hN hT)
    change b*(X:ℝ)≤Nat.primeCounting X*Real.log X at hc
    have h₄ : ((E T X).card:ℝ)*weight T*Real.log X≤(64*C*2^64)*X := by
      norm_num only [Nat.cast_ofNat] at h₂
      nlinarith only [h₂,h₃,mul_le_mul_of_nonneg_left hsize hC.le]
    have hdb : d*b=64*C*2^64 := by dsimp [d]; field_simp
    apply (le_of_mul_le_mul_right (a:=Real.log X) _ hl)
    nlinarith only [h₄,mul_le_mul_of_nonneg_left hc hd.le,
      congrArg (fun z : ℝ => z*(X:ℝ)) hdb]
  obtain ⟨K,hK⟩ := eventually_atTop.mp eventual
  let M := max 2 K
  let B := d*(Nat.primeCounting M+1)
  refine ⟨A,hA,B,by dsimp [B]; positivity,?_⟩
  intro T hT X hX
  apply (le_div_iff₀ (weight_pos hT)).mpr
  have hdB : d≤B := by dsimp [B]; nlinarith only [mul_nonneg hd.le (Nat.cast_nonneg (Nat.primeCounting M))]
  by_cases hx : K≤X
  · exact (hK X hx hT).trans (mul_le_mul_of_nonneg_right hdB (Nat.cast_nonneg _))
  · have hXM : X≤M := (le_of_not_ge hx).trans (le_max_right ..)
    have hcard : ((E T X).card:ℝ)≤(E T M).card := by exact_mod_cast card_le_card (mono T hXM)
    have hπ : 1≤Nat.primeCounting X := by
      have hh := Nat.primeCounting_eq_zero_iff (n:=X)
      omega
    apply ((mul_le_mul_of_nonneg_right hcard (weight_pos hT).le).trans (hK M (le_max_right ..) hT)).trans
    have h₁ : d*(Nat.primeCounting M)≤B := by dsimp [B]; linarith
    exact h₁.trans (le_mul_of_one_le_right (hd.le.trans hdB) (by exact_mod_cast hπ))

private lemma exponential_parameter : ∃ A : ℝ, 0<A ∧ ∃ B : ℝ, 0<B ∧ ∀ y : ℝ, 0≤y → ∀ X : ℕ, 2≤X →
    ((primeSet (fun p => A*(2+y)^2≤err p) X).card:ℝ) ≤ B*Nat.primeCounting X*Real.exp (-y/128) := by
  classical
  obtain ⟨A,hA,B,hB,H⟩ := cutoff_prime
  refine ⟨A,hA,B,hB,?_⟩; intro y hy X hX
  let T := ⌈Real.exp y⌉₊
  have he := Real.exp_pos y
  have he₁ := Real.one_le_exp hy
  have hceil : Real.exp y≤(T:ℝ) := Nat.le_ceil _
  have hT : 1≤T := by exact_mod_cast he₁.trans hceil
  have ht : (T:ℝ)≤2*Real.exp y := by
    have hh := Nat.ceil_lt_add_one he.le
    change (T:ℝ)<_ at hh
    linarith
  have hl := Real.log_le_log (show 0<(T:ℝ) by exact_mod_cast hT) ht
  rw [Real.log_mul (by norm_num) he.ne', Real.log_exp] at hl
  have hsmall : 1+Real.log T≤2+y := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hp : A*(1+Real.log T)^2≤A*(2+y)^2 := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [Real.log_nonneg (show 1≤(T:ℝ) by exact_mod_cast hT)]) hsmall 2) hA.le
  have hsub : primeSet (fun p => A*(2+y)^2≤err p) X ⊆ primeSet (fun p => A*(1+Real.log T)^2≤err p) X := by
    intro p h; obtain ⟨hX,hpr,he'⟩ := entry.mp h; exact entry.mpr ⟨hX,hpr,hp.trans he'⟩
  have hw := Real.rpow_le_rpow he.le hceil (show (0:ℝ)≤1/128 by norm_num)
  rw [← Real.exp_mul] at hw
  apply (show ((primeSet (fun p => A*(2+y)^2≤err p) X).card:ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans ((H hT X hX).trans ?_)
  apply (div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hw).trans_eq
  rw [div_eq_mul_inv,← Real.exp_neg]; ring_nf

/-- Uniform upper tail for the absolute error in the original signed sum,
simultaneously in the prime endpoint and the deviation threshold. -/
theorem prime_normalized_tail : ∃ C a : ℝ, 0<C ∧ 0<a ∧ ∀ X : ℕ, 2≤X → ∀ t : ℝ, 0≤t →
    ((primeSet (fun p => t≤|(S p:ℝ)/p-Real.log p/2|) X).card:ℝ) ≤ C*Nat.primeCounting X*Real.exp (-a*Real.sqrt t) := by
  classical
  obtain ⟨A,hA,B,hB,H⟩ := exponential_parameter
  let c := 1/(128*Real.sqrt A)
  have hc : 0<c := by dsimp [c]; positivity
  let C := (B+2)*Real.exp (2/128)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,c,hC,hc,?_⟩; intro X hX t ht
  let u := Real.sqrt (t/A)
  have hu₀ : 0≤u := Real.sqrt_nonneg _
  have hu : A*u^2=t := by dsimp [u]; rw [Real.sq_sqrt (by positivity)]; field_simp
  have hcu : c*Real.sqrt t = u/128 := by dsimp [c,u]; rw [Real.sqrt_div ht]; ring
  have hf : Real.exp (2/128)*Real.exp (-c*Real.sqrt t)=Real.exp (-(u-2)/128) := by
    rw [← Real.exp_add,neg_mul,hcu]; congr 1; ring
  by_cases htwo : 2≤u
  · have h := H (u-2) (by linarith) X hX
    rw [show 2+(u-2)=u by ring,hu] at h
    change _ ≤ C*Nat.primeCounting X*_
    apply h.trans
    rw [← hf]
    dsimp [C]; nlinarith only [mul_nonneg (mul_nonneg (Real.exp_pos (2/128)).le (Nat.cast_nonneg (Nat.primeCounting X) : (0:ℝ)≤Nat.primeCounting X))
      (Real.exp_pos (-c*Real.sqrt t)).le]
  · have h1 : 1≤Real.exp (-(u-2)/128) := Real.one_le_exp (by linarith)
    have hcard : ((primeSet (fun p => t≤err p) X).card:ℝ)≤Nat.primeCounting X := by
      exact_mod_cast (Nat.primesLE_card_eq_primeCounting X ▸ card_le_card (filter_subset _ (Nat.primesLE X)))
    apply hcard.trans
    calc
      _ ≤ (B+2)*Nat.primeCounting X := le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
      _ ≤ (B+2)*Nat.primeCounting X*Real.exp (-(u-2)/128) := le_mul_of_one_le_right (by positivity) h1
      _ = _ := by rw [← hf]; dsimp [C]; ring

end Arxiv.«2501.03234».ThetaSievedConcentration
#print axioms Arxiv.«2501.03234».ThetaSievedConcentration.prime_normalized_tail
