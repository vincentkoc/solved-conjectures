import ThetaSevenPrimeBias
import ThetaDyadicLaw

/-! First moments on joint quadratic sign classes at conductors three and seven. -/
namespace Arxiv.«2501.03234».ThetaJointCharacterBias
open Finset Filter ThetaCharacterSeven ThetaCharacterThree ThetaSevenPrimeBias ThetaRowCorrelations
open ThetaConditionalRows ThetaNaturalPrimeMeans ThetaCharacterPrimeMeans ThetaPrimeLaw ThetaCharacterCoefficient
open ThetaDiagonalConstant ThetaPrimeTailTransfer ThetaPeriodMeans ThetaDyadicLaw ThetaPrimeDensity
open scoped Topology
local instance (T : ℕ) : NeZero T.factorial := ⟨(Nat.factorial_pos T).ne'⟩

private def w3 (n : ℕ) : ℝ := chi n
private def cross (n : ℕ) : ℝ := w3 n*sevenWeight n

private theorem period3 : OnMod 3 w3 := by intro n; simp [w3,chi]

private theorem cross_period : OnMod 21 cross := fun n =>
  congrArg₂ (·*·) (onMod_lift (by decide : 3∣21) period3 n) (onMod_lift (by decide : 7∣21) weight_period n)

private theorem cross_mean : unitMean 21 cross=0 := by
  have H := unitMean_mul (by decide : Nat.Coprime 3 7) period3 weight_period
  unfold cross
  simpa only [show (3:ℕ)*7=21 by decide,weight_mean,mul_zero] using H

private theorem cross_bound (n : ℕ) : |cross n|≤1 := by
  rw [cross,abs_mul]
  have h : |w3 n|≤1 := by unfold w3 chi; split_ifs <;> norm_num
  exact (mul_le_of_le_one_right (abs_nonneg _) (weight_bound n)).trans h

private lemma cross_sub {P a : ℕ} (hP : 21∣P) (ha : a≤P) : cross (P-a)=cross a := by
  obtain ⟨b,hb⟩ := hP
  have h3 : (P-a)%3=(3-a%3)%3 := by omega
  have h7 : (P-a)%7=(7-a%7)%7 := by omega
  have a3 := Nat.mod_lt a (by decide : 0<3)
  have a7 := Nat.mod_lt a (by decide : 0<7)
  unfold cross sevenWeight w3 chi chi7
  rw [h3,h7]
  interval_cases a%3 <;> interval_cases a%7 <;> norm_num

private lemma cross_model_zero {T : ℕ} (hT : 21≤T) (V : ℕ) :
    unitMean T.factorial (fun n => cross n*model T V n)=0 := by
  let M := T.factorial
  let : NeZero M := ⟨(Nat.factorial_pos T).ne'⟩
  have h21 : 21∣M := Nat.dvd_factorial (by decide) hT
  have hc (u : (ZMod M)ˣ) : cross ((-u:(ZMod M)ˣ):ZMod M).val=cross (u:ZMod M).val := by
    have hM : 1<M := by
      have h := Nat.le_of_dvd (Nat.factorial_pos T) h21
      omega
    let : Fact (1<M) := ⟨hM⟩
    let : NeZero (u:ZMod M) := ⟨u.ne_zero⟩
    rw [Units.val_neg,ZMod.val_neg_of_ne_zero]
    exact cross_sub h21 (ZMod.val_lt (u:ZMod M)).le
  let f (u : (ZMod M)ˣ) := cross (u:ZMod M).val*model T V (u:ZMod M).val
  have he (u : (ZMod M)ˣ) : f (-u)= -(f u) := by
    dsimp only [f]
    rw [hc,ThetaRowReflection.model_neg_unit T V u,mul_neg]
  have H := Fintype.sum_equiv (Equiv.neg (ZMod M)ˣ) f (fun u => -f u)
    (fun u => by simp only [Equiv.neg_apply,he,neg_neg])
  rw [sum_neg_distrib] at H
  have hz : (∑ u, f u)=0 := by linarith
  change (∑ u,f u)/(M.totient:ℝ)=0
  rw [hz,zero_div]

private theorem cross_residual_zero (hAP : ProgressionMangoldt) :
    Tendsto (primeMean (fun p => cross p*residual p)) atTop (𝓝 0) := by
  have hw : Tendsto (primeMean cross) atTop (𝓝 0) := by simpa only [cross_mean] using periodic_prime_mean hAP cross_period
  suffices H : Tendsto (primeMean (fun p => cross p*scaledOff p)) atTop (𝓝 0) by
    simpa only [mul_zero] using bounded_residual_twist cross cross_bound hw H
  apply Metric.tendsto_nhds.mpr
  intro ε he
  obtain ⟨T,hT,H⟩ := ((eventually_ge_atTop 21).and (bounded_twist_approx_eventually cross cross_bound (half_pos he))).exists
  obtain ⟨V,hV⟩ := H.exists
  have hper : OnMod T.factorial (model T V) := ThetaConditionalRows.low_onMod
    (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1; omega) (mem_Icc.mp hd).2) _ _
  have hprod : OnMod T.factorial (fun n => cross n*model T V n) := fun n => congrArg₂ (·*·)
    (onMod_lift (Nat.dvd_factorial (by decide : 0<21) hT) cross_period n) (hper n)
  have hl := periodic_prime_mean hAP hprod
  rw [cross_model_zero hT] at hl
  filter_upwards [hV,Metric.tendsto_nhds.mp hl (ε/2) (half_pos he)] with X h₁ h₂
  have h := dist_triangle (primeMean (fun n => cross n*scaledOff n) X) (primeMean (fun n => cross n*model T V n) X) 0
  rw [← Real.dist_eq] at h₁
  linarith only [h,h₁,h₂]




private noncomputable def gate (s t : ℝ) (n : ℕ) : ℝ := if w3 n=s ∧ sevenWeight n=t then 1 else 0

private theorem gate_period (s t : ℝ) : OnMod 21 (gate s t) := by
  intro n
  simp only [gate,onMod_lift (by decide : 3∣21) period3 n,onMod_lift (by decide : 7∣21) weight_period n]

private lemma gate_identity {s t : ℝ} (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) {n : ℕ} (h3 : ¬3∣n) (h7 : ¬7∣n) :
    gate s t n=(1+s*w3 n)*(1+t*sevenWeight n)/4 := by
  have hW : w3 n=1 ∨ w3 n= -1 := by
    have h := Nat.mod_lt n (by decide : 0<3)
    have hn := Nat.dvd_iff_mod_eq_zero.not.mp h3
    unfold w3 chi
    interval_cases n%3 <;> norm_num at *
  have hV : sevenWeight n=1 ∨ sevenWeight n= -1 := by
    have hn := Nat.dvd_iff_mod_eq_zero.not.mp h7
    simp only [sevenWeight,chi7,if_neg hn]
    split_ifs <;> norm_num
  unfold gate
  rcases hs with rfl|rfl <;> rcases ht with rfl|rfl <;> rcases hW with H|H <;> rcases hV with G|G <;> norm_num [H,G]

private lemma mean_gate {s t : ℝ} (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1) : unitMean 21 (gate s t)=1/4 := by
  rcases hs with rfl|rfl <;> rcases ht with rfl|rfl <;>
    rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,sum_filter] <;>
    norm_num [show Nat.totient 21=12 by decide,sum_range_succ,gate,w3,chi,sevenWeight,chi7,Nat.Coprime]

private lemma gate_prime_mean {s t D : ℝ} (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1)
    (hAP : ProgressionMangoldt) (hD : Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D)) :
    Tendsto (primeMean (fun p => gate s t p*residual p)) atTop (𝓝 ((diagonalConstant+s*characterConstant+t*D)/4)) := by
  let f (p : ℕ) := (1+s*w3 p)*(1+t*sevenWeight p)/4*residual p
  have h3 : Tendsto (primeMean (fun p => w3 p*residual p)) atTop (𝓝 characterConstant) := prime_character_exact hAP
  have hB : Tendsto (primeMean residual) atTop (𝓝 diagonalConstant) := S_second_order_prime_mean hAP
  have H := (((hB.add (h3.const_mul s)).add (hD.const_mul t)).add
    ((cross_residual_zero hAP).const_mul (s*t))).div_const 4
  rw [mul_zero,add_zero] at H
  apply primeMean_of_close (g:=f) _ (H.congr' ?_)
  · intro ε he
    filter_upwards [eventually_gt_atTop 7] with p hp hprime
    have hn (q : ℕ) (hl : 1<q) (hu : q≤7) : ¬q∣p := by
      intro hh
      rcases (Nat.dvd_prime hprime).mp hh with hh|hh <;> omega
    rw [gate_identity hs ht (hn 3 (by decide) (by decide)) (hn 7 (by decide) (by decide))]
    simpa only [f,sub_self,abs_zero] using he
  · apply Eventually.of_forall
    intro X
    have he (n : ℕ) : f n=(residual n+s*(w3 n*residual n)+t*(sevenWeight n*residual n)+s*t*(cross n*residual n))/4 := by
      dsimp [f,cross]
      ring
    dsimp only []
    simp only [primeMean,he,← sum_div,sum_add_distrib,← mul_sum]
    ring


/-- A reduced dyadic class and the two prescribed real character signs. -/
def jointClass (q r : ℕ) (s t : ℝ) (p : ℕ) : Prop := p%q=r ∧ (chi p:ℝ)=s ∧ sevenWeight p=t

private lemma gate_sum (q r X : ℕ) (s t : ℝ) (f : ℕ → ℝ) :
    (∑ p∈primeSet (fun n => n%q=r) X,gate s t p*f p)=∑ p∈primeSet (jointClass q r s t) X,f p := by
  classical
  simp only [primeSet,sum_filter,gate,jointClass,w3]
  apply sum_congr rfl
  intro p _
  by_cases ha : (chi p:ℝ)=s <;> by_cases hb : sevenWeight p=t <;> by_cases hc : p%q=r <;> simp [ha,hb,hc]

private theorem joint_limits (hAP : ProgressionMangoldt) {k r : ℕ} (hr : r.Coprime (2^k)) (hlt : r<2^k)
    {s t D : ℝ} (hs : s=1 ∨ s= -1) (ht : t=1 ∨ t= -1)
    (hD : Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D)) :
    Tendsto (predicateMean (jointClass (2^k) r s t) residual) atTop (𝓝 (diagonalConstant+s*characterConstant+t*D)) ∧
      Tendsto (fun X => ((primeSet (jointClass (2^k) r s t) X).card:ℝ)/X.primeCounting) atTop
        (𝓝 ((1/4:ℝ)*(1/((2^k).totient:ℝ)))) := by
  let q := 2^k
  have hA := gate_prime_mean hs ht hAP hD
  have hnum := dyadic_restriction hAP hr hlt (by decide : Odd 21) (gate_period s t) LipschitzWith.id hA
  have hp := periodic_prime_mean hAP (gate_period s t)
  rw [mean_gate hs ht] at hp
  have hd := dyadic_restriction hAP hr hlt (by decide : Odd 21) (gate_period s t) (φ:=fun _ => (1:ℝ))
    (LipschitzWith.const 1) (by simpa only [mul_one] using hp)
  simp only [mul_one] at hd
  have hc (X : ℕ) : (∑ p∈primeSet (fun n => n%q=r) X,gate s t p)=((primeSet (jointClass q r s t) X).card:ℝ) := by
    simpa only [mul_one,sum_const,nsmul_eq_mul] using gate_sum q r X s t (fun _ => (1:ℝ))
  have hQ := class_nonempty hAP (show 0<q by dsimp [q]; positivity) hr hlt
  constructor
  · have H := hnum.div hd (by norm_num : (1/4:ℝ)≠0)
    have he (A : ℝ) : (A/4)/(1/4)=A := by ring
    rw [he] at H
    apply H.congr'
    filter_upwards [hQ] with X hx
    have hpos : ((primeSet (fun n => n%q=r) X).card:ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hx).ne'
    dsimp only [Pi.div_apply,progressionMean,predicateMean,id_eq]
    rw [gate_sum,hc]
    exact div_div_div_cancel_right₀ hpos _ _
  · have H := hd.mul (class_prime_density hAP (show 0<q by dsimp [q]; positivity) hr hlt)
    apply H.congr'
    filter_upwards [hQ] with X hx
    have hpos : ((primeSet (fun n => n%q=r) X).card:ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hx).ne'
    dsimp only [Pi.mul_apply,progressionMean]
    rw [hc]
    dsimp only [q] at *
    field_simp

/-- The same seven-bias D governs all four joint sign means, even after any
fixed reduced dyadic restriction. Each sign cell has one quarter of that class's primes. -/
theorem joint_prime_means (hAP : ProgressionMangoldt) :
    ∃ D : ℝ, 13/324 ≤ D ∧ Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D) ∧
      ∀ k r : ℕ, r.Coprime (2^k) → r<2^k → ∀ s t : ℝ, (s=1 ∨ s= -1) → (t=1 ∨ t= -1) →
        Tendsto (predicateMean (jointClass (2^k) r s t) residual) atTop (𝓝 (diagonalConstant+s*characterConstant+t*D)) ∧
        Tendsto (fun X => ((primeSet (jointClass (2^k) r s t) X).card:ℝ)/X.primeCounting) atTop
          (𝓝 ((1/4:ℝ)*(1/((2^k).totient:ℝ)))) := by
  obtain ⟨D,hD,H⟩ := seven_prime_bias hAP
  exact ⟨D,hD,H,fun _ _ hr hlt _ _ hs ht => joint_limits hAP hr hlt hs ht H⟩

#print axioms joint_prime_means

private lemma density_of_proportion {P : ℕ → Prop} {d : ℝ} (hd : 0<d)
    (h : Tendsto (fun X => ((primeSet P X).card:ℝ)/X.primeCounting) atTop (𝓝 d)) :
    PositiveLowerPrimeDensity P := by
  refine ⟨d/2,half_pos hd,?_⟩
  have hπ := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp Nat.tendsto_primeCounting
  filter_upwards [h.eventually_const_lt (half_lt_self hd),hπ.eventually_gt_atTop 0] with X hX hp
  exact ((lt_div_iff₀ hp).mp hX).le

/-- The original theta sum crosses both shifted half-log thresholds inside
specified joint sign classes and any fixed reduced dyadic progression. -/
theorem S_joint_excursions_of_bias (hAP : ProgressionMangoldt) {k r : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) {D u : ℝ}
    (hD : Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D)) (hu : u < characterConstant+D) :
    PositiveLowerPrimeDensity (fun p => jointClass (2^k) r 1 1 p ∧
      p*Real.log p/2+(diagonalConstant+u)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => jointClass (2^k) r (-1) (-1) p ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-u)*p) := by
  obtain ⟨hplus,dplus⟩ := joint_limits hAP hr hlt (s:=1) (t:=1) (Or.inl rfl) (Or.inl rfl) hD
  obtain ⟨hminus,dminus⟩ := joint_limits hAP hr hlt (s:= -1) (t:= -1) (Or.inr rfl) (Or.inr rfl) hD
  have hd : 0 < (1/4:ℝ)*(1/((2^k).totient:ℝ)) := by
    have h := Nat.totient_pos.mpr (show 0 < (2:ℕ)^k by positivity)
    positivity
  have hp := density_of_proportion hd dplus
  have hn := density_of_proportion hd dminus
  let a := diagonalConstant+characterConstant+D
  let b := diagonalConstant-characterConstant-D
  have hf : Tendsto (predicateMean (jointClass (2^k) r 1 1) (fun p => 1*residual p)) atTop (𝓝 a) := by
    have h' : Tendsto (predicateMean (jointClass (2^k) r 1 1) residual) atTop (𝓝 a) := by
      simpa only [a,one_mul] using hplus
    apply h'.congr'
    exact Eventually.of_forall fun X => by simp only [one_mul]
  have hg : Tendsto (predicateMean (jointClass (2^k) r (-1) (-1)) (fun p => -1*residual p)) atTop (𝓝 (-b)) := by
    have h' : Tendsto (predicateMean (jointClass (2^k) r (-1) (-1)) residual) atTop (𝓝 b) := by
      simpa only [b,neg_one_mul,sub_eq_add_neg] using hminus
    apply h'.neg.congr'
    exact Eventually.of_forall (fun X => by simp [predicateMean,← neg_div])
  have hhi := above_mean_density _ hp (s:=1) (by norm_num) (a:=diagonalConstant+u) (L:=a)
    (by dsimp [a]; linarith) hf
  have hlo := above_mean_density _ hn (s:= -1) (by norm_num) (a:= -(diagonalConstant-u)) (L:= -b)
    (by dsimp [b]; linarith) hg
  constructor
  · apply primeDensity_mono _ hhi
    rintro p hpr ⟨hcell,h⟩
    refine ⟨hcell,?_⟩
    simp only [one_mul,ThetaCharacterPrimeMeans.residual] at h
    have hp' : (0:ℝ)<p := by exact_mod_cast hpr.pos
    have hh := (lt_div_iff₀ hp').mp (lt_sub_iff_add_lt.mp h)
    linarith only [hh]
  · apply primeDensity_mono _ hlo
    rintro p hpr ⟨hcell,h⟩
    refine ⟨hcell,?_⟩
    simp only [neg_one_mul,neg_lt_neg_iff,ThetaCharacterPrimeMeans.residual] at h
    have hp' : (0:ℝ)<p := by exact_mod_cast hpr.pos
    have hh := (div_lt_iff₀ hp').mp (sub_lt_iff_lt_add.mp h)
    linarith only [hh]

#print axioms S_joint_excursions_of_bias

/-- A fully explicit improvement over the modulo-three excursion threshold. -/
theorem S_joint_excursions (hAP : ProgressionMangoldt) {k r : ℕ} (hr : r.Coprime (2^k))
    (hlt : r<2^k) {u : ℝ} (hu : u < characterConstant+13/324) :
    PositiveLowerPrimeDensity (fun p => jointClass (2^k) r 1 1 p ∧
      p*Real.log p/2+(diagonalConstant+u)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => jointClass (2^k) r (-1) (-1) p ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-u)*p) := by
  obtain ⟨D,hD,H⟩ := seven_prime_bias hAP
  exact S_joint_excursions_of_bias hAP hr hlt H (by linarith)

#print axioms S_joint_excursions

/-- Within 1 modulo 8 the opposite excursions localize further according to the
quadratic character modulo seven. The normalization still counts all primes. -/
theorem S_one_mod_eight_joint_excursions (hAP : ProgressionMangoldt) {u : ℝ}
    (hu : u < characterConstant+13/324) :
    PositiveLowerPrimeDensity (fun p => (p%24=1 ∧ (p%7=3 ∨ p%7=5 ∨ p%7=6)) ∧
      p*Real.log p/2+(diagonalConstant+u)*p < (S p:ℝ)) ∧
    PositiveLowerPrimeDensity (fun p => (p%24=17 ∧ (p%7=1 ∨ p%7=2 ∨ p%7=4)) ∧
      (S p:ℝ) < p*Real.log p/2+(diagonalConstant-u)*p) := by
  obtain ⟨hp,hn⟩ := S_joint_excursions (k:=3) (r:=1) hAP (by decide) (by decide) hu
  constructor
  · apply primeDensity_mono _ hp
    rintro p _ ⟨⟨h8,h3,h7⟩,h⟩
    change p%8=1 at h8
    have h3' : p%3=1 := by
      unfold chi at h3
      split_ifs at h3 <;> norm_num at h3
      assumption
    refine ⟨⟨by omega,?_⟩,h⟩
    have hlt := Nat.mod_lt p (by decide : 0<7)
    unfold sevenWeight chi7 at h7
    split_ifs at h7 <;> norm_num at *
    omega
  · apply primeDensity_mono _ hn
    rintro p _ ⟨⟨h8,h3,h7⟩,h⟩
    change p%8=1 at h8
    have h3' : p%3=2 := by
      unfold chi at h3
      split_ifs at h3 <;> norm_num at h3
      assumption
    refine ⟨⟨by omega,?_⟩,h⟩
    unfold sevenWeight chi7 at h7
    split_ifs at h7 <;> norm_num at *
    omega

#print axioms S_one_mod_eight_joint_excursions

private lemma mean_sum_limit {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto (primeMean f) atTop (𝓝 a)) (hg : Tendsto (primeMean g) atTop (𝓝 b)) :
    Tendsto (primeMean (fun p => f p+g p)) atTop (𝓝 (a+b)) :=
  (hf.add hg).congr' (Eventually.of_forall fun X => (mean_add _ _ X).symm)

private lemma mean_scale_limit {f : ℕ → ℝ} {a : ℝ} (b : ℝ)
    (hf : Tendsto (primeMean f) atTop (𝓝 a)) :
    Tendsto (primeMean (fun p => b*f p)) atTop (𝓝 (b*a)) :=
  (hf.const_mul b).congr' (Eventually.of_forall fun X => by rw [primeMean,primeMean,← mul_sum,mul_div_assoc])

/-- The two orthogonal prime-character correlations give a Bessel lower bound. -/
theorem variance_from_two_biases (hAP : ProgressionMangoldt) {D : ℝ}
    (H : Tendsto (primeMean (fun p => sevenWeight p*residual p)) atTop (𝓝 D)) :
    ∃ V : ℝ, characterConstant^2+D^2 ≤ V ∧ Tendsto (sampleVariance residual) atTop (𝓝 V) := by
  obtain ⟨_,V,_,_,_,_,hV,hvariance⟩ := S_prime_class_statistics hAP
  let B := diagonalConstant
  let C := characterConstant
  let z (p : ℕ) := residual p-B
  have hthird : Tendsto (primeMean w3) atTop (𝓝 0) := chi_prime_mean hAP
  have hseven : Tendsto (primeMean sevenWeight) atTop (𝓝 0) := by
    simpa only [weight_mean] using periodic_prime_mean hAP weight_period
  have hcross : Tendsto (primeMean cross) atTop (𝓝 0) := by
    simpa only [cross_mean] using periodic_prime_mean hAP cross_period
  have center {w : ℕ → ℝ} {b : ℝ} (hw : Tendsto (primeMean w) atTop (𝓝 0))
      (hb : Tendsto (primeMean (fun p => w p*residual p)) atTop (𝓝 b)) :
      Tendsto (primeMean (fun p => w p*z p)) atTop (𝓝 b) := by
    have L := mean_sum_limit hb (mean_scale_limit (-B) hw)
    rw [mul_zero,add_zero] at L
    apply L.congr'
    apply Eventually.of_forall
    intro X
    unfold primeMean
    congr 1
    apply sum_congr rfl
    intro p _
    dsimp [z]
    ring
  have h1 := center hthird (show Tendsto (primeMean (fun p => w3 p*residual p)) atTop (𝓝 C) from prime_character_exact hAP)
  have h2 := center hseven H
  have hconst : Tendsto (primeMean (fun _ => (1:ℝ))) atTop (𝓝 1) :=
    prime_mean_of_convergence (by intro ε he; simp [he])
  have hsum := mean_sum_limit (mean_sum_limit (mean_sum_limit (mean_scale_limit (2*C) h1) (mean_scale_limit (2*D) h2))
    (mean_scale_limit (-(C^2+D^2)) hconst)) (mean_scale_limit (-(2*C*D)) hcross)
  have hval : 2*C*C+2*D*D+ (-(C^2+D^2))*1+ (-(2*C*D))*0=C^2+D^2 := by ring
  rw [hval] at hsum
  have Hvar : C^2 + D^2 ≤ V := by
    apply le_of_tendsto_of_tendsto' hsum hV
    intro X
    apply mean_mono
    intro p
    change 2*C*(w3 p*z p)+2*D*(sevenWeight p*z p)+ (-(C^2+D^2))*1+
      (-(2*C*D))*(w3 p*sevenWeight p) ≤ z p^2
    have h3sq : (w3 p)^2 ≤ 1 := by unfold w3 chi; split_ifs <;> norm_num
    have h7sq : (sevenWeight p)^2 ≤ 1 := by unfold sevenWeight chi7; split_ifs <;> norm_num
    nlinarith only [sq_nonneg (z p-C*w3 p-D*sevenWeight p),
      mul_le_mul_of_nonneg_left h3sq (sq_nonneg C),mul_le_mul_of_nonneg_left h7sq (sq_nonneg D)]
  exact ⟨V,Hvar,hvariance⟩

#print axioms variance_from_two_biases

/-- Orthogonality of the two characters improves the all-prime limiting
variance by at least (13/324)² beyond the square of the exact modulo-three bias. -/
theorem variance_two_characters (hAP : ProgressionMangoldt) :
    ∃ V : ℝ, characterConstant^2+(13/324:ℝ)^2 ≤ V ∧ Tendsto (sampleVariance residual) atTop (𝓝 V) := by
  obtain ⟨D,hD,H⟩ := seven_prime_bias hAP
  obtain ⟨V,hV,hvariance⟩ := variance_from_two_biases hAP H
  refine ⟨V,?_,hvariance⟩
  nlinarith only [hV,hD,mul_self_le_mul_self (by norm_num : (0:ℝ)≤13/324) hD]

#print axioms variance_two_characters

end Arxiv.«2501.03234».ThetaJointCharacterBias
