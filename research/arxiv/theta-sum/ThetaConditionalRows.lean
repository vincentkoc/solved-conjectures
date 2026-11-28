import ThetaCharacterThree
import ThetaPrimeAsymptotic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Complete reduced-residue means of reciprocal rows in fixed progressions. -/
namespace Arxiv.«2501.03234».ThetaConditionalRows
open Finset ThetaPeriodMeans ThetaCharacterThree ThetaRowCorrelations

/-- Uniform mean over the reduced residues of a positive modulus. -/
noncomputable def unitMean (q : ℕ) [NeZero q] (f : ℕ → ℝ) : ℝ :=
  (∑ u : (ZMod q)ˣ,f (u:ZMod q).val)/q.totient

private lemma unitsMap_val {d P : ℕ} [NeZero d] [NeZero P] (h : d∣P) (u : (ZMod P)ˣ) :
    ((ZMod.unitsMap h u:(ZMod d)ˣ):ZMod d).val=(u:ZMod P).val%d := by
  rw [ZMod.unitsMap_val,← ZMod.natCast_zmod_val (u:ZMod P),ZMod.cast_natCast h,
    ZMod.val_natCast,ZMod.natCast_zmod_val]

/-- Enlarging a period preserves its normalized unit average. -/
theorem unitMean_lift {d P : ℕ} [NeZero d] [NeZero P] (h : d∣P) {f : ℕ → ℝ} (hf : OnMod d f) :
    unitMean P f=unitMean d f := by
  let π := ZMod.unitsMap h
  let F (u : (ZMod d)ˣ) := f (u:ZMod d).val
  have he (x : (ZMod P)ˣ) : F (π x)=f (x:ZMod P).val := by
    dsimp only [F,π]; rw [unitsMap_val,hf]
  have hl (v : (ZMod d)ˣ) : (∑ x : (ZMod P)ˣ,F (v*π x))=∑ x : (ZMod P)ˣ,F (π x) := by
    obtain ⟨a,ha⟩ := ZMod.unitsMap_surjective h v
    apply Fintype.sum_bijective (fun x : (ZMod P)ˣ => a*x) (Equiv.mulLeft a).bijective
    intro x; rw [map_mul,show π a=v from ha]
  have hr (x : (ZMod P)ˣ) : (∑ v : (ZMod d)ˣ,F (v*π x))=∑ v : (ZMod d)ˣ,F v :=
    Fintype.sum_bijective (fun v : (ZMod d)ˣ => v*π x) (Equiv.mulRight _).bijective _ _ (fun _ => rfl)
  have H : (d.totient:ℝ)*(∑ x : (ZMod P)ˣ,F (π x))=(P.totient:ℝ)*∑ v : (ZMod d)ˣ,F v := calc
    _ = ∑ v : (ZMod d)ˣ,∑ x : (ZMod P)ˣ,F (v*π x) := by simp [hl,ZMod.card_units_eq_totient]
    _ = _ := by rw [sum_comm]; simp [hr,ZMod.card_units_eq_totient]
  unfold unitMean
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos P)).ne')
    (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos d)).ne')).mpr
  simpa only [he,F,mul_comm] using H

private lemma unitMean_mean (d : ℕ) [NeZero d] (f : ℕ → ℝ) :
    unitMean d f = (d:ℝ)/d.totient*mean d (fun n => if n.Coprime d then f n else 0) := by
  rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,sum_filter]
  unfold mean
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne d),Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos d)).ne']

private lemma unit_onMod {d : ℕ} {f : ℕ → ℝ} (hf : OnMod d f) :
    OnMod d (fun n => if n.Coprime d then f n else 0) := by
  intro n
  have hc : (n%d).Coprime d ↔ n.Coprime d := by
    rw [← ZMod.isUnit_iff_coprime,← ZMod.isUnit_iff_coprime,ZMod.natCast_mod]
  simp only [hc,hf n]

/-- Independent reduced components factor across coprime moduli. -/
theorem unitMean_mul {d e : ℕ} [NeZero d] [NeZero e] (hc : d.Coprime e)
    {f g : ℕ → ℝ} (hf : OnMod d f) (hg : OnMod e g) :
    unitMean (d*e) (fun n => f n*g n)=unitMean d f*unitMean e g := by
  rw [unitMean_mean,unitMean_mean d,unitMean_mean e]
  have H (n : ℕ) : (if n.Coprime (d*e) then f n*g n else 0)=
      (if n.Coprime d then f n else 0)*(if n.Coprime e then g n else 0) := by
    simp only [Nat.coprime_mul_iff_right]; split_ifs <;> simp_all
  simp_rw [H]
  rw [mean_mul_coprime (NeZero.pos d) (NeZero.pos e) hc (unit_onMod hf) (unit_onMod hg),
    Nat.totient_mul hc,Nat.cast_mul,Nat.cast_mul]
  ring

private noncomputable def twist (n : ℕ) : ℝ := chi n

private lemma twist_onMod : OnMod 3 twist := by intro n; simp [twist,chi]

private lemma twist_zero : unitMean 3 twist=0 := by
  rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,sum_filter]
  norm_num [sum_range_succ,twist,chi,Nat.Coprime]

private lemma product_onMod {d e P : ℕ} (hd : d∣P) (he : e∣P)
    {f g : ℕ → ℝ} (hf : OnMod d f) (hg : OnMod e g) : OnMod P (fun n => f n*g n) := by
  intro n; exact congrArg₂ (·*·) (onMod_lift hd hf n) (onMod_lift he hg n)

private lemma three_divides_mean {P d : ℕ} [NeZero P] [NeZero d] (hd : d∣P) (h3 : 3∣d) (K : ℕ) :
    unitMean P (fun n => twist n*row d K n)=unitMean d (fun n => twist n*row d K n) :=
  unitMean_lift hd (product_onMod h3 (dvd_refl _) twist_onMod (row_onMod d K))

/-- In every common period, a row with denominator prime to three has exactly
zero character mean. Rows divisible by three have a nonnegative mean. -/
theorem twisted_row_mean {P d : ℕ} [NeZero P] [NeZero d] (hd : d∣P) (hP : 3∣P)
    (ho : Odd d) (K : ℕ) :
    0≤unitMean P (fun n => (chi n:ℝ)*row d K n) := by
  change 0≤unitMean P (fun n => twist n*row d K n)
  by_cases h3 : 3∣d
  · rw [three_divides_mean hd h3 K]
    exact div_nonneg (row_transform_nonneg ho h3 K) (by positivity)
  · have hc := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr h3
    rw [unitMean_lift (hc.mul_dvd_of_dvd_of_dvd hP hd) (product_onMod (Nat.dvd_mul_right 3 d)
      (Nat.dvd_mul_left d 3) twist_onMod (row_onMod d K)),unitMean_mul hc twist_onMod
      (row_onMod d K),twist_zero,zero_mul]

/-- A nonempty denominator-three window contributes at least four fifths to
the normalized character mean, also after lifting to a larger period. -/
theorem twisted_three_lower {P K : ℕ} [NeZero P] (hP : 3∣P) (hK : 0<K) :
    4/5≤unitMean P (fun n => (chi n:ℝ)*row 3 K n) := by
  change 4/5≤unitMean P (fun n => twist n*row 3 K n)
  rw [three_divides_mean hP (dvd_refl 3) K,unitMean,Nat.totient_prime (by decide : Nat.Prime 3)]
  change 4/5≤(∑ u : (ZMod 3)ˣ,(chi (u:ZMod 3).val:ℝ)*row 3 K (u:ZMod 3).val)/2
  linarith [row_three_lower hK]

/-- Even denominators contribute zero to every reciprocal row. -/
theorem even_row {d : ℕ} (hd : ¬Odd d) (K n : ℕ) : row d K n=0 := by
  have hn : d%2≠1 := fun h => hd (Nat.odd_iff.mpr h)
  have hw (w : ℕ) : wave n d w=0 := if_neg (fun H => hn H.2.1)
  simp [row,hw]

/-- The unit mean of a weighted finite model splits into its denominator rows. -/
theorem mean_low (P T : ℕ) [NeZero P] (K : ℕ → ℕ) (a h : ℕ → ℝ) :
    unitMean P (fun n => h n*low T K a n)=
      ∑ d∈Icc 2 T,(a d/d)*unitMean P (fun n => h n*row d (K d) n) := by
  unfold low unitMean
  simp_rw [mul_sum]
  rw [sum_comm,sum_div]
  apply sum_congr rfl; intro d _
  simp_rw [show ∀ x y z : ℝ,x*(y*z)=y*(x*z) by intros; ring,← mul_sum]
  ring

/-- The twist vanishes off the odd multiples of three. On those multiples
the character mean descends to the denominator's own unit group. -/
theorem twisted_low_exact {P T : ℕ} [NeZero P] (hP : 3 ∣ P)
    (hdP : ∀ d∈Icc 2 T, Odd d → d∣P) (K : ℕ → ℕ) (a : ℕ → ℝ) :
    unitMean P (fun n => (chi n:ℝ)*low T K a n) =
      ∑ d∈Icc 2 T, if h : Odd d ∧ 3 ∣ d then
        letI : NeZero d := ⟨h.1.pos.ne'⟩
        (a d/d)*unitMean d (fun n => (chi n:ℝ)*row d (K d) n)
      else 0 := by
  rw [mean_low]
  apply sum_congr rfl
  intro d hd
  by_cases ho : Odd d
  · let : NeZero d := ⟨ho.pos.ne'⟩
    have hdiv := hdP d hd ho
    by_cases h3 : 3 ∣ d
    · rw [dif_pos ⟨ho,h3⟩]
      exact congrArg ((a d/d)*·) (three_divides_mean hdiv h3 (K d))
    · rw [dif_neg (fun h => h3 h.2)]
      have hc := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr h3
      change (a d/d)*unitMean P (fun n => twist n*row d (K d) n)=0
      rw [unitMean_lift (hc.mul_dvd_of_dvd_of_dvd hP hdiv) (product_onMod (Nat.dvd_mul_right 3 d)
        (Nat.dvd_mul_left d 3) twist_onMod (row_onMod d (K d))),unitMean_mul hc twist_onMod
        (row_onMod d (K d)),twist_zero,zero_mul,mul_zero]
  · rw [dif_neg (fun h => ho h.1)]
    simp [even_row ho,unitMean]

/-- In a complete common period, the quadratic twist of every nonnegative
finite theta window retains the contribution of its denominator-three row. -/
theorem twisted_low_lower {P T : ℕ} [NeZero P] (hT : 3≤T)
    (hdP : ∀ d∈Icc 2 T, Odd d → d∣P) (K : ℕ → ℕ) (hK : 0<K 3)
    (a : ℕ → ℝ) (ha : ∀ d∈Icc 2 T, 0≤a d) :
    4/15*a 3 ≤ unitMean P (fun n => (chi n:ℝ)*low T K a n) := by
  have hm : 3∈Icc 2 T := mem_Icc.mpr ⟨by decide,hT⟩
  have h3 := hdP 3 hm (by decide)
  let b (d : ℕ) := (a d/d)*unitMean P (fun n => (chi n:ℝ)*row d (K d) n)
  have hb (d) (hd : d∈Icc 2 T) : 0≤b d := by
    dsimp only [b]
    by_cases ho : Odd d
    · let : NeZero d := ⟨ho.pos.ne'⟩
      exact mul_nonneg (div_nonneg (ha _ hd) (Nat.cast_nonneg _)) (twisted_row_mean (hdP _ hd ho) h3 ho _)
    · simp [even_row ho,unitMean]
  rw [mean_low]
  have H := mul_le_mul_of_nonneg_left (twisted_three_lower h3 hK) (div_nonneg (ha 3 hm) (by norm_num : (0:ℝ)≤3))
  apply le_trans (b:=b 3) _ (single_le_sum hb hm)
  dsimp only [b]; norm_num only [Nat.cast_ofNat]
  linarith

private lemma parity_form (j : ℕ) : parity j=if j%2=1 then 1 else -1 := by
  rcases Nat.even_or_odd j with he|ho
  · rw [parity,he.neg_one_pow,if_neg (by have := Nat.even_iff.mp he; omega)]
  · rw [parity,ho.neg_one_pow,if_pos (Nat.odd_iff.mp ho)]; norm_num

private lemma parity_sum {d : ℕ} [NeZero d] (hd : 1<d) (ho : Odd d) :
    (∑ u : (ZMod d)ˣ,parity (u:ZMod d).val)=0 := by
  let : Fact (1<d) := ⟨hd⟩
  have hn (u : (ZMod d)ˣ) : parity ((-u:(ZMod d)ˣ):ZMod d).val= -parity (u:ZMod d).val := by
    let : NeZero (u:ZMod d) := ⟨u.ne_zero⟩
    rw [Units.val_neg,ZMod.val_neg_of_ne_zero,parity_form,parity_form]
    have hlt := ZMod.val_lt (u:ZMod d)
    have he := Nat.odd_iff.mp ho
    split_ifs <;> norm_num <;> omega
  have H := Fintype.sum_equiv (Equiv.neg (ZMod d)ˣ)
    (fun u => parity ((-u:(ZMod d)ˣ):ZMod d).val) (fun u => parity (u:ZMod d).val) (by intros; rfl)
  simp only [hn,sum_neg_distrib] at H
  omega

private lemma wave_sum {d : ℕ} [NeZero d] (hd : 1<d) (w : ℕ) :
    (∑ u : (ZMod d)ˣ,wave (u:ZMod d).val d w)=0 := by
  by_cases h : d%2=1 ∧ w%2=1 ∧ w.Coprime d
  · let v := ZMod.unitOfCoprime w h.2.2
    rw [← parity_sum hd (Nat.odd_iff.mpr h.1)]
    apply Fintype.sum_bijective (fun u : (ZMod d)ˣ => v/u)
      ((show Function.Involutive (fun u : (ZMod d)ˣ => v/u) from fun u => div_div_cancel v u).bijective)
    exact wave_unit (Nat.odd_iff.mpr h.1) (Nat.odd_iff.mpr h.2.1) h.2.2
  · have hz (u : (ZMod d)ˣ) : wave (u:ZMod d).val d w=0 := if_neg (fun H => h H.2)
    simp [hz]

/-- Every single reciprocal row of denominator greater than one has zero
untwisted unit mean over any multiple of its period. -/
theorem row_mean_zero {P d : ℕ} [NeZero d] [NeZero P] (h : d∣P) (hd : 1<d) (K : ℕ) :
    unitMean P (row d K)=0 := by
  rw [unitMean_lift h (row_onMod d K),unitMean]
  unfold row; rw [sum_comm]
  simp_rw [← mul_sum,← Int.cast_sum,wave_sum hd,Int.cast_zero,mul_zero,sum_const_zero,zero_div]

/-- Every finite denominator model has mean zero over the units of a common period. -/
theorem low_mean_zero {P T : ℕ} [NeZero P] (hdP : ∀ d∈Icc 2 T, Odd d → d∣P)
    (K : ℕ → ℕ) (a : ℕ → ℝ) : unitMean P (low T K a)=0 := by
  have H := mean_low P T K a (fun _ => 1)
  simp only [one_mul] at H
  rw [H]; apply sum_eq_zero; intro d hd
  by_cases ho : Odd d
  · let : NeZero d := ⟨ho.pos.ne'⟩
    rw [row_mean_zero (hdP d hd ho) (mem_Icc.mp hd).1,mul_zero]
  · simp [even_row ho,unitMean]

/-- A common multiple of the odd denominators is a period of the finite model. -/
theorem low_onMod {P T : ℕ} (hdP : ∀ d∈Icc 2 T, Odd d → d∣P)
    (K : ℕ → ℕ) (a : ℕ → ℝ) : OnMod P (low T K a) := by
  intro n; unfold low; apply sum_congr rfl; intro d hd
  by_cases ho : Odd d
  · rw [onMod_lift (hdP _ hd ho) (row_onMod d _) n]
  · simp [even_row ho]

private lemma split_class {P : ℕ} [NeZero P] (h3 : 3∣P) (f : ℕ → ℝ) (hf : unitMean P f=0)
    (r : ℕ) (hr : r=1 ∨ r=2) :
    2*unitMean P (fun n => if n%3=r then f n else 0)=
      (if r=1 then 1 else -1)*unitMean P (fun n => (chi n:ℝ)*f n) := by
  let s : ℝ := if r=1 then 1 else -1
  have H (u : (ZMod P)ˣ) : 2*(if (u:ZMod P).val%3=r then f (u:ZMod P).val else 0)=
      f (u:ZMod P).val+s*((chi (u:ZMod P).val:ℝ)*f (u:ZMod P).val) := by
    have hcop := ((ZMod.val_coe_unit_coprime u).coprime_dvd_right h3).symm
    have hn := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mp hcop
    have hz : (u:ZMod P).val%3≠0 := fun H => hn (Nat.dvd_of_mod_eq_zero H)
    have ht := Nat.mod_lt (u:ZMod P).val (by decide : 0<3)
    have hu : (u:ZMod P).val%3=1 ∨ (u:ZMod P).val%3=2 := by omega
    rcases hr with rfl|rfl <;> rcases hu with h|h <;> norm_num [s,chi,h] <;> ring
  calc
    _ = unitMean P f+s*unitMean P (fun n => (chi n:ℝ)*f n) := by
      unfold unitMean
      rw [← mul_div_assoc,← mul_div_assoc,← add_div,mul_sum,mul_sum,← sum_add_distrib]
      exact congrArg (·/(P.totient:ℝ)) (sum_congr rfl (fun u _ => H u))
    _ = _ := by rw [hf,zero_add]

private def selectEight (n : ℕ) : ℝ := if n%8=1 then 1 else 0
private lemma eight_mean : unitMean 8 selectEight=1/4 := by
  rw [unitMean,ThetaReciprocalFibers.unit_sum_nat,sum_filter]
  have ht : Nat.totient 8=4 := by decide +kernel
  norm_num [sum_range_succ,selectEight,Nat.Coprime,ht]

private lemma class_crt {M : ℕ} [NeZero M] (hM : Odd M) (h3 : 3∣M) {f : ℕ → ℝ}
    (hf : OnMod M f) (r b : ℕ) (hr : (r=1 ∧ b=1) ∨ (r=2 ∧ b=17)) :
    unitMean (8*M) (fun n => if n%24=b then f n else 0) =
      (1/4)*unitMean M (fun n => if n%3=r then f n else 0) := by
  have hprod (n : ℕ) : (if n%24=b then f n else 0)=
      selectEight n*(if n%3=r then f n else 0) := by
    rcases hr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> unfold selectEight <;> split_ifs <;> first | rfl | omega | ring
  have hmod : OnMod M (fun n => if n%3=r then f n else 0) := by
    intro n; dsimp only; rw [Nat.mod_mod_of_dvd n h3,hf n]
  have hc : (8:ℕ).Coprime M := by
    change (2^3:ℕ).Coprime M
    exact (Nat.coprime_two_left.mpr hM).pow_left 3
  simp_rw [hprod]
  rw [unitMean_mul hc (show OnMod 8 selectEight by intro n; simp [selectEight]) hmod,eight_mean]

/-- The actual finite row sum has opposite signed means on 1 and 17 modulo
24, uniformly in its finite cutoffs. Both are classes of primes 1 modulo 8.
The means include a factor 1/8 for the proportion of reduced residues. -/
theorem low_class_bias {M T : ℕ} [NeZero M] (hM : Odd M) (hT : 3≤T)
    (hdM : ∀ d∈Icc 2 T, Odd d → d∣M) (K : ℕ → ℕ) (hK : 0<K 3)
    (a : ℕ → ℝ) (ha : ∀ d∈Icc 2 T, 0≤a d) :
    a 3/30 ≤ unitMean (8*M) (fun n => if n%24=1 then low T K a n else 0) ∧
    unitMean (8*M) (fun n => if n%24=17 then low T K a n else 0) ≤ -(a 3/30) := by
  have h3 := hdM 3 (mem_Icc.mpr ⟨by decide,hT⟩) (by decide)
  have hz := low_mean_zero hdM K a
  have h₁ := split_class h3 _ hz 1 (Or.inl rfl)
  have h₂ := split_class h3 _ hz 2 (Or.inr rfl)
  norm_num at h₁ h₂
  have hb := twisted_low_lower hT hdM K hK a ha
  rw [class_crt hM h3 (low_onMod hdM K a) 1 1 (Or.inl ⟨rfl,rfl⟩),
    class_crt hM h3 (low_onMod hdM K a) 2 17 (Or.inr ⟨rfl,rfl⟩)]
  constructor <;> linarith

private lemma unitMean_witness {q : ℕ} [NeZero q] {f : ℕ → ℝ} {c : ℝ} (h : c≤unitMean q f) :
    ∃ u : (ZMod q)ˣ,c≤f (u:ZMod q).val := by
  by_contra! H
  have hs := sum_lt_sum_of_nonempty (s:=univ) univ_nonempty
    (fun (u : (ZMod q)ˣ) _ => H u)
  have hc : (∑ u : (ZMod q)ˣ,f (u:ZMod q).val)<c*q.totient := by
    simpa [ZMod.card_units_eq_totient,mul_comm] using hs
  exact (not_lt_of_ge h) ((div_lt_iff₀ (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))).mpr hc)

private lemma prime_witness {q b : ℕ} [NeZero q] (h24 : 24∣q) {f : ℕ → ℝ}
    (hf : OnMod q f) {c : ℝ} (hc : 0<c)
    (h : c≤unitMean q (fun n => if n%24=b then f n else 0)) (B : ℕ) :
    ∃ p>B,p.Prime ∧ p%24=b ∧ c≤f p := by
  obtain ⟨u,hu⟩ := unitMean_witness h
  have hb : (u:ZMod q).val%24=b := by
    by_contra hn; simp [hn] at hu; linarith
  simp only [hb,ite_true] at hu
  obtain ⟨p,hp,hpr,he⟩ := Nat.forall_exists_prime_gt_and_eq_mod u.isUnit B
  have hv : p%q=(u:ZMod q).val := by simpa [ZMod.val_natCast] using congrArg ZMod.val he
  exact ⟨p,hp,hpr,by rw [← Nat.mod_mod_of_dvd p h24,hv,hb],by rwa [← hf p,hv]⟩

/-- For each fixed nonnegative window there are arbitrarily large primes
in both progressions exhibiting opposite signed values. The cutoffs are
chosen before the prime bound. -/
theorem low_prime_signs {T : ℕ} (hT : 3≤T) (K : ℕ → ℕ) (hK : 0<K 3)
    (a : ℕ → ℝ) (ha : ∀ d∈Icc 2 T, 0≤a d) (h₃ : 0<a 3) (B : ℕ) :
    (∃ p>B,p.Prime ∧ p%24=1 ∧ a 3/30≤low T K a p) ∧
    (∃ p>B,p.Prime ∧ p%24=17 ∧ low T K a p≤ -(a 3/30)) := by
  classical
  let s := (Icc 2 T).filter Odd
  let M := ∏ d∈s,d
  have odd_prod (t : Finset ℕ) (ht : ∀ d∈t, Odd d) : Odd (∏ d∈t,d) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert d t hd ih =>
      rw [prod_insert hd]
      exact (ht d (mem_insert_self ..)).mul (ih (fun i hi => ht i (mem_insert_of_mem hi)))
  have hM : Odd M := odd_prod s (fun d hd => (mem_filter.mp hd).2)
  let : NeZero M := ⟨hM.pos.ne'⟩
  have hdM (d) (hd : d∈Icc 2 T) (ho : Odd d) : d∣M := Finset.dvd_prod_of_mem id (mem_filter.mpr ⟨hd,ho⟩)
  have h3 := hdM 3 (mem_Icc.mpr ⟨by decide,hT⟩) (by decide)
  have h24 : 24∣8*M := Nat.mul_dvd_mul_left 8 h3
  have hper := onMod_lift (Nat.dvd_mul_left M 8) (low_onMod hdM K a)
  obtain ⟨hpos,hneg⟩ := low_class_bias hM hT hdM K hK a ha
  have he : unitMean (8*M) (fun n => if n%24=17 then -low T K a n else 0) =
       -unitMean (8*M) (fun n => if n%24=17 then low T K a n else 0) := by
    unfold unitMean
    have H (n : ℕ) : (if n%24=17 then -low T K a n else 0) = -(if n%24=17 then low T K a n else 0) := by
      split_ifs <;> simp
    simp_rw [H,sum_neg_distrib,neg_div]
  have hneg' : a 3/30≤unitMean (8*M) (fun n => if n%24=17 then -low T K a n else 0) := by rw [he]; linarith
  refine ⟨prime_witness h24 hper (by positivity) hpos B,?_⟩
  obtain ⟨p,hp,hpr,hr,hv⟩ := prime_witness h24 (fun n => congrArg Neg.neg (hper n)) (by positivity) hneg' B
  exact ⟨p,hp,hpr,hr,by linarith⟩

open ThetaReciprocalBlocks ThetaReciprocalInversion ThetaNondivisibleCone

/-- The entire finite rational cone agrees with the finite unit-row model
at each prime beyond the denominator cutoff. -/
theorem cone_eq_low {p J K : ℕ} (hp : p.Prime) (hJ : 2*J<p) (hK : K%2=1) :
    (rationalCone p J K:ℝ)=low (2*J) (coneWindow K) (commonWeight (2*J)) p := by
  have hc (d : ℕ) (hd : d∈Icc 1 (2*J)) : p.Coprime d := hp.coprime_iff_not_dvd.mpr
    (fun h => ((mem_Icc.mp hd).2.trans_lt hJ).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 h))
  have he := window_split (T:=2*J) le_rfl (coneWindow K) (by simp [coneWindow]) hc
  have hz : windowExtension (ThetaDenominatorTails.above (2*J) (coneWindow K)) (2*J) p=0 := by
    rw [window_primitive_rows _ hc]; apply sum_eq_zero; intro d hd
    simp [ThetaDenominatorTails.above,(mem_Icc.mp hd).2]
  rw [hz,sub_zero,ThetaPrimeAsymptotic.cone_interpolation hK hp hJ] at he
  exact_mod_cast he

/-- Once three occurs, its coefficient includes the unit common factor. -/
theorem commonWeight_three {Y : ℕ} (hY : 3≤Y) : 1≤commonWeight Y 3 := by
  have h1 : 1∈(Icc 1 (Y/3)).filter (·%2=1) := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,by omega⟩,rfl⟩
  have H := single_le_sum (f:=fun g : ℕ => ((g:ℝ)^2)⁻¹) (fun _ _ => by positivity) h1
  norm_num at H
  exact H

/-- Each fixed nondivisible rational cone has opposite signed excursions of
size at least 1/30 on arbitrarily large primes in the two classes 1 mod 8. -/
theorem rationalCone_prime_signs {J K : ℕ} (hJ : 2≤J) (hK : K%2=1) (B : ℕ) :
    (∃ p>B,p.Prime ∧ p%24=1 ∧ 1/30≤rationalCone p J K) ∧
    (∃ p>B,p.Prime ∧ p%24=17 ∧ rationalCone p J K≤ -(1/30)) := by
  have hT : 3≤2*J := by omega
  have hW := commonWeight_three hT
  have hw : 0<coneWindow K 3 := by simp [coneWindow]; omega
  have hs := low_prime_signs hT (coneWindow K) hw (commonWeight (2*J))
    (fun d _ => (commonWeight_bounds _ d).1) (by linarith) (max B (2*J))
  obtain ⟨⟨p,hp,hpr,hr,hl⟩,⟨q,hq,hqr,hs,hu⟩⟩ := hs
  rw [← cone_eq_low hpr (lt_of_le_of_lt (le_max_right _ _) hp) hK] at hl
  rw [← cone_eq_low hqr (lt_of_le_of_lt (le_max_right _ _) hq) hK] at hu
  refine ⟨⟨p,lt_of_le_of_lt (le_max_left _ _) hp,hpr,hr,?_⟩,
    ⟨q,lt_of_le_of_lt (le_max_left _ _) hq,hqr,hs,?_⟩⟩
  · apply (Rat.cast_le (K:=ℝ)).mp
    push_cast; linarith
  · apply (Rat.cast_le (K:=ℝ)).mp
    push_cast; linarith

#print axioms even_row
#print axioms mean_low

end Arxiv.«2501.03234».ThetaConditionalRows
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.commonWeight_three
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.low_onMod
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.cone_eq_low
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.rationalCone_prime_signs
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.low_prime_signs
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.low_class_bias
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.row_mean_zero
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.twisted_low_lower
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.twisted_row_mean
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.twisted_three_lower
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.unitMean_lift
#print axioms Arxiv.«2501.03234».ThetaConditionalRows.unitMean_mul

#print axioms Arxiv.«2501.03234».ThetaConditionalRows.low_mean_zero

#print axioms Arxiv.«2501.03234».ThetaConditionalRows.twisted_low_exact
