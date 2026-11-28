import ThetaReciprocalInversion

/-! A finite additive large-sieve inequality for the reduced frequencies of the theta cutoff. -/

namespace Arxiv.«2501.03234».ThetaReciprocalLargeSieve

open Finset ThetaReciprocalInversion
open scoped ComplexConjugate

private lemma phase_exp (t : ℝ) (n : ℕ) :
    phase t n = Complex.exp (Complex.I * ((-2*Real.pi*t*n : ℝ) : ℂ)) := by
  unfold phase; push_cast; congr 1; ring

private lemma phase_norm (t : ℝ) (n : ℕ) : ‖phase t n‖=1 := by
  rw [phase_exp,Complex.norm_exp_I_mul_ofReal]

private lemma phase_pow (t : ℝ) (n : ℕ) : phase t n = (phase t 1)^n := by
  unfold phase; rw [← Complex.exp_nat_mul]; push_cast; congr 1; ring

private lemma phase_diff (t s : ℝ) (n : ℕ) : phase t n * conj (phase s n) = phase (t-s) n := by
  rw [phase_exp,phase_exp,phase_exp,← Complex.exp_conj,← Complex.exp_add,map_mul,
    Complex.conj_I,Complex.conj_ofReal]
  congr 1; push_cast; ring

private noncomputable def kernel (X : ℕ) (t : ℝ) := ∑ n ∈ range X, phase t n

private lemma phase_gap {t : ℝ} (h : |t|≤1/2) : 4*|t| ≤ ‖phase t 1 - 1‖ := by
  rw [phase_exp,Complex.norm_exp_I_mul_ofReal_sub_one]
  have hx : 0 ≤ Real.pi*|t| := by positivity
  have hxl : Real.pi*|t| ≤ Real.pi/2 := by nlinarith [mul_le_mul_of_nonneg_left h Real.pi_pos.le]
  have hsin := Real.mul_le_sin hx hxl
  have he : (2/Real.pi)*(Real.pi*|t|)=2*|t| := by field_simp
  rw [he] at hsin
  have hn : 0≤Real.sin (Real.pi*|t|) := (by positivity : 0≤2*|t|).trans hsin
  have h₁ : (-2*Real.pi*t*(1:ℕ) : ℝ)/2=-(Real.pi*t) := by push_cast; ring
  rw [h₁,Real.sin_neg,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have ht : |Real.sin (Real.pi*t)|=Real.sin (Real.pi*|t|) := by
    by_cases ht : 0≤t
    · rw [abs_of_nonneg ht] at hn ⊢; exact abs_of_nonneg hn
    · rw [abs_of_neg (lt_of_not_ge ht),mul_neg,Real.sin_neg] at hn ⊢
      exact abs_of_nonpos (by linarith)
  rw [ht]; linarith

private lemma kernel_off {t : ℝ} (ht : t≠0) (h : |t|≤1/2) (X : ℕ) :
    ‖kernel X t‖ ≤ 1/(2*|t|) := by
  have htp := abs_pos.mpr ht
  have he : kernel X t = ∑ n ∈ range X, (phase t 1)^n := by
    unfold kernel; apply sum_congr rfl; intro n _; exact phase_pow _ _
  have hg := congrArg norm (geom_sum_mul (phase t 1) X)
  rw [← he,norm_mul] at hg
  have hgap := phase_gap h
  have hu : ‖(phase t 1)^X-1‖ ≤ 2 := by
    have H := norm_sub_le ((phase t 1)^X) 1
    rw [norm_pow,phase_norm,one_pow,norm_one] at H; linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hgap (norm_nonneg (kernel X t))]

private lemma inverse_distance_row {T a : ℕ} (ha : a≤T) :
    ∑ b ∈ range (T+1), ((Nat.dist a b : ℕ) : ℝ)⁻¹ ≤ 2*(harmonic T : ℝ) := by
  let H (j : ℕ) : ℝ := ∑ k ∈ range j, ((k:ℝ)+1)⁻¹
  have hr (j : ℕ) : H j = harmonic j := by simp [H,harmonic]
  have mono {r t : ℕ} (h : r≤t) : H r ≤ H t := sum_le_sum_of_subset_of_nonneg (range_mono h)
    (by intros; positivity)
  have left : ∑ b ∈ range (a+1), ((Nat.dist a b : ℕ) : ℝ)⁻¹ = H a := by
    have he (b : ℕ) (hb : b∈range (a+1)) : Nat.dist a b = a+1-1-b := by
      have := mem_range.mp hb; rw [Nat.dist_eq_sub_of_le_right (by omega)]; omega
    rw [sum_congr rfl (fun b hb => congrArg (fun x : ℕ => (x:ℝ)⁻¹) (he b hb)),
      sum_range_reflect (fun n : ℕ => (n:ℝ)⁻¹),sum_range_succ']
    simp [H]
  have right : ∑ j ∈ range (T-a), ((Nat.dist a (a+1+j) : ℕ) : ℝ)⁻¹ = H (T-a) := by
    apply sum_congr rfl; intro j _
    rw [Nat.dist_eq_sub_of_le (by omega),show a+1+j-a=j+1 by omega,Nat.cast_add,Nat.cast_one]
  rw [show T+1=(a+1)+(T-a) by omega,sum_range_add,left,right,← hr]
  linarith [mono ha,mono (Nat.sub_le T a)]

private lemma matrix_bound {ι : Type*} (s : Finset ι) (a : ι → ℝ) (D : ι → ι → ℝ)
    (hsym : ∀ i j, D i j = D j i) (hD : ∀ i j, 0≤D i j) {R : ℝ}
    (hrow : ∀ i ∈ s, ∑ j ∈ s, D i j ≤ R) :
    ∑ i ∈ s, ∑ j ∈ s, a i*a j*D i j ≤ R*∑ i ∈ s, (a i)^2 := by
  have he : (∑ i ∈ s, ∑ j ∈ s, (a j)^2*D i j) = ∑ i ∈ s, ∑ j ∈ s, (a i)^2*D i j := by
    rw [sum_comm]; apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _; rw [hsym j i]
  have hh : 2*(∑ i ∈ s, ∑ j ∈ s, a i*a j*D i j) ≤
      ∑ i ∈ s, ∑ j ∈ s, ((a i)^2*D i j+(a j)^2*D i j) := by
    simp only [mul_sum]
    apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
    nlinarith [mul_nonneg (sq_nonneg (a i-a j)) (hD i j)]
  simp only [sum_add_distrib] at hh; rw [he] at hh
  have hbound : (∑ i ∈ s, ∑ j ∈ s, (a i)^2*D i j) ≤ (∑ i ∈ s, (a i)^2)*R := by
    rw [sum_mul]; apply sum_le_sum; intro i hi
    rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
  linarith [mul_comm R (∑ i ∈ s, (a i)^2)]

private lemma gram_expansion {ι : Type*} (s : Finset ι) (a : ι → ℂ) (t : ι → ℝ) (X : ℕ) :
    ((∑ n ∈ range X, ‖∑ i ∈ s, a i*phase (t i) n‖^2 : ℝ) : ℂ) =
    ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j))*kernel X (t i-t j) := by
  push_cast; simp_rw [← Complex.mul_conj',map_sum,map_mul,sum_mul,mul_sum]
  have he (i j : ι) (n : ℕ) : (a i * phase (t i) n)*(conj (a j)*conj (phase (t j) n)) =
      (a i*conj (a j))*phase (t i-t j) n := by rw [← phase_diff]; ring
  simp_rw [he]; rw [sum_comm]
  apply sum_congr rfl; intro i _
  rw [sum_comm]
  simp_rw [← mul_sum,kernel]

private lemma grid_sieve {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (t : ι → ℝ)
    (bin : ι → ℕ) (X T : ℕ) (hb : ∀ i ∈ s, bin i≤T) (hinj : (s : Set ι).InjOn bin)
    (hspan : ∀ i ∈ s, ∀ j ∈ s, |t i-t j| ≤ 1/2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, (Nat.dist (bin i) (bin j) : ℝ) ≤ 2*T*|t i-t j|) :
    ∑ n ∈ range X, ‖∑ i ∈ s, a i*phase (t i) n‖^2 ≤
    ((X:ℝ)+2*T*harmonic T)*∑ i ∈ s, ‖a i‖^2 := by
  let D (i j : ι) : ℝ := (if i=j then (X:ℝ) else 0) + T*((Nat.dist (bin i) (bin j): ℝ)⁻¹)
  have hsym i j : D i j=D j i := by dsimp [D]; rw [Nat.dist_comm]; by_cases h : i=j <;> simp [h,Ne.symm]
  have hD i j : 0≤D i j := by dsimp [D]; split_ifs <;> positivity
  have hkernel (i : ι) (hi : i∈s) (j : ι) (hj : j∈s) : ‖kernel X (t i-t j)‖ ≤ D i j := by
    by_cases he : i=j
    · subst j; simp [kernel,phase,D,Nat.dist_self]
    · have hd := Nat.dist_pos_of_ne (fun e => he (hinj hi hj e))
      have hd' : 0<(Nat.dist (bin i) (bin j):ℝ) := by exact_mod_cast hd
      have h := hsep i hi j hj
      have hne : t i-t j≠0 := by intro H; rw [H,abs_zero,mul_zero] at h; linarith
      apply (kernel_off hne (hspan i hi j hj) X).trans
      simp only [D,if_neg he,zero_add,← div_eq_mul_inv]
      rw [div_le_div_iff₀ (by positivity) hd']
      linarith
  have rows (i : ι) (hi : i∈s) : ∑ j ∈ s, D i j ≤ (X:ℝ)+2*T*harmonic T := by
    have he : (∑ j ∈ s, ((Nat.dist (bin i) (bin j) : ℕ):ℝ)⁻¹) =
        ∑ b ∈ s.image bin, ((Nat.dist (bin i) b:ℕ):ℝ)⁻¹ := (sum_image (f := fun b => ((Nat.dist (bin i) b:ℕ):ℝ)⁻¹) hinj).symm
    have hin : s.image bin ⊆ range (T+1) := by
      intro b h; obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      exact mem_range.mpr (by have := hb j hj; omega)
    have hsum := (sum_le_sum_of_subset_of_nonneg hin (fun b _ _ =>
      show 0≤((Nat.dist (bin i) b:ℕ):ℝ)⁻¹ by positivity)).trans (inverse_distance_row (hb i hi))
    simp only [D,sum_add_distrib,sum_ite_eq,hi,if_true,← mul_sum]
    rw [he]; nlinarith [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (α:=ℝ) T)]
  have hnorm := congrArg norm (gram_expansion s a t X)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hnorm
  rw [hnorm]
  apply (norm_sum_le ..).trans
  apply le_trans _ (matrix_bound s (fun i => ‖a i‖) D hsym hD rows)
  apply sum_le_sum; intro i hi; apply (norm_sum_le ..).trans
  apply sum_le_sum; intro j hj
  simp only [norm_mul,Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (hkernel i hi j hj) (by positivity)

private lemma separated_half {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (t : ι → ℝ) (X T : ℕ) (ht : ∀ i ∈ s, t i ∈ Set.Icc 0 1)
    (hspan : ∀ i ∈ s, ∀ j ∈ s, |t i-t j| ≤ 1/2)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i≠j → 1 ≤ T*|t i-t j|) :
    ∑ n ∈ range X, ‖∑ i ∈ s, a i*phase (t i) n‖^2 ≤
    ((X:ℝ)+2*T*harmonic T)*∑ i ∈ s, ‖a i‖^2 := by
  let b (i : ι) := ⌊(T:ℝ)*t i⌋₊
  have lo (i : ι) (hi : i∈s) : (b i:ℝ) ≤ T*t i := Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (ht i hi).1)
  have up (i : ι) : (T:ℝ)*t i < (b i:ℝ)+1 := Nat.lt_floor_add_one _
  have lb (i j : ι) : (T:ℝ)*(t i-t j) ≤ T*|t i-t j| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (Nat.cast_nonneg _)
  have rb (i j : ι) : -((T:ℝ)*(t i-t j)) ≤ T*|t i-t j| := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (Nat.cast_nonneg _)
  refine grid_sieve s a t b X T ?_ ?_ hspan ?_
  · intro i hi
    exact_mod_cast (lo i hi).trans (by nlinarith [mul_le_mul_of_nonneg_left (ht i hi).2 (Nat.cast_nonneg (α:=ℝ) T)]
      : (T:ℝ)*t i ≤ T)
  · intro i hi j hj H
    by_contra hne
    have hh := hgap i hi j hj hne
    have hbin : (b i:ℝ)=(b j:ℝ) := by exact_mod_cast H
    rcases le_total (t i) (t j) with hl|hl
    · rw [abs_of_nonpos (sub_nonpos.mpr hl)] at hh
      linarith [lo i hi,up j]
    · rw [abs_of_nonneg (sub_nonneg.mpr hl)] at hh
      linarith [lo j hj,up i]
  · intro i hi j hj
    by_cases h : i=j
    · subst j; simp [Nat.dist_self]
    · have H := hgap i hi j hj h
      rcases le_total (b i) (b j) with hl|hl
      · rw [Nat.dist_eq_sub_of_le hl,Nat.cast_sub hl]
        linarith [lo j hj,up i,rb i j]
      · rw [Nat.dist_eq_sub_of_le_right hl,Nat.cast_sub hl]
        linarith [lo i hi,up j,lb i j]

/-- Finite large sieve on [0,1] for frequencies separated on the line by at least 1/T.
Splitting into half intervals controls wraparound in the geometric sum. -/
theorem separated_sieve {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a : ι → ℂ) (t : ι → ℝ) (X T : ℕ) (ht : ∀ i ∈ s, t i ∈ Set.Icc 0 1)
    (hgap : ∀ i ∈ s, ∀ j ∈ s, i≠j → 1 ≤ T*|t i-t j|) :
    ∑ n ∈ range X, ‖∑ i ∈ s, a i*phase (t i) n‖^2 ≤
    2*((X:ℝ)+2*T*harmonic T)*∑ i ∈ s, ‖a i‖^2 := by
  let A := s.filter fun i => t i≤1/2
  let B := s.filter fun i => ¬t i≤1/2
  have ha : A⊆s := filter_subset _ _
  have hb : B⊆s := filter_subset _ _
  have H₁ := separated_half A a t X T (fun i hi => ht i (ha hi)) (by
    intro i hi j hj; rw [abs_le]; constructor <;> linarith [(ht i (ha hi)).1,(ht j (ha hj)).1,
      (mem_filter.mp hi).2,(mem_filter.mp hj).2]) (fun i hi j hj => hgap i (ha hi) j (ha hj))
  have H₂ := separated_half B a t X T (fun i hi => ht i (hb hi)) (by
    intro i hi j hj; rw [abs_le]; constructor <;> linarith [(ht i (hb hi)).2,(ht j (hb hj)).2,
      (mem_filter.mp hi).2,(mem_filter.mp hj).2]) (fun i hi j hj => hgap i (hb hi) j (hb hj))
  have split {M : Type} [AddCommMonoid M] (f : ι→M) :
      ∑ i ∈ A, f i + ∑ i ∈ B, f i = ∑ i ∈ s, f i := sum_filter_add_sum_filter_not ..
  have he (n : ℕ) : ‖∑ i ∈ s, a i*phase (t i) n‖^2 ≤
       2*(‖∑ i ∈ A, a i*phase (t i) n‖^2 + ‖∑ i ∈ B, a i*phase (t i) n‖^2) := by
    rw [← split (fun i => a i*phase (t i) n)]
    apply (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le ..) 2).trans
    nlinarith [sq_nonneg (‖∑ i ∈ A, a i*phase (t i) n‖-‖∑ i ∈ B, a i*phase (t i) n‖)]
  apply (sum_le_sum (fun n _ => he n)).trans
  rw [← mul_sum,sum_add_distrib,← split (fun i => ‖a i‖^2)]
  linarith [H₁,H₂]

open ThetaReciprocalBlocks

private lemma farey_gap {q r h k Q : ℕ} (hq : 0<q) (hr : 0<r) (hqQ : q≤Q) (hrQ : r≤Q)
    (hh : h.Coprime q) (hk : k.Coprime r) (hne : q≠r ∨ h≠k) :
    1 ≤ ((Q^2 : ℕ) : ℝ)*|(h:ℝ)/q-(k:ℝ)/r| := by
  have hd : h*r≠k*q := by
    intro H
    have hqr : q ∣ r := hh.symm.dvd_of_dvd_mul_left (by rw [H]; exact dvd_mul_left _ _)
    have hrq : r ∣ q := hk.symm.dvd_of_dvd_mul_left (by rw [← H]; exact dvd_mul_left _ _)
    have h := Nat.dvd_antisymm hqr hrq
    subst r
    exact hne.elim (fun h => h rfl) (fun h => h (Nat.eq_of_mul_eq_mul_right hq H))
  have hqr : 0<(q:ℝ) := by exact_mod_cast hq
  have hrr : 0<(r:ℝ) := by exact_mod_cast hr
  have he : ((q:ℝ)*r)*|(h:ℝ)/q-(k:ℝ)/r| = |(h:ℝ)*r-k*q| := by
    rw [← abs_of_nonneg (mul_nonneg hqr.le hrr.le),← abs_mul]
    congr 1; field_simp
  have habs : 1 ≤ |(h:ℝ)*r-k*q| := by
    rcases lt_or_gt_of_ne hd with H|H
    · have H' : (h:ℝ)*r+1≤k*q := by exact_mod_cast H
      exact (show (1:ℝ) ≤ -((h:ℝ)*r-k*q) by linarith).trans (neg_le_abs _)
    · have H' : (k:ℝ)*q+1≤h*r := by exact_mod_cast H
      exact (show (1:ℝ) ≤ (h:ℝ)*r-k*q by linarith).trans (le_abs_self _)
  rw [← he] at habs
  apply habs.trans (mul_le_mul_of_nonneg_right _ (abs_nonneg _))
  exact_mod_cast (show q*r ≤ Q^2 by simpa [sq] using Nat.mul_le_mul hqQ hrQ)

/-- Contribution to the rational extension from a band of reduced denominators. -/
noncomputable def windowBand (L : ℕ → ℕ) (Y : ℕ) (s : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ s, ∑ h ∈ (range q).filter (·.Coprime q), windowCoordinate L Y q h * phase ((h:ℝ)/q) n

/-- Squared mass of the primitive coordinates at a given denominator. -/
noncomputable def windowMass (L : ℕ → ℕ) (Y q : ℕ) : ℝ :=
  ∑ h ∈ (range q).filter (·.Coprime q), ‖windowCoordinate L Y q h‖^2

/-- The variance on every translated interval is bounded by the mass on this band and the square
of its largest denominator (with one harmonic factor from the elementary large sieve). -/
theorem window_sieve_translate (L : ℕ → ℕ) (Y M X Q : ℕ) (s : Finset ℕ) (hs : ∀ q ∈ s, q ∈ Icc 1 Q) :
    ∑ n ∈ range X, ‖windowBand L Y s (M+n)‖^2 ≤
      2*((X:ℝ)+2*(Q^2:ℕ)*harmonic (Q^2))*∑ q ∈ s, windowMass L Y q := by
  let S := s.sigma fun q => (range q).filter (·.Coprime q)
  let t (z : Σ _ : ℕ, ℕ) := (z.2:ℝ)/z.1
  let a (z : Σ _ : ℕ, ℕ) := windowCoordinate L Y z.1 z.2 * phase (t z) M
  have he (z : Σ _ : ℕ, ℕ) (hz : z∈S) : 0<z.1 ∧ z.1≤Q ∧ z.2<z.1 ∧ z.2.Coprime z.1 := by
    obtain ⟨hq,hh⟩ := mem_sigma.mp hz
    exact ⟨(mem_Icc.mp (hs _ hq)).1,(mem_Icc.mp (hs _ hq)).2,mem_range.mp (mem_filter.mp hh).1,(mem_filter.mp hh).2⟩
  have ht (z : Σ _ : ℕ, ℕ) (hz : z∈S) : t z ∈ Set.Icc 0 1 := by
    obtain ⟨hq,_,hk,_⟩ := he z hz
    constructor
    · dsimp [t]; positivity
    · apply (div_le_one (Nat.cast_pos.mpr hq)).mpr; exact_mod_cast hk.le
  have hgap (z : Σ _ : ℕ, ℕ) (hz : z∈S) (w : Σ _ : ℕ, ℕ) (hw : w∈S) (hne : z≠w) :
      1 ≤ (↑(Q^2 : ℕ):ℝ)*|t z-t w| := by
    obtain ⟨hq,hqQ,_,hh⟩ := he z hz
    obtain ⟨hr,hrQ,_,hk⟩ := he w hw
    apply farey_gap hq hr hqQ hrQ hh hk
    by_contra! H
    apply hne; cases z; cases w; simp_all
  have H := separated_sieve S a t X (Q^2) ht hgap
  have hshift (u : ℝ) (n : ℕ) : phase u (M+n) = phase u M*phase u n := by
    rw [phase_pow u (M+n),pow_add,← phase_pow,← phase_pow]
  simpa only [windowBand,windowMass,sum_sigma',S,a,t,norm_mul,phase_norm,mul_one,hshift,mul_assoc] using H

#print axioms window_sieve_translate

/-- The finite interval variance is bounded by the mass on this band and the square
of its largest denominator (with one harmonic factor from the elementary large sieve). -/
theorem window_sieve (L : ℕ → ℕ) (Y X Q : ℕ) (s : Finset ℕ) (hs : ∀ q ∈ s, q ∈ Icc 1 Q) :
    ∑ n ∈ range X, ‖windowBand L Y s n‖^2 ≤
      2*((X:ℝ)+2*(Q^2:ℕ)*harmonic (Q^2))*∑ q ∈ s, windowMass L Y q := by
  simpa using window_sieve_translate L Y 0 X Q s hs

/-- Contribution to the rational extension from a band of reduced denominators. -/
noncomputable def band (Y : ℕ) (s : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ q ∈ s, ∑ h ∈ (range q).filter (·.Coprime q), blockCoordinate Y q h * phase ((h:ℝ)/q) n

/-- The finite interval variance is bounded by the mass on this band and the square
of its largest denominator (with one harmonic factor from the elementary large sieve). -/
theorem band_sieve (Y X Q : ℕ) (s : Finset ℕ) (hs : ∀ q ∈ s, q ∈ Icc 1 Q) :
    ∑ n ∈ range X, ‖band Y s n‖^2 ≤
      2*((X:ℝ)+2*(Q^2:ℕ)*harmonic (Q^2))*∑ q ∈ s, primitiveEnergy Y q :=
  window_sieve (fun d => d-1) Y X Q s hs

end Arxiv.«2501.03234».ThetaReciprocalLargeSieve
#print axioms Arxiv.«2501.03234».ThetaReciprocalLargeSieve.separated_sieve
#print axioms Arxiv.«2501.03234».ThetaReciprocalLargeSieve.band_sieve
#print axioms Arxiv.«2501.03234».ThetaReciprocalLargeSieve.window_sieve
