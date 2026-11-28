import ThetaReciprocalVariance
/-! Cancellation of projected reciprocal numerators over complete periods. -/

namespace Arxiv.«2501.03234».ThetaUniformWindows
open Finset ThetaReciprocalBlocks ThetaReciprocalFibers ThetaReciprocalLargeSieve

private lemma coeff_neg {q m : ℕ} [NeZero q] [NeZero (q*m)] (hd : 1<q*m)
    (ho : (q*m)%2=1) (v : (ZMod (q*m))ˣ) (h : ZMod q) :
    reciprocalCoeff q m (-v) h = -reciprocalCoeff q m v h := by
  let : Nontrivial (ZMod (q*m)) := ZMod.nontrivial_iff.mpr (by omega)
  have hs (x : (ZMod (q*m))ˣ) :
      (-1:ℂ)^((↑((-v)/x):ZMod (q*m)).val) = -((-1:ℂ)^((↑(v/x):ZMod (q*m)).val)) := by
    let y : ZMod (q*m) := ↑(v/x)
    let : NeZero y := ⟨(v/x).ne_zero⟩
    have he : (↑((-v)/x):ZMod (q*m)) = -y := by simp [y, div_eq_mul_inv]
    rw [he,ZMod.val_neg_of_ne_zero y]
    change (-1:ℂ)^(q*m-y.val) = -((-1:ℂ)^y.val)
    simp only [neg_one_pow_eq_ite,Nat.even_iff]
    have := ZMod.val_lt y
    split_ifs <;> norm_num <;> omega
  unfold reciprocalCoeff
  rw [show ((-1:ℤ):ℂ) = -1 by norm_num]
  simp_rw [hs,neg_mul,sum_neg_distrib]
  ring

private lemma vector_reflect {q m : ℕ} [NeZero q] (hd : 1<q*m) {j : ℕ} (hj : j≤2*(q*m)) :
    numeratorVector q m (2*(q*m)-j) = -numeratorVector q m j := by
  have hdpos : 0<q*m := by omega
  let : NeZero (q*m) := ⟨hdpos.ne'⟩
  have hz : ((2*(q*m)-j:ℕ):ZMod (q*m)) = -(j:ZMod (q*m)) := by
    rw [Nat.cast_sub hj,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_sub]
  have hc : (2*(q*m)-j).Coprime (q*m) ↔ j.Coprime (q*m) := by
    rw [← ZMod.isUnit_iff_coprime,← ZMod.isUnit_iff_coprime,hz,IsUnit.neg_iff]
  have hpar : (2*(q*m)-j)%2=j%2 := by omega
  unfold numeratorVector
  split_ifs with H G G
  · have hu : ZMod.unitOfCoprime _ H.2.2.2 = -ZMod.unitOfCoprime _ G.2.2.2 := by
      apply Units.ext; exact hz
    rw [hu,← WithLp.toLp_neg]
    apply congrArg (WithLp.toLp 2); funext h
    exact coeff_neg hd (by rw [Nat.mul_mod,G.1,G.2.1]) _ _
  · exact (G ⟨H.1,H.2.1,hpar ▸ H.2.2.1,hc.mp H.2.2.2⟩).elim
  · exact (H ⟨G.1,G.2.1,hpar.symm ▸ G.2.2.1,hc.mpr G.2.2.2⟩).elim
  · exact neg_zero.symm

private lemma vector_period (q m j : ℕ) [NeZero q] :
    numeratorVector q m (2*(q*m)+j) = numeratorVector q m j := by
  have hz : ((2*(q*m)+j:ℕ):ZMod (q*m)) = (j:ZMod (q*m)) := by
    rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add]
  have hc : (2*(q*m)+j).Coprime (q*m) ↔ j.Coprime (q*m) := by
    rw [← ZMod.isUnit_iff_coprime,← ZMod.isUnit_iff_coprime,hz]
  have hpar : (2*(q*m)+j)%2=j%2 := by omega
  unfold numeratorVector
  split_ifs with H G G
  · have hu : ZMod.unitOfCoprime _ H.2.2.2 = ZMod.unitOfCoprime _ G.2.2.2 := by
      apply Units.ext; exact hz
    rw [hu]
  · exact (G ⟨H.1,H.2.1,hpar ▸ H.2.2.1,hc.mp H.2.2.2⟩).elim
  · exact (H ⟨G.1,G.2.1,hpar.symm ▸ G.2.2.1,hc.mpr G.2.2.2⟩).elim
  · rfl

/-- Abel bound for a decreasing nonnegative real weight and bounded vector partial sums. -/
theorem weighted_prefix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℕ → E) (w : ℕ → ℝ) (C : ℝ) (hw : ∀ i, 0≤w i) (hm : Antitone w)
    (hs : ∀ n, ‖∑ i ∈ range n, v i‖ ≤ C) (n : ℕ) :
    ‖∑ i ∈ range n, w i • v i‖ ≤ w 0*C := by
  have hC : 0≤C := by simpa using hs 0
  cases n with
  | zero => simpa using mul_nonneg (hw 0) hC
  | succ n =>
    rw [sum_range_by_parts]
    simp only [Nat.succ_sub_one]
    apply (norm_sub_le ..).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hw n)]
    apply (add_le_add (mul_le_mul_of_nonneg_left (hs _) (hw n)) (norm_sum_le ..)).trans
    have hb (i : ℕ) : ‖(w (i+1)-w i) • (∑ j ∈ range (i+1), v j)‖ ≤ (w i-w (i+1))*C := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr (hm (Nat.le_succ i))),neg_sub]
      exact mul_le_mul_of_nonneg_left (hs _) (sub_nonneg.mpr (hm (Nat.le_succ i)))
    apply (add_le_add (le_refl _) (sum_le_sum fun i _ => hb i)).trans
    rw [← sum_mul,sum_range_sub']
    exact le_of_eq (by ring)

private lemma reflect_period {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (v : ℕ → E) (hz : v 0=0) (href : ∀ j≤2*d, v (2*d-j) = -v j) :
    ∑ i ∈ range (2*d), v (i+1)=0 := by
  let D := 2*d
  have h := sum_range_reflect v (D+1)
  simp only [Nat.add_sub_cancel] at h
  have he : ∑ i ∈ range (D+1), v (D-i) = ∑ i ∈ range (D+1), -v i := by
    apply sum_congr rfl; intro i hi
    exact href i (by have := mem_range.mp hi; omega)
  rw [he,sum_neg_distrib] at h
  have hzero : ∑ i ∈ range (D+1), v i = 0 := by
    have htwo : (2:ℝ) • (∑ i ∈ range (D+1), v i) = 0 := by rw [two_smul,← neg_eq_iff_add_eq_zero,h]
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rwa [sum_range_succ',hz,add_zero] at hzero

private lemma period_prefix {E : Type*} [NormedAddCommGroup E] {d : ℕ} (hd : 0<d)
    (v : ℕ → E) {M : ℝ} (hv : ∀ j, ‖v j‖≤M) (hp : ∀ j, v (2*d+j)=v j)
    (hz : ∑ i ∈ range (2*d), v (i+1)=0) (n : ℕ) :
    ‖∑ i ∈ range n, v (i+1)‖ ≤ (2*d:ℕ)*M := by
  let D := 2*d
  have hM := (norm_nonneg _).trans (hv 0)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hl : D≤n
    · have hi := ih (n-D) (by dsimp [D]; omega)
      have he := sum_range_add (fun i => v (i+1)) D (n-D)
      rw [Nat.add_sub_of_le hl,hz,zero_add] at he
      simp only [D,Nat.add_assoc,hp] at he
      rwa [he]
    · apply (norm_sum_le ..).trans
      apply (sum_le_sum (s:=range n) (fun i _ => hv (i+1))).trans
      simp only [sum_const,card_range,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show n≤D by omega)) hM

/-- Reciprocal sum with an odd reflected wave, uniformly in the length. -/
theorem reciprocal_window {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (hd : 0<d) (v : ℕ → E) {M : ℝ} (hv : ∀ j, ‖v j‖≤M) (hz : v 0=0)
    (hp : ∀ j, v (2*d+j)=v j) (href : ∀ j≤2*d, v (2*d-j) = -v j) (n : ℕ) :
    ‖∑ i ∈ range n, ((i:ℝ)+1)⁻¹ • v (i+1)‖ ≤ 3*((harmonic d:ℝ)*M) := by
  let D := 2*d
  let row (n : ℕ) := ∑ i ∈ range n, ((i:ℝ)+1)⁻¹ • v (i+1)
  have hM := (norm_nonneg _).trans (hv 0)
  have hH : (1:ℝ)≤harmonic d := by
    calc (1:ℝ) = harmonic 1 := by norm_num [harmonic]
         _ ≤ _ := harmonic_mono_real hd
  have hD (i : ℕ) (hi : i≤D) : ‖row i‖ ≤ 2*(harmonic d:ℝ)*M := by
    have ha : ‖row i‖≤(harmonic i:ℝ)*M := by
      apply (norm_sum_le ..).trans
      have hr : (harmonic i:ℝ) = ∑ k ∈ range i, ((k:ℝ)+1)⁻¹ := by simp [harmonic]
      rw [hr,sum_mul]
      apply sum_le_sum; intro j _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hv _) (by positivity)
    apply ha.trans
    exact mul_le_mul_of_nonneg_right ((harmonic_mono_real hi).trans (by exact_mod_cast harmonic_product 2 d)) hM
  change ‖row n‖≤_
  by_cases hn : n≤D
  · nlinarith only [hD n hn,mul_nonneg (by linarith : 0≤(harmonic d:ℝ)) hM]
  let w (i : ℕ) : ℝ := ((D:ℝ)+i+1)⁻¹
  have hw (i : ℕ) : 0≤w i := by dsimp [w]; positivity
  have hm : Antitone w := by
    intro a b hab; dsimp [w]; apply inv_anti₀ (by positivity); exact_mod_cast (show D+a+1≤D+b+1 by omega)
  have ht := weighted_prefix (fun i => v (i+1)) w ((D:ℝ)*M) hw hm
    (period_prefix hd v hv hp (reflect_period v hz href)) (n-D)
  have he : row n = row D + ∑ i ∈ range (n-D), w i • v (i+1) := by
    dsimp only [row]; nth_rw 1 [show n=D+(n-D) by omega]; rw [sum_range_add]
    congr 1; apply sum_congr rfl; intro i _
    rw [Nat.add_assoc,hp]; simp [w]
  have hscale : w 0*((D:ℝ)*M) ≤ M := by
    have hpos : (0:ℝ)<D+1 := by positivity
    dsimp [w]; rw [Nat.cast_zero,add_zero,← div_eq_inv_mul,div_le_iff₀ hpos]
    nlinarith only [hM]
  rw [he]
  apply (norm_add_le ..).trans
  nlinarith only [hD D (le_refl _),ht.trans hscale,mul_le_mul_of_nonneg_right hH hM]

/-- Summation by parts bounds the weighted tail after the first period,
uniformly in the end of the numerator window. -/
theorem numeratorWindow_uniform {q m : ℕ} [NeZero q] (hd : 1<q*m) (n : ℕ) :
    ‖numeratorWindow q m n‖ ≤ 3*((harmonic (q*m):ℝ)*(m.divisors.card/(m:ℝ))) :=
  reciprocal_window (d:=q*m) (by omega) (fun j => numeratorVector q m j) (fun j => numeratorVector_bound q m j)
    (by simp [numeratorVector]) (fun j => vector_period q m j) (fun _ => vector_reflect hd) n

/-- All numerator windows that omit the divisible row have the same block envelope. -/
theorem windowBlock_uniform : ∃ C : ℝ, 0≤C ∧ ∀ (L : ℕ → ℕ), L 1=0 →
    ∀ (Y q : ℕ) [NeZero q], ‖windowBlock L Y q‖ ≤ C*(1+Real.log q)/q := by
  obtain ⟨C,hC,h⟩ := aggregate_bound
  refine ⟨3*C,by positivity,?_⟩
  intro L hL Y q _
  apply h Y q 3 (by norm_num)
  intro m hm
  by_cases hd : 1<q*m
  · exact numeratorWindow_uniform hd _
  · have hpos := Nat.mul_pos (NeZero.pos q) (mem_Icc.mp hm).1
    have he : q*m=1 := by omega
    rw [he,hL,numeratorWindow,sum_range_zero,norm_zero]
    norm_num [harmonic]; positivity

/-- The constant in the primitive squared mass tail is uniform over all windows
omitting the divisible row, including windows of scale-dependent width. -/
theorem windowEnergy_uniform : ∃ C : ℝ, 0≤C ∧ ∀ L : ℕ → ℕ, L 1=0 → ∀ Y Q : ℕ, 0<Q →
    ∀ s : Finset ℕ, (∀ q ∈ s, Q≤q) →
    ∑ q ∈ s, windowMass L Y q ≤ C/(Q:ℝ)^(15/16:ℝ) := by
  obtain ⟨A,hA,ha⟩ := windowBlock_uniform
  let E (_ q : ℕ) := (A*(1+Real.log q)/q)^2
  obtain ⟨C,hC,ht⟩ := energy_tail_of_bound E A hA (fun _ _ _ => le_rfl)
  refine ⟨C,hC,?_⟩; intro L hL Y Q hQ s hs
  apply (sum_le_sum _).trans (ht Y Q hQ s hs)
  intro q hq
  let : NeZero q := ⟨(hQ.trans_le (hs q hq)).ne'⟩
  apply le_trans _ (pow_le_pow_left₀ (norm_nonneg _) (ha L hL Y q) 2)
  simpa only [windowMass,windowCoordinate,dif_neg (NeZero.ne q)] using primitive_mass_le q (windowBlock L Y q)

/-- A single second-moment constant works for all numerator windows with empty
divisible row, including a different choice of window at each scale. -/
theorem window_variance_uniform : ∃ K : ℝ, 0≤K ∧ ∀ L : ℕ → ℕ, L 1=0 → ∀ N : ℕ, 1≤N →
    ∑ n ∈ range (N^64+1), ‖ThetaReciprocalInversion.windowExtension L (2*N^52) n‖^2 ≤ K*(N:ℝ)^64 := by
  obtain ⟨C,hC,ht⟩ := windowEnergy_uniform
  exact ⟨15876*C,by positivity,fun L hL N hN =>
    ThetaReciprocalVariance.window_variance_from_energy hC (ht L hL) N hN⟩

/-- Every zero-mean reflected periodic wave has convergent reciprocal
prefixes in their natural order. -/
theorem reciprocal_window_cauchy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (hd : 0<d) (v : ℕ → E) {M : ℝ} (hv : ∀ j, ‖v j‖≤M) (hz : v 0=0)
    (hp : ∀ j, v (2*d+j)=v j) (hr : ∀ j≤2*d, v (2*d-j)= -v j) :
    CauchySeq (fun K : ℕ => ∑ i∈range K, ((i:ℝ)+1)⁻¹ • v (i+1)) := by
  have hm : Antitone (fun i : ℕ => ((i:ℝ)+1)⁻¹) := by
    intro a b hab; exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hl : Filter.Tendsto (fun i : ℕ => ((i:ℝ)+1)⁻¹) Filter.atTop (nhds 0) := by
    simp only [← one_div]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact hm.cauchySeq_series_mul_of_tendsto_zero_of_bounded hl
    (period_prefix hd v hv hp (reflect_period v hz hr))

#print axioms weighted_prefix

end Arxiv.«2501.03234».ThetaUniformWindows
#print axioms Arxiv.«2501.03234».ThetaUniformWindows.reciprocal_window_cauchy
#print axioms Arxiv.«2501.03234».ThetaUniformWindows.numeratorWindow_uniform
#print axioms Arxiv.«2501.03234».ThetaUniformWindows.windowBlock_uniform
#print axioms Arxiv.«2501.03234».ThetaUniformWindows.windowEnergy_uniform
#print axioms Arxiv.«2501.03234».ThetaUniformWindows.window_variance_uniform
#print axioms Arxiv.«2501.03234».ThetaUniformWindows.reciprocal_window
