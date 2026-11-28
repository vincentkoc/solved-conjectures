import ThetaIntervalKernel
import ThetaShortPrimeBand
import ThetaRowProgressionDiscrepancy

/-! Changing the upper common-factor cutoff costs a bounded amount on the low
rows. The signed prime approximation then uses the translated high-row energy. -/
namespace Arxiv.«2501.03234».ThetaLocalModelError
open Real Finset ThetaReciprocalBlocks ThetaRowCorrelations ThetaPrimeTailTransfer
open ThetaPrimeMeanSquare ThetaReciprocalInversion ThetaIdentityModels ThetaCalibratedCone
open ThetaDivisibleDiagonal ThetaPrimeDensity ThetaNondivisibleCone ThetaPrimeAsymptotic ThetaDenominatorTails
noncomputable section

theorem row_bound {d : ℕ} (hd : 1<d) (K n : ℕ) :
    |row d K n|≤3*(1+log d) := by
  have h := row_fiber (by omega : 0<d) (by decide : 0<1) (by simpa using hd : 1<d*1)
    (Nat.mod_lt n (by omega : 0<d)) K
  have hh : |row d K n|≤3*(harmonic d:ℝ) := by simpa [row_onMod d K n] using h
  linarith only [hh,harmonic_le_one_add_log d]

private theorem weight {J V N d : ℕ} (hN : 0<N) (hd : 0<d) (hJ : N*d≤J) (hJV : J≤V) :
    |commonWeight V d-commonWeight J d|≤(N:ℝ)⁻¹ := by
  classical
  let A (n : ℕ) := (Icc 1 (n/d)).filter (·%2=1)
  have hs : A J⊆A V := by
    intro g hg; obtain ⟨h,ho⟩ := mem_filter.mp hg
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp h).1,(mem_Icc.mp h).2.trans (Nat.div_le_div_right hJV)⟩,ho⟩
  have hn : N≤J/d := (Nat.le_div_iff_mul_le hd).mpr hJ
  change |(∑ g∈A V,((g:ℝ)^2)⁻¹)-(∑ g∈A J,((g:ℝ)^2)⁻¹)|≤_
  rw [←sum_sdiff hs,add_sub_cancel_right,abs_of_nonneg (sum_nonneg fun _ _ => by positivity)]
  simp only [←inv_pow]
  apply le_trans _ (ThetaIntervalKernel.inv_square_sum hN (hn.trans (Nat.div_le_div_right hJV)))
  apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
  intro g hg; obtain ⟨hv,hj⟩ := mem_sdiff.mp hg
  obtain ⟨hg,ho⟩ := mem_filter.mp hv
  have hgt : J/d<g := by
    by_contra! h; exact hj (mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hg).1,h⟩,ho⟩)
  exact mem_Ico.mpr ⟨by omega,by have := (mem_Icc.mp hg).2; omega⟩

theorem swap_ratio {N T J V : ℕ} (hN : 0<N) (hTN : T≤N) (hJ : N^2≤J) (hV : J≤V)
    (K : ℕ → ℕ) (n : ℕ) : |low T K (commonWeight V) n-low T K (commonWeight J) n|≤3*(T:ℝ)/N := by
  unfold low
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ _d∈Icc 2 T, 3*(N:ℝ)⁻¹ := by
             apply sum_le_sum; intro d hd
             obtain ⟨h,ht⟩ := mem_Icc.mp hd
             have hd₀ : 0<(d:ℝ) := by exact_mod_cast (by omega : 0<d)
             have hb := weight hN (by omega : 0<d)
               ((Nat.mul_le_mul_left N (ht.trans hTN)).trans (by simpa [pow_two] using hJ)) hV
             have hr := row_bound h (K d) n
             rw [←sub_mul,←sub_div,abs_mul,abs_div,abs_of_pos hd₀]
             have hlin : |row d (K d) n|≤3*d := by linarith only [hr,log_le_sub_one_of_pos hd₀]
             apply (mul_le_mul (div_le_div_of_nonneg_right hb hd₀.le) hlin (abs_nonneg _) (by positivity)).trans_eq
             field_simp
       _ ≤ _ := by
             rw [sum_const,nsmul_eq_mul,Nat.card_Icc]
             have hc : (T+1-2:ℕ)≤T := by omega
             calc _ ≤ (T:ℝ)*(3*(N:ℝ)⁻¹) := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
                  _ = _ := by ring

theorem swap {N T J V : ℕ} (hN : 0<N) (hTN : T≤N) (hJ : N^2≤J) (hV : J≤V)
    (K : ℕ → ℕ) (n : ℕ) : |low T K (commonWeight V) n-low T K (commonWeight J) n|≤3 := by
  apply (swap_ratio hN hTN hJ hV K n).trans
  rw [div_le_iff₀ (by exact_mod_cast hN : (0:ℝ)<N)]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hTN) (by norm_num)

theorem height {Y : ℕ} (hY : 1≤Y) (N n : ℕ) :
    |model Y N n|≤3*Z*(1+log Y)^2 := by
  let A := commonWeight (2*N^52)
  let K := coneWindow (coneWidth N)
  change |∑ d∈Icc 2 Y,(A d/d)*row d (K d) n|≤_
  have hZ : 0≤Z := tsum_nonneg fun _ => by positivity
  have hL : 0≤1+log (Y:ℝ) := by linarith [log_nonneg (by exact_mod_cast hY : (1:ℝ)≤Y)]
  apply (abs_sum_le_sum_abs ..).trans
  calc _ ≤ ∑ d∈Icc 2 Y,(3*Z*(1+log Y))*(d:ℝ)⁻¹ := by
             apply sum_le_sum; intro d hd; obtain ⟨h,hy⟩ := mem_Icc.mp hd
             have hdp : 0<(d:ℝ) := by exact_mod_cast (by omega : 0<d)
             obtain ⟨ha,hz⟩ := commonWeight_bounds (2*N^52) d
             change A d≤Z at hz
             have H := row_bound h (K d) n
             rw [abs_mul,abs_of_nonneg (div_nonneg ha hdp.le)]
             apply (mul_le_mul (div_le_div_of_nonneg_right hz hdp.le) (H.trans (by
               linarith [log_le_log hdp (by exact_mod_cast hy : (d:ℝ)≤Y)] : 3*(1+log d)≤3*(1+log Y))) (abs_nonneg _) (by positivity)).trans_eq
             ring
       _ ≤ _ := by
             rw [←mul_sum]
             have hh : (∑ d∈Icc 2 Y,(d:ℝ)⁻¹)≤1+log Y := by
               apply le_trans _ (harmonic_le_one_add_log Y)
               simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
               exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by decide) le_rfl) (fun _ _ _ => by positivity)
             nlinarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hZ) hL)]

/-- The same signed low model works at the elementary and Weil cutoffs. -/
theorem signed {e : ℕ} (he : 32≤e) (he' : e≤48) (kernel : Kernel e) :
    ∃ D : ℝ, 0<D ∧ ∀ {N T p : ℕ}, 2≤N → T≤N → p.Prime → N^56≤p → p≤N^64 →
    let F := windowExtension (above T (coneWindow (coneWidth N))) (2*cutoff e N) p
    |(S p:ℝ)/p-log p/2-(8/π^2)*model T N p|≤D+(8/π^2)*‖F‖ := by
  obtain ⟨C,hC,hdiag⟩ := S_sub_offDiagonal_asymptotic
  let c := 8/π^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨C+2301000+c*3,by positivity,?_⟩
  intro N T p hN hTN hp hl hh F
  let : Fact p.Prime := ⟨hp⟩
  let J := cutoff e N
  let K := coneWindow (coneWidth N)
  have hN1 : 1≤N := by omega
  obtain ⟨h₁,h₂,_⟩ := cutoff_bounds he he' hN1
  have hJ : J≤N^52 := h₂.trans (Nat.pow_le_pow_right hN1 (by decide))
  have hy := (Nat.mul_le_mul_left 2 hJ).trans_lt (cutoff_inside hN hl)
  have hTK : T≤2*J := by have := (Nat.le_self_pow (by decide : 2≠0) N).trans h₁; dsimp only [J]; omega
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have ho := hp.eq_two_or_odd.resolve_left (by have := Nat.pow_le_pow_left hN 56; omega)
  have h₃ := hdiag p (by simpa using ho)
  have h₄ := cone_error he he' kernel hN hp hl hh
  let B := (rationalCone p J (coneWidth N):ℝ)
  have hcore : |(S p:ℝ)/p-log p/2-c*B|≤C+2301000 := by
    rw [show (S p:ℝ)/p-log p/2-c*B=((S p:ℝ)-offDiagonal p-p*log p/2+(offDiagonal p-(8*p/π^2)*B))/p by dsimp [c]; field_simp; ring,
      abs_div,abs_of_pos hpR,div_le_iff₀ hpR]
    exact (abs_add_le ..).trans (by dsimp only [B,J]; linarith only [h₃,h₄])
  have hu (d : ℕ) (hd : d∈Icc 1 (2*J)) : p.Coprime d := hp.coprime_iff_not_dvd.mpr
    (fun hv => ((mem_Icc.mp hd).2.trans_lt hy).not_ge (Nat.le_of_dvd (mem_Icc.mp hd).1 hv))
  have hs := window_split hTK K (by simp [K,coneWindow]) hu
  rw [cone_interpolation (show coneWidth N%2=1 by unfold coneWidth;omega) hp hy] at hs
  let V := low T K (commonWeight (2*J)) p
  have hb : |B-V|=‖F‖ := by
    rw [←Real.norm_eq_abs,←Complex.norm_real,Complex.ofReal_sub]
    congr 1
    change (↑(↑(rationalCone p J (coneWidth N)):ℝ):ℂ)-_=_
    rw [Complex.ofReal_ratCast]
    change (rationalCone p J (coneWidth N):ℂ)-_= (V:ℂ) at hs
    linear_combination hs
  have hswap : |model T N p-V|≤3 := swap (by omega : 0<N) hTN
    (h₁.trans (by omega : cutoff e N≤2*J)) (Nat.mul_le_mul_left 2 hJ) K p
  have hdiff := (abs_sub_le B V (model T N p)).trans (add_le_add (le_of_eq hb) ((abs_sub_comm ..).le.trans hswap))
  have h := abs_sub_le ((S p:ℝ)/p-log p/2) (c*B) (c*model T N p)
  rw [←mul_sub,abs_mul,abs_of_pos hc] at h
  change _≤C+2301000+c*3+c*‖F‖
  linarith only [h,hcore,mul_le_mul_of_nonneg_left hdiff hc.le]

/-- At all but an explicit number of sites in the interval the signed model
error is bounded by a constant independent of the interval and the cutoff. -/
theorem exceptions {e : ℕ} (he : 32≤e) (he' : e≤48) (kernel : Kernel e) :
    ∃ D B : ℝ, 0<D ∧ 0<B ∧ ∀ {N T : ℕ}, 2≤N → 2≤T → T≤N →
    ∀ M H : ℕ, ∀ s : Finset ℕ, (∀ p∈s, M≤p ∧ p<M+H ∧ p.Prime ∧ N^56≤p ∧ p≤N^64) →
    (((s.filter (fun p => D≤|(S p:ℝ)/p-log p/2-(8/π^2)*model T N p|)).card:ℝ)) ≤
      B*(1+log N)^8*((H:ℝ)/(T:ℝ)^(1/64:ℝ)+(N:ℝ)^e) := by
  classical
  obtain ⟨D,hD,h⟩ := signed he he' kernel
  obtain ⟨B,hB,hv⟩ := ThetaShortPrimeBand.high_rows he he'
  let c := 8/π^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨D+c,B,by positivity,hB,?_⟩
  intro N T hN hT hTN M H s hs
  let K := coneWindow (coneWidth N)
  let F := windowExtension (above T K) (2*cutoff e N)
  let E := s.filter (fun p => D+c≤|(S p:ℝ)/p-log p/2-c*model T N p|)
  have he (p : ℕ) (hp : p∈E) : 1≤‖F p‖^2 := by
    obtain ⟨h₁,h₂⟩ := mem_filter.mp hp
    obtain ⟨_,_,hpr,hl,hu⟩ := hs p h₁
    have H := h hN hTN hpr hl hu
    change _≤D+c*‖F p‖ at H
    have hh : 1≤‖F p‖ := by
      apply (mul_le_mul_iff_right₀ hc).mp
      change D+c≤_ at h₂; linarith only [H,h₂]
    exact one_le_pow₀ hh
  have hi : Set.InjOn (M+·) (range H : Finset ℕ) := fun _ _ _ _ h => Nat.add_left_cancel h
  have sub : E⊆(range H).image (M+·) := by
    intro p hp
    obtain ⟨hl,hr,_⟩ := hs p (mem_filter.mp hp).1
    exact mem_image.mpr ⟨p-M,mem_range.mpr (by omega),by omega⟩
  change (E.card:ℝ)≤_
  calc _ = ∑ _p∈E,(1:ℝ) := by simp
       _ ≤ ∑ p∈E,‖F p‖^2 := sum_le_sum he
       _ ≤ ∑ p∈(range H).image (M+·),‖F p‖^2 := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => sq_nonneg _)
       _ = ∑ i∈range H,‖F (M+i)‖^2 := sum_image hi
       _ ≤ _ := hv hN hT M H K

#print axioms signed
#print axioms exceptions

#print axioms swap_ratio
#print axioms swap
#print axioms height
end
end Arxiv.«2501.03234».ThetaLocalModelError
