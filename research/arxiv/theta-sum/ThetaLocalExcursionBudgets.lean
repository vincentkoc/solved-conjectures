import ThetaLocalExcursionScales

/-! Simultaneous budgets for the prime count, individual row discrepancies,
and approximation errors on a translated interval. -/
namespace Arxiv.«2501.03234».ThetaLocalExcursionBudgets
open Real Filter ThetaIdentityModels ThetaLocalPrimeCounts ThetaLocalExcursionScales
noncomputable section

private theorem numeric {B L J H m W Y U v : ℝ}
    (hB : 0<B) (hL : 2≤L) (hconst : 2*(B*2^8*(2^16+1))≤L)
    (hH : 0≤H) (hW : H/(2*L^2)≤W) (hY : 1≤Y) (hYmax : Y≤L^1024)
    (hU : 0<U) (hUL : U≤L) (hv : v≤U) (hm : 0≤ m) (hmL : m≤L)
    (hJ : J*L^16≤H) (hpower : L^16≤2^16*Y^(1/64:ℝ)) :
    let δ := H/L^1030
    δ≤W ∧ Y*(v*δ)≤W ∧ U*(B*(1+m)^8*(H/Y^(1/64:ℝ)+J))≤W := by
  intro δ
  have hpos : 0<L := by linarith
  have h1 : 1≤L := by linarith
  have hδ : 0≤δ := by dsimp [δ]; positivity
  have h5 : 2*L^2≤L^5 := calc
    _ ≤ L*L^2 := mul_le_mul_of_nonneg_right hL (sq_nonneg _)
    _ = L^3 := by ring
    _ ≤ _ := pow_le_pow_right₀ h1 (by decide)
  have hsmall := (div_le_div_of_nonneg_left hH (show 0<2*L^2 by positivity) h5).trans hW
  refine ⟨(div_le_div_of_nonneg_left hH (pow_pos hpos 5) (pow_le_pow_right₀ h1 (by decide : 5≤1030))).trans hsmall,?_,?_⟩
  · calc Y*(v*δ) = (Y*v)*δ := by ring
         _ ≤ L^1025*δ := by
             apply mul_le_mul_of_nonneg_right _ hδ
             calc Y*v ≤ Y*L := mul_le_mul_of_nonneg_left (hv.trans hUL) (by linarith)
                  _ ≤ L^1024*L := mul_le_mul_of_nonneg_right hYmax hpos.le
                  _ = _ := by ring
         _ = H/L^5 := by dsimp [δ]; field_simp
         _ ≤ _ := hsmall
  · have hy : 0<Y^(1/64:ℝ) := rpow_pos_of_pos (by linarith) _
    have hj := (le_div_iff₀ (pow_pos hpos 16)).mpr hJ
    have hs : H/Y^(1/64:ℝ)≤2^16*H/L^16 := by
      rw [div_le_div_iff₀ hy (pow_pos hpos 16)]; nlinarith only [mul_le_mul_of_nonneg_left hpower hH]
    have he : H/Y^(1/64:ℝ)+J≤(2^16+1)*H/L^16 := (add_le_add hs hj).trans_eq (by ring)
    let K := B*2^8*(2^16+1)
    have hk : 2*K≤L^5 := hconst.trans (by simpa using pow_le_pow_right₀ h1 (by decide : 1≤5))
    have hlow : 0≤(2^16+1)*H/L^16 := by positivity
    have hh : (1+m)^8≤(2*L)^8 := pow_le_pow_left₀ (by linarith) (by linarith) _
    calc _ ≤ U*(B*(1+m)^8*((2^16+1)*H/L^16)) := by gcongr
         _ ≤ L*(B*(2*L)^8*((2^16+1)*H/L^16)) :=
           mul_le_mul hUL (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hB.le) hlow)
             (by positivity) hpos.le
         _ = (2*K/L^5)*(H/(2*L^2)) := by dsimp [K]; field_simp
         _ ≤ H/(2*L^2) := mul_le_of_le_one_left (by positivity) ((div_le_one (pow_pos hpos 5)).mpr hk)
         _ ≤ _ := hW

theorem eventual {e : ℕ} {θ B : ℝ} (hθ : (e:ℝ)/64<θ) (hB : 0<B) :
    ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, 2≤N ∧ N^56≤X ∧ 2*X≤N^64 ∧ cutoff X≤N ∧
    ∀ H : ℕ, H≤X → (X:ℝ)^θ≤H → ∀ m : ℕ, 0 < m → (m:ℝ)≤log X →
    let L := log (X:ℝ)
    let Y := cutoff X
    let w := mass X H/m.totient
    let δ := (H:ℝ)/L^1030
    let U := height X
    2≤Y ∧ m≤Y ∧ max m 3≤N ∧ δ≤w ∧ Y*(3*Z*(1+log Y)*δ)≤w ∧
      U*(B*(1+log N)^8*((H:ℝ)/(Y:ℝ)^(1/64:ℝ)+(N:ℝ)^e))≤w ∧
      (∀ d≤Y, (m*d:ℕ)≤L^1025) := by
  have ht := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [band hθ,cutoff_bounds,height_small (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℕ),
    ht.eventually_ge_atTop 4,ht.eventually_ge_atTop (2*(B*2^8*(2^16+1)))] with X hN hY hsmall hx hL hC
  obtain ⟨N,hn,hl,hu,hyn,hln,hj⟩ := hN
  refine ⟨N,hn,hl,hu,hyn,?_⟩
  intro H hH hθH m hm hmL L Y w δ U
  obtain ⟨hy,hyL,hymax,_,hpow⟩ := hY
  change 4≤L at hL
  change L≤(Y:ℝ) at hyL
  have hmy : m≤Y := by exact_mod_cast hmL.trans hyL
  have h3 : 3≤Y := by exact_mod_cast (show (3:ℝ)≤Y by linarith only [hyL,hL])
  have hφ : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
  have hLp : 0<L := by change 4≤L at hL; linarith
  have hφL : (m.totient:ℝ)≤L := (Nat.cast_le.mpr (Nat.totient_le m)).trans hmL
  have hW : (H:ℝ)/(2*L^2)≤w := calc
    _ = ((H:ℝ)/(2*L))/L := by ring
    _ ≤ ((H:ℝ)/(2*L))/m.totient := div_le_div_of_nonneg_left (by positivity) hφ hφL
    _ ≤ _ := div_le_div_of_nonneg_right (mass_lower hx hH) hφ.le
  have hZ : 1≤Z := (weight_one (by decide : 0<1) (le_refl 1)).trans (ThetaReciprocalBlocks.commonWeight_bounds 1 1).2
  have hlog := log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hv : 3*Z*(1+log Y)≤U := by
    change 3*Z*(1+log Y)≤3*Z*(1+log Y)^2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith only [hlog,sq_nonneg (log (Y:ℝ))]
  have hU : 0<U := by change 0<3*Z*(1+log Y)^2; positivity
  rw [rpow_one] at hsmall
  have h := numeric hB (show 2≤L by change 4≤L at hL; linarith) hC (Nat.cast_nonneg H) hW
    (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega)) hymax hU hsmall hv
    (log_nonneg (show (1:ℝ)≤N by exact_mod_cast (show 1≤N by omega))) hln (hj.trans hθH) hpow
  refine ⟨hy,hmy,max_le (hmy.trans hyn) (h3.trans hyn),h.1,h.2.1,h.2.2,?_⟩
  intro d hd; push_cast
  calc (m:ℝ)*d≤L*L^1024 := mul_le_mul hmL ((Nat.cast_le.mpr hd).trans hymax) (Nat.cast_nonneg _) hLp.le
       _ = _ := by ring

#print axioms eventual
end
end Arxiv.«2501.03234».ThetaLocalExcursionBudgets
