import ThetaPopularLagCounts

/-! A positive proportion of physical displacements up to each H already
have the same-tail excess, under the ordinary prime-pair upper sieve. -/
namespace Arxiv.«2501.03234».ThetaFrequentTailGaps
open Real Filter Finset ThetaProgressionTailPairs ThetaLagSignCounts ThetaAsymmetricTails
open ThetaPrimeLagBounds ThetaNaturalPrimeMeans ThetaPositiveLag ThetaPopularLagCounts
noncomputable section

def excess (q r X h : ℕ) (t : ℝ) : ℝ :=
  (classCount q r X h (sameTail t):ℝ)-classCount q r X h (oppositeTail t)

def gaps (q r X H : ℕ) (t b : ℝ) := (Icc 1 H).filter
  (fun h => q∣h ∧ b*X≤excess q r X h t*(log X)^2)

theorem marked_excess (q r X h : ℕ) (t : ℝ) (ht : 0≤t) :
    corr X h (fun p => mark t (restricted q r p))=excess q r X h t := by
  rw [marked X h t,excess]
  have a : ¬t<0 := not_lt.mpr ht
  have b : ¬0< -t := by linarith
  rw [count_eq (P:=sameTail t) (fun x => by simp [sameTail,a,b]) (fun x => by simp [sameTail,a,b]),
    count_eq (P:=oppositeTail t) (fun x => by simp [oppositeTail,a,b]) (fun x => by simp [oppositeTail,a,b])]

theorem original (U : Upper) (hAP : ProgressionMangoldt) {q r : ℕ}
    (hq : 0<q) (hr : r<q) (hu : r.Coprime q) (t : ℝ) (ht : 0≤t) :
    ∃ A b η : ℝ,0<A ∧ 0<b ∧ 0<η ∧ ∀ᶠ X : ℕ in atTop,∀ H : ℕ,A*log X≤H → H≤X →
      η*H≤((gaps q r X H t b).card:ℝ) := by
  classical
  obtain ⟨D,hD,hd,c,hc,hs⟩ := class_scales hAP hq hr hu t ht
  let f (p : ℕ) := mark t (restricted q r p)
  have hf (p : ℕ) : |f p|≤1 := by dsimp [f,mark];split_ifs <;> norm_num
  obtain ⟨δ,K,hδ,hK,hp⟩ := many U hD hc hf hs
  have hD' : 0<(D:ℝ) := by exact_mod_cast hD
  refine ⟨2*D*(K+1),c/2,δ/(2*D),by positivity,half_pos hc,by positivity,?_⟩
  filter_upwards [hp,(tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1]
    with X hx hlog
  change 1≤log X at hlog
  intro H hH hh
  let L := H/D
  have hcap : D*L≤H := Nat.mul_div_le ..
  have hur : H<D*L+D := by
    have h := Nat.mod_add_div H D
    have h' := Nat.mod_lt H hD
    dsimp [L];omega
  have hu' : (H:ℝ)<(D:ℝ)*L+D := by exact_mod_cast hur
  have hDL : (D:ℝ)≤D*log X := by nlinarith only [mul_le_mul_of_nonneg_left hlog hD'.le]
  have hl : K*log X≤L := by
    apply (mul_le_mul_iff_right₀ hD').mp
    nlinarith only [hH,hu',hDL,mul_nonneg (mul_nonneg hD'.le hK.le) (zero_le_one.trans hlog)]
  have hhalf : (H:ℝ)≤2*D*L := by
    nlinarith only [hH,hu',hDL,mul_nonneg (mul_nonneg hD'.le hK.le) (zero_le_one.trans hlog)]
  have lower := hx L hl (hcap.trans hh)
  let S := popular X D L f (c/2)
  have hi : Set.InjOn (fun k : ℕ => D*k) S := fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hD he
  have hsub : S.image (fun k => D*k)⊆gaps q r X H t (c/2) := by
    intro h he
    obtain ⟨k,hk,rfl⟩ := mem_image.mp he
    obtain ⟨hk,he⟩ := mem_filter.mp hk
    obtain ⟨h₀,hlt⟩ := mem_erase.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hD (Nat.pos_of_ne_zero h₀),
      (Nat.mul_le_mul_left D (mem_range.mp hlt).le).trans hcap⟩,
      hd.trans (dvd_mul_right ..),by simpa only [f,marked_excess q r X (D*k) t ht] using he⟩
  have hcnt := card_le_card hsub
  rw [card_image_of_injOn hi] at hcnt
  apply le_trans _ (lower.trans (Nat.cast_le.mpr hcnt))
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<2*(D:ℝ))]
  nlinarith only [mul_le_mul_of_nonneg_left hhalf hδ.le]

#print axioms original
end
end Arxiv.«2501.03234».ThetaFrequentTailGaps
