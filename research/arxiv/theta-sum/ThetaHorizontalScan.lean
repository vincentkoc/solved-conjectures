import ThetaHorizontalTable

/-! Sparse threshold comparisons in the sub-square-root table of horizontal phases. -/
namespace Arxiv.«2501.03234».ThetaHorizontalScan
open Finset Filter Real Asymptotics ThetaAdditiveReciprocity ThetaReciprocalMesh
open ThetaMeshObstruction ThetaHorizontalTable ThetaBourgainGaraev ThetaSquareRootWindow
noncomputable section

def checks (p : ℕ) (α : ℝ) : Finset (ℕ×ℕ) :=
  ((tests p 1).filter (fun n => n≤radius p α)) ×ˢ (Icc 1 (radius p α))

def alert (p n j : ℕ) : Prop := 2*(n:ℝ)<resolution p*‖horizontal p n (j:ℤ)‖

theorem count : ∀ᶠ p : ℕ in atTop, ∀ α : ℝ,
    ((checks p α).card:ℝ)≤34359738368*(log p)^2*log (log p)*(sqrt p*exp (-(log p)^α)) := by
  filter_upwards [test_count] with p h
  intro α
  have hsub : ((tests p 1).filter (fun n => n≤radius p α)).card≤(tests p 1).card := card_le_card (filter_subset ..)
  have hr : (radius p α:ℝ) ≤ sqrt p*exp (-(log p)^α) := Nat.floor_le (by positivity)
  rw [checks,card_product,Nat.card_Icc]
  simp only [Nat.add_sub_cancel,Nat.cast_mul]
  exact mul_le_mul ((Nat.cast_le.mpr hsub).trans (h 1)) hr (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans (h 1))

theorem comparison_ratio {α : ℝ} (hα : 0<α) :
    Tendsto (fun p : ℕ => ((checks p α).card:ℝ)/sqrt p) atTop (nhds 0) := by
  have hu := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have ht := (tendsto_rpow_atTop hα).comp hu
  have hf := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3/α) 1 zero_lt_one).comp ht).const_mul 34359738368
  rw [mul_zero] at hf
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _ hf
  filter_upwards [count,hu.eventually_ge_atTop 1,eventually_ge_atTop 1] with p hc hlog hp
  let u := log (p:ℝ)
  have hu' : 0<u := by change 1≤u at hlog;linarith
  have hp' : 0<sqrt (p:ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0<p by omega))
  change _ ≤ 34359738368*((u^α)^(3/α)*exp ((-1)*(u^α)))
  rw [neg_one_mul,←rpow_mul hu'.le,show α*(3/α)=3 by field_simp,show (3:ℝ)=((3:ℕ):ℝ) by norm_num,rpow_natCast]
  apply (div_le_iff₀ hp').mpr
  apply (hc α).trans
  change 34359738368*u^2*log u*(sqrt p*exp (-u^α))≤_
  have hsmall := mul_le_mul_of_nonneg_left (log_le_self hu'.le) (sq_nonneg u)
  have hh := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hp'.le (exp_pos (-u^α)).le)
  nlinarith only [hh]

private theorem rounded {p N : ℕ} {α : ℝ} (hM : 4≤resolution p) (hN : 1<(N:ℝ)) (hl : 1≤log (log (N:ℝ)))
    (hlo : exp (sqrt (log p)/512)≤(N:ℝ)) (hNp : N<p) {j : ℤ} (hj : j≠0)
    (hbox : max (N:ℝ) |(j:ℝ)| ≤ sqrt p*exp (-(log p)^α))
    (hs : (N:ℝ)/(268435456*log N*log (log N))<‖horizontal p N j‖) :
    ∃ m k : ℕ, (m,k)∈checks p α ∧ m≤N ∧ 3*N≤4*m ∧ alert p m k := by
  let M := resolution p
  have hnpos : 0<(N:ℝ) := by linarith
  have hlog := log_pos hN
  have hd : 0<log (log (N:ℝ)) := by linarith
  have hL := log_le_log hnpos (show (N:ℝ)≤p by exact_mod_cast hNp.le)
  have hD := log_le_log hlog hL
  have hmul := mul_le_mul hL hD hd.le (hlog.le.trans hL)
  have hb : (1073741824:ℝ)*log (N:ℝ)*log (log N)≤M := by
    apply le_trans _ (Nat.le_ceil _);linarith only [hmul]
  have hp' : 0<(M:ℝ) := lt_of_lt_of_le (by positivity) hb
  obtain ⟨m,hg,hm,hgap⟩ := approximate hNp.le (Nat.cast_pos.mp hnpos) (Nat.cast_pos.mp hp')
  have hsmall := (Nat.mul_le_mul_right (N-m) hM).trans hgap
  have h3 : 3*N≤4*m := by omega
  have hgap' := (Nat.cast_le (α:=ℝ)).mpr hgap
  rw [Nat.cast_mul,Nat.cast_sub hm] at hgap'
  have ht := ThetaHorizontalTable.prefix_change p m (N-m) j
  rw [Nat.add_sub_of_le hm,Nat.cast_sub hm] at ht
  have htri := (norm_le_norm_add_norm_sub' (horizontal p N j) (horizontal p m j)).trans (add_le_add_right ht _)
  have hsig := (div_lt_iff₀ (by positivity : 0<(268435456:ℝ)*log (N:ℝ)*log (log N))).mp hs
  have htol := mul_le_mul_of_nonneg_left htri hp'.le
  have hs' := mul_le_mul_of_nonneg_right hb (norm_nonneg (horizontal p N j))
  have hr : N≤radius p α := Nat.le_floor ((le_max_left _ _).trans hbox)
  have hjcast : (j.natAbs:ℝ)=|(j:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have hjr : j.natAbs≤radius p α := Nat.le_floor (hjcast.trans_le ((le_max_right _ _).trans hbox))
  have hx : 1≤(p:ℝ) := hN.le.trans (by exact_mod_cast hNp.le)
  have hcap : (m:ℝ)≤(p:ℝ)^(3/4+(1:ℝ)) := ((Nat.cast_le.mpr (hm.trans hNp.le)).trans_eq (rpow_one _).symm).trans
    (rpow_le_rpow_of_exponent_le hx (by norm_num))
  have htest : m∈tests p 1 := mem_filter.mpr ⟨hg,
    (mul_le_mul_of_nonneg_left hlo (by norm_num : (0:ℝ)≤3)).trans (by exact_mod_cast h3),hcap,hm.trans_lt hNp⟩
  refine ⟨m,j.natAbs,mem_product.mpr ⟨mem_filter.mpr ⟨htest,hm.trans hr⟩,mem_Icc.mpr ⟨?_,hjr⟩⟩,hm,h3,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hj)
  · unfold alert
    rw [ThetaHorizontalTable.norm_natAbs]
    change 2*(m:ℝ)<(M:ℝ)*‖horizontal p m j‖
    nlinarith only [hsig,hgap',htol,hs',show (m:ℝ)≤N by exact_mod_cast hm,hnpos]

/-- The horizontal obstruction in a square table of o(p) phase terms. Distinct
surviving prefix lengths each have a positive multiplier and a large norm. -/
theorem many (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ α : ℝ, 0<α → α<1/3 → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      CompleteEstimate p → (S p:ℝ)≤(p:ℝ)*log p/100 →
        ∃ G : Finset ℕ, b*ThetaInteriorResonance.weight (log p)≤G.card ∧
          (∀ n∈G, ∃ j : ℕ, (n,j)∈checks p α ∧ alert p n j) ∧
          ∀ n m : ℕ, n∈G → m∈G → n < m → 3*n≤2*m := by
  classical
  obtain ⟨b,hb,H⟩ := ThetaHorizontalBox.many estimate
  refine ⟨b,hb,?_⟩
  intro α ha ha'
  filter_upwards [H α ha ha',controls] with p hh hc
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hW hS
  obtain ⟨E,hsep,hsize,hbox⟩ := (hh hp ho hS).2 hW
  have hf (n : ℕ) (hn : n∈E) : ∃ m k : ℕ, (m,k)∈checks p α ∧ m≤n ∧ 3*n≤4*m ∧ alert p m k := by
    obtain ⟨hlo,hp',j,hj,_,hB,hs⟩ := hbox n hn
    obtain ⟨hx,hL⟩ := hc.2 n hlo
    exact rounded hc.1 hx hL hlo hp' hj hB hs
  choose g k hg hlo hhi hsig using hf
  let f (n : ℕ) := if h : n∈E then g n h else 0
  have hval {n : ℕ} (hn : n∈E) : f n=g n hn := dif_pos hn
  obtain ⟨hcard,hs⟩ := image_separated E f hsep (fun n hn => by rw [hval hn];exact ⟨hlo n hn,hhi n hn⟩)
  refine ⟨E.image f,?_,?_,hs⟩
  · rw [hcard]
    simpa only [ThetaInteriorResonance.weight,mul_div_assoc] using hsize
  · intro n hn
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hn
    rw [hval hv]
    exact ⟨k v hv,hg v hv,hsig v hv⟩

theorem growth (estimate : InitialSumEstimate) (weil : ∀ (p : ℕ) [Fact p.Prime],CompleteEstimate p)
    {α : ℝ} (ha : 0<α) (ha' : α<1/3)
    (quiet : ∀ᶠ p : ℕ in atTop, p.Prime → _root_.Odd p →
      ∀ v∈checks p α, ¬alert p v.1 v.2) (n : ℕ) : type_of% (conjecture_4_4 n) := by
  obtain ⟨b,hb,H⟩ := many estimate
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [H α ha ha',quiet,hlog.eventually_gt_atTop (100*(n:ℝ)),
    (tendsto_log_atTop.comp hlog).eventually_gt_atTop 0] with p hh hq hl hv
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hS : (p:ℝ)*log p/100<(S p:ℝ) := by
    by_contra! hsmall
    obtain ⟨G,hsize,hG,_⟩ := hh hp ho (weil p) hsmall
    change 0<log (log (p:ℝ)) at hv
    have hu : 0<log (p:ℝ) := log_pos (by exact_mod_cast hp.one_lt)
    have hpos : 0<b*ThetaInteriorResonance.weight (log p) := by unfold ThetaInteriorResonance.weight;positivity
    obtain ⟨m,hm⟩ := card_pos.mp (Nat.cast_pos.mp (hpos.trans_le hsize))
    obtain ⟨j,hj,hA⟩ := hG m hm
    exact hq hp ho (m,j) hj hA
  change 100*(n:ℝ)<log (p:ℝ) at hl
  have ht := mul_lt_mul_of_pos_right hl (Nat.cast_pos.mpr hp.pos : 0<(p:ℝ))
  exact_mod_cast (show (n:ℝ)*(p:ℝ)<(S p:ℝ) by linarith)

#print axioms many
#print axioms growth

#print axioms count
#print axioms comparison_ratio
end
end Arxiv.«2501.03234».ThetaHorizontalScan
