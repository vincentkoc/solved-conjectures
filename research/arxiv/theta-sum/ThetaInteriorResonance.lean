import ThetaSubcriticalResonance

/-! Removing both endpoint regions from the length range of the reciprocal-sum obstruction. -/
namespace Arxiv.«2501.03234».ThetaInteriorResonance
open Finset Filter Real Asymptotics ThetaResonantLengths ThetaSquareRootWindow
open ThetaManyReciprocalSums ThetaResonancePacking ThetaBourgainGaraev
noncomputable section

/-- A factor-two separated family loses at most 4d+2v+2 points after removing
logarithmic intervals of widths d at the left endpoint and d+v at the right. -/
theorem trim (F : Finset ℕ) (hs : separated F) {L U d v : ℝ} (hd : 0≤d) (hv : 0≤v)
    (hw : ∀ n∈F, 0<n ∧ L≤log n ∧ log n≤U+v) :
    ∃ E⊆F, (∀ n∈E,L+d≤log n ∧ log n≤U-d) ∧ (F.card:ℝ)≤E.card+4*d+2*v+2 := by
  classical
  let E := F.filter (fun (n : ℕ) => L+d≤log n ∧ log n≤U-d)
  let A := F.filter (fun (n : ℕ) => log n<L+d)
  let B := F.filter (fun (n : ℕ) => U-d<log n)
  have hA := packing A (fun n m hn hm => hs n m (mem_filter.mp hn).1 (mem_filter.mp hm).1)
    (show L≤L+d by linarith) (fun n hn => ⟨(hw n (mem_filter.mp hn).1).1,
      (hw n (mem_filter.mp hn).1).2.1,(mem_filter.mp hn).2.le⟩)
  have hB := packing B (fun n m hn hm => hs n m (mem_filter.mp hn).1 (mem_filter.mp hm).1)
    (show U-d≤U+v by linarith) (fun n hn => ⟨(hw n (mem_filter.mp hn).1).1,
      (mem_filter.mp hn).2.le,(hw n (mem_filter.mp hn).1).2.2⟩)
  have hsub : F⊆(E∪A)∪B := by
    intro n hn
    by_cases h : log (n:ℝ)<L+d
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hn,h⟩))
    by_cases h' : U-d<log (n:ℝ)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn,h'⟩)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn,le_of_not_gt h,le_of_not_gt h'⟩))
  have hcnt : F.card≤E.card+A.card+B.card := ((card_le_card hsub).trans (card_union_le ..)).trans
    (Nat.add_le_add_right (card_union_le ..) _)
  have hh : (F.card:ℝ)≤E.card+A.card+B.card := by exact_mod_cast hcnt
  exact ⟨E,filter_subset _ _,fun _ hn => (mem_filter.mp hn).2,by linarith only [hA,hB,hh]⟩

def weight (u : ℝ) := u^((1:ℝ)/3)/(log u)^((8:ℝ)/3)

private theorem overhead {c : ℝ} (hc : 0<c) : ∀ᶠ u : ℝ in atTop,
    64*log u+2 ≤ (c/4)*weight u := by
  have hh := (isLittleO_log_rpow_rpow_atTop ((11:ℝ)/3) (by norm_num : (0:ℝ)<1/3)).bound
    (by positivity : 0<c/264)
  filter_upwards [hh,tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with u h hv hu
  have hup : 0<u := by linarith
  have hvp : 0<log u := by linarith
  change ‖(log u)^((11:ℝ)/3)‖ ≤ c/264*‖u^((1:ℝ)/3)‖ at h
  simp only [Real.norm_of_nonneg (rpow_nonneg hvp.le _),Real.norm_of_nonneg (rpow_nonneg hup.le _)] at h
  have hid : log u*(log u)^((8:ℝ)/3)=(log u)^((11:ℝ)/3) := by
    calc _ = (log u)^(1:ℝ)*(log u)^((8:ℝ)/3) := by rw [rpow_one]
         _ = _ := by rw [←rpow_add hvp];norm_num
  unfold weight
  rw [←mul_div_assoc,le_div_iff₀ (rpow_pos_of_pos hvp _)]
  have hw := mul_le_mul_of_nonneg_right (by linarith only [hv] : 64*log u+2≤66*log u)
    (rpow_nonneg hvp.le ((8:ℝ)/3))
  rw [mul_assoc,hid] at hw
  linarith only [h,hw]

def family (p : ℕ) [Fact p.Prime] (B b : ℝ) : Prop :=
  let d := b*weight (log p)
  ∃ E : Finset ℕ, E⊆lengths p 1 ∧ separated E ∧
    (∀ n∈E, exp (sqrt (log p)/512+d)≤n ∧ (n:ℝ)≤B*exp (-d)) ∧ 8*d≤E.card

theorem interior (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ B : ℝ, 0<B → (∀ t a : ZMod p, a≠0 → ‖ThetaReciprocalCutoff.kloosterman t a‖ ≤ 2*B) →
        (S p:ℝ)≤(p:ℝ)*log p/100 → family p B b := by
  classical
  obtain ⟨c,hc,H⟩ := many estimate
  refine ⟨c/16,by positivity,?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [H 1 (by norm_num),upper_logs,hlog.eventually (overhead hc),
    (tendsto_log_atTop.comp hlog).eventually_ge_atTop 1] with p hh hu hcost hlogp
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro B hB hK hS
  obtain ⟨F,hF,hsep,hsize⟩ := hh hp ho hS
  let u := log (p:ℝ)
  let d := (c/16)*weight u
  change 1≤log u at hlogp
  have hup : 0<u := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hv : 0≤log u := by linarith
  have hd : 0≤d := by dsimp [d,weight];positivity
  have hlow (n) (hn : n∈F) : exp (sqrt u/512)≤(n:ℝ) := (mem_filter.mp (hF hn)).2.1.1
  obtain ⟨E,hE,hband,hcount⟩ := trim F hsep (L:=sqrt u/512) (U:=log B) hd
    (mul_nonneg (by norm_num : (0:ℝ)≤32) hv) (fun n hn => by
      obtain ⟨hp',hupper⟩ := hu hp ho 1 B hB hK n (hF hn)
      exact ⟨hp',(le_log_iff_exp_le (by exact_mod_cast hp')).mpr (hlow n hn),hupper⟩)
  refine ⟨E,hE.trans hF,fun n m hn hm => hsep n m (hE hn) (hE hm),?_,?_⟩
  · intro n hn
    have hnpos := (exp_pos _).trans_le (hlow n (hE hn))
    obtain ⟨hl,hh⟩ := hband n hn
    change exp (sqrt u/512+d)≤_ ∧ (n:ℝ)≤B*exp (-d)
    refine ⟨(le_log_iff_exp_le hnpos).mp hl,?_⟩
    calc (n:ℝ) = exp (log n) := (exp_log hnpos).symm
         _ ≤ exp (log B-d) := exp_le_exp.mpr hh
         _ = _ := by rw [sub_eq_add_neg,exp_add,exp_log hB]
  · change 8*d≤E.card
    have hs : c*weight u≤F.card := by simpa only [u,weight,mul_div_assoc] using hsize
    change 64*log u+2≤(c/4)*weight u at hcost
    dsimp only [d] at *
    linarith only [hs,hcount,hcost]

theorem elementary_and_weil (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ)≤(p:ℝ)*log p/100 →
        family p ((p:ℝ)^((3:ℝ)/4)) b ∧ (CompleteEstimate p → family p (sqrt p) b) := by
  obtain ⟨b,hb,H⟩ := interior estimate
  refine ⟨b,hb,?_⟩
  filter_upwards [H] with p hp'
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  have hx : 0<(p:ℝ) := Nat.cast_pos.mpr hp.pos
  exact ⟨hp' hp ho _ (rpow_pos_of_pos hx _) ThetaReciprocalCutoff.kloosterman_bound hS,
    fun hK => hp' hp ho _ (sqrt_pos.mpr hx) hK hS⟩

#print axioms trim
#print axioms interior
#print axioms elementary_and_weil
end
end Arxiv.«2501.03234».ThetaInteriorResonance
