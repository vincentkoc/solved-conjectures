import ThetaAllWindowMoments

/-! Exponential concentration around the projection on the small prime coordinates. -/
namespace Arxiv.«2501.03234».ThetaCenteredExposure
open Real Filter Finset ThetaUnitExposure ThetaSmoothFiltration ThetaExposureLayers
open ThetaTiltBudget ThetaSmoothConditionalModel ThetaConditionalRows ThetaFiniteExposure
noncomputable section

theorem modulus_dvd {P T t : ℕ} (h : T≤t) : modulus P T ∣ modulus P t :=
  prod_dvd_prod_of_subset _ _ _ (fun _ hp => mem_filter.mpr
    ⟨(mem_filter.mp hp).1,((mem_filter.mp hp).2).trans h⟩)

theorem shift {Ω : Type*} [Fintype Ω] (k l : Ω → ℕ)
    (f : Ω → ℝ) (h : ∀ a b, l a=l b → k a=k b) (x : Ω) :
    proj l (fun a => f a-proj k f a) x=proj l f x-proj k f x := by
  classical
  let A := fiber l (l x)
  have hc : 0<(A.card:ℝ) := Nat.cast_pos.mpr (card_pos.mpr (fiber_nonempty l x))
  change (∑ a∈A,(f a-proj k f a))/A.card=(∑ a∈A,f a)/A.card-proj k f x
  rw [sum_sub_distrib]
  have he : (∑ a∈A,proj k f a)=∑ _a∈A,proj k f x := by
    apply sum_congr rfl
    intro a ha
    simp only [proj,h a x (mem_filter.mp ha).2]
  rw [he,sum_const,nsmul_eq_mul]
  field_simp

theorem centered_mgf : ∀ᶠ T : ℕ in atTop, ∀ (Y : ℕ) (W : Window), [NeZero Y.factorial] →
    ∀ v : ℝ, |v|=tilt T →
    (∑ x : (ZMod Y.factorial)ˣ, exp (v*(rowModel Y W (x:ZMod Y.factorial).val-value Y W T x))) ≤
      exp total*Y.factorial.totient := by
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp eventual_size
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop (max 2 (max Q L))] with T hT
  intro Y W _ v hv
  let k (t : ℕ) := key (P:=Y.factorial) (modulus Y.factorial t)
  let g (x : (ZMod Y.factorial)ˣ) := rowModel Y W (x:ZMod Y.factorial).val
  let f (x : (ZMod Y.factorial)ˣ) := g x-value Y W T x
  have hf (t : ℕ) (ht : T≤t) (x : (ZMod Y.factorial)ˣ) :
      proj (k t) f x=value Y W t x-value Y W T x :=
    shift (k T) (k t) g (refine (modulus_dvd ht)) x
  let F (t : ℕ) := ∑ x : (ZMod Y.factorial)ˣ, exp (v*proj (k t) f x)
  have hF (t : ℕ) : 0≤F t := sum_nonneg fun _ _ => (exp_pos _).le
  have hstep (t : ℕ) (ht : T≤t) : F (t+1) ≤ exp (charge (t+1))*F t := by
    have H := within (by omega : 1≤T) (by omega : T≤t+1) hv
    have ha := hQ (t+1) (by omega)
    have hl := hL (t+1) (by omega)
    apply le_trans _ (mul_le_mul_of_nonneg_right (exp_le_exp.mpr H.2) (hF _))
    apply step _ _ _ (refine (modulus_dvd (Nat.le_succ t)))
      (le_trans (by positivity [envelope_nonneg]) ha) H.1
    intro x y he
    have hb : value Y W T x=value Y W T y := by
      simp only [value,proj,refine (modulus_dvd ht) x y he]
    rw [hf _ (by omega),hf _ (by omega),hb,sub_sub_sub_cancel_right]
    exact (oscillation hl W x y he).trans ha
  have telescope (t : ℕ) (ht : T≤t) :
      F t≤exp (∑ q∈Ico (T+1) (t+1),charge q)*F T := by
    induction t,ht using Nat.le_induction with
    | base => simp
    | succ t ht ih =>
      rw [sum_Ico_succ_top (by omega),exp_add,mul_right_comm]
      have H := mul_le_mul_of_nonneg_left ih (exp_pos (charge (t+1))).le
      apply (hstep _ ht).trans
      simpa only [mul_comm (exp (charge (t+1)))] using H
  let t := max T Y.factorial
  have hbase : F T=Y.factorial.totient := by simp [F,hf _ le_rfl,ZMod.card_units_eq_totient]
  have hend : F t=∑ x : (ZMod Y.factorial)ˣ,exp (v*f x) := by
    simp only [F,k,terminal (Nat.factorial_pos _) (le_max_right T Y.factorial),final_project,t]
  change (∑ x : (ZMod Y.factorial)ˣ,exp (v*f x))≤_
  rw [←hend,←hbase]
  exact (telescope _ (le_max_left ..)).trans
    (mul_le_mul_of_nonneg_right (exp_le_exp.mpr (bounded _)) (hF _))

#print axioms centered_mgf
end
end Arxiv.«2501.03234».ThetaCenteredExposure
