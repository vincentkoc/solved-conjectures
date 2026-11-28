import ThetaModelExponentialMoment

/-! Uniform exponential moments for arbitrary finite numerator windows. -/
namespace Arxiv.«2501.03234».ThetaAllWindowMoments
open Finset Real Filter ThetaModelExponentialMoment ThetaSmoothConditionalModel ThetaConditionalRows
open ThetaTiltBudget ThetaPeriodMeans ThetaRowCorrelations
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩

/-- Enumerate a complete period by its residue representatives. -/
theorem sum_period {q : ℕ} [NeZero q] (f : ℕ → ℝ) :
    ∑ n∈range q,f n = ∑ x : ZMod q,f x.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => exact (Fin.sum_univ_eq_sum_range f (q+1)).symm

theorem unit_bound : ∃ a K : ℝ, 0<a ∧ 0<K ∧ ∀ (Y : ℕ) (W : Window), 2≤Y →
    unitMean Y.factorial (fun n => exp (a*|rowModel Y W n|))≤K := by
  obtain ⟨T,hT,h⟩ := ((eventually_ge_atTop 1).and model_mgf).exists
  let a := tilt T
  let B := exp (total+a*height T)
  have ha : 0<a := tilt_pos hT
  refine ⟨a,2*B,ha,by dsimp [B];positivity,?_⟩
  intro Y W hY
  have hp := h Y W hY a (abs_of_pos ha)
  have hn := h Y W hY (-a) (by rw [abs_neg,abs_of_pos ha])
  have he (z : ℝ) : exp (a*|z|)≤exp (a*z)+exp ((-a)*z) := by
    rcases le_total 0 z with hz|hz
    · rw [abs_of_nonneg hz];linarith only [exp_pos ((-a)*z)]
    · rw [abs_of_nonpos hz,mul_neg,← neg_mul];linarith only [exp_pos (a*z)]
  unfold unitMean at *
  have hs := sum_le_sum (s:=univ) (fun u (_ : u∈(univ : Finset (ZMod Y.factorial)ˣ)) =>
    he (rowModel Y W (u:ZMod Y.factorial).val))
  rw [sum_add_distrib] at hs
  have hh := div_le_div_of_nonneg_right hs (Nat.cast_nonneg Y.factorial.totient (α:=ℝ))
  rw [add_div] at hh
  exact hh.trans (by change _ ≤ 2*exp (total+a*height T);linarith only [hp,hn])

def masked (W : Window) (n : ℕ) : Window :=
  ⟨fun d => if n.Coprime d then W.width d else 0,W.weightCutoff⟩

theorem orbit_model (Y n : ℕ) (W : Window) : ∃ v : (ZMod Y.factorial)ˣ, ∀ t : ℕ,
    rowModel Y W (n*t)=rowModel Y (masked W n) ((v:ZMod Y.factorial).val*t) := by
  classical
  let S := (Icc 2 Y).filter (n.Coprime ·)
  let m := S.lcm id
  have hm : m∣Y.factorial := by
    apply Finset.lcm_dvd
    intro d hd
    have hdI := mem_Icc.mp (mem_filter.mp hd).1
    exact Nat.dvd_factorial (by change 0 < d; omega) hdI.2
  have hm' : 0 < m := Nat.pos_of_dvd_of_pos hm (Nat.factorial_pos _)
  let : NeZero m := ⟨hm'.ne'⟩
  have hc₀ : n.Coprime (∏ d∈S,d) := Nat.coprime_prod_right_iff.mpr (fun d hd => (mem_filter.mp hd).2)
  have hc : n.Coprime m := hc₀.coprime_dvd_right (Finset.lcm_dvd (fun d hd => dvd_prod_of_mem id hd))
  obtain ⟨v,hv⟩ := ZMod.unitsMap_surjective hm (ZMod.unitOfCoprime n hc)
  have hh : ((v:ZMod Y.factorial).val:ZMod m)=(n:ZMod m) := by
    have h := congrArg (fun u : (ZMod m)ˣ => (u:ZMod m)) hv
    rw [ZMod.unitsMap_val,ZMod.coe_unitOfCoprime,← ZMod.natCast_zmod_val (v:ZMod Y.factorial),
      ZMod.cast_natCast hm] at h
    exact h
  have hmod := (ZMod.natCast_eq_natCast_iff ..).mp hh
  refine ⟨v,?_⟩;intro t
  unfold rowModel low
  apply sum_congr rfl
  intro d hd
  dsimp only [masked]
  by_cases hgood : n.Coprime d
  · rw [if_pos hgood]
    have hdv : d∣m := dvd_lcm (f:=id) (mem_filter.mpr ⟨hd,hgood⟩)
    have hsame := (hmod.of_dvd hdv).mul_right t
    rw [← row_onMod d (W.width d) (n*t),← row_onMod d (W.width d) ((v:ZMod Y.factorial).val*t)]
    rw [show ((v:ZMod Y.factorial).val*t)%d=(n*t)%d from hsame]
  · have hn : ¬(n*t).Coprime d := fun h => hgood (h.coprime_dvd_left (dvd_mul_right ..))
    simp [if_neg hgood,row,wave_of_not_coprime hn]

theorem periodic (Y : ℕ) (W : Window) : OnMod Y.factorial (rowModel Y W) :=
  low_onMod (fun d hd _ => Nat.dvd_factorial (by have := (mem_Icc.mp hd).1;omega) (mem_Icc.mp hd).2) _ _

/-- The same exponential integral bound holds on all residues, including the
nonunits. Multiplicative orbits replace the omitted rows by a masked window. -/
theorem all_bound : ∃ a K : ℝ, 0<a ∧ 0<K ∧ ∀ (Y : ℕ) (W : Window), 2≤Y →
    mean Y.factorial (fun n => exp (a*|rowModel Y W n|))≤K := by
  classical
  obtain ⟨a,K,ha,hK,H⟩ := unit_bound
  refine ⟨a,K,ha,hK,?_⟩
  intro Y W hY
  let Q := Y.factorial
  let f (x : ZMod Q) := exp (a*|rowModel Y W x.val|)
  have ht : 0<(Q.totient:ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.factorial_pos _))
  have hQ : 0<(Q:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hf (x : ZMod Q) : ∑ u : (ZMod Q)ˣ,f ((u:ZMod Q)*x)≤K*Q.totient := by
    obtain ⟨v,hv⟩ := orbit_model Y x.val W
    let g (u : (ZMod Q)ˣ) := exp (a*|rowModel Y (masked W x.val) (u:ZMod Q).val|)
    have he (u : (ZMod Q)ˣ) : f ((u:ZMod Q)*x)=g (v*u) := by
      dsimp only [f,g,Units.val_mul]
      rw [mul_comm (u:ZMod Q) x,ZMod.val_mul,ZMod.val_mul,
        periodic Y W,periodic Y (masked W x.val),hv]
    simp_rw [he]
    rw [show (∑ u : (ZMod Q)ˣ,g (v*u))=∑ u,g u from
      Fintype.sum_bijective _ (Equiv.mulLeft v).bijective _ _ (fun _ => rfl)]
    exact (div_le_iff₀ ht).mp (H Y (masked W x.val) hY)
  have hs := sum_le_sum (s:=univ) (fun x (_ : x∈(univ : Finset (ZMod Q))) => hf x)
  rw [sum_comm] at hs
  have he (u : (ZMod Q)ˣ) : (∑ x : ZMod Q, f ((u:ZMod Q)*x))=∑ x,f x :=
    Fintype.sum_bijective _ (Units.mulLeft u).bijective _ _ (fun _ => rfl)
  simp only [he,sum_const,card_univ,nsmul_eq_mul,ZMod.card_units_eq_totient,ZMod.card] at hs
  unfold mean
  rw [sum_period,div_le_iff₀ hQ]
  change ∑ x : ZMod Q,f x ≤ K*Q
  exact (mul_le_mul_iff_right₀ ht).mp (by linarith only [hs])

#print axioms all_bound
#print axioms unit_bound
#print axioms orbit_model
end
end Arxiv.«2501.03234».ThetaAllWindowMoments
