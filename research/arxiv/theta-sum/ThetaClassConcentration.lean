import ThetaSmoothRefinement
import ThetaCenteredExposure

/-! A class-relative exponential tail after the low prime coordinates have
been exposed. The estimate is uniform even on rare compact residue classes. -/
namespace Arxiv.«2501.03234».ThetaClassConcentration
open Real Finset Filter ThetaUnitExposure ThetaExposureLayers ThetaTiltBudget ThetaSmoothConditionalModel
open ThetaSmoothRefinement ThetaPrimeTailTransfer ThetaPeriodMeans ThetaConditionalRows
open ThetaSmoothRows ThetaIdentityModels ThetaIdentityFiber ThetaFactorialRows
noncomputable section
local instance (Y : ℕ) : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩

def m (T : ℕ) := ThetaCompactModulus.modulus T
def bias (T : ℕ) := (2160*Z)*(612*zetaBound)*(log T)^2/(T:ℝ)^(1/16:ℝ)

theorem compact_divides {P T : ℕ} (hp : 0<P) (h : m T∣P) :
    m T∣ThetaSmoothFiltration.modulus P T := by
  let M := m T
  have hm : 0<M := ThetaCompactModulus.positive T
  have hf := (Nat.factorization_le_iff_dvd hm.ne' hp.ne').mpr h
  calc M = ∏ p∈M.primeFactors,p^M.factorization p := (Nat.prod_factorization_pow_eq_self hm.ne').symm
       _ ∣ ∏ p∈M.primeFactors,p^P.factorization p := prod_dvd_prod_of_dvd _ _ (fun p _ => pow_dvd_pow _ (hf p))
       _ ∣ _ := prod_dvd_prod_of_subset _ _ _ (fun p hpM => mem_filter.mpr
         ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpM,(Nat.dvd_of_mem_primeFactors hpM).trans h,hp.ne'⟩,
          ThetaCompactModulus.smooth hpM⟩)

theorem approximation {T Y : ℕ} (hT : 2≤T) (hl : 1≤log T) (hP : m T∣Y.factorial)
    (V : Window) (x : (ZMod Y.factorial)ˣ) :
    |value Y V T x-cond (m T) (key (m T) x) Y V|≤bias T := by
  let M := ThetaSmoothFiltration.modulus Y.factorial T
  have hm := ThetaSmoothFiltration.pos (Nat.factorial_pos Y) T
  let : NeZero M := ⟨hm.ne'⟩
  have hd : M∣Y.factorial := ThetaSmoothFiltration.divides (Nat.factorial_pos Y) T
  have hh := compact_divides (Nat.factorial_pos _) hP
  change m T∣M at hh
  change |ThetaFiniteExposure.proj (key M) _ x-_|≤_
  rw [project hd]
  have H := difference hT hl hh (ThetaSmoothFiltration.prime_bound _ _) (Nat.mod_lt (x:ZMod Y.factorial).val hm)
    (key_unit hd x) hd V
  change |cond M (key M x) Y V-cond (m T) ((key M x)%(m T)) Y V|≤bias T at H
  simpa only [key,Nat.mod_mod_of_dvd _ hh] using H

/-- Uniform first absolute moment about the arithmetic conditional mean,
normalized by the mass of this individual class. -/
theorem finite : ∀ᶠ T : ℕ in atTop, ∀ Y : ℕ, m T∣Y.factorial →
    ∀ (V : Window) (r : ℕ), r< m T → r.Coprime (m T) →
    let av := cond (m T) r Y V
    (m T).totient*unitMean Y.factorial (fun n => selectClass r (m T) n*|rowModel Y V n-av|)
      ≤ bias T+2*exp total/tilt T := by
  have hl := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ThetaCenteredExposure.centered_weighted,eventually_ge_atTop (2:ℕ),hl.eventually_ge_atTop 1] with T h hT hl
  intro Y hd V r hr hc av
  let M := m T
  let : NeZero M := ⟨(ThetaCompactModulus.positive T).ne'⟩
  let U := (ZMod Y.factorial)ˣ
  let w (x : U) := selectClass r M (x:ZMod Y.factorial).val
  let f (x : U) := rowModel Y V (x:ZMod Y.factorial).val
  let c (x : U) := value Y V T x
  have hw (x : U) : 0≤w x := by dsimp [w,selectClass]; split <;> norm_num
  have hf (x y : U) (he : key (ThetaSmoothFiltration.modulus Y.factorial T) x=key (ThetaSmoothFiltration.modulus Y.factorial T) y) : w x=w y := by
    have he' := ThetaUnitExposure.refine (compact_divides (Nat.factorial_pos _) hd) x y he
    change (if key M x=r then (1:ℝ) else 0)=(if key M y=r then 1 else 0)
    rw [he']
  have ht := tilt_pos (by omega : 0<T)
  have hp := h Y V w hw hf _ (abs_of_pos ht)
  have hn := h Y V w hw hf (-(tilt T)) (by rw [abs_neg,abs_of_pos ht])
  let W := ∑ x : U,w x
  have point (x : U) : w x*(tilt T*|f x-av|)≤w x*(tilt T*bias T)+
      (w x*exp (tilt T*(f x-c x))+w x*exp (-tilt T*(f x-c x))) := by
    by_cases he : key M x=r
    · have hc' := approximation hT hl hd V x
      change |c x-cond M (key M x) Y V|≤bias T at hc'
      rw [he] at hc'
      have htri := (abs_sub_le (f x) (c x) av).trans (add_le_add_right hc' _)
      have H : tilt T*|f x-c x|≤exp (tilt T*(f x-c x))+exp (-tilt T*(f x-c x)) := by
        rcases le_total 0 (f x-c x) with ha|ha
        · rw [abs_of_nonneg ha]; linarith only [add_one_le_exp (tilt T*(f x-c x)),exp_pos (-tilt T*(f x-c x))]
        · rw [abs_of_nonpos ha]; linarith only [add_one_le_exp (-tilt T*(f x-c x)),exp_pos (tilt T*(f x-c x))]
      apply (mul_le_mul_of_nonneg_left (by linarith only [H,mul_le_mul_of_nonneg_left htri ht.le] :
        tilt T*|f x-av|≤tilt T*bias T+(exp (tilt T*(f x-c x))+exp (-tilt T*(f x-c x)))) (hw x)).trans_eq
      ring
    · have hx : w x=0 := if_neg he
      simp [hx]
  have HH := sum_le_sum (s:=univ) (fun x _ => point x)
  simp only [sum_add_distrib,←sum_mul] at HH
  change (∑ x : U,w x*exp (tilt T*(f x-c x)))≤exp total*W at hp
  change (∑ x : U,w x*exp (-tilt T*(f x-c x)))≤exp total*W at hn
  have hsum : tilt T*(∑ x : U,w x*|f x-av|)≤W*(tilt T*bias T)+2*exp total*W := by
    calc _ = ∑ x : U,w x*(tilt T*|f x-av|) := by
               rw [mul_sum]; exact sum_congr rfl (fun _ _ => by ring)
         _ ≤ W*(tilt T*bias T)+((∑ x : U,w x*exp (tilt T*(f x-c x)))+(∑ x : U,w x*exp (-tilt T*(f x-c x)))) := HH
         _ ≤ W*(tilt T*bias T)+(exp total*W+exp total*W) := add_le_add_right (add_le_add hp hn) _
         _ = _ := by ring
  have hunit := (unitMean_lift hd (selectClass_mod r M)).trans (unit_class hr hc)
  have hφ : 0<(M.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos M)
  have hQ : 0<(Y.factorial.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.factorial_pos _)
  change W/Y.factorial.totient=1/(M.totient:ℝ) at hunit
  field_simp at hunit
  change (M.totient:ℝ)*((∑ x : U,w x*|f x-av|)/Y.factorial.totient)≤_
  rw [←mul_div_assoc,div_le_iff₀ hQ]
  apply (le_of_mul_le_mul_left (a:=tilt T) _ ht)
  calc _ ≤ (M.totient:ℝ)*(W*(tilt T*bias T)+2*exp total*W) := (by linarith only [mul_le_mul_of_nonneg_left hsum hφ.le])
       _ = _ := by rw [←hunit]; field_simp

#print axioms approximation
#print axioms finite
end
end Arxiv.«2501.03234».ThetaClassConcentration
