import ThetaFiberModelTransfer
import ThetaMovingPrimeModelError

/-! From a one-fiber model mean and the original prime variance to actual prime excursions. -/
namespace Arxiv.«2501.03234».ThetaFiberSecondMoment
open Finset Filter Real ThetaFiberDiscrepancy ThetaConditionalRows ThetaPrimeTailTransfer ThetaIdentityModels ThetaIdentityFiber
noncomputable section

theorem transfer : ∃ C : ℝ,0<C ∧ ∀ {N Y l b : ℕ} (s : Finset ℕ) (v : ℕ → ℝ) {M δ z J α : ℝ},
    2≤N → 0 < l → b < l → b.Coprime l → l≤Y → Y≤N → 0≤M → 0≤δ → |z|=1 →
    (∀ p∈s,p.Prime ∧ N^56≤p ∧ p≤N^64) → (∀ p∈s,1/2 ≤ v p ∧ v p ≤ 1) →
    OnClass s v l b l M δ → (∀ d∈Icc 2 Y,OnClass s v l b (l*d) M δ) →
    let w := M/l.totient
    δ≤w → Y*(l*(3*Z*(1+log Y)*δ))≤w → (N:ℝ)^64/(log N*(Y:ℝ)^(1/128:ℝ))≤w →
    letI : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
    J ≤ z*(l.totient*unitMean Y.factorial (fun n => selectClass b l n*model Y N n)) →
    0 ≤ α → 4*α+C ≤ (8/π^2)*J →
    (w*α)^2 ≤ ((s.filter (fun p => p%l=b ∧ α ≤ z*((S p:ℝ)/p-log p/2))).card:ℝ)*(∑ p∈s,((S p:ℝ)/p-log p/2)^2) := by
  classical
  obtain ⟨D,B,hD,hB,H⟩ := ThetaMovingPrimeModelError.square
  let c := 8/π^2
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨c+2+4*D+B,by positivity,?_⟩
  intro N Y l b s v M δ z J α hN hl hb hbc hlY hYN hM hδ hz hs hv hcl hrows w hδw herr htail hJ hα hfit
  let : NeZero Y.factorial := ⟨Nat.factorial_ne_zero _⟩
  let Dset := s.filter (fun p => p%l=b)
  let R (p : ℕ) := (S p:ℝ)/p-log p/2
  let f := model Y N
  let e (p : ℕ) := R p-c*f p
  have hφ := Nat.cast_pos (α:=ℝ).mpr (Nat.totient_pos.mpr hl)
  have hw : 0≤w := div_nonneg hM hφ.le
  have hmass : (∑ p∈Dset,v p) ≤ 2*w := by
    have ha := (abs_le.mp (hcl b hb (Nat.mod_eq_of_lt hb))).2
    rw [if_pos hbc] at ha
    change (∑ p∈Dset,v p)-w ≤ δ at ha;linarith
  have hcard : (Dset.card:ℝ) ≤ 4*w := by
    have hh : ∑ _p∈Dset,(1:ℝ) ≤ ∑ p∈Dset,2*v p := sum_le_sum (fun p hp => by linarith only [(hv p (mem_filter.mp hp).1).1])
    rw [←mul_sum] at hh;simp only [sum_const,nsmul_eq_mul,mul_one] at hh;linarith
  have hvar := H hN (by omega : 1≤Y) hYN Dset (fun p hp => hs p (mem_filter.mp hp).1)
  have hE : (∑ p∈Dset,(e p)^2) ≤ (4*D+B)*w := by
    change (∑ p∈Dset,(e p)^2) ≤ _ at hvar
    rw [mul_div_assoc] at hvar;nlinarith only [hvar,mul_le_mul_of_nonneg_left hcard hD.le,mul_le_mul_of_nonneg_left htail hB]
  have hdiff : (∑ p∈Dset,v p*(c*(z*f p)-z*R p)) ≤ (2+4*D+B)*w := by
    calc _ ≤ ∑ p∈Dset,(v p+(e p)^2) := by
           apply sum_le_sum;intro p hp
           have ⟨hlo,hhi⟩ := hv p (mem_filter.mp hp).1
           have he : c*(z*f p)-z*R p ≤ |e p| := calc
             _ ≤ |z*(-e p)| := by rw [show c*(z*f p)-z*R p=z*(-e p) by dsimp [e];ring];exact le_abs_self _
             _ = _ := by rw [abs_mul,hz,one_mul,abs_neg]
           have ha : |e p| ≤ 1+(e p)^2 := by nlinarith only [sq_nonneg (|e p|-1/2),sq_abs (e p)]
           nlinarith only [mul_le_mul_of_nonneg_left (he.trans ha) (by linarith only [hlo] : 0≤v p),mul_le_mul_of_nonneg_right hhi (sq_nonneg (e p))]
         _ ≤ _ := by rw [sum_add_distrib];linarith only [hE,hmass]
  have hm := ThetaFiberModelTransfer.selected_model (V:=N) hl hlY hδ hrows
  have hfs : (∑ n∈s,v n*(selectClass b l n*model Y N n))=∑ n∈Dset,v n*f n := by
    rw [sum_filter];apply sum_congr rfl;intro n _;by_cases he : n%l=b <;> simp [selectClass,he,f]
  rw [hfs] at hm
  let u := unitMean Y.factorial (fun n => selectClass b l n*model Y N n)
  have hscale : w*(l.totient:ℝ)=M := by dsimp [w];field_simp
  have hmean : w*J ≤ z*(M*u) := by
    calc _ ≤ w*(z*(l.totient*u)) := mul_le_mul_of_nonneg_left hJ hw
         _ = _ := by rw [←hscale];ring
  have hclose : |z*(∑ n∈Dset,v n*f n)-z*(M*u)| ≤ w := by rw [←mul_sub,abs_mul,hz,one_mul];exact hm.trans herr
  have hdiff' : c*(z*∑ n∈Dset,v n*f n)-(∑ n∈Dset,v n*(z*R n)) ≤ (2+4*D+B)*w := by
    apply le_trans _ hdiff;apply le_of_eq
    rw [mul_sum,mul_sum,←sum_sub_distrib];apply sum_congr rfl;intros;ring
  let G := Dset.filter (fun p => α ≤ z*R p)
  have hupper : (∑ n∈Dset,v n*(z*R n)) ≤ 2*w*α+∑ p∈G,|R p| := by
    calc _ ≤ ∑ n∈Dset,(v n*α+if α ≤ z*R n then |R n| else 0) := by
           apply sum_le_sum;intro p hp;obtain ⟨hlo,hhi⟩ := hv p (mem_filter.mp hp).1
           have h₀ : 0 ≤ v p := by linarith
           by_cases he : α ≤ z*R p
           · rw [if_pos he]
             have ha : z*R p ≤ |R p| := (le_abs_self _).trans_eq (by rw [abs_mul,hz,one_mul])
             linarith only [mul_le_mul hhi ha (hα.trans he) zero_le_one,mul_nonneg h₀ hα]
           · rw [if_neg he,add_zero];exact mul_le_mul_of_nonneg_left (le_of_not_ge he) h₀
         _ ≤ _ := by
           rw [sum_add_distrib,←sum_mul,←sum_filter];exact add_le_add (mul_le_mul_of_nonneg_right hmass hα) le_rfl
  have hg : G=s.filter (fun p => p%l=b ∧ α ≤ z*((S p:ℝ)/p-log p/2)) := by ext p;simp [G,Dset,R,and_assoc]
  rw [←hg]
  have hmodel : w*J-w ≤ z*∑ n∈Dset,v n*f n := by linarith only [(abs_le.mp hclose).1,hmean]
  change 4*α+(c+2+4*D+B) ≤ c*J at hfit
  have hfirst : w*α ≤ ∑ p∈G,|R p| := by
    nlinarith only [hupper,hdiff',mul_le_mul_of_nonneg_left hmodel hc.le,mul_le_mul_of_nonneg_left hfit hw,mul_nonneg hw hα]
  have hcs := sum_mul_sq_le_sq_mul_sq G (fun _ => (1:ℝ)) (fun p => |R p|)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,sq_abs] at hcs
  have hGs : G⊆s := (filter_subset _ _).trans (filter_subset _ _)
  exact ((pow_le_pow_left₀ (mul_nonneg hw hα) hfirst 2).trans hcs).trans (mul_le_mul_of_nonneg_left
    (sum_le_sum_of_subset_of_nonneg hGs (fun p _ _ => sq_nonneg (R p))) (Nat.cast_nonneg _))

#print axioms transfer
end
end Arxiv.«2501.03234».ThetaFiberSecondMoment
