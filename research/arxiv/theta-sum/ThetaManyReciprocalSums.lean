import ThetaResonantLengths
import ThetaBourgainGaraev

/-! Under the Bourgain–Garaev estimate, a small theta value forces simultaneous
large reciprocal sums at a growing number of distinct prefix lengths. -/
namespace Arxiv.«2501.03234».ThetaManyReciprocalSums
open Real Filter ThetaBourgainGaraev ThetaResonanceScales ThetaResonantBlock
open ThetaResonantCount ThetaResonantLengths
noncomputable section

private theorem cost {c u v : ℝ} (hc : 1≤c) (hu : 1≤u) (hv : 1≤v) :
    let A := (5*c*u*v^4)^((2:ℝ)/3)
    1≤A ∧ (5*v)*(c*u*v^3) = A*sqrt A ∧
    A = (5*c)^((2:ℝ)/3)*u^((2:ℝ)/3)*v^((8:ℝ)/3) := by
  let x := 5*c*u*v^4
  have hx : 1≤x := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith : 1≤5*c) hu) (one_le_pow₀ hv)
  have hx₀ : 0<x := by linarith
  change 1≤x^((2:ℝ)/3) ∧ _ = x^((2:ℝ)/3)*sqrt (x^((2:ℝ)/3)) ∧ _
  refine ⟨one_le_rpow hx (by norm_num),?_,?_⟩
  · rw [sqrt_eq_rpow,←rpow_mul hx₀.le,←rpow_add hx₀]
    norm_num
    ring
  · rw [mul_rpow (by positivity) (by positivity),mul_rpow (by positivity) (by positivity),
      ←rpow_natCast_mul (by linarith : 0≤v)]
    norm_num

private theorem depth_bound {p : ℕ} (hp : 0<p) (ht : 1≤depth p) :
    log (p:ℝ) ≤ 2*(depth p:ℝ) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1<2) p
  change p<2^(depth p+1) at h
  have hh := log_le_log (Nat.cast_pos.mpr hp) (show (p:ℝ) ≤ (2:ℝ)^(depth p+1) by exact_mod_cast h.le)
  rw [log_pow,Nat.cast_succ] at hh
  have hz := mul_le_mul_of_nonneg_left (show log 2 ≤ 1 by linarith [log_two_lt_d9])
    (show 0≤(depth p:ℝ)+1 by positivity)
  have ht' : (1:ℝ)≤depth p := by exact_mod_cast ht
  linarith

theorem many_levels (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ (levels p (lowerLevel p) (depth p)).card := by
  obtain ⟨c,hc,hest⟩ := estimate
  let d := (5*c)^((2:ℝ)/3)
  have hd : 0<d := by dsimp [d];positivity
  refine ⟨1/(4194304*d),by positivity,?_⟩
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hest,scales,hlog.eventually_ge_atTop 1,
    (tendsto_log_atTop.comp hlog).eventually_ge_atTop 1] with p he H hu hv
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  let u := log (p:ℝ)
  let v := log u
  change 1≤u at hu
  change 1≤v at hv
  let A := (5*c*u*v^4)^((2:ℝ)/3)
  obtain ⟨hA,hcost,hdec⟩ := cost hc hu hv
  change 1≤A at hA
  change _=A*sqrt A at hcost
  change A=d*u^((2:ℝ)/3)*v^((8:ℝ)/3) at hdec
  have hu₀ : 0<u := by linarith
  have hv₀ : 0<v := by linarith
  obtain ⟨hp₀,hs₀,hsmall,hst,htfit,hfit,hdepth,_⟩ := H
  have ht₀ : 2 ≤ depth p := by omega
  have ht' : (0:ℝ)<depth p := by exact_mod_cast (show 0<depth p by omega)
  have hht : (harmonic (depth p):ℝ)+2 ≤ 5*v := by
    have h := log_le_log ht' hdepth
    rw [log_mul (by norm_num) hu₀.ne'] at h
    change log (depth p:ℝ) ≤ log 2+v at h
    linarith [harmonic_le_one_add_log (depth p), log_two_lt_d9]
  have hK : 1≤c*u*v^3 := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hc hu) (one_le_pow₀ hv)
  have hKA := (mul_le_mul_of_nonneg_right hht (by linarith only [hK] : 0≤c*u*v^3)).trans hcost.le
  have hpr := Nat.odd_iff.mp ho
  have hA₀ : 0<A := by linarith
  have ht := count hA₀ htfit hst hsmall (small_sum_forces_triangle hpr hp₀ hS)
    (fun i hi => peak hpr hi ht₀ (by omega) hK hA hKA he)
  have hh := (div_le_iff₀ (by positivity)).mp ht
  have hdu := depth_bound hp.pos (by omega : 1 ≤ depth p)
  change u ≤ _ at hdu
  rw [hdec] at hh
  have hu' : u^((1:ℝ)/3)*u^((2:ℝ)/3)=u := by rw [←rpow_add hu₀];norm_num
  change (1/(4194304*d))*u^((1:ℝ)/3)/v^((8:ℝ)/3) ≤ _
  apply (div_le_iff₀ (rpow_pos_of_pos hv₀ _)).mpr
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_iff₀ (by positivity)).mpr
  apply le_of_mul_le_mul_right _ (rpow_pos_of_pos hu₀ ((2:ℝ)/3))
  rw [hu']
  nlinarith only [hdu,hh]

theorem many (estimate : InitialSumEstimate) : ∃ b : ℝ, 0<b ∧ ∀ δ : ℝ, 0<δ →
    ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      (S p:ℝ) ≤ (p:ℝ)*log p/100 →
        ∃ E : Finset ℕ, E ⊆ lengths p δ ∧ separated E ∧
          b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3) ≤ E.card := by
  obtain ⟨c,hc,H⟩ := many_levels estimate
  refine ⟨c/3,by positivity,?_⟩
  intro δ hδ
  filter_upwards [H,counted hδ] with p hsize hcnt
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  intro hS
  obtain ⟨E,hE,hs,hcard⟩ := hcnt hp ho
  refine ⟨E,hE,hs,?_⟩
  have h : ((levels p (lowerLevel p) (depth p)).card:ℝ) ≤ 3*(E.card:ℝ) := by exact_mod_cast hcard
  have ht := (hsize hp ho hS).trans h
  calc
    _ = (c*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3))/3 := by ring
    _ ≤ _ := (div_le_iff₀ (by norm_num)).mpr (by linarith only [ht])

/-- It is enough to rule out a growing family of separated large sums. -/
theorem sparse_implies_growth (estimate : InitialSumEstimate) {δ : ℝ} (hδ : 0<δ)
    (sparse : ∀ b : ℝ, 0<b → ∀ᶠ p : ℕ in atTop, ∀ hp : p.Prime, _root_.Odd p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ E : Finset ℕ, E ⊆ lengths p δ → separated E →
        (E.card:ℝ) < b*(log p)^((1:ℝ)/3)/(log (log p))^((8:ℝ)/3))
    (n : ℕ) : type_of% (conjecture_4_4 n) := by
  obtain ⟨b,hb,H⟩ := many estimate
  have hlog := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [H δ hδ,sparse b hb,hlog.eventually_gt_atTop (100*(n:ℝ))] with p h hs hu
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hS : (p:ℝ)*log p/100 < (S p:ℝ) := by
    by_contra! hsmall
    obtain ⟨E,hE,hsep,hm⟩ := h hp ho hsmall
    exact (not_lt_of_ge hm) (hs hp ho E hE hsep)
  change 100*(n:ℝ) < log (p:ℝ) at hu
  have hh := mul_lt_mul_of_pos_right hu (Nat.cast_pos.mpr hp.pos : 0<(p:ℝ))
  exact_mod_cast (show (n:ℝ)*(p:ℝ)<(S p:ℝ) by linarith)

#print axioms many_levels
#print axioms many
#print axioms sparse_implies_growth
end
end Arxiv.«2501.03234».ThetaManyReciprocalSums
