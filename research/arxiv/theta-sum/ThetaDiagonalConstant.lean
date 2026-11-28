import ThetaCotangentMidpoints
import ThetaOffDiagonalSigns
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
/-! Second-order asymptotics of the divisible theta diagonal. -/
namespace Arxiv.«2501.03234».ThetaDiagonalConstant
open Finset Filter ThetaDivisibleDiagonal ThetaPrimeDensity ThetaOffDiagonalSigns
open scoped Topology

private lemma odd_harmonic_identity (n : ℕ) : oddHarmonic n=(harmonic (2*n):ℝ)-(harmonic n:ℝ)/2 := by
  induction n with
  | zero => simp [oddHarmonic,harmonic]
  | succ n ih =>
    rw [show oddHarmonic (n+1)=oddHarmonic n+(2*(n:ℝ)+1)⁻¹ from sum_range_succ ..,ih,
      show 2*(n+1)=2*n+1+1 by omega,harmonic_succ,harmonic_succ,harmonic_succ]
    push_cast
    have h : (2*(n:ℝ)+1+1)⁻¹=((n:ℝ)+1)⁻¹/2 := by rw [show 2*(n:ℝ)+1+1=2*(n+1) by ring,mul_inv_rev]; ring
    rw [h]; ring

theorem odd_harmonic_constant : Tendsto (fun n : ℕ => oddHarmonic n-Real.log (2*(n:ℝ))/2)
    atTop (𝓝 ((Real.eulerMascheroniConstant+Real.log 2)/2)) := by
  have ht : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    apply tendsto_atTop.mpr; intro b; filter_upwards [eventually_ge_atTop b] with n h; omega
  have h := (Real.tendsto_harmonic_sub_log.comp ht).sub (Real.tendsto_harmonic_sub_log.div_const 2)
  have h' := h.add_const (Real.log 2/2)
  convert h'.congr' ?_ using 1
  · ring
  · filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp; rw [odd_harmonic_identity]; push_cast; rw [Real.log_mul (by norm_num) (by positivity)]; ring
private lemma multiplier_bracket {u : ℕ} (hu : 0<u) (p : ℕ) :
    p≤(2*multiplierCount p u+1)*u ∧ 2*multiplierCount p u*u≤p+u := by
  let k := (p-1)/u
  have h₁ : k*u≤p := (Nat.div_mul_le_self _ _).trans (Nat.sub_le ..)
  have h₂ : p≤(k+1)*u := by
    have H := (Nat.div_lt_iff_lt_mul hu).mp (show (p-1)/u<k+1 from Nat.lt_succ_self k)
    omega
  have H : 2*multiplierCount p u≤k+1 ∧ k≤2*multiplierCount p u := by dsimp [k,multiplierCount]; omega
  refine ⟨h₂.trans (Nat.mul_le_mul_right u (by omega)), (Nat.mul_le_mul_right u H.1).trans ?_⟩
  rw [Nat.add_mul,one_mul]; omega

private lemma multiplier_limit {u : ℕ} (hu : 0<u) :
    Tendsto (fun p : ℕ => (2*(multiplierCount p u:ℝ)*u)/(p:ℝ)) atTop (𝓝 1) := by
  have lim : Tendsto (fun p : ℕ => (u:ℝ)/(p:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have lo := tendsto_const_nhds (x:=(1:ℝ)) |>.sub lim
  have hi := tendsto_const_nhds (x:=(1:ℝ)) |>.add lim
  rw [sub_zero] at lo; rw [add_zero] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' lo hi <;>
    filter_upwards [eventually_ge_atTop 1] with p hp
  · have H : (p:ℝ)≤(2*(multiplierCount p u:ℝ)+1)*u := by exact_mod_cast (multiplier_bracket hu p).1
    have hp' : 0<(p:ℝ) := by exact_mod_cast hp
    rw [le_div_iff₀ hp']; field_simp
    nlinarith
  · have H : 2*(multiplierCount p u:ℝ)*u≤(p:ℝ)+u := by exact_mod_cast (multiplier_bracket hu p).2
    have hp' : 0<(p:ℝ) := by exact_mod_cast hp
    rw [div_le_iff₀ hp']; field_simp
    nlinarith

private lemma multiplier_atTop {u : ℕ} (hu : 0<u) : Tendsto (fun p => multiplierCount p u) atTop atTop := by
  apply tendsto_atTop.mpr; intro b
  filter_upwards [eventually_ge_atTop ((2*b+1)*u+1)] with p hp
  have H := (multiplier_bracket hu p).1
  by_contra! hn
  have HH := Nat.mul_le_mul_right u (show 2*multiplierCount p u+1≤2*b+1 by omega)
  omega

private lemma odd_row_constant {u : ℕ} (hu : 0<u) : Tendsto
    (fun p : ℕ => oddHarmonic (multiplierCount p u)-Real.log p/2)
    atTop (𝓝 ((Real.eulerMascheroniConstant+Real.log 2-Real.log u)/2)) := by
  have H := odd_harmonic_constant.comp (multiplier_atTop hu)
  have L := (multiplier_limit hu).log (by norm_num)
  rw [Real.log_one] at L
  have A := (H.add (L.div_const 2)).sub_const (Real.log u/2)
  convert A.congr' ?_ using 1
  · ring
  · filter_upwards [eventually_ge_atTop 1,(tendsto_atTop.mp (multiplier_atTop hu) 1)] with p hp hm
    have hp' : (p:ℝ)≠0 := by positivity
    have hm' : (multiplierCount p u:ℝ)≠0 := by positivity
    have hu' : (u:ℝ)≠0 := by positivity
    dsimp; rw [Real.log_div (by positivity) hp',Real.log_mul (by positivity) hu']; ring

private lemma normalized_inner {u : ℕ} (hu : 0<u) :
    Tendsto (fun p : ℕ => (Real.pi*u/(p:ℝ))*∑ k∈range (multiplierCount p u),
      (ThetaCotangentTriangle.weight p (u*(2*k+1))-ThetaReciprocalCutoff.linearWeight p (u*(2*k+1))))
    atTop (𝓝 (Real.log (2/Real.pi))) := by
  let y (p : ℕ) := Real.pi*u/(2*(p:ℝ))
  have hy : Tendsto y atTop (𝓝 0) := by
    have H : Tendsto (fun p : ℕ => (Real.pi*u/2)/(p:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply H.congr'; exact Filter.Eventually.of_forall (fun p => by dsimp [y]; ring)
  have he : Tendsto (fun p : ℕ => 2*(multiplierCount p u:ℝ)*y p) atTop (𝓝 (Real.pi/2)) := by
    have H := (multiplier_limit hu).mul_const (Real.pi/2)
    rw [one_mul] at H
    apply H.congr'; exact Filter.Eventually.of_forall (fun p => by dsimp [y]; ring)
  have hpos : ∀ᶠ p : ℕ in atTop, 0<y p := by
    filter_upwards [eventually_ge_atTop 1] with p hp; dsimp [y]; positivity
  apply (ThetaCotangentMidpoints.odd_mesh_correction hpos hy he).congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hfac : 2*y p=Real.pi*u/p := by dsimp [y]; ring
  rw [hfac]; congr 1; apply sum_congr rfl
  intro k _
  change _ = (Real.tan (Real.pi*(u*(2*k+1):ℕ)/(2*(p:ℝ))))⁻¹-2*p/(Real.pi*(u*(2*k+1):ℕ))
  push_cast; rw [Real.tan_eq_sin_div_cos,inv_div]
  have heq : (2*(k:ℝ)+1)*y p=Real.pi*(u*(2*k+1))/(2*(p:ℝ)) := by dsimp [y]; ring
  rw [heq,inv_div]

open ThetaCotangentTriangle ThetaReciprocalCutoff

private lemma outer_weight_error {p u : ℕ} (hu : 0<u) (hp : u<p) :
    |(weight p u-linearWeight p u)*∑ k∈range (multiplierCount p u),weight p (u*(2*k+1))| ≤ p := by
  have hp' := hu.trans hp
  have hu' : (u:ℝ)≠0 := by positivity
  have hwu := weight_pos hu hp
  have hwl : weight p u≤linearWeight p u := weight_upper hu hp
  have hdiag := (abs_le.mp (product_error hu le_rfl hp)).1
  rw [div_self hu'] at hdiag
  have h₁ : (linearWeight p u-weight p u)*weight p u≤1 := by
    nlinarith only [hdiag,mul_nonneg (hwu.le.trans hwl) (sub_nonneg.mpr hwl)]
  have hsum : 0≤∑ k∈range (multiplierCount p u),weight p (u*(2*k+1)) := by
    apply sum_nonneg; intro k hk
    exact (weight_pos (by positivity) ((multiplier_mem hu hp').mp hk)).le
  rw [abs_mul,abs_of_nonpos (sub_nonpos.mpr hwl),abs_of_nonneg hsum,neg_sub,mul_sum]
  have h : (∑ k∈range (multiplierCount p u),(linearWeight p u-weight p u)*weight p (u*(2*k+1)))≤
      ∑ _k∈range (multiplierCount p u),(1:ℝ) := by
    apply sum_le_sum; intro k hk
    exact (mul_le_mul_of_nonneg_left (weight_antitone hu ((multiplier_mem hu hp').mp hk)
      (Nat.le_mul_of_pos_right u (by omega))) (sub_nonneg.mpr hwl)).trans h₁
  apply h.trans
  simp only [sum_const,card_range,nsmul_eq_mul,mul_one]
  exact_mod_cast (show multiplierCount p u≤p by
    have := Nat.div_le_self (p-1) u; dsimp [multiplierCount]; omega)

private noncomputable def cotRowDifference (p u : ℕ) : ℝ :=
  (2/(p:ℝ)^2)*(weight p u*∑ k∈range (multiplierCount p u),weight p (u*(2*k+1))-
    (2*p/Real.pi)^2*((u:ℝ)^2)⁻¹*oddHarmonic (multiplierCount p u))

private lemma cot_row_constant {u : ℕ} (hu : 0<u) :
    Tendsto (fun p => cotRowDifference p u) atTop (𝓝 ((4/(Real.pi^2*u^2))*Real.log (2/Real.pi))) := by
  let A (p : ℕ) := (weight p u-linearWeight p u)*∑ k∈range (multiplierCount p u),weight p (u*(2*k+1))
  have hA : Tendsto (fun p : ℕ => (2/(p:ℝ)^2)*A p) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun p : ℕ => 2/(p:ℝ)) atTop (𝓝 0) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
    filter_upwards [eventually_gt_atTop u] with p hp
    have hp' : 0<(p:ℝ) := by exact_mod_cast hu.trans hp
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ)^2)]
    exact (mul_le_mul_of_nonneg_left (outer_weight_error hu hp) (by positivity)).trans_eq (by field_simp)
  have H := hA.add ((normalized_inner hu).const_mul (4/(Real.pi^2*u^2)))
  rw [zero_add] at H
  apply H.congr'; filter_upwards [eventually_gt_atTop u] with p hp
  have hp' : (p:ℝ)≠0 := by exact_mod_cast (hu.trans hp).ne'
  have hu' : (u:ℝ)≠0 := by positivity
  have hlin : (∑ k∈range (multiplierCount p u),linearWeight p (u*(2*k+1)))=
      linearWeight p u*oddHarmonic (multiplierCount p u) := by
    rw [oddHarmonic,mul_sum]; apply sum_congr rfl; intro k _
    have hk : (2*(k:ℝ)+1)≠0 := by positivity
    dsimp [linearWeight]; push_cast; field_simp
  dsimp only [A,cotRowDifference]
  rw [sum_sub_distrib,hlin]
  unfold linearWeight
  field_simp; ring

private lemma cot_difference_limit : Tendsto
    (fun p : ℕ => divisibleDiagonal p/p-(8/Real.pi^2)*harmonicDiagonal p)
    atTop (𝓝 (Real.log (2/Real.pi)/2)) := by
  let f (p j : ℕ) := if j<p/2 then cotRowDifference p (2*j+1) else 0
  let l (j : ℕ) := (4/(Real.pi^2*(2*(j:ℝ)+1)^2))*Real.log (2/Real.pi)
  have h (j : ℕ) : Tendsto (fun p => f p j) atTop (𝓝 (l j)) := by
    have H := cot_row_constant (u:=2*j+1) (by omega)
    push_cast at H
    apply H.congr'; filter_upwards [eventually_ge_atTop (2*j+2)] with p hp
    simp [f,show j<p/2 by omega]
  have hb : ∀ᶠ p : ℕ in atTop, ∀ j, ‖f p j‖ ≤ 2*((2*(j:ℝ)+1)^2)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with p hp j
    by_cases hj : j<p/2
    · have hp' : (p:ℝ)≠0 := by positivity
      have hu : 2*j+1<p := by omega
      have H := row_linearization (u:=2*j+1) (by omega) hu
      push_cast at H
      dsimp only [f]; rw [if_pos hj,Real.norm_eq_abs,cotRowDifference,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ)^2)]
      push_cast
      apply (mul_le_mul_of_nonneg_left H (by positivity)).trans_eq
      field_simp
    · simp [f,hj]; positivity
  have H := tendsto_tsum_of_dominated_convergence (odd_reciprocal_square.summable.mul_left 2) h hb
  have he : (∑' j,l j)=Real.log (2/Real.pi)/2 := by
    have hh := (odd_reciprocal_square.mul_left ((4/Real.pi^2)*Real.log (2/Real.pi)))
    calc
      _ = _ := (hh.congr_fun (g:=l) (fun j => by simp only [l,div_eq_mul_inv,mul_inv_rev]; ring)).tsum_eq
      _ = _ := by field_simp; ring
  rw [he] at H
  apply H.congr'; filter_upwards [eventually_ge_atTop 1] with p hp
  have hsum := hasSum_sum_of_ne_finset_zero (L:=.unconditional ℕ) (s:=range (p/2)) (f:=f p)
    (by intro j hj; exact if_neg (fun h => hj (mem_range.mpr h)))
  rw [hsum.tsum_eq]
  have hr (j : ℕ) (hj : j∈range (p/2)) : f p j=cotRowDifference p (2*j+1) := if_pos (mem_range.mp hj)
  rw [sum_congr rfl hr]
  simp only [cotRowDifference,← mul_sum,sum_sub_distrib]
  unfold divisibleDiagonal harmonicDiagonal
  push_cast
  simp_rw [mul_assoc ((2*(p:ℝ)/Real.pi)^2),← mul_sum]
  have hp' : (p:ℝ)≠0 := by positivity
  field_simp; ring

/-- The second-order coefficient of the exact divisible cotangent diagonal. -/
noncomputable def diagonalConstant : ℝ := Real.log (2/Real.pi)/2+
  (8/Real.pi^2)*∑' j : ℕ, ((2*(j:ℝ)+1)^2)⁻¹*
    ((Real.eulerMascheroniConstant+Real.log 2-Real.log (2*(j:ℝ)+1))/2)

theorem diagonal_second_order : Tendsto (fun p : ℕ => divisibleDiagonal p/p-Real.log p/2)
    atTop (𝓝 diagonalConstant) := by
  let L (j : ℕ) := (Real.eulerMascheroniConstant+Real.log 2-Real.log (2*(j:ℝ)+1))/2
  have hh := harmonic_diagonal_limit (L:=L) (fun j => by simpa [L] using odd_row_constant (u:=2*j+1) (by omega))
  have H := cot_difference_limit.add (hh.const_mul (8/Real.pi^2))
  apply H.congr'; apply Filter.Eventually.of_forall; intro p
  dsimp; field_simp; ring

/-- A positive fraction of all primes satisfy the predicate along arbitrarily large endpoints. -/
def PositiveUpperPrimeDensity (P : ℕ → Prop) : Prop :=
  ∃ δ : ℝ, 0<δ ∧ ∃ᶠ X : ℕ in atTop, δ*Nat.primeCounting X≤((primeSet P X).card:ℝ)

/-- Discarding finitely many primes preserves positive upper prime density. -/
theorem PositiveUpperPrimeDensity.of_eventually_imp {P Q : ℕ → Prop} (h : ∀ᶠ p : ℕ in atTop, P p → Q p)
    (hP : PositiveUpperPrimeDensity P) : PositiveUpperPrimeDensity Q := by
  classical
  obtain ⟨B,hB⟩ := eventually_atTop.mp h
  obtain ⟨δ,hδ,H⟩ := hP
  obtain ⟨n,hn⟩ := exists_nat_gt (B/(δ/2))
  have hsmall : ∀ᶠ X : ℕ in atTop, (B:ℝ)≤(δ/2)*Nat.primeCounting X := by
    filter_upwards [Nat.tendsto_primeCounting.eventually_ge_atTop n] with X hX
    have h' := (div_lt_iff₀ (half_pos hδ)).mp hn
    have hn' : (n:ℝ)≤Nat.primeCounting X := by exact_mod_cast hX
    linarith only [h',mul_le_mul_of_nonneg_left hn' (half_pos hδ).le]
  refine ⟨δ/2,half_pos hδ,(H.and_eventually hsmall).mono (fun X hh => ?_)⟩
  have hsubset : primeSet P X⊆range B∪primeSet Q X := by
    intro p hp; by_cases hle : B≤p
    · apply mem_union_right
      simp only [primeSet,mem_filter] at hp ⊢
      exact ⟨hp.1,hB p hle hp.2⟩
    · exact mem_union_left _ (mem_range.mpr (lt_of_not_ge hle))
  have hcard := (card_le_card hsubset).trans (card_union_le ..)
  rw [card_range] at hcard
  have hcard' : ((primeSet P X).card:ℝ)≤B+((primeSet Q X).card:ℝ) := by exact_mod_cast hcard
  linarith only [hh.1,hh.2,hcard']

private lemma normalized_excursions {b c : ℝ}
    (hb : Tendsto (fun p : ℕ => divisibleDiagonal p/p-Real.log p/2) atTop (𝓝 b))
    (hc : c<32/(15*Real.pi^2)) :
    PositiveUpperPrimeDensity (fun p => p%24=1 ∧ b+c<(S p:ℝ)/p-Real.log p/2) ∧
    PositiveUpperPrimeDensity (fun p => p%24=17 ∧ (S p:ℝ)/p-Real.log p/2<b-c) := by
  obtain ⟨d,hcd,hD⟩ := exists_between hc
  obtain ⟨H₁,H₂⟩ := S_prime_excursion_densities hD
  constructor
  · apply PositiveUpperPrimeDensity.of_eventually_imp _ H₁
    filter_upwards [hb.eventually_const_lt (show b-(d-c)<b by linarith),eventually_ge_atTop 1] with p hp hp' H
    refine ⟨H.1,?_⟩
    have h : d<((S p:ℝ)-divisibleDiagonal p)/p := (lt_div_iff₀ (by exact_mod_cast hp')).mpr H.2
    rw [sub_div] at h
    linarith
  · apply PositiveUpperPrimeDensity.of_eventually_imp _ H₂
    filter_upwards [hb.eventually_lt_const (show b<b+(d-c) by linarith),eventually_ge_atTop 1] with p hp hp' H
    refine ⟨H.1,?_⟩
    have h : ((S p:ℝ)-divisibleDiagonal p)/p< -d :=
      (div_lt_iff₀ (by exact_mod_cast hp')).mpr (by linarith only [H.2])
    rw [sub_div] at h
    linarith
private lemma no_center_concentration {b c : ℝ}
    (hb : Tendsto (fun p : ℕ => divisibleDiagonal p/p-Real.log p/2) atTop (𝓝 b))
    (hc : c<32/(15*Real.pi^2)) (a : ℝ) :
    PositiveUpperPrimeDensity (fun p => p%8=1 ∧ c < |(S p:ℝ)/p-Real.log p/2-a|) := by
  obtain ⟨hp,hn⟩ := normalized_excursions hb hc
  by_cases h : a≤b
  · apply PositiveUpperPrimeDensity.of_eventually_imp _ hp; apply Eventually.of_forall
    intro p H
    exact ⟨by have := H.1; omega, by linarith only [H.2,h,le_abs_self ((S p:ℝ)/p-Real.log p/2-a)]⟩
  · apply PositiveUpperPrimeDensity.of_eventually_imp _ hn; apply Eventually.of_forall
    intro p H
    exact ⟨by have := H.1; omega, by linarith only [H.2,lt_of_not_ge h,neg_le_abs ((S p:ℝ)/p-Real.log p/2-a)]⟩


/-- The normalized original sum has opposite excursions about the explicit
diagonal constant on sets of positive upper prime density. -/
theorem S_centered_prime_excursions {c : ℝ} (hc : c<32/(15*Real.pi^2)) :
    PositiveUpperPrimeDensity (fun p => p%24=1 ∧ diagonalConstant+c<(S p:ℝ)/p-Real.log p/2) ∧
    PositiveUpperPrimeDensity (fun p => p%24=17 ∧ (S p:ℝ)/p-Real.log p/2<diagonalConstant-c) :=
  normalized_excursions diagonal_second_order hc

/-- No real second coefficient concentrates the prime theta sum, even
when restricted to primes that are one modulo eight. -/
theorem S_prime_no_single_center {c : ℝ} (hc : c<32/(15*Real.pi^2)) (a : ℝ) :
    PositiveUpperPrimeDensity (fun p => p%8=1 ∧ c < |(S p:ℝ)/p-Real.log p/2-a|) :=
  no_center_concentration diagonal_second_order hc a

end Arxiv.«2501.03234».ThetaDiagonalConstant
#print axioms Arxiv.«2501.03234».ThetaDiagonalConstant.odd_harmonic_constant
#print axioms Arxiv.«2501.03234».ThetaDiagonalConstant.diagonal_second_order
#print axioms Arxiv.«2501.03234».ThetaDiagonalConstant.S_centered_prime_excursions
#print axioms Arxiv.«2501.03234».ThetaDiagonalConstant.S_prime_no_single_center

#print axioms Arxiv.«2501.03234».ThetaDiagonalConstant.PositiveUpperPrimeDensity.of_eventually_imp
