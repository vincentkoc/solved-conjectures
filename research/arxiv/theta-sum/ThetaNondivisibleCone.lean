import ThetaReciprocalBlocks
import ThetaDivisibleDiagonal

/-! Cutoffs for the nondivisible pairs in the theta cotangent sum. -/

open Finset

namespace Arxiv.«2501.03234».ThetaNondivisibleCone
private def centered {u : ℕ} (x : ZMod u) : ℤ :=
  if x=0 then 0 else if x.val%2=1 then 1 else -1

private lemma centered_neg {u : ℕ} (hu : u%2=1) (x : ZMod u) :
    centered (-x) = -centered x := by
  let : NeZero u := ⟨by omega⟩
  by_cases hx : x=0
  · simp [hx,centered]
  let : NeZero x := ⟨hx⟩
  simp only [centered,if_neg hx,if_neg (neg_ne_zero.mpr hx),ZMod.val_neg_of_ne_zero x]
  have hl := ZMod.val_lt x
  split_ifs <;> omega

private lemma period_zero {u : ℕ} (hu : u%2=1) (a : ZMod u) :
    ∑ i ∈ range u, centered ((i:ZMod u)*a) = 0 := by
  let : NeZero u := ⟨by omega⟩
  let f (x : ZMod u) := centered (x*a)
  have hn (x : ZMod u) : f (-x) = -f x := by dsimp [f]; rw [neg_mul,centered_neg hu]
  have h := Equiv.sum_comp (Equiv.neg (ZMod u)) f
  change ∑ x : ZMod u, f (-x) = ∑ x, f x at h
  simp_rw [hn,sum_neg_distrib] at h
  have he := (ZMod.finEquiv u).toEquiv.sum_comp f
  rw [← Fin.sum_univ_eq_sum_range]
  change ∑ x : Fin u, f ((x:ℕ):ZMod u) = 0
  have hf (x : Fin u) : f ((x:ℕ):ZMod u) = f ((ZMod.finEquiv u) x) := by
    have hv : ((ZMod.finEquiv u) x).val=x.val := by cases u with | zero => exact Fin.elim0 x | succ u => rfl
    rw [← hv,ZMod.natCast_zmod_val]
  simp_rw [hf]
  change ∑ x : Fin u, f ((ZMod.finEquiv u).toEquiv x) = 0
  rw [he]; omega

private lemma centered_abs_le {u : ℕ} (x : ZMod u) : |centered x|≤1 := by
  dsimp [centered]; split_ifs <;> norm_num

private lemma prefix_bound {u : ℕ} (hu : u%2=1) (a : ZMod u) (n : ℕ) :
    |∑ i ∈ range n, centered ((i:ZMod u)*a)| ≤ (u:ℤ) := by
  have hu₀ : 0<u := by omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : u≤n
    · have he := ih (n-u) (by omega)
      have hw := period_zero hu a
      have hsum := sum_range_add (fun i : ℕ => centered ((i:ZMod u)*a)) u (n-u)
      rw [Nat.add_sub_of_le h,hw,zero_add] at hsum
      simp only [Nat.cast_add,ZMod.natCast_self,zero_add] at hsum
      rwa [hsum]
    · apply (abs_sum_le_sum_abs ..).trans
      calc _ ≤ ∑ i ∈ range n, (1:ℤ) := sum_le_sum (fun i _ => centered_abs_le _)
           _ ≤ (u:ℤ) := by simp; omega

open ThetaCotangentTriangle (reciprocalSign)

private lemma sign_eq_centered {p u : ℕ} (hc : p.Coprime u) (v : ℕ) :
    (if u∣v then (0:ℤ) else reciprocalSign p u v) =
      centered ((v:ZMod u)*(p:ZMod u)⁻¹) := by
  have hz : (v:ZMod u)*(p:ZMod u)⁻¹ = 0 ↔ u∣v := by
    constructor
    · intro h
      have hh := congrArg (·*(p:ZMod u)) h
      rw [mul_assoc,mul_comm ((p:ZMod u)⁻¹),ZMod.coe_mul_inv_eq_one p hc,mul_one,zero_mul] at hh
      exact (ZMod.natCast_eq_zero_iff v u).mp hh
    · intro h; rw [(ZMod.natCast_eq_zero_iff v u).mpr h,zero_mul]
  simp only [centered,hz,reciprocalSign]

/-- On an odd arithmetic progression beginning at a multiple of u, the signed
nondivisible part has discrepancy at most u, uniformly in the length. -/
theorem nondivisible_prefix {p u s : ℕ} (hu : u%2=1) (hc : p.Coprime u) (hs : u∣s) (n : ℕ) :
    |∑ i ∈ range n, (if u∣s+2*i then (0:ℤ) else reciprocalSign p u (s+2*i))| ≤ (u:ℤ) := by
  simp_rw [sign_eq_centered hc]
  have h (i : ℕ) : ((↑(s+2*i : ℕ):ZMod u)*(p:ZMod u)⁻¹) =
      (i:ZMod u)*(2*(p:ZMod u)⁻¹) := by
    push_cast
    rw [(ZMod.natCast_eq_zero_iff s u).mpr hs,zero_add]
    ring
  simp_rw [h]
  exact prefix_bound hu _ n

open ThetaCotangentTriangle (weight quotientSign)
open ThetaReciprocalCutoff (weight_le weight_mass weighted_abs discrepancy kloosterman kloosterman_bound kernelDiscrepancy
  elementary_discrepancy reciprocal_interval_of_kernel)

/-- Reciprocal sign with the divisible pairs removed. -/
noncomputable def nondivSign (p u v : ℕ) : ℤ :=
  if u ∣ v then 0 else reciprocalSign p u v

/-- The weighted tail of one numerator row beyond an odd multiple Ku costs at most p/K. -/
theorem numerator_tail {p u K l : ℕ} (hu : u%2=1) (hK : 0<K) (hc : p.Coprime u)
    (hl : 2*l+1=K*u) :
    |∑ k ∈ Ico l (p/2), weight p (2*k+1)*(nondivSign p u (2*k+1):ℝ)| ≤ (p:ℝ)/K := by
  by_cases h₀ : l<p/2
  · rw [sum_Ico_eq_sum_range]
    let w (i : ℕ) := weight p (2*(l+i)+1)
    let g (i : ℕ) : ℝ := nondivSign p u (2*(l+i)+1)
    have hpre (m : ℕ) (_ : m≤p/2-l) : |∑ i ∈ range m, g i| ≤ (u:ℝ) := by
      have h := nondivisible_prefix hu hc (s:=2*l+1) (hl ▸ dvd_mul_left u K) m
      have he (i : ℕ) : 2*(l+i)+1 = 2*l+1+2*i := by omega
      dsimp only [g,nondivSign]; simp_rw [he]
      exact_mod_cast h
    have H := weighted_abs w g (Nat.cast_nonneg u)
      (ThetaCotangentTriangle.weight_pos (by omega) (by dsimp [w]; omega)).le
      (fun i hi => (ThetaCotangentTriangle.weight_pos (by omega) (by omega)).le)
      (fun i hi => ThetaCotangentTriangle.weight_antitone (by omega) (by omega) (by omega)) hpre
    apply H.trans
    have hh : w 0 ≤ (p:ℝ)/(K*u) := by
      dsimp [w]; rw [hl]; exact_mod_cast weight_le (p:=p) (u:=K*u) (by omega) (by omega)
    have hur : 0<(u:ℝ) := by exact_mod_cast (show 0<u by omega)
    have hKr : 0<(K:ℝ) := by exact_mod_cast hK
    exact (mul_le_mul_of_nonneg_left hh hur.le).trans_eq (by field_simp)
  · rw [Ico_eq_empty_of_le (by omega : p/2≤l),sum_empty,abs_zero]
    positivity

private lemma divisor_count (s v n : ℕ) (hv : 0<v) :
    ((range n).filter (fun i => s+2*i∣v)).card ≤ v.divisors.card := by
  apply card_le_card_of_injOn (fun i => s+2*i)
  · intro i hi
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hi).2,hv.ne'⟩
  · intro i _ j _ he; dsimp at he; omega

private lemma denominator_prefix {p : ℕ} [Fact p.Prime] {B : ℝ} (hB : 0≤B)
    (bound : ∀ a b : ZMod p,b≠0 → ‖kloosterman a b‖≤B) (hp : p%2=1)
    (l k n : ℕ) (hk : k<p/2) (hn : n≤p/2-l) :
    |∑ i ∈ range n, (nondivSign p (2*(l+i)+1) (2*k+1):ℝ)| ≤
      kernelDiscrepancy p B + 2*(p.sqrt:ℝ) := by
  let v := 2*k+1
  let u (i : ℕ) := 2*(l+i)+1
  let f (i : ℕ) : ℝ := quotientSign p (u i) v
  have hv : (v:ZMod p) ≠ 0 := by
    intro h; have hh := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt (show v<p by dsimp [v]; omega),ZMod.val_zero] at hh
    dsimp [v] at hh; omega
  have he (i : ℕ) : u i = 2*l+1+2*i := by dsimp [u]; omega
  have hfull : |∑ i ∈ range n, f i| ≤ kernelDiscrepancy p B := by
    dsimp only [f]; simp_rw [he]
    have h := reciprocal_interval_of_kernel hB bound hp (2*l+1) v n hv (by omega) (by intro i hi; constructor <;> omega)
    simpa only [Int.cast_sum] using h
  let D := (range n).filter (fun i => u i ∣ v)
  have hc : D.card ≤ 2*p.sqrt := by
    have hh : D.card ≤ v.divisors.card := by
      dsimp only [D]; simp_rw [he]; exact divisor_count _ _ _ (by dsimp [v]; omega)
    exact hh.trans ((ThetaReciprocalBlocks.divisors_card_sqrt v).trans
      (Nat.mul_le_mul_left _ (Nat.sqrt_le_sqrt (by dsimp [v]; omega))))
  have hd : |∑ i ∈ D, f i| ≤ (2*(p.sqrt:ℝ)) := by
    apply (abs_sum_le_sum_abs ..).trans
    have hone (i : ℕ) : |f i|=(1:ℝ) := by dsimp [f,quotientSign]; split_ifs <;> norm_num
    simp_rw [hone]; simpa using (show (D.card:ℝ)≤2*(p.sqrt:ℝ) by exact_mod_cast hc)
  have hsplit : ∑ i ∈ range n, (nondivSign p (u i) v:ℝ) =
      (∑ i ∈ range n, f i) - ∑ i ∈ D, f i := by
    rw [show D=(range n).filter (fun i => u i∣v) by rfl,sum_filter,← sum_sub_distrib]
    apply sum_congr rfl; intro i hi
    dsimp only [f,nondivSign]
    split_ifs with h
    · simp
    · have hh := mem_range.mp hi
      rw [ThetaCotangentTriangle.quotient_eq_reciprocal_of_not_dvd hp (by dsimp [u]; omega)
        (by dsimp [v]; omega) h (by dsimp [u]; omega) (by dsimp [v]; omega),sub_zero]
  change |∑ i ∈ range n, (nondivSign p (u i) v:ℝ)| ≤ _
  rw [hsplit]
  exact (abs_sub _ _).trans (add_le_add hfull hd)


private lemma denominator_tail {p : ℕ} [Fact p.Prime] {B : ℝ} (hB : 0≤B)
    (bound : ∀ a b : ZMod p,b≠0 → ‖kloosterman a b‖≤B) (hp : p%2=1)
    {J k : ℕ} (hk : k<p/2) :
    |∑ j ∈ Ico J (p/2), weight p (2*j+1)*(nondivSign p (2*j+1) (2*k+1):ℝ)| ≤
      (kernelDiscrepancy p B + 2*(p.sqrt:ℝ))*((p:ℝ)/(2*J+1)) := by
  have hD : 0≤kernelDiscrepancy p B+2*(p.sqrt:ℝ) := by unfold kernelDiscrepancy; positivity
  by_cases h₀ : J<p/2
  · rw [sum_Ico_eq_sum_range]
    let w (i : ℕ) := weight p (2*(J+i)+1)
    let g (i : ℕ) : ℝ := nondivSign p (2*(J+i)+1) (2*k+1)
    have H := weighted_abs w g hD
      (ThetaCotangentTriangle.weight_pos (by omega) (by dsimp [w]; omega)).le
      (fun i hi => (ThetaCotangentTriangle.weight_pos (by omega) (by omega)).le)
      (fun i hi => ThetaCotangentTriangle.weight_antitone (by omega) (by omega) (by omega))
      (fun m hm => denominator_prefix hB bound hp J k m hk hm)
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ hD
    simpa [w] using weight_le (p:=p) (u:=2*J+1) (by omega) (by omega)
  · rw [Ico_eq_empty_of_le (by omega : p/2≤J),sum_empty,abs_zero]
    positivity

/-- Denominator-limited cotangent sum with the divisible pairs masked. -/
noncomputable def strip (p J : ℕ) : ℝ :=
  2/(p:ℝ) * ∑ j ∈ range J, weight p (2*j+1) *
    ∑ k ∈ range (p/2), weight p (2*k+1)*(nondivSign p (2*j+1) (2*k+1):ℝ)

/-- Cotangent sum inside u < 2J and v < Ku, for odd K. -/
noncomputable def cotCone (p J K : ℕ) : ℝ :=
  2/(p:ℝ) * ∑ j ∈ range J, weight p (2*j+1) *
    ∑ k ∈ range (K*(2*j+1)/2), weight p (2*k+1)*(nondivSign p (2*j+1) (2*k+1):ℝ)

lemma full_strip (p : ℕ) : ThetaDivisibleDiagonal.offDiagonal p = strip p (p/2) := by
  unfold ThetaDivisibleDiagonal.offDiagonal strip
  congr 1
  apply sum_congr rfl; intro j _
  congr 1
  rw [sum_filter]
  apply sum_congr rfl; intro k _
  dsimp only [nondivSign]
  split_ifs <;> simp_all

/-- Denominators beyond the cutoff cost a single Kloosterman discrepancy plus
a divisor count to remove the multiples. -/
theorem denominator_cutoff_of_kernel {p : ℕ} [Fact p.Prime] {B : ℝ} (hB : 0≤B)
    (bound : ∀ a b : ZMod p,b≠0 → ‖kloosterman a b‖≤B) (hp : p%2=1) {J : ℕ} (hJ : J≤p/2) :
    |ThetaDivisibleDiagonal.offDiagonal p-strip p J| ≤
      2*(kernelDiscrepancy p B+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*J+1) := by
  rw [full_strip]
  let w (j : ℕ) := weight p (2*j+1)
  let g (j k : ℕ) : ℝ := nondivSign p (2*j+1) (2*k+1)
  let D := kernelDiscrepancy p B+2*(p.sqrt:ℝ)
  let E := D*((p:ℝ)/(2*J+1))
  have hD : 0≤D := by dsimp [D,kernelDiscrepancy]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hpr : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  change |2/(p:ℝ)*(∑ j ∈ range (p/2), w j*∑ k ∈ range (p/2), w k*g j k) -
    2/(p:ℝ)*(∑ j ∈ range J, w j*∑ k ∈ range (p/2), w k*g j k)| ≤ _
  rw [← mul_sub,← sum_Ico_eq_sub _ hJ,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ))]
  have hswap : ∑ j ∈ Ico J (p/2), w j*∑ k ∈ range (p/2), w k*g j k =
      ∑ k ∈ range (p/2), w k*∑ j ∈ Ico J (p/2), w j*g j k := by
    simp_rw [mul_sum]; rw [sum_comm]; apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro j _; ring
  rw [hswap]
  have H : |∑ k ∈ range (p/2), w k*∑ j ∈ Ico J (p/2), w j*g j k| ≤
      ((p:ℝ)*harmonic (p/2))*E := by
    apply (abs_sum_le_sum_abs ..).trans
    apply le_trans _ (mul_le_mul_of_nonneg_right (weight_mass (le_refl (p/2))) hE)
    rw [sum_mul]; apply sum_le_sum; intro k hk
    have hlt := mem_range.mp hk
    have hw : 0≤w k := (ThetaCotangentTriangle.weight_pos (by omega) (by omega)).le
    rw [abs_mul,abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (denominator_tail hB bound hp hlt) hw
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0≤2/(p:ℝ))).trans
  dsimp [E,D]; apply le_of_eq; field_simp

theorem denominator_cutoff {p : ℕ} [Fact p.Prime] (hp : p%2=1) {J : ℕ} (hJ : J≤p/2) :
    |ThetaDivisibleDiagonal.offDiagonal p-strip p J| ≤
      2*(discrepancy p+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*J+1) := by
  simpa only [elementary_discrepancy] using denominator_cutoff_of_kernel (by positivity)
    (fun a b hb => kloosterman_bound a b hb) hp hJ

/-- For fixed odd width K, cutting the numerator rows at Ku loses at most
2 p H_J / K for the entire denominator strip. -/
theorem width_cutoff {p : ℕ} [Fact p.Prime] {J K : ℕ} (hK : K%2=1) (hJ : J≤p/2)
    (hfit : K*(2*J) ≤ p) :
    |strip p J-cotCone p J K| ≤ 2*(p:ℝ)*harmonic J/K := by
  let w (j : ℕ) := weight p (2*j+1)
  let g (j k : ℕ) : ℝ := nondivSign p (2*j+1) (2*k+1)
  let L (j : ℕ) := K*(2*j+1)/2
  have hpr : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hK' : 0<K := by omega
  have hr (j : ℕ) (hj : j ∈ range J) :
      |w j*(∑ k ∈ range (p/2), w k*g j k)-w j*∑ k ∈ range (L j), w k*g j k| ≤ w j*((p:ℝ)/K) := by
    have hj' := mem_range.mp hj
    have hu : 2*j+1 < p := by omega
    have hlt : K*(2*j+1) ≤ p := (Nat.mul_le_mul_left K (show 2*j+1≤2*J by omega)).trans hfit
    have hL : L j≤p/2 := by dsimp [L]; omega
    have ho : (K*(2*j+1))%2=1 := by rw [Nat.mul_mod,hK]; omega
    have he : 2*L j+1=K*(2*j+1) := by dsimp [L]; omega
    have hc : p.Coprime (2*j+1) := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h => hu.not_ge (Nat.le_of_dvd (by omega) h))
    have hw : 0≤w j := (ThetaCotangentTriangle.weight_pos (by omega) hu).le
    rw [← mul_sub,← sum_Ico_eq_sub _ hL,abs_mul,abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left (numerator_tail (by omega : (2*j+1)%2=1) hK' hc he) hw
  change |2/(p:ℝ)*(∑ j ∈ range J, w j*∑ k ∈ range (p/2), w k*g j k) -
    2/(p:ℝ)*(∑ j ∈ range J, w j*∑ k ∈ range (L j), w k*g j k)| ≤ _
  rw [← mul_sub,← sum_sub_distrib,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ))]
  apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum hr)) (by positivity)).trans
  rw [← sum_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (weight_mass hJ)
    (by positivity : 0≤(p:ℝ)/K)) (by positivity : 0≤2/(p:ℝ))).trans
  apply le_of_eq; field_simp

/-- Rational approximation on the cone u < 2J, v < Ku (K odd). -/
noncomputable def rationalCone (p J K : ℕ) : ℚ :=
  ∑ j ∈ range J, ∑ k ∈ range (K*(2*j+1)/2),
    (nondivSign p (2*j+1) (2*k+1):ℚ)/((2*(j:ℚ)+1)*(2*(k:ℚ)+1))

open ThetaReciprocalCutoff (linearWeight product_error)

private lemma product_cone {p u v K : ℕ} (hu : 0<u) (hv : 0<v) (hul : u<p) (hvl : v<p)
    (hwidth : v≤K*u) :
    |weight p u * weight p v - linearWeight p u * linearWeight p v| ≤ (u:ℝ)/v + K := by
  rcases le_total v u with h|h
  · exact (product_error hv h hul).trans (by linarith [Nat.cast_nonneg (α:=ℝ) K])
  · rw [mul_comm (weight _ _),mul_comm (linearWeight _ _)]
    have hr : (v:ℝ)/u ≤ K := (div_le_iff₀ (Nat.cast_pos.mpr hu)).mpr (by exact_mod_cast hwidth)
    exact (product_error hu h hvl).trans (hr.trans (by linarith [show 0≤(u:ℝ)/v by positivity]))

theorem rationalization {p J K : ℕ} (hp : 0<p) (hJ : J≤p/2) (hfit : K*(2*J) ≤ p) :
    |cotCone p J K - (8*p/Real.pi^2)*(rationalCone p J K:ℝ)| ≤
      2*(J:ℝ)^2*(2*(harmonic (K*J):ℝ)+(K:ℝ)^2)/p := by
  let w (j : ℕ) := weight p (2*j+1)
  let a (j : ℕ) := linearWeight p (2*j+1)
  let s (j k : ℕ) : ℝ := nondivSign p (2*j+1) (2*k+1)
  let L (j : ℕ) := K*(2*j+1)/2
  have hp₀ : 0<(p:ℝ) := by exact_mod_cast hp
  have he : (8*p/Real.pi^2)*(rationalCone p J K:ℝ) =
      2/(p:ℝ)*∑ j ∈ range J, a j*∑ k ∈ range (L j), a k*s j k := by
    dsimp [rationalCone,a,s,L,linearWeight]; push_cast; simp_rw [mul_sum]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro k _
    field_simp; ring
  rw [he]
  change |2/(p:ℝ)*(∑ j ∈ range J, w j*∑ k ∈ range (L j), w k*s j k) - _| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ)),← sum_sub_distrib]
  have hinner (j : ℕ) (hj : j ∈ range J) :
      |w j*∑ k ∈ range (L j), w k*s j k - a j*∑ k ∈ range (L j), a k*s j k| ≤
        2*J*(harmonic (K*J):ℝ)+(K:ℝ)^2*J := by
    have hj' := mem_range.mp hj
    have hlt : K*(2*j+1) ≤ K*(2*J) := Nat.mul_le_mul_left K (by omega)
    have hL : L j≤K*J := by dsimp [L]; rw [show K*(2*J)=2*(K*J) by ring] at hlt; omega
    simp only [mul_sum,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    calc
      _ ≤ ∑ k ∈ range (L j), ((2*(J:ℝ))*((k:ℝ)+1)⁻¹+K) := by
        apply sum_le_sum; intro k hk
        have hk' := mem_range.mp hk
        have hwidth : 2*k+1 ≤ K*(2*j+1) := by dsimp [L] at hk'; omega
        have hvl : 2*k+1 < p := by
          have := hlt.trans hfit; dsimp [L] at hk'
          by_cases hK : K=0
          · simp [hK] at hk'
          have hstrict := Nat.mul_lt_mul_of_pos_left (show 2*j+1<2*J by omega) (Nat.pos_of_ne_zero hK)
          omega
        have hs : |s j k|≤1 := by dsimp [s,nondivSign,reciprocalSign]; split_ifs <;> norm_num
        rw [← mul_assoc,← mul_assoc,← sub_mul,abs_mul]
        apply (mul_le_mul_of_nonneg_left hs (abs_nonneg _)).trans
        rw [mul_one,← div_eq_mul_inv]
        apply (product_cone (by omega) (by omega) (by omega) hvl hwidth).trans
        apply add_le_add _ le_rfl
        push_cast; apply div_le_div₀ (by positivity) _ (by positivity) _ <;> linarith [Nat.cast_nonneg (α:=ℝ) k, (show (j:ℝ)+1≤J by exact_mod_cast hj')]
      _ ≤ ∑ k ∈ range (K*J), ((2*(J:ℝ))*((k:ℝ)+1)⁻¹+K) :=
        sum_le_sum_of_subset_of_nonneg (range_mono hL) (by intros; positivity)
      _ = _ := by
        rw [sum_add_distrib,← mul_sum]; simp [harmonic]; ring
  apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum hinner)) (by positivity)).trans
  simp only [sum_const,card_range,nsmul_eq_mul]
  apply le_of_eq; ring

/-- Deterministic transfer of the entire nondivisible part to a fixed-width
rational cone. The term divided by K is the discarded numerator tail. -/
theorem offDiagonal_cone_error_of_kernel {p : ℕ} [Fact p.Prime] {B : ℝ} (hB : 0≤B)
    (bound : ∀ a b : ZMod p,b≠0 → ‖kloosterman a b‖≤B) (hp : p%2=1) {J K : ℕ}
    (hK : K%2=1) (hJ : J≤p/2) (hfit : K*(2*J) ≤ p) :
    |ThetaDivisibleDiagonal.offDiagonal p - (8*p/Real.pi^2)*(rationalCone p J K:ℝ)| ≤
    2*(kernelDiscrepancy p B+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*J+1) + 2*(p:ℝ)*harmonic J/K +
      2*(J:ℝ)^2*(2*(harmonic (K*J):ℝ)+(K:ℝ)^2)/p := by
  apply (abs_sub_le _ (cotCone p J K) _).trans
  apply add_le_add _ (rationalization (Fact.out : p.Prime).pos hJ hfit)
  exact (abs_sub_le _ (strip p J) _).trans (add_le_add (denominator_cutoff_of_kernel hB bound hp hJ) (width_cutoff hK hJ hfit))


theorem offDiagonal_cone_error {p : ℕ} [Fact p.Prime] (hp : p%2=1) {J K : ℕ}
    (hK : K%2=1) (hJ : J≤p/2) (hfit : K*(2*J) ≤ p) :
    |ThetaDivisibleDiagonal.offDiagonal p - (8*p/Real.pi^2)*(rationalCone p J K:ℝ)| ≤
    2*(discrepancy p+2*(p.sqrt:ℝ))*p*harmonic (p/2)/(2*J+1) + 2*(p:ℝ)*harmonic J/K +
      2*(J:ℝ)^2*(2*(harmonic (K*J):ℝ)+(K:ℝ)^2)/p := by
  simpa only [elementary_discrepancy] using offDiagonal_cone_error_of_kernel (by positivity)
    (fun a b hb => kloosterman_bound a b hb) hp hK hJ hfit

end Arxiv.«2501.03234».ThetaNondivisibleCone
#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.nondivisible_prefix
#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.numerator_tail
#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.denominator_cutoff
#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.width_cutoff
#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.rationalization
#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.offDiagonal_cone_error

#print axioms Arxiv.«2501.03234».ThetaNondivisibleCone.offDiagonal_cone_error_of_kernel
