import ThetaCotangentTriangle
import ThetaFourierBound

/-! Incomplete reciprocal sums in the lower cotangent triangle. -/

namespace Arxiv.«2501.03234».ThetaReciprocalCutoff

open Finset
open ThetaDiagonal (U)

variable {p : ℕ} [Fact p.Prime]

/-- The complete two-parameter Kloosterman sum over the nonzero residues. -/
noncomputable def kloosterman (a b : ZMod p) : ℂ :=
  ∑ x : U p, ZMod.stdAddChar (a*(x:ZMod p) + b*(↑(x⁻¹) : ZMod p))

private def parameter (b : ZMod p) (t : U p) : ZMod p :=
  b * (1+(t:ZMod p)) * (1+(↑(t⁻¹):ZMod p))

private lemma parameter_fiber {b : ZMod p} (hb : b≠0) {s t : U p}
    (he : parameter b s = parameter b t) : s=t ∨ s=t⁻¹ := by
  let x := (s : ZMod p)
  let y := (t : ZMod p)
  have hx : x≠0 := s.ne_zero
  have hy : y≠0 := t.ne_zero
  simp only [parameter,Units.val_inv_eq_inv_val] at he
  change b*(1+x)*(1+x⁻¹)=b*(1+y)*(1+y⁻¹) at he
  rw [mul_assoc,mul_assoc b, mul_right_inj' hb] at he
  field_simp at he
  have h : (x-y)*(x*y-1)=0 := by linear_combination he
  rcases mul_eq_zero.mp h with hxy|hxy
  · exact Or.inl (Units.ext (sub_eq_zero.mp hxy))
  · right; apply Units.ext
    rw [Units.val_inv_eq_inv_val]
    change x=y⁻¹
    field_simp
    exact sub_eq_zero.mp hxy

private lemma parameter_multiplicity {b : ZMod p} (hb : b≠0) (z : ZMod p) :
    (univ.filter (fun t : U p => parameter b t=z)).card ≤ 2 := by
  by_cases h : (univ.filter (fun t : U p => parameter b t=z)).Nonempty
  · obtain ⟨t,ht⟩ := h
    apply le_trans _ (card_le_two (a := t) (b := t⁻¹))
    apply card_le_card
    intro s hs
    have he := parameter_fiber hb ((mem_filter.mp hs).2.trans (mem_filter.mp ht).2.symm)
    simpa using he
  · simp [not_nonempty_iff_eq_empty.mp h]

open ThetaFourier (orthog)

open scoped ComplexConjugate

private lemma conj_char (x : ZMod p) : conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [ZMod.stdAddChar_apply,← Circle.coe_inv_eq_conj,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv]

private lemma second_moment (a : ZMod p) :
    ∑ b : ZMod p, ‖kloosterman a b‖^2 = (p:ℝ)*(p-1) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj',kloosterman,map_sum,conj_char,mul_sum,sum_mul,← AddChar.map_add_eq_mul]
  let f (x y : U p) := a*((x:ZMod p)-(y:ZMod p))
  let g (x y : U p) := (↑(x⁻¹):ZMod p)-(↑(y⁻¹):ZMod p)
  have he (b : ZMod p) (x y : U p) : a*(x:ZMod p)+b*(↑(x⁻¹):ZMod p) +
      -(a*(y:ZMod p)+b*(↑(y⁻¹):ZMod p)) = f x y + g x y*b := by dsimp [f,g]; ring
  simp_rw [he,AddChar.map_add_eq_mul]
  rw [sum_comm]
  simp_rw [sum_comm (s := (univ : Finset (ZMod p))) (t := (univ : Finset (U p))),← mul_sum,orthog]
  have hz (x y : U p) : g x y=0 ↔ x=y := by
    simp only [g,sub_eq_zero,Units.val_inj,inv_inj]
  simp_rw [hz,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true,f,sub_self,mul_zero,
    AddChar.map_zero_eq_one,one_mul]
  simp [Nat.totient_prime (Fact.out : p.Prime),Nat.cast_sub (Fact.out : p.Prime).one_le,mul_comm]

private lemma square_expansion (a b : ZMod p) :
    kloosterman a b ^ 2 = p-1 +
      ∑ t ∈ (univ : Finset (U p)).erase (-1), kloosterman a (parameter b t) := by
  let e (x : U p) := ZMod.stdAddChar (a*(x:ZMod p) + b*(↑(x⁻¹):ZMod p))
  have hs : kloosterman a b ^ 2 = ∑ t : U p, ∑ x : U p, e x * e (t*x) := by
    rw [sum_comm]; change (∑ x : U p, e x)^2=_
    rw [sq,sum_mul]; apply sum_congr rfl; intro x _
    rw [mul_sum]
    exact (Equiv.sum_comp (Equiv.mulRight x) (fun y : U p => e x*e y)).symm
  rw [hs,← sum_erase_add _ _ (mem_univ (-1 : U p)),add_comm]
  have hm : (∑ x : U p, e x*e (-1*x)) = p-1 := by
    have h (x : U p) : e x*e (-x)=1 := by
      simp only [e,← AddChar.map_add_eq_mul,Units.val_neg,Units.val_inv_eq_inv_val,inv_neg,mul_neg,
        ← neg_add,add_neg_cancel,AddChar.map_zero_eq_one]
    simp [h,Nat.totient_prime (Fact.out : p.Prime),Nat.cast_sub (Fact.out : p.Prime).one_le]
  rw [hm]
  congr 1
  apply sum_congr rfl; intro t ht
  have ht' : (1 : ZMod p)+(t:ZMod p)≠0 := by
    intro h; apply (mem_erase.mp ht).1
    apply Units.ext; change (t:ZMod p) = -1; linear_combination h
  let d := Units.mk0 _ ht'
  have hh := Equiv.sum_comp (Equiv.mulLeft d)
    (fun y : U p => ZMod.stdAddChar (a*(y:ZMod p) + parameter b t*(↑(y⁻¹):ZMod p)))
  change _ = ∑ y : U p, ZMod.stdAddChar (a*(y:ZMod p)+parameter b t*(↑(y⁻¹):ZMod p))
  rw [← hh]
  apply sum_congr rfl; intro x _
  dsimp [e]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Units.val_mul,Units.val_inv_eq_inv_val,mul_inv_rev,parameter]
  change _ = a*((1+(t:ZMod p))*(x:ZMod p)) + _ * ((x:ZMod p)⁻¹*(1+(t:ZMod p))⁻¹)
  field_simp
  ring

private lemma bound_sq (a b : ZMod p) (hb : b≠0) :
    ‖kloosterman a b‖^2 ≤ p + Real.sqrt (2*(p:ℝ)^3) := by
  let I := (univ : Finset (U p)).erase (-1)
  let V (z : ZMod p) := ‖kloosterman a z‖
  have hmulti : ∑ t ∈ I, V (parameter b t)^2 ≤ 2 * ∑ z : ZMod p, V z^2 := by
    calc
      _ ≤ ∑ t : U p, V (parameter b t)^2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
      _ = ∑ z : ZMod p, ∑ t ∈ univ.filter (fun t : U p => parameter b t=z), V z^2 := by
        symm; exact sum_fiberwise_of_maps_to' (fun _ _ => mem_univ _) (fun z => V z^2)
      _ ≤ _ := by
        rw [mul_sum]; apply sum_le_sum; intro z _
        simp only [sum_const,nsmul_eq_mul]
        gcongr
        exact_mod_cast parameter_multiplicity hb z
  have hcard : (I.card : ℝ) ≤ p := by
    exact_mod_cast ((card_le_card (s := I) (subset_univ _)).trans
      (by simp [Nat.totient_prime (Fact.out : p.Prime)] : (univ : Finset (U p)).card≤p))
  have hcs := sum_mul_sq_le_sq_mul_sq I (fun _ => (1:ℝ)) (fun t => V (parameter b t))
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have hm := second_moment a
  change ∑ z : ZMod p, V z^2 = _ at hm
  rw [hm] at hmulti
  have hle : (∑ t ∈ I, V (parameter b t))^2 ≤ 2*(p:ℝ)^3 := by
    apply hcs.trans
    apply (mul_le_mul hcard hmulti (by positivity) (by positivity)).trans
    nlinarith [sq_nonneg (p:ℝ)]
  have hp0 : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_le
  calc
    _ = ‖kloosterman a b ^ 2‖ := (norm_pow _ _).symm
    _ ≤ ‖(p:ℂ)-1‖ + ∑ t ∈ I, V (parameter b t) := by
      rw [square_expansion]; exact (norm_add_le ..).trans (add_le_add_right (norm_sum_le ..) _)
    _ ≤ _ := by
      have hnp : ‖(p:ℂ)-1‖ = (p:ℝ)-1 := by
        rw [← Complex.ofReal_natCast,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      rw [hnp]
      linarith [Real.le_sqrt_of_sq_le hle]

/-- The elementary three-quarter-power bound suffices for completing the reciprocal interval. -/
theorem kloosterman_bound (a b : ZMod p) (hb : b≠0) :
    ‖kloosterman a b‖ ≤ 2*(p:ℝ)^(3/4:ℝ) := by
  have hp : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_le
  have hpp : 0<(p:ℝ) := by linarith
  let t := (p:ℝ)^(3/4:ℝ)
  have ht : 0≤t := Real.rpow_nonneg hpp.le _
  have h4 : t^4 = (p:ℝ)^3 := by
    dsimp [t]; rw [← Real.rpow_mul_natCast hpp.le]; norm_num
  have hsq : (p:ℝ) ≤ t^2 := by
    rw [show (p:ℝ) = (p:ℝ)^(1:ℝ) by simp] at ⊢
    dsimp [t]; rw [← Real.rpow_mul_natCast hpp.le]
    apply Real.rpow_le_rpow_of_exponent_le hp; norm_num
  have hs : Real.sqrt (2*(p:ℝ)^3) ≤ 2*t^2 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [pow_nonneg ht 4]
  have hbnd := bound_sq a b hb
  change _ ≤ 2*t
  nlinarith [mul_nonneg ht (norm_nonneg (kloosterman a b))]

open ThetaCotangentTriangle (coeff quotientSign weight)

/-- Additive transform of a progression with common difference two. -/
private noncomputable def amp (s : ZMod p) (n : ℕ) (t : ZMod p) : ℂ :=
  ∑ i ∈ range n, ZMod.stdAddChar ((s+2*(i:ZMod p))*t)

private lemma norm_char (x : ZMod p) : ‖ZMod.stdAddChar x‖=1 := Circle.norm_coe _

private lemma amp_le {s t : ZMod p} (n : ℕ) (ht : 2*t ≠ 0) :
    ‖amp s n t‖ ≤ ThetaFourier.weight (2*t) := by
  let z := ZMod.stdAddChar (2*t)
  have he : amp s n t = (∑ i ∈ range n, z^i)*ZMod.stdAddChar (s*t) := by
    rw [amp,sum_mul]
    apply sum_congr rfl; intro i _
    rw [← AddChar.map_nsmul_eq_pow,← AddChar.map_add_eq_mul,nsmul_eq_mul]
    congr 1; ring
  rw [ThetaFourier.weight,le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (ThetaFourier.char_ne_one _ ht)))]
  rw [he,norm_mul,norm_char,mul_one,← norm_mul,geom_sum_mul]
  exact (norm_sub_le ..).trans (by norm_num [norm_pow,z])

private lemma amp_mass (hp : p%2=1) (s : ZMod p) (n : ℕ) :
    ∑ t : ZMod p, ‖amp s n t‖ ≤ n+(p:ℝ)*harmonic (p/2) := by
  have h2 : (2:ZMod p)≠0 := by
    have hgt : 2<p := by have := (Fact.out : p.Prime).two_le; omega
    have he := ZMod.val_natCast_of_lt hgt
    intro hh; change (2:ZMod p).val=2 at he; rw [hh,ZMod.val_zero] at he; omega
  rw [← sum_erase_add _ _ (mem_univ (0:ZMod p))]
  have hz : ‖amp s n 0‖=(n:ℝ) := by simp [amp]
  rw [hz,add_comm]; gcongr
  calc
    _ ≤ ∑ t ∈ univ.erase (0:ZMod p), ThetaFourier.weight (2*t) := by
      apply sum_le_sum; intro t ht
      exact amp_le _ (mul_ne_zero h2 (mem_erase.mp ht).1)
    _ = ∑ t ∈ univ.erase (0:ZMod p), ThetaFourier.weight t := by
      apply sum_nbij' (fun t => 2*t) (fun t => (2:ZMod p)⁻¹*t) <;> simp [h2]
    _ ≤ _ := ThetaFourier.weight_mass hp

private lemma coeff_is_diff (hp : p%2=1) (t : ZMod p) :
    coeff t = amp 1 (p/2) t - amp 1 (p/2) (-t) := by
  rw [coeff,ThetaDiagonal.sum_by_sign hp]
  let f (n : ℕ) := ZMod.stdAddChar ((n:ZMod p)*t) - ZMod.stdAddChar ((n:ZMod p)*(-t))
  calc
    _ = ∑ a ∈ ThetaDiagonal.oddReps p, f (ThetaDiagonal.rep a) := by
      apply sum_congr rfl; intro a ha
      have ho : ThetaDiagonal.sign a=1 := if_pos (mem_filter.mp ha).2
      simp [ThetaDiagonal.sign_neg hp,ho,f,ThetaDiagonal.rep,sub_eq_add_neg]
    _ = _ := by
      rw [ThetaCotangentTriangle.sum_odd_indices hp,amp,amp,← sum_sub_distrib]
      apply sum_congr rfl; intro i _
      dsimp [f]; push_cast; rw [add_comm (1:ZMod p)]

private lemma coeff_mass (hp : p%2=1) :
    ∑ t : ZMod p, ‖coeff t‖ ≤ 2*((p/2 : ℕ)+(p:ℝ)*harmonic (p/2)) := by
  calc
    _ ≤ ∑ t : ZMod p, (‖amp 1 (p/2) t‖+‖amp 1 (p/2) (-t)‖) := by
      apply sum_le_sum; intro t _; rw [coeff_is_diff hp]; exact norm_sub_le ..
    _ = 2 * ∑ t : ZMod p, ‖amp 1 (p/2) t‖ := by
      rw [sum_add_distrib,← Equiv.sum_comp (Equiv.neg (ZMod p)) (fun t => ‖amp 1 (p/2) t‖),two_mul]
      simp
    _ ≤ _ := by gcongr; exact amp_mass hp _ _

private lemma coeff_invert (y : U p) :
    ∑ b : ZMod p, coeff (-b)*ZMod.stdAddChar ((y:ZMod p)*b) = (p:ℂ)*ThetaDiagonal.sign y := by
  simp only [coeff,sum_mul,mul_assoc,← AddChar.map_add_eq_mul]
  rw [sum_comm]
  simp_rw [show ∀ (x : U p) (b : ZMod p), (x:ZMod p)*(-b)+(y:ZMod p)*b=((y:ZMod p)-x)*b by intros; ring,
    ← mul_sum,orthog,sub_eq_zero,Units.val_inj,mul_ite,mul_zero]
  simp [sum_ite_eq,mul_comm]

private lemma complete_phase (s b : ZMod p) (n : ℕ)
    (hs : ∀ i<n, s+2*(i:ZMod p)≠0) :
    ∑ a : ZMod p, amp s n (-a)*kloosterman a b =
    (p:ℂ)*∑ i ∈ range n, ZMod.stdAddChar (b/(s+2*(i:ZMod p))) := by
  let f (i : ℕ) := s+2*(i:ZMod p)
  have hx (i : ℕ) (x : U p) (a : ZMod p) :
      f i*(-a)+(a*(x:ZMod p)+b*(↑(x⁻¹):ZMod p)) =
      b*(↑(x⁻¹):ZMod p)+((x:ZMod p)-f i)*a := by ring
  conv_lhs => simp only [amp,kloosterman,sum_mul,mul_sum,← AddChar.map_add_eq_mul]
  simp_rw [sum_comm (s := (univ : Finset (U p))) (t := range n)]
  change (∑ a : ZMod p, ∑ i ∈ range n, ∑ x : U p, ZMod.stdAddChar
    (f i*(-a)+(a*(x:ZMod p)+b*(↑(x⁻¹):ZMod p)))) = _
  rw [sum_comm,mul_sum]
  apply sum_congr rfl; intro i hi
  rw [sum_comm]
  simp_rw [hx,AddChar.map_add_eq_mul,← mul_sum,orthog]
  let y := Units.mk0 (f i) (hs i (mem_range.mp hi))
  have he (x : U p) : (x:ZMod p)-f i=0 ↔ x=y := by rw [sub_eq_zero]; change ((x:ZMod p)=(y:ZMod p)) ↔ x=y; exact Units.val_inj
  simp only [he,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]
  rw [Units.val_inv_eq_inv_val]
  change ZMod.stdAddChar (b*(f i)⁻¹)*p=_
  rw [mul_comm,← div_eq_mul_inv]

private lemma sign_completion (s v n : ℕ) (hv : (v:ZMod p)≠0)
    (hs : ∀ i<n, 0<s+2*i ∧ s+2*i<p) :
    (p:ℂ)^2 * ∑ i ∈ range n, (quotientSign p (s+2*i) v : ℂ) =
    ∑ b : ZMod p, coeff (-b)*∑ a : ZMod p, amp s n (-a)*kloosterman a (b*v) := by
  have hn (i : ℕ) (hi : i<n) : (s:ZMod p)+2*(i:ZMod p)≠0 := by
    intro h
    have he : ((s+2*i:ℕ):ZMod p)=0 := by push_cast; exact h
    have := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hs i hi).2,ZMod.val_zero] at this
    exact (hs i hi).1.ne' this
  simp_rw [complete_phase (s:ZMod p) _ n hn,mul_left_comm (coeff _),← mul_sum]
  rw [sq,mul_assoc]; congr 1
  simp_rw [mul_sum]; rw [sum_comm (s := (univ : Finset (ZMod p))) (t := range n)]
  apply sum_congr rfl; intro i hi
  let y := Units.mk0 ((v:ZMod p)/((s:ZMod p)+2*(i:ZMod p))) (div_ne_zero hv (hn i (mem_range.mp hi)))
  have hsign : ThetaDiagonal.sign y = quotientSign p (s+2*i) v := by
    simp only [quotientSign,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; rfl
  rw [← hsign,← coeff_invert y]
  apply sum_congr rfl; intro b _
  dsimp [y]; rw [mul_div_assoc,mul_comm b]

/-- Uniform interval discrepancy for the parity of modular reciprocals. -/
noncomputable def discrepancy (p : ℕ) : ℝ := 4*(p:ℝ)^(3/4:ℝ)*(1+(harmonic (p/2):ℝ))^2

/-- Parity discrepancy from a uniform complete Kloosterman estimate. -/
noncomputable def kernelDiscrepancy (p : ℕ) (B : ℝ) : ℝ := 2*B*(1+(harmonic (p/2):ℝ))^2

omit [Fact p.Prime] in
theorem elementary_discrepancy : kernelDiscrepancy p (2*(p:ℝ)^(3/4:ℝ))=discrepancy p := by
  unfold kernelDiscrepancy discrepancy
  ring

theorem reciprocal_interval_of_kernel {K : ℝ} (hK : 0≤K)
    (bound : ∀ a b : ZMod p,b≠0 → ‖kloosterman a b‖≤K) (hp : p%2=1) (s v n : ℕ) (hv : (v:ZMod p)≠0)
    (hn : n≤p) (hs : ∀ i<n, 0<s+2*i ∧ s+2*i<p) :
    |((∑ i ∈ range n, quotientSign p (s+2*i) v : ℤ) : ℝ)| ≤ kernelDiscrepancy p K := by
  have h0 : coeff (0:ZMod p)=0 := by rw [coeff_is_diff hp,neg_zero,sub_self]
  have hb (b : ZMod p) : ‖coeff (-b)*∑ a : ZMod p, amp s n (-a)*kloosterman a (b*v)‖ ≤
      ‖coeff (-b)‖*((∑ a : ZMod p, ‖amp s n (-a)‖)*K) := by
    by_cases hz : b=0
    · simp [hz,h0]
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le ..).trans
    rw [sum_mul]; apply sum_le_sum; intro a _
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (bound a _ (mul_ne_zero hz hv)) (norm_nonneg _)
  let H : ℝ := harmonic (p/2)
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have HH : 0≤H := by dsimp [H]; exact_mod_cast (show 0 ≤ harmonic (p/2) by unfold harmonic; positivity)
  have ha : (∑ a : ZMod p, ‖amp s n (-a)‖) ≤ p*(1+H) := by
    rw [show (∑ a : ZMod p, ‖amp s n (-a)‖) = ∑ a : ZMod p, ‖amp s n a‖ from
      Equiv.sum_comp (Equiv.neg (ZMod p)) (fun t => ‖amp (s:ZMod p) n t‖)]
    have hnr : (n:ℝ)≤p := by exact_mod_cast hn
    exact (amp_mass hp _ _).trans (by dsimp [H]; linarith)
  have hc : (∑ b : ZMod p, ‖coeff (-b)‖) ≤ 2*p*(1+H) := by
    rw [show (∑ b : ZMod p, ‖coeff (-b)‖) = ∑ b : ZMod p, ‖coeff b‖ from
      Equiv.sum_comp (Equiv.neg (ZMod p)) (fun t => ‖coeff t‖)]
    apply (coeff_mass hp).trans
    have hhalf : ((p/2:ℕ):ℝ)≤p := by exact_mod_cast (show p/2≤p by omega)
    dsimp [H]; linarith
  have hh := congrArg norm (sign_completion s v n hv hs)
  rw [norm_mul,norm_pow,Complex.norm_natCast] at hh
  have hab : ‖∑ i ∈ range n, (quotientSign p (s+2*i) v : ℂ)‖ =
      |((∑ i ∈ range n, quotientSign p (s+2*i) v : ℤ):ℝ)| := by
    rw [← Int.cast_sum,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [hab] at hh
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hp0)).mp
  calc
    _ = _ := hh
    _ ≤ _ := (norm_sum_le ..).trans (sum_le_sum (fun b _ => hb b))
    _ = (∑ b : ZMod p, ‖coeff (-b)‖)*((∑ a : ZMod p, ‖amp s n (-a)‖)*K) := (sum_mul ..).symm
    _ ≤ (2*p*(1+H))*((p*(1+H))*K) := by gcongr
    _ = _ := by dsimp [H,kernelDiscrepancy]; ring

theorem reciprocal_interval (hp : p%2=1) (s v n : ℕ) (hv : (v:ZMod p)≠0)
    (hn : n≤p) (hs : ∀ i<n, 0<s+2*i ∧ s+2*i<p) :
    |((∑ i ∈ range n, quotientSign p (s+2*i) v : ℤ) : ℝ)| ≤ discrepancy p := by
  simpa only [elementary_discrepancy] using reciprocal_interval_of_kernel (by positivity)
    (fun a b hb => kloosterman_bound a b hb) hp s v n hv hn hs

open ThetaCotangentTriangle (reciprocalSign lowerTriangle)

/-- Restrict the lower triangle to its first J odd denominators. -/
noncomputable def cotPrefix (p J : ℕ) : ℝ :=
  2/(p:ℝ) * ∑ j ∈ range J, weight p (2*j+1) *
    ∑ k ∈ range j, weight p (2*k+1)*reciprocalSign p (2*j+1) (2*k+1)

/-- Elementary reciprocal majorant for a cotangent weight. -/
theorem weight_le {p u : ℕ} (hu : 0<u) (hul : u<p) : weight p u ≤ (p:ℝ)/u := by
  apply (ThetaCotangentTriangle.weight_upper hu hul).trans
  have h : 0<(u:ℝ) := by exact_mod_cast hu
  rw [div_le_div_iff₀ (by positivity) h]
  nlinarith [mul_nonneg (show 0≤(p:ℝ)*u by positivity) (show 0≤Real.pi-2 by linarith [Real.pi_gt_three])]

private lemma harmonic_range (n : ℕ) :
    (harmonic n : ℝ) = ∑ i ∈ range n, ((i:ℝ)+1)⁻¹ := by simp [harmonic]

/-- Total cotangent mass on an initial segment of odd indices. -/
theorem weight_mass {p N : ℕ} (hN : N≤p/2) :
    ∑ k ∈ range N, weight p (2*k+1) ≤ (p:ℝ)*harmonic N := by
  rw [harmonic_range,mul_sum]
  apply sum_le_sum; intro k hk
  have hh := mem_range.mp hk
  apply (weight_le (by omega) (by omega)).trans
  rw [← div_eq_mul_inv]
  gcongr; push_cast; linarith

/-- Summation by parts against a decreasing positive weight. -/
theorem weighted_abs (w g : ℕ → ℝ) {D : ℝ} {n : ℕ} (hD : 0≤D) (hw₀ : 0≤w 0)
    (hw : ∀ i<n, 0≤w i) (hm : ∀ i, i+1<n → w (i+1)≤w i)
    (hg : ∀ k≤n, |∑ i ∈ range k, g i|≤D) :
    |∑ i ∈ range n, w i*g i| ≤ D*w 0 := by
  apply abs_le.mpr
  constructor
  · simpa only [neg_mul] using ThetaCotangentTriangle.weighted_prefix_lower w g hD hw₀ hw hm
      (fun k hk => (abs_le.mp (hg k hk)).1)
  · have h := ThetaCotangentTriangle.weighted_prefix_lower w (fun i => -g i) hD hw₀ hw hm
      (fun k hk => by rw [sum_neg_distrib]; linarith [(abs_le.mp (hg k hk)).2])
    simpa only [mul_neg,sum_neg_distrib,neg_mul,neg_le_neg_iff] using h

private lemma tail_row (hp : p%2=1) {k J l : ℕ} (hk : k<l) (hJ : J≤l) :
    |∑ j ∈ Ico l (p/2), weight p (2*j+1)*(reciprocalSign p (2*j+1) (2*k+1):ℝ)| ≤
      discrepancy p * ((p:ℝ)/(2*J+1)) := by
  have hD : 0≤discrepancy p := by unfold discrepancy; positivity
  by_cases hl : l<p/2
  · rw [sum_Ico_eq_sum_range]
    let w (i : ℕ) := weight p (2*(l+i)+1)
    let g (i : ℕ) : ℝ := reciprocalSign p (2*(l+i)+1) (2*k+1)
    have hpre (m : ℕ) (hm : m≤p/2-l) : |∑ i ∈ range m, g i| ≤ discrepancy p := by
      have hv : ((2*k+1 : ℕ):ZMod p)≠0 := by
        intro h; have := congrArg ZMod.val h
        rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at this; omega
      have hi := reciprocal_interval hp (2*l+1) (2*k+1) m hv (by omega)
        (fun i hi => by constructor <;> omega)
      rw [Int.cast_sum] at hi
      apply le_trans (le_of_eq _) hi
      congr 1; apply sum_congr rfl; intro i h
      have hix := mem_range.mp h
      rw [ThetaCotangentTriangle.quotient_eq_reciprocal hp (by omega) (by omega) (by omega) (by omega)]
      dsimp [g]; rw [show 2*(l+i)+1=2*l+1+2*i by omega]
    have H := weighted_abs w g hD
      (ThetaCotangentTriangle.weight_pos (by omega) (by dsimp [w]; omega)).le
      (fun i hi => (ThetaCotangentTriangle.weight_pos (by omega) (by omega)).le)
      (fun i hi => ThetaCotangentTriangle.weight_antitone (by omega) (by omega) (by omega)) hpre
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ hD
    dsimp [w]; apply (weight_le (by omega) (by omega)).trans
    push_cast; gcongr
  · rw [Ico_eq_empty_of_le (by omega : p/2≤l),sum_empty,abs_zero]
    positivity

lemma transpose_tail (N J : ℕ) (w : ℕ → ℝ) (g : ℕ → ℕ → ℝ) :
    ∑ j ∈ Ico J N, w j * ∑ k ∈ range j, w k * g j k =
      ∑ k ∈ range N, w k * ∑ j ∈ Ico (max J (k+1)) N, w j * g j k := by
  have h₁ (j : ℕ) (hj : j ∈ Ico J N) : range j = (range N).filter (·<j) := by
    ext k; simp; have := (mem_Ico.mp hj).2; omega
  have h₂ (k : ℕ) : (Ico J N).filter (k<·) = Ico (max J (k+1)) N := by
    ext j; simp; omega
  calc
    _ = ∑ j ∈ Ico J N, ∑ k ∈ range N, (if k<j then w j*(w k*g j k) else 0) := by
      apply sum_congr rfl; intro j hj; rw [h₁ j hj,sum_filter,mul_sum]
      apply sum_congr rfl; intro k _; split_ifs <;> simp
    _ = _ := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      rw [← h₂,sum_filter,mul_sum]
      apply sum_congr rfl; intro j _; split_ifs <;> ring

/-- A finite bound on the whole discarded triangle, uniform over odd primes and cutoffs. -/
theorem cotPrefix_error (hp : p%2=1) {J : ℕ} (hJ : J≤p/2) :
    |lowerTriangle p - cotPrefix p J| ≤ 2*discrepancy p*p*harmonic (p/2)/(2*J+1) := by
  let N := p/2
  let w (j : ℕ) := weight p (2*j+1)
  let g (j k : ℕ) : ℝ := reciprocalSign p (2*j+1) (2*k+1)
  let E := discrepancy p*((p:ℝ)/(2*J+1))
  have hD : 0≤discrepancy p := by unfold discrepancy; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  change |2/(p:ℝ)*(∑ j ∈ range N, w j*∑ k ∈ range j, w k*g j k) -
    2/(p:ℝ)*(∑ j ∈ range J, w j*∑ k ∈ range j, w k*g j k)| ≤ _
  rw [← mul_sub,← sum_Ico_eq_sub _ hJ,transpose_tail,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ))]
  have H : |∑ k ∈ range N, w k*∑ j ∈ Ico (max J (k+1)) N, w j*g j k| ≤
      ((p:ℝ)*harmonic N)*E := by
    apply (abs_sum_le_sum_abs ..).trans
    apply le_trans _ (mul_le_mul_of_nonneg_right (weight_mass (le_refl (p/2))) hE)
    rw [sum_mul]; apply sum_le_sum; intro k hk
    have hl : k<N := mem_range.mp hk
    have hw : 0≤w k := (ThetaCotangentTriangle.weight_pos (by omega) (by dsimp [N] at hl; omega)).le
    rw [abs_mul,abs_of_nonneg hw]; apply mul_le_mul_of_nonneg_left _ hw
    exact tail_row hp (l := max J (k+1)) (by omega) (by omega)
  apply (mul_le_mul_of_nonneg_left H (by positivity : 0≤2/(p:ℝ))).trans
  dsimp [E,N]
  apply le_of_eq
  field_simp

/-- Reciprocal approximation to the cotangent weight. -/
noncomputable def linearWeight (p u : ℕ) : ℝ := 2*p/(Real.pi*u)

private lemma linearWeight_error {p u : ℕ} (hu : 0<u) (hul : u<p) :
    linearWeight p u - weight p u ≤ Real.pi*u/(4*p) := by
  let x : ℝ := Real.pi*u/(2*p)
  have hp : 0<(p:ℝ) := by exact_mod_cast hu.trans hul
  have hu' : 0<(u:ℝ) := by exact_mod_cast hu
  have h₀ : 0<x := by dsimp [x]; positivity
  have h₁ : x<Real.pi/2 := by
    dsimp [x]; rw [div_lt_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left (show (u:ℝ)<p by exact_mod_cast hul) Real.pi_pos
    linarith
  have hc := Real.cos_pos_of_mem_Ioo (show x ∈ Set.Ioo (-(Real.pi/2)) (Real.pi/2) from
    ⟨by linarith [Real.pi_pos],h₁⟩)
  have hs := Real.sin_pos_of_pos_of_lt_pi h₀ (by linarith [Real.pi_pos])
  have hcot : Real.cos x / x ≤ weight p u := by
    change _ ≤ (Real.tan x)⁻¹
    rw [Real.tan_eq_sin_div_cos,inv_div]
    exact div_le_div_of_nonneg_left hc.le hs (Real.sin_le h₀.le)
  have hlin : linearWeight p u = 1/x := by dsimp [linearWeight,x]; field_simp
  have he : Real.pi*u/(4*p) = x/2 := by dsimp [x]; ring
  rw [hlin,he]
  apply (sub_le_sub_left hcot _).trans
  rw [← sub_div,div_le_iff₀ h₀]
  nlinarith [Real.one_sub_sq_div_two_lt_cos h₀.ne']

/-- Uniform pointwise cost of linearizing a product of two cotangent weights. -/
theorem product_error {p u v : ℕ} (hv : 0<v) (hvu : v≤u) (hul : u<p) :
    |weight p u*weight p v-linearWeight p u*linearWeight p v| ≤ (u:ℝ)/v := by
  have hu := hv.trans_le hvu
  have hvl := hvu.trans_lt hul
  have hw₁ := (ThetaCotangentTriangle.weight_pos hu hul).le
  have hw₂ := (ThetaCotangentTriangle.weight_pos hv hvl).le
  have hl₁ : weight p u ≤ linearWeight p u := ThetaCotangentTriangle.weight_upper hu hul
  have hl₂ : weight p v ≤ linearWeight p v := ThetaCotangentTriangle.weight_upper hv hvl
  have hlv := hw₂.trans hl₂
  rw [abs_of_nonpos (sub_nonpos.mpr (mul_le_mul hl₁ hl₂ hw₂ (hw₁.trans hl₁))),neg_sub]
  have h₁ := mul_le_mul_of_nonneg_right (linearWeight_error hu hul) hlv
  have h₂ := mul_le_mul (linearWeight_error hv hvl) hl₁ hw₁ (by positivity)
  calc
    _ = (linearWeight p u-weight p u)*linearWeight p v +
        (linearWeight p v-weight p v)*weight p u := by ring
    _ ≤ _ := add_le_add h₁ h₂
    _ = (u:ℝ)/(2*v)+v/(2*u) := by
      have hp : (p:ℝ)≠0 := by exact_mod_cast (hu.trans hul).ne'
      dsimp [linearWeight]; field_simp; ring
    _ ≤ _ := by
      have hur : 0<(u:ℝ) := by exact_mod_cast hu
      have hvr : 0<(v:ℝ) := by exact_mod_cast hv
      have hle : (v:ℝ)≤u := by exact_mod_cast hvu
      field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0≤(u:ℝ)+v by positivity)]

/-- A rational harmonic sum. J counts the odd denominators 1,3,…,2J−1. -/
noncomputable def rationalPrefix (p J : ℕ) : ℚ :=
  ∑ j ∈ range J, ∑ k ∈ range j,
    (reciprocalSign p (2*j+1) (2*k+1) : ℚ)/((2*(j:ℚ)+1)*(2*(k:ℚ)+1))

private lemma rationalPrefix_error {p J : ℕ} (hp : 0<p) (hJ : J≤p/2) :
    |cotPrefix p J - (8*p/Real.pi^2)*(rationalPrefix p J : ℝ)| ≤
      4*(J:ℝ)^2*harmonic J/p := by
  let w (j : ℕ) := weight p (2*j+1)
  let a (j : ℕ) := linearWeight p (2*j+1)
  let s (j k : ℕ) : ℝ := reciprocalSign p (2*j+1) (2*k+1)
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp
  have he : (8*p/Real.pi^2)*(rationalPrefix p J : ℝ) =
      2/(p:ℝ)*∑ j ∈ range J, a j * ∑ k ∈ range j, a k*s j k := by
    dsimp [rationalPrefix,a,s,linearWeight]
    push_cast; simp_rw [mul_sum]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro k _
    field_simp; ring
  rw [he]
  change |2/(p:ℝ)*(∑ j ∈ range J, w j*∑ k ∈ range j, w k*s j k) - _| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤2/(p:ℝ)),← sum_sub_distrib]
  have hinner (j : ℕ) (hj : j ∈ range J) :
      |w j*∑ k ∈ range j, w k*s j k - a j*∑ k ∈ range j, a k*s j k| ≤ 2*J*(harmonic J : ℝ) := by
    simp only [mul_sum,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    rw [harmonic_range,mul_sum]
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (range_mono (mem_range.mp hj).le)
      (fun k _ _ => show 0≤(2*(J:ℝ))*((k:ℝ)+1)⁻¹ by positivity))
    apply sum_le_sum; intro k hk
    have hk' := mem_range.mp hk
    have hj' := mem_range.mp hj
    have hs : |s j k|=1 := by dsimp [s,reciprocalSign]; split_ifs <;> norm_num
    rw [← mul_assoc,← mul_assoc,← sub_mul,abs_mul,hs,mul_one]
    apply (product_error (by omega) (by omega) (by omega)).trans
    push_cast; rw [← div_eq_mul_inv]
    apply div_le_div₀ (by positivity) _ (by positivity) _
    · exact_mod_cast (show 2*j+1≤2*J by omega)
    · linarith [Nat.cast_nonneg (α := ℝ) k]
  apply (mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs ..).trans (sum_le_sum hinner)) (by positivity)).trans
  simp only [sum_const,card_range,nsmul_eq_mul]; apply le_of_eq; ring

/-- Finite error after replacing the lower triangle by a rational reciprocal sum. -/
theorem rational_cutoff_error (hp : p%2=1) {J : ℕ} (hJ : J≤p/2) :
    |lowerTriangle p - (8*p/Real.pi^2)*(rationalPrefix p J : ℝ)| ≤
      2*discrepancy p*p*harmonic (p/2)/(2*J+1) + 4*(J:ℝ)^2*harmonic J/p := by
  exact (abs_sub_le (lowerTriangle p) (cotPrefix p J) _).trans
    (add_le_add (cotPrefix_error hp hJ) (rationalPrefix_error (Fact.out : p.Prime).pos hJ))

/-- Number of positive odd integers at most p^α. -/
noncomputable def cutoff (p : ℕ) (α : ℝ) : ℕ := (⌊(p:ℝ)^α⌋₊+1)/2

/-- Error made in the complementary triangle by using just the rational sum below p^α. -/
noncomputable def cutoffError (α : ℝ) (p : ℕ) : ℝ :=
  lowerTriangle p - (8*p/Real.pi^2)*(rationalPrefix p (cutoff p α) : ℝ)

private lemma cutoff_bounds {p : ℕ} (hp : 1<p) {α : ℝ} (h₀ : 0≤α) (h₁ : α<1) :
    cutoff p α ≤ p/2 ∧ (cutoff p α : ℝ) ≤ (p:ℝ)^α ∧ (p:ℝ)^α ≤ 2*(cutoff p α:ℝ)+1 := by
  have hpr : 1<(p:ℝ) := by exact_mod_cast hp
  have hx := Real.one_le_rpow hpr.le h₀
  have hxp := Real.rpow_lt_self_of_one_lt hpr h₁
  let n := ⌊(p:ℝ)^α⌋₊
  have hl : (n:ℝ)≤(p:ℝ)^α := Nat.floor_le (by positivity)
  have hh : (p:ℝ)^α < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hn : n<p := by exact_mod_cast hl.trans_lt hxp
  have hn₁ : 1≤n := (Nat.one_le_floor_iff _).mpr hx
  change (n+1)/2≤p/2 ∧ (((n+1)/2 : ℕ):ℝ)≤_ ∧ _≤2*((((n+1)/2:ℕ):ℝ))+1
  refine ⟨by omega, le_trans (by exact_mod_cast (show (n+1)/2≤n by omega)) hl, hh.le.trans ?_⟩
  exact_mod_cast (show n+1≤2*((n+1)/2)+1 by omega)

private lemma harmonic_le_log {p : ℕ} (hp : 3≤p) {n : ℕ} (hn : n≤p) :
    (harmonic n : ℝ) ≤ 2*Real.log p := by
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have hlog : 1≤Real.log p := (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans hp')
  by_cases h : n=0
  · simp [h,harmonic]; linarith
  apply (harmonic_le_one_add_log n).trans
  have h := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h : 0<(n:ℝ)) (show (n:ℝ)≤p by exact_mod_cast hn)
  linarith

/-- Explicit power-saving bound for every cutoff exponent between three quarters and one. -/
theorem cutoffError_bound (hp : p%2=1) {α : ℝ} (hα : 3/4<α) (hα' : α<1) :
    |cutoffError α p| ≤ 152*(p:ℝ)^(max (7/4-α) (2*α-1))*(Real.log p)^3 := by
  have hp₃ : 3≤p := by have := (Fact.out : p.Prime).two_le; omega
  have hpr : (3:ℝ)≤p := by exact_mod_cast hp₃
  have hp0 : 0<(p:ℝ) := by linarith
  have hlog : 1≤Real.log p := (Real.le_log_iff_exp_le hp0).mpr (Real.exp_one_lt_three.le.trans hpr)
  let J := cutoff p α
  let L := Real.log p
  let r := max (7/4-α) (2*α-1)
  obtain ⟨hJ,hJl,hJh⟩ := cutoff_bounds (p := p) (by omega) (by linarith : 0≤α) hα'
  have hHm : (harmonic (p/2) : ℝ) ≤ 2*L := harmonic_le_log hp₃ (by omega)
  have hHJ : (harmonic J : ℝ) ≤ 2*L := harmonic_le_log hp₃ (by dsimp [J]; omega)
  have hH0 : (0:ℝ) ≤ harmonic (p/2) := by exact_mod_cast (show 0≤harmonic (p/2) by unfold harmonic; positivity)
  have hJ0 : (0:ℝ) ≤ harmonic J := by exact_mod_cast (show 0≤harmonic J by unfold harmonic; positivity)
  have hD : discrepancy p ≤ 36*(p:ℝ)^(3/4:ℝ)*L^2 := by
    have h : (1+(harmonic (p/2):ℝ))^2 ≤ (3*L)^2 := by gcongr; dsimp [L] at *; linarith
    dsimp [discrepancy]; nlinarith only [mul_le_mul_of_nonneg_left h
      (show 0≤4*(p:ℝ)^(3/4:ℝ) by positivity)]
  have hbase : 1≤(p:ℝ) := by linarith
  have h₁ : (p:ℝ)^(3/4:ℝ)*p/p^α ≤ (p:ℝ)^r := by
    rw [← Real.rpow_add_one hp0.ne',← Real.rpow_sub hp0]
    apply Real.rpow_le_rpow_of_exponent_le hbase
    dsimp [r]; norm_num
  have h₂ : ((p:ℝ)^α)^2/p ≤ (p:ℝ)^r := by
    rw [← Real.rpow_mul_natCast hp0.le,← Real.rpow_sub_one hp0.ne']
    apply Real.rpow_le_rpow_of_exponent_le hbase
    dsimp [r]; norm_num [mul_comm α]
  apply (rational_cutoff_error hp hJ).trans
  have htail : 2*discrepancy p*p*harmonic (p/2)/(2*(J:ℝ)+1) ≤ 144*(p:ℝ)^r*L^3 := by
    calc
      _ ≤ 2*(36*(p:ℝ)^(3/4:ℝ)*L^2)*p*(2*L)/p^α := by gcongr
      _ = 144*((p:ℝ)^(3/4:ℝ)*p/p^α)*L^3 := by ring
      _ ≤ _ := by gcongr
  have hsmall : 4*(J:ℝ)^2*harmonic J/p ≤ 8*(p:ℝ)^r*L^3 := by
    calc
      _ ≤ 4*((p:ℝ)^α)^2*(2*L)/p := by gcongr
      _ = 8*(((p:ℝ)^α)^2/p)*L := by ring
      _ ≤ 8*(p:ℝ)^r*L := by gcongr
      _ ≤ _ := by
        gcongr
        change L≤L^3
        have hL : 1≤L := hlog
        nlinarith [mul_nonneg (show 0≤L-1 by linarith) (sq_nonneg L),sq_nonneg (L-1)]
  change _ ≤ 152*(p:ℝ)^r*L^3
  linarith only [htail,hsmall]

open Asymptotics Filter in
/-- The discarded contribution and the cotangent linearization together cost o(p). -/
theorem cutoffError_isLittleO {α : ℝ} (hα : 3/4<α) (hα' : α<1) :
    cutoffError α =o[atTop ⊓ principal {p : ℕ | p.Prime}] (fun p : ℕ => (p:ℝ)) := by
  let l := (atTop : Filter ℕ) ⊓ principal {p : ℕ | p.Prime}
  let r := max (7/4-α) (2*α-1)
  have hr : r<1 := max_lt (by linarith) (by linarith)
  have hB : cutoffError α =O[l] (fun p : ℕ => (p:ℝ)^r*(Real.log p)^3) := by
    apply IsBigO.of_bound 152
    rw [Filter.eventually_inf_principal]
    filter_upwards [eventually_ge_atTop (3:ℕ)] with p hp
    intro hprime
    have hp' : p.Prime := hprime
    let : Fact p.Prime := ⟨hp'⟩
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (p:ℝ)^r*(Real.log p)^3)]
    simpa only [r,mul_assoc] using cutoffError_bound (Nat.odd_iff.mp (hp'.odd_of_ne_two (by omega))) hα hα'
  have hL : (fun p : ℕ => (Real.log p)^3) =o[l] (fun p : ℕ => (p:ℝ)^(1-r)) := by
    simpa only [Real.rpow_natCast] using
      ((isLittleO_log_rpow_rpow_atTop (3:ℕ) (show 0<1-r by linarith)).natCast_atTop.mono
        (show l≤atTop from inf_le_left))
  apply hB.trans_isLittleO
  have h := (isBigO_refl (fun p : ℕ => (p:ℝ)^r) l).mul_isLittleO hL
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [(eventually_gt_atTop (0:ℕ)).filter_mono (show l≤atTop from inf_le_left)] with p hp
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp
  change (p:ℝ)^r*(p:ℝ)^(1-r)=p
  rw [← Real.rpow_add hp',show r+(1-r)=1 by ring,Real.rpow_one]

open Filter in
/-- A lower bound on the rational harmonic sum alone implies the exact lower-growth
conclusion of the pinned Conjecture 4.4. -/
theorem growth_of_rationalPrefix {α b : ℝ} (hα : 3/4<α) (hα' : α<1) (hb : b<3/32)
    (hR : ∀ᶠ p : ℕ in atTop, p.Prime → Odd p →
      -b*Real.log p ≤ (rationalPrefix p (cutoff p α) : ℝ)) (n : ℕ) :
    ∀ᶠ p : ℕ in atTop, p.Prime → Odd p → n*p < S p := by
  let c : ℝ := 3/(4*Real.pi^2)
  let d : ℝ := 8/Real.pi^2
  have hπ : 0<Real.pi^2 := by positivity
  have hcoef : 0<c-d*b := by
    dsimp [c,d]; field_simp; linarith
  have herr := (cutoffError_isLittleO hα hα').bound (by norm_num : (0:ℝ)<1)
  rw [eventually_inf_principal] at herr
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp ((n+1+c*Real.log 6)/(c-d*b)))
  filter_upwards [hR,herr,eventually_ge_atTop N] with p hR herr hpN
  intro hp ho
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hsmall := herr hp
  simp only [Real.norm_eq_abs,abs_of_nonneg hp0.le,one_mul,cutoffError] at hsmall
  have hneg := (abs_le.mp hsmall).1
  have hB := mul_le_mul_of_nonneg_left (hR hp ho) (show 0≤d*p by dsimp [d]; positivity)
  have hlog : (n+1+c*Real.log 6)/(c-d*b)<Real.log p := by
    rw [← Real.exp_lt_exp,Real.exp_log hp0]; exact hN.trans_le (by exact_mod_cast hpN)
  have hS := ThetaCotangentTriangle.S_sub_lowerTriangle_log (Nat.odd_iff.mp ho)
  rw [Real.log_div hp0.ne' (by norm_num)] at hS
  change c*p*(Real.log p-Real.log 6) ≤ (S p:ℝ)-lowerTriangle p at hS
  rw [show (8:ℝ)*p/Real.pi^2=d*p by dsimp [d]; ring] at hneg
  have hh := mul_lt_mul_of_pos_right ((div_lt_iff₀ hcoef).mp hlog) hp0
  have hr : (n:ℝ)*p < (S p:ℝ) := by linarith only [hS,hB,hneg,hh]
  exact_mod_cast hr

end Arxiv.«2501.03234».ThetaReciprocalCutoff
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.kloosterman_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.reciprocal_interval
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.cotPrefix_error
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.rational_cutoff_error
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.cutoffError_bound
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.cutoffError_isLittleO
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.growth_of_rationalPrefix
#print axioms Arxiv.«2501.03234».ThetaFourier.weight_mass
#print axioms Arxiv.«2501.03234».ThetaFourier.char_ne_one
#print axioms Arxiv.«2501.03234».ThetaFourier.orthog
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.weighted_prefix_lower
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.weight_antitone
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.weight_pos
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.weight_upper
#print axioms Arxiv.«2501.03234».ThetaCotangentTriangle.sum_odd_indices
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.product_error
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.weight_le
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.weight_mass
#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.weighted_abs

#print axioms Arxiv.«2501.03234».ThetaReciprocalCutoff.reciprocal_interval_of_kernel
