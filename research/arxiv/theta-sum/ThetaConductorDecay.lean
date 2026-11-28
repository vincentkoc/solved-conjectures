import ThetaSpectralVariance
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Uniform conductor estimates for the full prime spectral coefficients. -/
namespace Arxiv.«2501.03234».ThetaConductorDecay
open Finset Filter Topology Complex DirichletCharacter ThetaDirichletRows ThetaDirichletEuler
open ThetaPrimitiveSpectrum ThetaLevelCoefficients
open scoped ZMod ComplexConjugate
noncomputable section

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
private lemma norm_neg_one : ‖χ (-1)‖=1 := by
  rcases χ.even_or_odd with h|h <;> rw [h] <;> simp

private lemma conj_gauss : conj (gaussSum χ ZMod.stdAddChar)=χ⁻¹ (-1)*gaussSum χ⁻¹ ZMod.stdAddChar := by
  calc _ = ∑ a : ZMod q,χ⁻¹ a * ZMod.stdAddChar (-a) := by
             simp only [gaussSum,map_sum,map_mul,AddChar.map_neg_eq_conj]
             apply sum_congr rfl
             intro a _
             rw [←MulChar.star_apply']
             rfl
       _ = ∑ a : ZMod q,χ⁻¹ (-a)*ZMod.stdAddChar a := by
             simpa only [Equiv.neg_apply,neg_neg] using
               (Equiv.sum_comp (Equiv.neg (ZMod q)) fun a => χ⁻¹ (-a)*ZMod.stdAddChar a)
       _ = _ := by
             rw [gaussSum,mul_sum]
             apply sum_congr rfl
             intro a _
             rw [show -a=(-1)*a by ring,map_mul,mul_assoc]

/-- The primitive Gauss sum has norm equal to the square root of the conductor. -/
theorem gauss_norm (hχ : χ.IsPrimitive) : ‖gaussSum χ ZMod.stdAddChar‖=Real.sqrt q := by
  let t := gaussSum χ ZMod.stdAddChar
  have H : ZMod.dft (χ:ZMod q → ℂ)=(χ⁻¹ (-1)*t) • (⇑(χ⁻¹)) := by
    funext a
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
    rw [show -a=(-1)*a by ring,map_mul]
    simp only [Pi.smul_apply,smul_eq_mul,t]; ring
  have hi : (χ⁻¹).IsPrimitive := (conductor_inv χ).trans hχ
  have h2 := congrFun (ZMod.dft_dft (χ:ZMod q → ℂ)) 1
  rw [H,ZMod.dft_const_smul] at h2
  change (χ⁻¹ (-1)*t)*ZMod.dft (⇑(χ⁻¹)) 1=(q:ℂ)*χ (-1) at h2
  rw [hi.fourierTransform_eq_inv_mul_gaussSum,inv_inv] at h2
  have hn := congrArg norm h2
  simp only [norm_mul,norm_neg_one,norm_natCast,one_mul,mul_one] at hn
  have hc := congrArg norm (conj_gauss χ)
  simp only [norm_conj,norm_mul,norm_neg_one,one_mul] at hc
  dsimp only [t] at hn
  rw [←hc] at hn
  calc _ = Real.sqrt (‖gaussSum χ ZMod.stdAddChar‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
       _ = _ := by rw [sq,hn]

theorem lvalue_bound (hne : χ≠1) : ‖LFunction χ 1‖≤2+Real.log q := by
  have h := ThetaCharacterHarmonicLimit.harmonic_error χ hne (NeZero.pos q)
  have hq : (q:ℝ)≠0 := by exact_mod_cast NeZero.ne q
  rw [div_self hq] at h
  let s := ∑ i∈range q,χ (i:ZMod q)/(i:ℂ)
  have htri := norm_add_le (LFunction χ 1-s) s
  rw [sub_add_cancel] at htri
  have ha : ‖s‖≤∑ i∈range q,(i:ℝ)⁻¹ := by
    apply (norm_sum_le ..).trans
    apply sum_le_sum
    intro i _
    rw [norm_div,norm_natCast,←one_div]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) (Nat.cast_nonneg _)
  have he : ∑ i∈range (q+1),(i:ℝ)⁻¹=(harmonic q:ℝ) := by
    rw [sum_range_succ',harmonic]; push_cast; simp
  have hm := (sum_le_sum_of_subset_of_nonneg (f:=fun i : ℕ => (i:ℝ)⁻¹)
    (range_mono (Nat.le_succ q)) (fun i _ _ => by positivity)).trans_eq he
  change ‖LFunction χ 1-s‖≤1 at h
  linarith [harmonic_le_one_add_log q]

private def major (n : ℕ) : ℝ :=
  if 3≤n then (((n:ℝ)-1)^2/(((n:ℝ)-2)*n))^2 else 1

private lemma major_one (n : ℕ) : 1≤ major n := by
  unfold major
  split_ifs with h
  · have h3 : (3:ℝ)≤n := by exact_mod_cast h
    have hd : 0<((n:ℝ)-2)*n := mul_pos (by linarith) (by linarith)
    have hh : 1≤((n:ℝ)-1)^2/(((n:ℝ)-2)*n) := (one_le_div hd).mpr (by nlinarith)
    nlinarith
  · rfl

omit [NeZero q] in
private lemma local_upper {p : ℕ} (hp : p.Prime) :
    ‖1+factor χ p/((p:ℂ)^2-1)‖≤ major p := by
  by_cases h2 : p=2
  · subst p; norm_num [factor,major]
  have h3 : 3≤p := by have := hp.two_le; omega
  have h3' : (3:ℝ)≤p := by exact_mod_cast h3
  have hpos : 0<(p:ℝ) := by linarith
  have hz : 0<(p:ℝ)^2-1 := by nlinarith
  have hd : 0<(p:ℝ)-1 := by linarith
  have hd' : 0<(p:ℝ)-2 := by linarith
  have hcoe : (p:ℂ)^2-1=(((p:ℝ)^2-1:ℝ):ℂ) := by push_cast; rfl
  have hden : (p:ℝ)^2-1=((p:ℝ)-1)*((p:ℝ)+1) := by ring
  calc _ ≤ ‖(1:ℂ)‖+‖factor χ p/((p:ℂ)^2-1)‖ := norm_add_le ..
       _ ≤ 1+(2*((p:ℝ)+1)/((p:ℝ)-1))/((p:ℝ)^2-1) := by
         rw [norm_one,norm_div,hcoe,norm_real,Real.norm_eq_abs,abs_of_pos hz]
         gcongr; exact factor_bound χ hp
       _ = 1+2/((p:ℝ)-1)^2 := by rw [hden]; field_simp
       _ ≤ major p := by
         rw [major,if_pos h3]
         have hlin : 1/((p:ℝ)-1)^2≤1/(((p:ℝ)-2)*p) := by
           gcongr; nlinarith
         have he : ((p:ℝ)-1)^2/(((p:ℝ)-2)*p)=1+1/(((p:ℝ)-2)*p) := by field_simp; ring
         rw [he]
         rw [show 2/((p:ℝ)-1)^2=2*(1/((p:ℝ)-1)^2) by ring]
         generalize (1:ℝ)/((p:ℝ)-1)^2=x at hlin ⊢
         generalize (1:ℝ)/(((p:ℝ)-2)*p)=y at hlin ⊢
         nlinarith only [hlin,sq_nonneg y]

private lemma telescope (N : ℕ) :
    ∏ n∈range (N+3),major n = (2*((N:ℝ)+1)/((N:ℝ)+2))^2 := by
  induction N with
  | zero => norm_num [sum_range_succ,prod_range_succ,major]
  | succ N ih =>
    rw [show N+1+3=N+3+1 by omega,prod_range_succ,ih,major,if_pos (by omega)]
    push_cast
    rw [show (N:ℝ)+3-2=N+1 by ring,show (N:ℝ)+3-1=N+2 by ring]
    field_simp; ring

omit [NeZero q] in
/-- Uniform norm bound for the conductor Euler correction. -/
theorem product_upper : ‖∑' n,weight χ n‖≤4 := by
  rw [product_value]
  let F (p : Nat.Primes) := 1+factor χ p/(((p:ℕ):ℂ)^2-1)
  change ‖∏' p,F p‖≤4
  by_cases H : Multipliable F
  · apply le_of_tendsto H.hasProd.norm
    apply Eventually.of_forall
    intro s
    let N := ∑ p∈s,(p:ℕ)
    have hsub : s.image Subtype.val⊆range (N+3) := by
      intro j hj
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
      have hh : (p:ℕ)≤N := single_le_sum (f:=fun i : Nat.Primes => (i:ℕ)) (fun i _ => Nat.zero_le _) hp
      exact mem_range.mpr (by omega)
    calc _ ≤ ∏ p∈s,major (p:ℕ) := prod_le_prod (fun _ _ => norm_nonneg _) (fun p _ => local_upper χ p.property)
         _ = ∏ n∈s.image Subtype.val,major n := (prod_image (fun _ _ _ _ h => Subtype.val_injective h)).symm
         _ ≤ ∏ n∈range (N+3),major n := prod_le_prod_of_subset_of_one_le hsub
           (fun n _ => zero_le_one.trans (major_one n)) (fun n _ _ => major_one n)
         _ ≤ 4 := by
           rw [telescope]
           have hz : 0<(N:ℝ)+2 := by positivity
           have h : 2*((N:ℝ)+1)/((N:ℝ)+2)≤2 := (div_le_iff₀ hz).mpr (by linarith)
           have h' : 0≤2*((N:ℝ)+1)/((N:ℝ)+2) := by positivity
           nlinarith
  · rw [tprod_eq_one_of_not_multipliable H,norm_one]; norm_num

omit [NeZero q] in
private lemma factor_at_two (ho : _root_.Odd q) :
    ‖4*χ⁻¹ 2-2‖*‖1-χ 2/2‖ = 5-4*(χ 2).re := by
  let z := χ 2
  have hunit : ‖z‖=1 := χ.unit_norm_eq_one (ZMod.unitOfCoprime 2 ho.coprime_two_left)
  have hcon : χ⁻¹ 2=conj z := (MulChar.star_apply' χ _).symm
  have hzz : z*conj z=1 := by rw [mul_conj,←Complex.sq_norm,hunit]; norm_num
  have he : 4*conj z-2=4*conj z*(1-z/2) := by linear_combination 2*hzz
  change ‖4*χ⁻¹ 2-2‖*‖1-z/2‖=5-4*z.re
  rw [hcon,he,norm_mul,norm_mul,norm_conj,hunit,mul_one]
  have hz : normSq z=1 := by rw [←Complex.sq_norm,hunit]; norm_num
  have hc : ‖(4:ℂ)‖=4 := by norm_num
  rw [hc,mul_assoc,←sq,Complex.sq_norm,normSq_sub,normSq_one,normSq_div,hz]
  simp [Complex.normSq_apply,Complex.div_re]
  ring

/-- Exact coefficient magnitude on the nonzero spectrum, requiring no Gauss-sum phase. -/
theorem odd_magnitude (hχ : χ.IsPrimitive) (ho : _root_.Odd q) (hq : 1<q) (hod : χ.Odd) :
    ‖coefficient χ‖=(5-4*(χ 2).re)*‖LFunction χ 1‖^2*‖∑' n,weight χ n‖/
      (Real.pi*Real.sqrt q*q.totient) := by
  have hi : (χ⁻¹).IsPrimitive := (conductor_inv χ).trans hχ
  have hq0 : 0<(q:ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have ht : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hs := Real.sqrt_pos.mpr hq0
  rw [odd_closed_form χ hχ hod ho hq,←product_value,norm_mul,norm_div]
  simp only [norm_mul,norm_pow,norm_I,one_mul,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    norm_natCast,gauss_norm _ hi]
  rw [←factor_at_two χ ho]
  field_simp
  rw [show ((2:ℂ)-χ 2)/2=1-χ 2/2 by ring]
  linear_combination ‖4*χ⁻¹ 2-2‖*‖LFunction χ 1‖^2*‖1-χ 2/2‖*‖∑' n,weight χ n‖*(Real.sq_sqrt hq0.le)

#print axioms odd_magnitude

private theorem transport {q m : ℕ} [NeZero q] [NeZero m] (e : q=m) {hd : q∣m}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ m) (h : changeLevel hd χ=ψ) :
    coefficient χ=coefficient ψ := by
  subst m
  simpa only [changeLevel_self] using congrArg coefficient h

theorem primitive_value {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hne : χ≠1) (ho : _root_.Odd q) : value χ=coefficient χ := by
  have hc : χ.conductor=q := hχ
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [value,if_neg hne,if_pos (hc.symm ▸ ho)]
  exact transport hc χ.primitiveCharacter χ χ.changeLevel_primitiveCharacter

theorem primitive_lvalue_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1<q) (hAP : ThetaNaturalPrimeMeans.ProgressionMangoldt) :
    ‖value χ‖≤12*‖LFunction χ 1‖^2/(Real.sqrt q*q.totient) := by
  have hne : χ≠1 := by
    intro he
    have h : χ.conductor=q := hχ
    rw [he,conductor_one] at h; omega
  have hc : χ.conductor=q := hχ
  have h0 : 0≤12*‖LFunction χ 1‖^2/(Real.sqrt q*q.totient) := by positivity
  by_cases ho : _root_.Odd q
  · rw [primitive_value χ hχ hne ho]
    by_cases hod : χ.Odd
    · rw [odd_magnitude χ hχ ho hq hod]
      have ha : 5-4*(χ 2).re≤9 := by
        have hr := (abs_le.mp ((abs_re_le_norm _).trans (χ.norm_le_one (2:ZMod q)))).1
        linarith
      have ht : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
      have hq' : 0<(q:ℝ) := by exact_mod_cast NeZero.pos q
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc _ ≤ 9*‖LFunction χ 1‖^2*4*(Real.sqrt q*q.totient) := by
                 gcongr; exact product_upper χ
           _ ≤ _ := by
                 have hπ : 36≤12*Real.pi := by linarith [Real.pi_gt_three]
                 nlinarith only [mul_le_mul_of_nonneg_right hπ
                   (show 0≤‖LFunction χ 1‖^2*(Real.sqrt q*q.totient) by positivity)]
    · have hh := (spectrum χ hχ hq hAP).2
      simp only [ho,if_true,true_and] at hh
      rw [not_ne_iff.mp (mt hh.mp hod),norm_zero]; exact h0
  · rw [value,if_neg hne,if_neg (hc.symm ▸ ho),norm_zero]; exact h0

/-- Uniform per-character conductor estimate. -/
theorem primitive_bound (hχ : χ.IsPrimitive) (hAP : ThetaNaturalPrimeMeans.ProgressionMangoldt) :
    ‖value χ‖ ≤ 12*(2+Real.log q)^2/(Real.sqrt q*q.totient) := by
  by_cases he : χ=1
  · simp only [he,value,if_true,norm_zero]; positivity
  · have hq : 1<q := by
      have h := mt (eq_one_iff_conductor_eq_one (χ:=χ)).mpr he
      have hc : χ.conductor=q := hχ
      have := NeZero.pos q
      omega
    apply (primitive_lvalue_bound χ hχ hq hAP).trans
    gcongr
    exact lvalue_bound χ he

#print axioms primitive_lvalue_bound
#print axioms primitive_bound

#print axioms product_upper

#print axioms gauss_norm
#print axioms lvalue_bound
end
end Arxiv.«2501.03234».ThetaConductorDecay
