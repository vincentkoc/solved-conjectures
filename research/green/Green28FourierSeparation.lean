import Green28InverseStability
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A two-frequency obstruction to approximating uniform integer arithmetic progressions by convolution. -/

namespace Green28FourierSeparation
open Finset Green28 Green28InverseStability MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable def coeff {ι : Type*} [Fintype ι] (P : PMF ι) (z : ι → ℂ) : ℂ :=
  ∑ i, ((P i).toReal:ℂ)*z i

private theorem total {ι : Type*} [Fintype ι] (P : PMF ι) : ∑ i, (P i).toReal = 1 := by
  have h := congrArg ENNReal.toReal P.tsum_coe
  rwa [tsum_fintype,ENNReal.toReal_sum (fun _ _ => P.apply_ne_top _),ENNReal.toReal_one] at h

/-- The characteristic-function doubling inequality for arbitrary finite unit phases. -/
theorem doubling {ι : Type*} [Fintype ι] (P : PMF ι) (z : ι → ℂ) (unit : ∀ i, ‖z i‖ = 1) :
    2*‖coeff P z‖^2 ≤ 1+‖coeff P (fun i => z i^2)‖ := by
  classical
  let w := fun i => (P i).toReal
  let a := coeff P z
  let b := coeff P (fun i => z i^2)
  have one : ∑ i, w i = 1 := total P
  have oneC : (∑ i, (w i:ℂ)) = 1 := by exact_mod_cast one
  have centered : (∑ i, (w i:ℂ)*(z i-a)^2) = b-a^2 := by
    calc
      _ = ∑ i, ((w i:ℂ)*z i^2 - (w i*z i)*(2*a) + (w i:ℂ)*a^2) := by
        apply sum_congr rfl;intro i _;ring
      _ = _ := by
        rw [sum_add_distrib,sum_sub_distrib,←sum_mul,←sum_mul,oneC,one_mul]
        change b-a*(2*a)+a^2 = b-a^2
        ring
  have re (i : ι) : w i*(z i*conj a).re = ((w i:ℂ)*z i*conj a).re := by
    rw [mul_assoc];simp
  have proj : (∑ i, w i*(z i*conj a).re) = ‖a‖^2 := by
    simp_rw [re]
    rw [←Complex.re_sum,←sum_mul]
    change (a*conj a).re = _
    rw [Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have variance : (∑ i, w i*‖z i-a‖^2) = 1-‖a‖^2 := by
    calc
      _ = ∑ i, (w i + w i*‖a‖^2 - 2*(w i*(z i*conj a).re)) := by
        apply sum_congr rfl;intro i _
        rw [←Complex.normSq_eq_norm_sq,Complex.normSq_sub,Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq,unit];ring
      _ = _ := by
        rw [sum_sub_distrib,sum_add_distrib,←sum_mul,←mul_sum,proj,one];ring
  have bound : ‖b-a^2‖ ≤ 1-‖a‖^2 := by
    rw [←centered,←variance]
    apply (norm_sum_le ..).trans
    exact sum_le_sum fun i _ => by rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  have tri := norm_sub_le b (b-a^2)
  rw [sub_sub_cancel,norm_pow] at tri
  change 2*‖a‖^2 ≤ 1+‖b‖
  linarith

private theorem projected_event {ι : Type*} (g : ℤ → ι) (P : PMF ℤ) (S : Finset ι) :
    (∑ i ∈ S, ((P.map g) i).toReal) = P.toMeasure.real (g ⁻¹' (S:Set ι)) := by
  rw [Measure.real,PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (.of_discrete),
    ←PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_apply_finset,ENNReal.toReal_sum (fun i _ => (P.map g).apply_ne_top i)]

/-- Total variation controls all bounded complex Fourier tests on finite quotients of the integers. -/
theorem coeff_close {ι : Type*} [Fintype ι] {P Q : PMF ℤ} {δ : ℝ} (h : TVLe δ P Q)
    (g : ℤ → ι) (z : ι → ℂ) (unit : ∀ i, ‖z i‖ = 1) :
    ‖coeff (P.map g) z - coeff (Q.map g) z‖ ≤ 2*δ := by
  classical
  let d := fun i => ((P.map g) i).toReal - ((Q.map g) i).toReal
  let S := Finset.univ.filter (fun i => 0 ≤ d i)
  have zero : ∑ i, d i = 0 := by simp only [d,sum_sub_distrib,total,sub_self]
  have posPart : ∑ i ∈ S, d i ≤ δ := by
    simp only [d,sum_sub_distrib,projected_event]
    linarith [h (g ⁻¹' (S:Set ι))]
  have l1 : (∑ i, |d i|) = 2*∑ i ∈ S, d i := by
    have point (i : ι) : |d i| = 2*(if 0 ≤ d i then d i else 0)-d i := by
      by_cases pos : 0 ≤ d i
      · rw [if_pos pos,abs_of_nonneg pos];ring
      · rw [if_neg pos,abs_of_neg (lt_of_not_ge pos)];ring
    simp_rw [point]
    rw [sum_sub_distrib,←mul_sum,zero,sub_zero,←sum_filter]
  have diff : coeff (P.map g) z - coeff (Q.map g) z = ∑ i, (d i:ℂ)*z i := by
    unfold coeff
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [←sub_mul,←Complex.ofReal_sub]
  calc
    _ ≤ ∑ i, |d i| := by
      rw [diff]
      exact (norm_sum_le ..).trans (sum_le_sum fun i _ => by simp [Complex.norm_real,Real.norm_eq_abs,unit])
    _ ≤ _ := by linarith

private theorem coeff_bind {ι κ : Type*} [Fintype ι] [Fintype κ] (P : PMF ι)
    (f : ι → PMF κ) (z : κ → ℂ) : coeff (P.bind f) z = coeff P (fun i => coeff (f i) z) := by
  unfold coeff
  simp only [PMF.bind_apply,tsum_fintype,ENNReal.toReal_sum (fun i _ =>
    ENNReal.mul_ne_top (P.apply_ne_top i) ((f i).apply_ne_top _)),ENNReal.toReal_mul,
    Complex.ofReal_sum,Complex.ofReal_mul,sum_mul,mul_sum,mul_assoc]
  exact sum_comm

private theorem coeff_pure {ι : Type*} [Fintype ι] (a : ι) (z : ι → ℂ) :
    coeff (PMF.pure a) z = z a := by
  classical
  rw [coeff,sum_eq_single a]
  · simp
  · intro i _ hi;simp [PMF.pure_apply,hi]
  · simp

private theorem coeff_map {ι κ : Type*} [Fintype ι] [Fintype κ] (P : PMF ι) (f : ι → κ) (z : κ → ℂ) :
    coeff (P.map f) z = coeff P (fun i => z (f i)) := by
  change coeff (P.bind fun i => PMF.pure (f i)) z = _
  simp only [coeff_bind,coeff_pure]

/-- Fourier coefficient after applying a finite-valued additive map to the integer law. -/
noncomputable def freq {G : Type*} [Fintype G] [AddGroup G] (g : ℤ →+ G) (z : G → ℂ) (P : PMF ℤ) : ℂ :=
  coeff (P.map g) z

private theorem freq_sum {G : Type*} [Fintype G] [AddGroup G] (g : ℤ →+ G)
    (z : G → ℂ) (add : ∀ a b, z (a+b)=z a*z b) (P Q : PMF ℤ) :
    freq g z (indepSum P Q) = freq g z P * freq g z Q := by
  have transfer : (indepSum P Q).map g = (P.map g).bind (fun a => (Q.map g).map (fun b => a+b)) := by
    simp only [indepSum,Bind.bind,PMF.map_bind,PMF.pure_map,PMF.bind_map,PMF.map_comp,
      Function.comp_def,map_add]
    rfl
  unfold freq
  rw [transfer,coeff_bind]
  simp only [coeff_map]
  unfold coeff
  simp only [add]
  simp_rw [show ∀ a b, (((Q.map g) b).toReal:ℂ) * (z a*z b) = z a*(((Q.map g) b).toReal*z b) by intro a b;ring,
    ←mul_sum,←mul_assoc,←sum_mul]

/-- For two independent summands, one frequency and its double distinguish their Fourier
magnitudes when the output has large first coefficient and small second coefficient. -/
theorem two_frequencies {G : Type*} [Fintype G] [AddGroup G] (g : ℤ →+ G)
    (z : G → ℂ) (add : ∀ a b, z (a+b)=z a*z b) (unit : ∀ i, ‖z i‖=1)
    {P Q R : PMF ℤ} {δ : ℝ} (near : TVLe δ (indepSum P Q) R) :
    2*‖freq g z R‖-1-4*δ-Real.sqrt (‖freq g (fun i => z i^2) R‖+2*δ) ≤
      |‖freq g z P‖^2-‖freq g z Q‖^2| := by
  let a := ‖freq g z P‖
  let b := ‖freq g z Q‖
  let c := ‖freq g (fun i => z i^2) P‖
  let d := ‖freq g (fun i => z i^2) Q‖
  have hs (i j : G) : z (i+j)^2 = z i^2*z j^2 := by rw [add,mul_pow]
  have h1 := (abs_norm_sub_norm_le _ _).trans (coeff_close near g z unit)
  have h2 := (abs_norm_sub_norm_le _ _).trans (coeff_close near g (fun i => z i^2) (by simp [unit]))
  change |‖freq g z (indepSum P Q)‖-‖freq g z R‖| ≤ _ at h1
  change |‖freq g (fun i => z i^2) (indepSum P Q)‖-‖freq g (fun i => z i^2) R‖| ≤ _ at h2
  rw [freq_sum g z add,norm_mul] at h1
  rw [freq_sum g _ hs,norm_mul] at h2
  have first : ‖freq g z R‖ - 2*δ ≤ a*b := by linarith [(abs_le.mp h1).1]
  have second : c*d ≤ ‖freq g (fun i => z i^2) R‖+2*δ := by linarith [(abs_le.mp h2).2]
  have da : 2*a^2 ≤ 1+c := doubling (P.map g) z unit
  have db : 2*b^2 ≤ 1+d := doubling (Q.map g) z unit
  have mc : min c d ≤ Real.sqrt (‖freq g (fun i => z i^2) R‖+2*δ) := by
    apply Real.le_sqrt_of_sq_le
    apply le_trans _ second
    rcases le_total c d with h|h
    · rw [min_eq_left h,pow_two];exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    · rw [min_eq_right h,pow_two];exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  change _ ≤ |a^2-b^2|
  rcases le_total c d with h|h
  · rw [min_eq_left h] at mc
    nlinarith [sq_nonneg (a-b),neg_le_abs (a^2-b^2)]
  · rw [min_eq_right h] at mc
    nlinarith [sq_nonneg (a-b),le_abs_self (a^2-b^2)]

/-- The arithmetic progression with initial term `a`, spacing `d`, and `k` terms. -/
def progression (a : ℤ) (d k : ℕ) : Finset ℤ := (range k).image (fun j : ℕ => a+(d:ℤ)*j)

theorem progression_ne (a : ℤ) (d : ℕ) {k : ℕ} (hk : 0 < k) : (progression a d k).Nonempty :=
  ⟨a,mem_image.mpr ⟨0,mem_range.mpr hk,by simp⟩⟩

theorem mem_unit_progression {a z : ℤ} {k : ℕ} : z ∈ progression a 1 k ↔ a ≤ z ∧ z < a+(k:ℤ) := by
  constructor
  · intro h
    obtain ⟨j,hj,rfl⟩ := mem_image.mp h
    have := mem_range.mp hj
    simp only [Nat.cast_one,one_mul]
    omega
  · intro ⟨lo,hi⟩
    exact mem_image.mpr ⟨(z-a).toNat,mem_range.mpr (by omega),by simp only [Nat.cast_one,one_mul];omega⟩

private theorem mapped_uniform {G : Type*} [Fintype G] (g : ℤ → G) (z : G → ℂ)
    {S : Finset ℤ} (hs : S.Nonempty) :
    coeff ((PMF.uniformOfFinset S hs).map g) z = (S.card:ℂ)⁻¹*∑ i ∈ S, z (g i) := by
  classical
  have atom (j : G) : ((PMF.uniformOfFinset S hs).map g j).toReal =
      ∑ i ∈ S, if j=g i then (S.card:ℝ)⁻¹ else 0 := by
    rw [PMF.map_apply,tsum_eq_sum (s:=S) (fun i hi => by simp [PMF.uniformOfFinset_apply_of_notMem hs hi]),
      ENNReal.toReal_sum]
    · apply sum_congr rfl
      intro i hi
      by_cases eq : j=g i <;> simp [eq,PMF.uniformOfFinset_apply_of_mem hs hi]
    · intro i hi
      split <;> simp [PMF.uniformOfFinset_apply_of_mem hs hi,hs.ne_empty]
  unfold coeff
  simp only [atom,Complex.ofReal_sum,sum_mul]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [sum_eq_single (g i)]
  · simp
  · intro j _ h;simp [h]
  · simp

private theorem progression_coeff {G : Type*} [Fintype G] [AddGroup G] (g : ℤ →+ G)
    (z : G → ℂ) (add : ∀ u v, z (u+v)=z u*z v) (zero : z 0=1)
    (a : ℤ) {k d : ℕ} (hd : 0 < d) (hk : 0 < k) :
    freq g z (PMF.uniformOfFinset (progression a d k) (progression_ne a d hk)) =
      (k:ℂ)⁻¹*z (g a)*∑ j ∈ range k, z (g (d:ℤ))^j := by
  classical
  have inj : Function.Injective (fun j : ℕ => a+(d:ℤ)*j) := by
    intro i j eq
    dsimp at eq
    exact_mod_cast mul_left_cancel₀ (show (d:ℤ) ≠ 0 by exact_mod_cast hd.ne') (add_left_cancel eq)
  have pow (j : ℕ) : z (g ((d:ℤ)*j)) = z (g (d:ℤ))^j := by
    induction j with
    | zero => simp [zero]
    | succ j ih => rw [Nat.cast_succ,mul_add,mul_one,map_add,add,ih,pow_succ]
  rw [freq,mapped_uniform,progression,card_image_of_injective _ inj,card_range,sum_image inj.injOn]
  simp_rw [map_add,add,pow]
  rw [←mul_sum,mul_assoc]

private abbrev modMap (k : ℕ) := (Int.castRingHom (ZMod (2*k))).toAddMonoidHom

private theorem progression_spectrum (a : ℤ) {k d : ℕ} (hk : 2 ≤ k) (hd : 0 < d) [NeZero (2*(k*d))] :
    let g := modMap (k*d)
    let χ := (ZMod.stdAddChar (N:=2*(k*d)) : ZMod (2*(k*d)) → ℂ)
    let U := PMF.uniformOfFinset (progression a d k) (progression_ne a d (by omega))
    2/Real.pi ≤ ‖freq g χ U‖ ∧ freq g (fun x => χ x^2) U = 0 := by
  classical
  let g := modMap (k*d)
  let χ := (ZMod.stdAddChar (N:=2*(k*d)) : ZMod (2*(k*d)) → ℂ)
  let U := PMF.uniformOfFinset (progression a d k) (progression_ne a d (by omega))
  let w := χ (g (d:ℤ))
  change 2/Real.pi ≤ ‖freq g χ U‖ ∧ freq g (fun x => χ x^2) U = 0
  have add (x y) : χ (x+y) = χ x*χ y := AddChar.map_add_eq_mul _ _ _
  have zero : χ 0 = 1 := AddChar.map_zero_eq_one _
  have unit (x) : ‖χ x‖ = 1 := Circle.norm_coe _
  have kR : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have kC : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have dC : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have form : w = Complex.exp (Complex.I * ((Real.pi / k : ℝ):ℂ)) := by
    change ZMod.stdAddChar ((d:ℤ):ZMod (2*(k*d))) = _
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    field_simp
  have powk : w^k = -1 := by
    rw [form,←Complex.exp_nat_mul,←Complex.exp_pi_mul_I]
    congr 1
    push_cast
    field_simp
  have chord : ‖w-1‖ ≤ Real.pi/k := by
    rw [form]
    simpa only [Real.norm_eq_abs,abs_of_pos (div_pos Real.pi_pos kR)] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=Real.pi / k))
  have different : w^2 ≠ 1 := by
    intro same
    have eq : χ (g ((d:ℤ)+d)) = χ 0 := by
      rw [map_add,add,←pow_two,zero]
      exact same
    have eq' := ZMod.injective_stdAddChar eq
    change (((d:ℤ)+d:ℤ):ZMod (2*(k*d))) = 0 at eq'
    have dv := (ZMod.natCast_eq_zero_iff (d+d) (2*(k*d))).mp (by push_cast at eq' ⊢;exact eq')
    have lo := Nat.le_of_dvd (by omega : 0<d+d) dv
    have hi := Nat.mul_le_mul_right d hk
    omega
  let S := ∑ j ∈ range k, w^j
  have mult := geom_sum_mul w k
  change S*(w-1) = _ at mult
  rw [powk] at mult
  have n := congrArg norm mult
  rw [norm_mul,show (-1-1:ℂ)=(-2:ℝ) by norm_num] at n
  norm_num at n
  have bound : 2 ≤ ‖S‖*(Real.pi/k) := n ▸ mul_le_mul_of_nonneg_left chord (norm_nonneg _)
  let V := ∑ j ∈ range k,(w^2)^j
  have ns := geom_sum_mul (w^2) k
  change V*(w^2-1) = (w^2)^k-1 at ns
  rw [←pow_mul,Nat.mul_comm 2 k,pow_mul,powk] at ns
  have v0 : V = 0 := (mul_eq_zero.mp (by calc V*(w^2-1) = (-1:ℂ)^2-1 := ns
                                             _ = 0 := by norm_num)).resolve_right (sub_ne_zero.mpr different)
  constructor
  · rw [progression_coeff g χ add zero a hd (by omega : 0<k)]
    change 2/Real.pi ≤ ‖(k:ℂ)⁻¹*χ (g a)*S‖
    rw [norm_mul,norm_mul,unit,mul_one,norm_inv,Complex.norm_natCast]
    rw [div_le_iff₀ Real.pi_pos]
    calc 2 ≤ ‖S‖*(Real.pi/k) := bound
         _ = _ := by ring
  · have hs (x y) : χ (x+y)^2 = χ x^2*χ y^2 := by rw [add,mul_pow]
    rw [progression_coeff g _ hs (by simp [zero]) a hd (by omega : 0<k)]
    change _ * V = 0
    rw [v0,mul_zero]

/-- The law of the difference of two independent draws from the same marginal. -/
noncomputable def differenceLaw (P : PMF ℤ) : PMF ℤ := indepSum P (P.map (fun x => -x))

/-- Squared modulus of the Fourier coefficient at the angle `π/k`. -/
noncomputable def halfPower (k : ℕ) (hk : 2 ≤ k) (P : PMF ℤ) : ℝ :=
  letI : NeZero (2*k) := ⟨by omega⟩
  ‖freq (modMap k) ZMod.stdAddChar P‖^2

private theorem freq_difference {G : Type*} [Fintype G] [AddGroup G] (g : ℤ →+ G) (χ : G → ℂ)
    (add : ∀ a b, χ (a+b) = χ a*χ b) (neg : ∀ a, χ (-a) = conj (χ a)) (P : PMF ℤ) :
    freq g χ (differenceLaw P) = ((‖freq g χ P‖^2:ℝ):ℂ) := by
  have swap : ((P.map (fun x : ℤ => -x)).map g) = (P.map g).map (fun x => -x) := by
    simp only [PMF.map_comp,Function.comp_def,map_neg]
  have reflected : freq g χ (P.map (fun x : ℤ => -x)) = conj (freq g χ P) := by
    unfold freq
    rw [swap,coeff_map]
    simp only [coeff,neg,map_sum,map_mul,Complex.conj_ofReal]
  rw [differenceLaw,freq_sum g χ add,reflected,Complex.mul_conj,Complex.normSq_eq_norm_sq]

private theorem two_le_period {k d : ℕ} (hk : 2 ≤ k) (hd : 0 < d) : 2 ≤ k*d :=
  hk.trans (Nat.le_mul_of_pos_right k hd)

/-- An approximate uniform arithmetic progression forces different Fourier magnitudes in its two factors.
The approximate input supports and their locations are unrestricted. -/
theorem progression_power_gap {k d : ℕ} (hk : 2 ≤ k) (hd : 0 < d) (a : ℤ) {P Q : PMF ℤ} {δ : ℝ}
    (h : TVLe δ (indepSum P Q) (PMF.uniformOfFinset (progression a d k) (progression_ne a d (by omega)))) :
    4/Real.pi-1-4*δ-Real.sqrt (2*δ) ≤ |halfPower (k*d) (two_le_period hk hd) P - halfPower (k*d) (two_le_period hk hd) Q| := by
  have period := two_le_period hk hd
  let _ : NeZero (2*(k*d)) := ⟨by omega⟩
  let χ := (ZMod.stdAddChar (N:=2*(k*d)) : ZMod (2*(k*d)) → ℂ)
  have gap := two_frequencies (modMap (k*d)) χ (AddChar.map_add_eq_mul _)
    (fun i => Circle.norm_coe _) h
  obtain ⟨first,second⟩ := progression_spectrum a hk hd
  change freq (modMap (k*d)) (fun i => χ i^2) _ = 0 at second
  rw [second,norm_zero,zero_add] at gap
  change _ ≤ |‖freq (modMap (k*d)) χ P‖^2 - ‖freq (modMap (k*d)) χ Q‖^2|
  linarith [show 4/Real.pi=2*(2/Real.pi) by ring]

/-- Closeness of the difference laws controls the same spectral discrepancy. -/
theorem difference_power_close {k : ℕ} (hk : 2 ≤ k) {P Q : PMF ℤ} {η : ℝ}
    (h : TVLe η (differenceLaw P) (differenceLaw Q)) :
    |halfPower k hk P - halfPower k hk Q| ≤ 2*η := by
  let _ : NeZero (2*k) := ⟨by omega⟩
  let χ := (ZMod.stdAddChar (N:=2*k) : ZMod (2*k) → ℂ)
  have neg (x : ZMod (2*k)) : χ (-x) = conj (χ x) := by
    have unit : ‖χ x‖ = 1 := Circle.norm_coe _
    apply mul_right_cancel₀ (show χ x ≠ 0 by intro h;rw [h,norm_zero] at unit;norm_num at unit)
    calc χ (-x)*χ x = χ (-x+x) := (AddChar.map_add_eq_mul _ _ _).symm
         _ = 1 := by rw [neg_add_cancel];exact AddChar.map_zero_eq_one _
         _ = conj (χ x)*χ x := by rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,unit];norm_num
  have diff := coeff_close h (modMap k) χ (fun x => Circle.norm_coe _)
  change ‖freq (modMap k) χ (differenceLaw P) - freq (modMap k) χ (differenceLaw Q)‖ ≤ _ at diff
  rw [freq_difference _ _ (AddChar.map_add_eq_mul _) neg,freq_difference _ _ (AddChar.map_add_eq_mul _) neg,
    ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at diff
  exact diff

/-- Neither the sum nor the two difference laws can simultaneously meet tolerances whose
sum is at most `1/52`, for any nontrivial finite uniform arithmetic progression. -/
theorem progression_difference_gap {k d : ℕ} (hk : 2 ≤ k) (hd : 0 < d) (a : ℤ) {P Q : PMF ℤ} {δ η : ℝ}
    (out : TVLe δ (indepSum P Q) (PMF.uniformOfFinset (progression a d k) (progression_ne a d (by omega))))
    (corr : TVLe η (differenceLaw P) (differenceLaw Q)) : 1/52 < δ+η := by
  have d0 : 0 ≤ δ := by simpa using out ∅
  have e0 : 0 ≤ η := by simpa using corr ∅
  have spectral := (progression_power_gap hk hd a out).trans (difference_power_close (two_le_period hk hd) corr)
  by_contra! small
  have sq := Real.sq_sqrt (by linarith : 0 ≤ 2*δ)
  have root : Real.sqrt (2*δ) ≤ 19612/100000 := by
    by_contra! h
    nlinarith [sq_pos_of_pos (show 0 < Real.sqrt (2*δ)-19612/100000 by linarith)]
  have piBound : (4:ℝ)/3.1416 ≤ 4/Real.pi := div_le_div_of_nonneg_left (by norm_num) Real.pi_pos Real.pi_lt_d4.le
  linarith

/-- Equal difference laws give a universal exclusion for every integer arithmetic progression
of at least two points. This includes independent copies and reflected or translated copies. -/
theorem equal_differences_gap {P Q : PMF ℤ} (same : differenceLaw P = differenceLaw Q)
    (a : ℤ) {k d : ℕ} (hk : 2 ≤ k) (hd : 0 < d) :
    ¬TVLe (1/52) (indepSum P Q) (PMF.uniformOfFinset (progression a d k) (progression_ne a d (by omega))) := by
  intro near
  have corr : TVLe 0 (differenceLaw P) (differenceLaw Q) := fun E => by simp [same]
  linarith [progression_difference_gap hk hd a near corr]

/-- Uniform progressions are separated by more than `1/52` from every convolution square. -/
theorem iid_progression_gap (P : PMF ℤ) (a : ℤ) {k d : ℕ} (hk : 2 ≤ k) (hd : 0 < d) :
    ¬TVLe (1/52) (indepSum P P) (PMF.uniformOfFinset (progression a d k) (progression_ne a d (by omega))) :=
  equal_differences_gap rfl a hk hd

#print axioms doubling
#print axioms coeff_close
#print axioms two_frequencies
#print axioms progression_ne
#print axioms mem_unit_progression
#print axioms progression_power_gap
#print axioms difference_power_close
#print axioms progression_difference_gap
#print axioms equal_differences_gap
#print axioms iid_progression_gap
end Green28FourierSeparation
