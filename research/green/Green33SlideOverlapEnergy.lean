import Mathlib

/-! Fourier energy and joint correlations of translated finite supports. -/
open Finset
open scoped BigOperators ComplexConjugate
namespace Green33SlideConcentration
variable {G:Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def transform (f:G→ℂ) (χ:AddChar G ℂ):ℂ:=∑ x,f x*χ x

theorem invert (f:G→ℂ) (a:G) :
    ∑ χ:AddChar G ℂ,χ (-a)*transform f χ=(Fintype.card G:ℂ)*f a := by
  classical
  simp only [transform,mul_sum]
  rw [sum_comm]
  have term (x:G) (χ:AddChar G ℂ):χ (-a)*(f x*χ x)=f x*χ (x-a):=by
    rw [sub_eq_add_neg,χ.map_add_eq_mul];ring
  simp_rw [term,←mul_sum,AddChar.sum_apply_eq_ite,sub_eq_zero]
  simp [mul_ite,mul_comm]

theorem bilinear (f g:G→ℂ) :
    ∑ χ:AddChar G ℂ,transform f χ*transform g (-χ) =
      (Fintype.card G:ℂ)*∑ x,f x*g x := by
  classical
  change ∑ χ:AddChar G ℂ,transform f χ*(∑ x,g x*(-χ) x)=_
  simp only [mul_sum]
  rw [sum_comm]
  have term (x:G) (χ:AddChar G ℂ) :
      transform f χ*(g x*(-χ) x)=g x*(χ (-x)*transform f χ) := by
    rw [AddChar.neg_apply,χ.map_neg_eq_inv];ring
  simp_rw [term,←mul_sum,invert]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _;ring

theorem parseval (f:G→ℂ) :
    ∑ χ:AddChar G ℂ,‖transform f χ‖^2=(Fintype.card G:ℝ)*∑ x,‖f x‖^2 := by
  classical
  have eq (χ:AddChar G ℂ):
      transform (fun x => conj (f x)) (-χ)=conj (transform f χ) := by
    simp only [transform,map_sum,map_mul,AddChar.neg_apply,←AddChar.inv_apply_eq_conj]
    simp only [χ.map_neg_eq_inv]
  have b:=bilinear f (fun x => conj (f x))
  simp_rw [eq,Complex.mul_conj,Complex.normSq_eq_norm_sq] at b
  exact_mod_cast b
#print axioms invert
#print axioms bilinear
#print axioms parseval
noncomputable def correlation (f:G→ℂ) (t:G):ℂ:=∑ x,conj (f x)*f (x+t)

omit [DecidableEq G] in
theorem transform_correlation (f:G→ℂ) (χ:AddChar G ℂ) :
    transform (correlation f) χ=conj (transform f χ)*transform f χ := by
  classical
  have step (t x:G):(conj (f x)*f (x+t))*χ t=
      (conj (f x)*χ (-x))*(f (x+t)*χ (x+t)) := by
    rw [χ.map_add_eq_mul,χ.map_neg_eq_inv]
    have nz:χ x≠0:=by intro z;have h:=χ.norm_apply x;rw [z,norm_zero] at h;norm_num at h
    field_simp
  have shift (x:G):∑ t,f (x+t)*χ (x+t)=transform f χ :=
    Equiv.sum_comp (Equiv.addLeft x) (fun t => f t*χ t)
  change (∑ t,(∑ x,conj (f x)*f (x+t))*χ t)=_
  simp only [sum_mul,step]
  rw [sum_comm]
  simp_rw [←mul_sum,shift]
  rw [←sum_mul]
  congr 1
  simp only [transform,map_sum,map_mul,←AddChar.inv_apply_eq_conj,χ.map_neg_eq_inv]

/-- A uniform bound on the unnormalized transform bounds the mean square
of all shift correlations, with no cyclicity assumption. -/
theorem correlation_energy (f:G→ℂ) (B:ℝ) (bound:∀ χ,‖transform f χ‖≤B) :
    ∑ t,‖correlation f t‖^2 ≤ B^2 * ∑ x,‖f x‖^2 := by
  have h:=parseval (correlation f)
  simp only [transform_correlation,norm_mul,RCLike.norm_conj,mul_pow] at h
  have b:=sum_le_sum (s:=(univ:Finset (AddChar G ℂ))) (fun χ _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (bound χ) 2) (sq_nonneg ‖transform f χ‖))
  rw [←mul_sum,parseval] at b
  rw [h] at b
  apply (mul_le_mul_iff_right₀ (by positivity : 0<(Fintype.card G:ℝ))).mp
  convert b using 1
  ring
#print axioms transform_correlation
#print axioms correlation_energy
noncomputable def dens (S:Finset G):ℝ := (S.card:ℝ)/(Fintype.card G:ℝ)
noncomputable def centered (S:Finset G) (x:G):ℂ := (if x∈S then 1 else 0)-(dens S:ℂ)

theorem centered_transform (S:Finset G) (χ:AddChar G ℂ) :
    transform (centered S) χ = if χ=0 then 0 else ∑ x∈S,χ x := by
  classical
  have id:∑ x:G,(if x∈S then 1 else 0:ℂ)*χ x=∑ x∈S,χ x:=by simp [ite_mul]
  simp only [transform,centered,sub_mul,sum_sub_distrib,←mul_sum,id]
  rw [AddChar.sum_eq_ite]
  split_ifs with h
  · subst χ
    simp [dens]
  · simp

theorem centered_norm_le (S:Finset G) (x:G) : ‖centered S x‖≤1 := by
  have pos:(0:ℝ)<Fintype.card G:=by positivity
  have lo:0≤dens S:=by unfold dens;positivity
  have hi:dens S≤1:=by rw [dens,div_le_one pos];exact_mod_cast card_le_univ S
  by_cases h:x∈S
  · have eq:centered S x=((1-dens S:ℝ):ℂ):=by simp [centered,h]
    rw [eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith
  · simp only [centered,h,if_false,zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg lo]
    exact hi

/-- For a finite set, the average squared overlap error is at most its
largest squared nonconstant character sum, in count units. -/
theorem centered_energy (S:Finset G) (B:ℝ) (nonneg:0≤B)
    (bound:∀ χ:AddChar G ℂ,χ≠0→‖∑ s∈S,χ s‖≤B) :
    ∑ t,‖correlation (centered S) t‖^2 ≤ B^2*Fintype.card G := by
  classical
  have b:=correlation_energy (centered S) B (fun χ => by
    rw [centered_transform];split_ifs with h
    · simpa only [norm_zero] using nonneg
    · exact bound χ h)
  apply b.trans (mul_le_mul_of_nonneg_left _ (sq_nonneg _))
  have mass:=sum_le_sum (s:=(univ:Finset G)) fun x _ => pow_le_pow_left₀ (norm_nonneg _) (centered_norm_le S x) 2
  simpa using mass
#print axioms centered_transform
#print axioms centered_energy
def overlap (S:Finset G) (t:G):ℕ := (S.filter fun x => x+t∈S).card

theorem centered_correlation (S:Finset G) (t:G) :
    correlation (centered S) t=((overlap S t:ℝ)-(Fintype.card G:ℝ)*(dens S)^2:ℝ) := by
  classical
  let u (x:G):ℂ:=if x∈S then 1 else 0
  let p:ℂ:=dens S
  have mass:∑ x:G,u x=(S.card:ℂ):=by simp [u]
  have shifted:∑ x:G,u (x+t)=(S.card:ℂ):=(Equiv.sum_comp (Equiv.addRight t) u).trans mass
  have both:∑ x:G,u x*u (x+t)=(overlap S t:ℂ):=by
    simp only [u,ite_mul,one_mul,zero_mul,←sum_filter,filter_mem_eq_inter,univ_inter]
    simp [overlap]
  have part (x:G):conj (centered S x)*centered S (x+t)=
      u x*u (x+t)-p*u x-p*u (x+t)+p^2 := by
    have conj0:conj (u x)=u x:=by by_cases h:x∈S <;> simp [u,h]
    change conj (u x-p)*(u (x+t)-p)=_
    rw [map_sub,conj0,show conj p=p from Complex.conj_ofReal (dens S)]
    ring
  simp only [correlation,part,sum_add_distrib,sum_sub_distrib,←mul_sum,both,mass,shifted,sum_const,card_univ,nsmul_eq_mul]
  push_cast
  simp only [p,dens,Complex.ofReal_div,Complex.ofReal_natCast]
  have nz:(Fintype.card G:ℂ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring
#print axioms centered_correlation
theorem overlap_deviation (S:Finset G) (B:ℝ) (nonneg:0≤B)
    (bound:∀ χ:AddChar G ℂ,χ≠0→‖∑ s∈S,χ s‖≤B) :
    ∑ t:G,|(overlap S t:ℝ)/Fintype.card G-(dens S)^2| ≤ B := by
  classical
  let k:ℝ:=Fintype.card G
  let e (t:G):=‖correlation (centered S) t‖
  have kp:0<k:=by dsimp [k];positivity
  have cauchy:=sum_mul_sq_le_sq_mul_sq (univ:Finset G) e (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,sum_const,card_univ,nsmul_eq_mul] at cauchy
  have energy:=centered_energy S B nonneg bound
  have sq:(∑ t,e t)^2≤(B*k)^2:=calc
    _≤(∑ t,(e t)^2)*k:=by simpa only [mul_one] using cauchy
    _≤(B^2*k)*k:=mul_le_mul_of_nonneg_right energy kp.le
    _=_:=by ring
  have lin:=le_of_sq_le_sq sq (mul_nonneg nonneg kp.le)
  have point (t:G):|(overlap S t:ℝ)/k-(dens S)^2|=e t/k := by
    have eq:(overlap S t:ℝ)/k-(dens S)^2=((overlap S t:ℝ)-k*(dens S)^2)/k:=by field_simp
    rw [eq,abs_div,abs_of_pos kp]
    simp only [e,centered_correlation,Complex.norm_real,Real.norm_eq_abs];rfl
  change (∑ t:G,|(overlap S t:ℝ)/k-(dens S)^2|)≤B
  simp_rw [point]
  rw [←sum_div,div_le_iff₀ kp]
  exact lin
#print axioms overlap_deviation
theorem overlap_mass (S:Finset G) : ∑ d:G,overlap S d=S.card^2 := by
  classical
  simp only [overlap,card_filter]
  rw [sum_comm]
  have point (x:G):∑ d:G,(if x+d∈S then 1 else 0:ℕ)=S.card :=
    (Equiv.sum_comp (Equiv.addLeft x) (fun y => (if y∈S then 1 else 0:ℕ))).trans (by simp)
  simp [point,sq]

noncomputable def overlapRate (S:Finset G) (d:G):ℝ := (overlap S d:ℝ)/Fintype.card G
theorem rate_bounds (S:Finset G) (d:G) : 0≤overlapRate S d ∧ overlapRate S d≤1 := by
  have k:(0:ℝ)<Fintype.card G:=by positivity
  constructor
  · unfold overlapRate;positivity
  · rw [overlapRate,div_le_one k]
    exact_mod_cast (card_filter_le _ _).trans (card_le_univ S)

theorem quadratic_rate (S:Finset G) :
    ∑ d:G,overlapRate S d=(Fintype.card G:ℝ)*(dens S)^2 := by
  simp only [overlapRate,←sum_div,←Nat.cast_sum,overlap_mass,Nat.cast_pow,dens]
  have nz:(Fintype.card G:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  field_simp
#print axioms overlap_mass
#print axioms quadratic_rate
open Finset
theorem prod_distance {J:Type*} (S:Finset J) (f g:J→ℝ)
    (hf:∀ j,0≤f j ∧ f j≤1) (hg:∀ j,0≤g j ∧ g j≤1) :
    |(∏ j∈S,f j)-(∏ j∈S,g j)|≤∑ j∈S,|f j-g j| := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp only [prod_insert ha,sum_insert ha]
    let x:=∏ j∈S,f j
    let y:=∏ j∈S,g j
    have xp:0≤x:=prod_nonneg fun j _ => (hf j).1
    have xu:x≤1:=prod_le_one (fun j _ => (hf j).1) (fun j _ => (hf j).2)
    change |f a*x-g a*y|≤_
    rw [show f a*x-g a*y=(f a-g a)*x+g a*(x-y) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg xp,abs_of_nonneg (hg a).1]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) xu)
      ((mul_le_of_le_one_left (abs_nonneg _) (hg a).2).trans ih)
#print axioms prod_distance
variable {J:Type*} [Fintype J]
/-- One block can have arbitrary autocorrelations. Each remaining block
contributes at most its largest nonconstant Fourier coefficient to the error. -/
theorem joint_overlap (D:Finset G) (M:J→Finset G) (B:J→ℝ) (bp:∀ j,0≤B j)
    (bound:∀ j (χ:AddChar G ℂ),χ≠0→‖∑ x∈M j,χ x‖≤B j) :
    |(∑ d:G,overlapRate D d*∏ j,overlapRate (M j) d)-
      (Fintype.card G:ℝ)*(dens D)^2*∏ j,(dens (M j))^2| ≤ ∑ j,B j := by
  classical
  let C:=∏ j,(dens (M j))^2
  have est (d:G) :
      |overlapRate D d*(∏ j,overlapRate (M j) d)-overlapRate D d*C| ≤
        ∑ j,|overlapRate (M j) d-(dens (M j))^2| := by
    rw [←mul_sub,abs_mul,abs_of_nonneg (rate_bounds D d).1]
    apply (mul_le_of_le_one_left (abs_nonneg _) (rate_bounds D d).2).trans
    apply prod_distance univ _ _ (fun j => rate_bounds (M j) d)
    intro j
    have lo:0≤dens (M j):=by unfold dens;positivity
    have hi:dens (M j)≤1:=by rw [dens,div_le_one (by positivity)];exact_mod_cast card_le_univ (M j)
    exact ⟨sq_nonneg _,by nlinarith [mul_nonneg lo (sub_nonneg.mpr hi)]⟩
  rw [←quadratic_rate,Finset.sum_mul,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum (fun d _ => est d)).trans
  rw [sum_comm]
  apply sum_le_sum
  intro j _
  exact overlap_deviation (M j) (B j) (bp j) (bound j)
#print axioms joint_overlap

end Green33SlideConcentration
