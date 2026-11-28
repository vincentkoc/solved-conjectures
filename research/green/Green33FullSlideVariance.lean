import Green33OddSlideVariance

/-! Concentration of sumset coverage under independent odd quotient translations. -/
open Finset Filter Green33LayerSlides
open scoped Pointwise Topology
namespace Green33SlideConcentration
variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
/-- The original size plus three times the surplus in the unordered-pair budget. -/
noncomputable def slideCost (k n:ℕ):ℝ := k+3*((((k+1).choose 2:ℕ):ℝ)-n)

theorem slots_cover (T:Finset H) (full:T+T=univ) : Fintype.card H ≤ (T.card+1).choose 2 := by
  have h:=mixed_pair_budget T ∅ ∅ (empty_subset _) (empty_subset _) (by simp)
  simpa [full] using h

theorem critical_row_cost {m:ℕ+} (π:H→+ZMod m) (T:Finset H) (full:T+T=univ)
    (a b:ZMod m) (ne:a≠b) (t:H) (label:π t=a+b) (χ:AddChar π.ker ℂ) (nz:χ≠0) :
    ‖∑ z∈(rowSupport π T t a b)ᶜ,χ z‖ ≤ slideCost T.card (Fintype.card H) := by
  classical
  let k:ℝ:=T.card
  let n:ℝ:=Fintype.card H
  let s:ℝ:=((T.card+1).choose 2:ℕ)
  have sn:n ≤ s:=by dsimp [n,s];exact_mod_cast slots_cover T full
  have id:k^2+k=2*s:=by dsimp [k,s];rw [Nat.cast_choose_two,Nat.cast_add_one];ring
  have pos:0 ≤ k^2+2*k-2*n:=by
    have : 0 ≤ k:=by unfold k;positivity
    linarith
  let B:=Real.sqrt (k^2+2*k-2*n)
  have cap (ψ:AddChar H ℂ) (hz:ψ≠0):‖∑ x∈T,ψ x‖ ≤ B := by
    apply Real.le_sqrt_of_sq_le
    have hh:=Green33Fourier.character_norm_sq_bound T full ψ hz
    dsimp [k,n];linarith
  have localBound:=mixed_row_bound π T a b t label B cap χ nz
  have cost:=mixed_pair_budget T (layer π T a) (layer π T b) (filter_subset _ _) (filter_subset _ _)
    (Finset.disjoint_left.mpr fun _ ha hb => ne ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2))
  rw [full,card_univ] at cost
  have h:n+((layer π T a).card:ℝ)*(layer π T b).card ≤ s+(layer π T a+layer π T b).card:=by
    dsimp [n,s];exact_mod_cast cost
  let U:=rowSupport π T t a b
  have total:=U.sum_add_sum_compl (fun z => χ z)
  rw [AddChar.sum_eq_zero_iff_ne_zero.mpr nz] at total
  have eq:(∑ z∈Uᶜ,χ z)=-(∑ z∈U,χ z):=by linear_combination total
  change ‖∑ z∈Uᶜ,χ z‖ ≤ _
  rw [eq,norm_neg]
  apply localBound.trans
  rw [show B^2=k^2+2*k-2*n from Real.sq_sqrt pos]
  change _ ≤ k+3*(s-n)
  linarith

theorem full_row_variance {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (T:Finset H)
    (full:T+T=univ) (c:ZMod m) (t:H) (row:π t=c+c) :
    (∑ h:ZMod m→π.ker,(dens (missSet π T t h)-rowMiss π T t)^2)/(Fintype.card π.ker:ℝ)^m.val  ≤
      ((positiveHalf m).card:ℝ)*slideCost T.card (Fintype.card H)/Fintype.card π.ker := by
  have nn:0 ≤ slideCost T.card (Fintype.card H) := by
    have b:(Fintype.card H:ℝ) ≤ (((T.card+1).choose 2:ℕ):ℝ):=by exact_mod_cast slots_cover T full
    unfold slideCost
    linarith [Nat.cast_nonneg (α:=ℝ) T.card]
  have bound (j:positiveHalf m) (χ:AddChar π.ker ℂ) (nz:χ≠0) :=
    critical_row_cost π T full (c+j.val) (c-j.val) (by
      intro eq
      rw [sub_eq_add_neg] at eq
      have e:=add_left_cancel eq
      have lt:=(mem_filter.mp j.property).2
      rw [←e] at lt
      exact lt_irrefl _ lt) t (by rw [row];abel) χ nz
  simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul] using
    row_variance odd π T c t row (fun _ => slideCost T.card (Fintype.card H)) (fun _ => nn) bound
#print axioms critical_row_cost
#print axioms full_row_variance
noncomputable def coverage {m:ℕ+} (π:H→+ZMod m) (T:Finset H) (h:ZMod m→π.ker) : ℝ :=
  ((displaced π T h+displaced π T h).card:ℝ)/Fintype.card H

/-- The fraction covered in one slide is the complement of the mean of its
row miss fractions, with every target and its actual translates counted. -/
theorem coverage_rows {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (T:Finset H)
    (s:ZMod m→H) (right:Function.RightInverse s π) (h:ZMod m→π.ker) :
    coverage π T h=1-(∑ c:ZMod m,dens (missSet π T (s (c+c)) h))/(m:ℝ) := by
  classical
  let e:=((doubleEquiv odd).prodCongr (Equiv.refl π.ker)).trans (sectionCoordinates π s right)
  let A:=displaced π T h+displaced π T h
  let f (a:H):ℕ:=if a∉A then 1 else 0
  have eq:=e.sum_comp f
  rw [Fintype.sum_prod_type] at eq
  have src:(∑ c:ZMod m,(missSet π T (s (c+c)) h).card)=Aᶜ.card := by
    simp only [missSet,card_filter]
    change (∑ c:ZMod m,∑ x:π.ker,f (e (c,x)))=_
    rw [eq]
    dsimp only [f];rw [←card_filter];congr 1;ext a;simp
  have n:(m:ℝ)*(Fintype.card π.ker:ℝ)=(Fintype.card H:ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_prod,ZMod.card] using Fintype.card_congr e :
      m.val*Fintype.card π.ker=Fintype.card H)
  have size:((A.card:ℝ)+Aᶜ.card)=(Fintype.card H:ℝ):=by exact_mod_cast card_add_card_compl A
  have k:(Fintype.card π.ker:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  have d:(m:ℝ)≠0:=by exact_mod_cast m.pos.ne'
  change (A.card:ℝ)/(Fintype.card H:ℝ)=_
  simp only [dens,←sum_div,←Nat.cast_sum,src]
  rw [←n] at size ⊢
  field_simp [k,d]
  linarith

theorem square_of_mean {I J:Type*} [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
    (f:I→J→ℝ) (B:ℝ) (cap:∀ i,(∑ j,(f i j)^2)/(Fintype.card J:ℝ)≤B) :
    (∑ j,((∑ i,f i j)/(Fintype.card I:ℝ))^2)/(Fintype.card J:ℝ)≤B := by
  classical
  let a:ℝ:=Fintype.card I
  let b:ℝ:=Fintype.card J
  have ap:0<a:=by dsimp [a];positivity
  have bp:0<b:=by dsimp [b];positivity
  have one (j:J):((∑ i,f i j)/a)^2 ≤ (∑ i,(f i j)^2)/a := by
    have cc:=sum_mul_sq_le_sq_mul_sq (univ:Finset I) (fun i => f i j) (fun _ => (1:ℝ))
    simp only [mul_one,one_pow,sum_const,card_univ,nsmul_eq_mul] at cc
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos ap) ap]
    nlinarith [mul_le_mul_of_nonneg_right cc ap.le]
  change (∑ j,((∑ i,f i j)/a)^2)/b≤B
  apply (div_le_div_of_nonneg_right (sum_le_sum fun j _ => one j) bp.le).trans
  rw [←sum_div,sum_comm,div_div, mul_comm a b,←div_div,sum_div]
  apply (div_le_iff₀ ap).mpr
  have hi:=sum_le_sum (s:=(univ:Finset I)) fun i _ => cap i
  simpa only [sum_const,card_univ,nsmul_eq_mul,mul_comm B,a,b] using hi
#print axioms coverage_rows
#print axioms square_of_mean
/-- The loss of concentration is controlled by the size and the original
unordered-pair surplus. The bound holds even when the odd quotient grows. -/
theorem full_coverage_variance {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (onto:Function.Surjective π)
    (T:Finset H) (full:T+T=univ) :
    (∑ h:ZMod m→π.ker,(coverage π T h-meanCoverage π T)^2)/(Fintype.card π.ker:ℝ)^m.val ≤
      ((positiveHalf m).card:ℝ)*(m:ℝ)*slideCost T.card (Fintype.card H)/Fintype.card H := by
  classical
  let s:=Function.surjInv onto
  have right:Function.RightInverse s π:=Function.rightInverse_surjInv onto
  let f (c:ZMod m) (h:ZMod m→π.ker):=dens (missSet π T (s (c+c)) h)-rowMiss π T (s (c+c))
  have eq (h:ZMod m→π.ker):
      (coverage π T h-meanCoverage π T)^2=((∑ c:ZMod m,f c h)/(m:ℝ))^2 := by
    rw [coverage_rows odd π T s right h,meanCoverage_rows odd π T s right]
    simp only [f,sum_sub_distrib]
    ring
  simp_rw [eq]
  have row (c:ZMod m):=full_row_variance odd π T full c (s (c+c)) (right _)
  have cap:=square_of_mean f (((positiveHalf m).card:ℝ)*slideCost T.card (Fintype.card H)/Fintype.card π.ker)
    (fun c => by simpa only [Fintype.card_fun,ZMod.card,Nat.cast_pow] using row c)
  simp only [Fintype.card_fun,ZMod.card,Nat.cast_pow] at cap
  apply cap.trans_eq
  have size:(m:ℝ)*(Fintype.card π.ker:ℝ)=(Fintype.card H:ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_prod,ZMod.card] using Fintype.card_congr (sectionCoordinates π s right) :
      m.val*Fintype.card π.ker=Fintype.card H)
  have nz:(m:ℝ)≠0:=by exact_mod_cast m.pos.ne'
  have kn:(Fintype.card π.ker:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero
  rw [←size]
  field_simp
#print axioms full_coverage_variance

end Green33SlideConcentration
