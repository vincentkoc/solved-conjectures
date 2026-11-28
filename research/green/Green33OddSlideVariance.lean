import Green33SlideRowMoments
import Green33LayerTransformBounds

/-! Bounds for variance over independent quotient-layer translations. -/
open Finset Green33LayerSlides Filter
open scoped Pointwise Topology
namespace Green33SlideConcentration
variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
theorem first_row_moment {m:ℕ+} (π:H→+ZMod m) (A:Finset H) (t:H) :
    (∑ h:ZMod m→π.ker,dens (missSet π A t h))/(Fintype.card π.ker:ℝ)^m.val=rowMiss π A t := by
  classical
  have eq:(univ.filter fun p:π.ker×(ZMod m→π.ker) =>
    t+(p.1:H)∉displaced π A p.2+displaced π A p.2).card =
      ∑ h:ZMod m→π.ker,(missSet π A t h).card := by
    simp only [missSet,card_filter,Fintype.sum_prod_type]
    rw [sum_comm]
  simp only [dens,←sum_div,rowMiss,eq,Nat.cast_sum,div_div]

theorem rowMiss_densities {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (c:ZMod m) (t:H) (row:π t=c+c) :
    let S (a b:ZMod m):=(rowSupport π A t a b)ᶜ
    rowMiss π A t=dens (S c c)*∏ j:positiveHalf m,dens (S (c+j.val) (c-j.val)) := by
  intro S
  have rate (a b:ZMod m) (lab:π t=a+b) :
      dens (S a b)=1-((layer π A a+layer π A b).card:ℝ)/(Fintype.card π.ker:ℝ) := by
    unfold dens S
    rw [card_compl,Nat.cast_sub (card_le_univ _),rowSupport_card _ _ _ _ _ lab]
    have kp:(Fintype.card π.ker:ℝ)≠0:=by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [rowMiss_product odd π A c t row,rate _ _ row]
  congr 1
  apply prod_congr rfl
  intro j _
  exact (rate _ _ (by rw [row];abel)).symm

theorem row_variance {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (c:ZMod m) (t:H) (row:π t=c+c) (B:positiveHalf m→ℝ) (bp:∀ j,0≤B j)
    (bound:∀ j:positiveHalf m,∀ χ:AddChar π.ker ℂ,χ≠0→
      ‖∑ x∈(rowSupport π A t (c+j.val) (c-j.val))ᶜ,χ x‖≤B j) :
    (∑ h:ZMod m→π.ker,(dens (missSet π A t h)-rowMiss π A t)^2)/(Fintype.card π.ker:ℝ)^m.val ≤
      (∑ j,B j)/Fintype.card π.ker := by
  classical
  let D:=(rowSupport π A t c c)ᶜ
  let M (j:positiveHalf m):=(rowSupport π A t (c+j.val) (c-j.val))ᶜ
  let X (h:ZMod m→π.ker):=dens (missSet π A t h)
  let μ:=rowMiss π A t
  let k:ℝ:=Fintype.card π.ker
  let P:=∏ j,(dens (M j))^2
  let v:ℝ:=∑ d:π.ker,overlapRate D d*∏ j,overlapRate (M j) d
  have kp:0<k:=by dsimp [k];positivity
  have first:(∑ h,X h)/k^m.val=μ:=first_row_moment π A t
  have second:(∑ h,(X h)^2)/k^m.val=v/k:=physical_second_moment odd π A c t row
  have center:μ^2=(dens D)^2*P:=by
    rw [show μ=dens D*∏ j,dens (M j) from rowMiss_densities odd π A c t row,mul_pow,←prod_pow]
  have count:((Fintype.card (ZMod m→π.ker):ℕ):ℝ)=k^m.val:=by simp [k,ZMod.card]
  have diff:(∑ h,(X h-μ)^2)/k^m.val=v/k-μ^2 := by
    simp only [sub_sq,sum_add_distrib,sum_sub_distrib,mul_assoc,←sum_mul,←mul_sum,sum_const,card_univ,nsmul_eq_mul,count]
    have h1:∑ h,X h=μ*k^m.val:=(div_eq_iff (pow_ne_zero _ kp.ne')).mp first
    have h2:∑ h,(X h)^2=v/k*k^m.val:=(div_eq_iff (pow_ne_zero _ kp.ne')).mp second
    rw [h1,h2]
    field_simp [kp.ne']
    ring
  have est:=joint_overlap D M B bp bound
  change (∑ h,(X h-μ)^2)/k^m.val≤(∑ j,B j)/k
  rw [diff,center,div_sub',div_le_div_iff_of_pos_right kp]
  · apply (le_abs_self _).trans
    rw [show k*((dens D)^2*P)=k*(dens D)^2*P by ring]
    exact est
  · exact kp.ne'
#print axioms row_variance

end Green33SlideConcentration
