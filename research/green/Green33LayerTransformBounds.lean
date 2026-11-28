import Green33OddRowSlides

/-! Character bounds for mixed sum supports inside cyclic quotient rows. -/
open scoped Pointwise
open Finset Green33LayerSlides
open scoped Pointwise
namespace Green33SlideConcentration
variable {G C:Type*} [AddCommGroup G] [AddCommGroup C] [DecidableEq C] [Fintype C]

theorem restricted_transform (π:G→+C) (T:Finset G) (c:C) (ψ:AddChar G ℂ) :
    ∑ η:AddChar C ℂ,η (-c)*∑ a∈T,(ψ+η.compAddMonoidHom π) a =
      (Fintype.card C:ℂ)*∑ a∈layer π T c,ψ a := by
  classical
  simp only [AddChar.add_apply,AddChar.compAddMonoidHom_apply,mul_sum]
  rw [sum_comm]
  have point (a:G) :
      ∑ η:AddChar C ℂ,η (-c)*(ψ a*η (π a))=ψ a*(if π a=c then (Fintype.card C:ℂ) else 0) := by
    simp_rw [show ∀ η:AddChar C ℂ,η (-c)*(ψ a*η (π a))=ψ a*η (-c+π a) by
      intro η;rw [η.map_add_eq_mul];ring]
    rw [←mul_sum,AddChar.sum_apply_eq_ite]
    have eq:-c+π a=0↔π a=c:=by rw [add_comm,←sub_eq_add_neg,sub_eq_zero]
    simp only [eq]
  simp_rw [point]
  simp [layer,sum_filter,mul_comm]
#print axioms restricted_transform

theorem restricted_transform_bound (π:G→+C) (T:Finset G) (c:C) (ψ:AddChar G ℂ)
    (high:∃ z:π.ker,ψ (z:G)≠1) (B:ℝ) (bound:∀ χ:AddChar G ℂ,χ≠0→‖∑ a∈T,χ a‖≤B) :
    ‖∑ a∈layer π T c,ψ a‖≤B := by
  classical
  obtain ⟨z,hz⟩:=high
  have nz (η:AddChar C ℂ):ψ+η.compAddMonoidHom π≠0 := by
    intro h
    apply hz
    have v:=congrArg (fun χ:AddChar G ℂ => χ (z:G)) h
    simpa only [AddChar.add_apply,AddChar.compAddMonoidHom_apply,AddMonoidHom.mem_ker.mp z.property,AddChar.map_zero_eq_one,mul_one,AddChar.zero_apply] using v
  have e:=restricted_transform π T c ψ
  have b:=norm_sum_le (univ:Finset (AddChar C ℂ)) (fun η => η (-c)*∑ a∈T,(ψ+η.compAddMonoidHom π) a)
  rw [e,norm_mul,Complex.norm_natCast] at b
  have u:=sum_le_sum (s:=(univ:Finset (AddChar C ℂ))) fun η _ => show ‖η (-c)*∑ a∈T,(ψ+η.compAddMonoidHom π) a‖≤B by simpa only [norm_mul,AddChar.norm_apply,one_mul] using bound _ (nz η)
  have h:=b.trans u
  simp only [sum_const,card_univ,AddChar.card_eq,nsmul_eq_mul] at h
  exact (mul_le_mul_iff_right₀ (by positivity : 0<(Fintype.card C:ℝ))).mp h
#print axioms restricted_transform_bound

variable {G:Type*} [AddCommGroup G] [Fintype G]

/-- Orthogonality gives an ambient extension for each character of a subgroup. -/
theorem exists_extension (K:AddSubgroup G) (θ:AddChar K ℂ) :
    ∃ χ:AddChar G ℂ,χ.compAddMonoidHom K.subtype=θ := by
  classical
  let w (χ:AddChar G ℂ) := ∑ z:K,(χ.compAddMonoidHom K.subtype-θ) z
  have total:∑ χ:AddChar G ℂ,w χ=(Fintype.card G:ℂ) := by
    dsimp only [w]
    rw [sum_comm]
    simp only [sub_eq_add_neg,AddChar.add_apply,AddChar.compAddMonoidHom_apply,AddSubgroup.subtype_apply]
    simp_rw [←sum_mul,AddChar.sum_apply_eq_ite]
    simp [ite_mul]
  by_contra! no
  have zero (χ:AddChar G ℂ):w χ=0:=AddChar.sum_eq_zero_iff_ne_zero.mpr (sub_ne_zero.mpr (no χ))
  simp only [zero,sum_const_zero] at total
  exact (show (Fintype.card G:ℂ)≠0 by exact_mod_cast Fintype.card_ne_zero) total.symm
#print axioms exists_extension

section Loss
/-- Replacing multiplicities by their support changes a Fourier coefficient by
at most the number of repeated image entries. -/
theorem image_loss {X Y:Type*} [DecidableEq Y] (S:Finset X) (f:X→Y) (w:Y→ℂ)
    (unit:∀ y,‖w y‖≤1) :
    ‖(∑ x∈S,w (f x))-(∑ y∈S.image f,w y)‖ ≤ (S.card:ℝ)-(S.image f).card := by
  classical
  obtain ⟨R,sub,inj,eq⟩:=exists_subset_injOn_image_eq_of_surjOn (S:Set X) (S.image f)
    (show (S:Set X).SurjOn f (S.image f) by intro y hy;exact mem_image.mp hy)
  have card:R.card=(S.image f).card:=by rw [←eq,card_image_of_injOn inj]
  have sum:(∑ y∈S.image f,w y)=∑ x∈R,w (f x) := by rw [←eq,sum_image inj]
  have inc:R⊆S:=sub
  rw [sum,←sum_sdiff inc (f:=fun x => w (f x)),add_sub_cancel_right]
  have b:=(norm_sum_le (S\R) (fun x => w (f x))).trans (sum_le_sum fun x _ => unit (f x))
  simpa [card_sdiff_of_subset inc,card,Nat.cast_sub (card_image_le (f:=f) (s:=S))] using b
#print axioms image_loss

variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Finite H]
theorem sum_support_loss (E B:Finset H) (χ:AddChar H ℂ) :
    ‖(∑ a∈E,χ a)*(∑ b∈B,χ b)-∑ z∈E+B,χ z‖ ≤ (E.card:ℝ)*B.card-(E+B).card := by
  let f (p:H×H):=p.1+p.2
  have img:(E×ˢB).image f=E+B:=by
    ext z
    constructor
    · intro h;obtain ⟨⟨a,b⟩,hab,eq⟩:=mem_image.mp h
      exact mem_add.mpr ⟨a,(mem_product.mp hab).1,b,(mem_product.mp hab).2,eq⟩
    · intro h;obtain ⟨a,ha,b,hb,eq⟩:=mem_add.mp h
      exact mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,eq⟩
  have bd:=image_loss (E×ˢB) f χ (fun z => (χ.norm_apply z).le)
  rw [img,card_product,Nat.cast_mul] at bd
  rw [sum_mul]
  simp only [mul_sum]
  simpa only [f,sum_product,χ.map_add_eq_mul] using bd
#print axioms sum_support_loss

end Loss
open Green33LayerSlides
variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]
theorem mixed_row_bound {m:ℕ+} (π:H→+ZMod m) (T:Finset H) (a b:ZMod m) (t:H)
    (label:π t=a+b) (B:ℝ) (bound:∀ χ:AddChar H ℂ,χ≠0→‖∑ x∈T,χ x‖≤B)
    (θ:AddChar π.ker ℂ) (nonzero:θ≠0) :
    ‖∑ z∈rowSupport π T t a b,θ z‖ ≤ B^2+
      ((layer π T a).card:ℝ)*(layer π T b).card-(layer π T a+layer π T b).card := by
  classical
  obtain ⟨χ,ext⟩:=exists_extension π.ker θ
  have high:∃ z:π.ker,χ (z:H)≠1 := by
    by_contra! all
    apply nonzero
    rw [←ext]
    exact AddChar.ext _ _ all
  let E:=layer π T a
  let F:=layer π T b
  let S:=rowSupport π T t a b
  let f (z:π.ker):=t+(z:H)
  have inj:Set.InjOn f (S:Set π.ker):=fun _ _ _ _ h => Subtype.ext (add_left_cancel h)
  have img:S.image f=E+F := by
    apply eq_of_subset_of_card_le
    · intro z hz;obtain ⟨x,hx,rfl⟩:=mem_image.mp hz;exact (mem_filter.mp hx).2
    · rw [card_image_of_injOn inj,rowSupport_card _ _ _ _ _ label]
  have wt:∑ x∈E+F,χ x=χ t*∑ z∈S,θ z := by
    rw [←img,sum_image inj,mul_sum]
    apply sum_congr rfl
    intro z _
    change χ (t+(z:H))=_
    rw [χ.map_add_eq_mul,←ext];rfl
  have val:‖∑ z∈S,θ z‖=‖∑ x∈E+F,χ x‖:=by rw [wt,norm_mul,χ.norm_apply,one_mul]
  rw [show rowSupport π T t a b=S from rfl,val]
  let P:ℂ:=(∑ x∈E,χ x)*(∑ y∈F,χ y)
  let U:ℂ:=∑ x∈E+F,χ x
  have cap:‖P‖≤B^2:=by
    rw [pow_two,show ‖P‖=‖∑ x∈E,χ x‖*‖∑ y∈F,χ y‖ from norm_mul ..]
    have e:=restricted_transform_bound π T a χ high B bound
    have f':=restricted_transform_bound π T b χ high B bound
    exact mul_le_mul e f' (norm_nonneg _) ((norm_nonneg _).trans e)
  have err:=sum_support_loss E F χ
  have triangle:‖U‖≤‖P‖+‖P-U‖:=by simpa only [sub_sub_cancel] using norm_sub_le P (P-U)
  exact triangle.trans (by change ‖P‖+‖P-U‖≤_; change ‖P-U‖≤_ at err;linarith)
#print axioms mixed_row_bound
end Green33SlideConcentration
