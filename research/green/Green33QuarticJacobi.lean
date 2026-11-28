import Green33QuarticReal
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! A quartic Jacobi sum decides the sign condition for two cyclic laws. -/

open Finset Green33QuarticReal Green33RealBudget Green33PrimeFlatness

namespace Green33QuarticJacobi

variable {p : ℕ+} [Fact p.val.Prime]
local notation "F" => ZMod p
local notation "C" => MulChar F ℂ

/-- Nonzero labels where a fourth-order character is real. -/
noncomputable def labels (χ : C) : Finset F := univ.filter fun x => χ x=1 ∨ χ x= -1

/-- Difference of the indicators of the two real character classes. -/
noncomputable def sign (χ : C) (x : F) : ℤ :=
  if χ x=1 then 1 else if χ x= -1 then -1 else 0

private lemma point (χ : C) (h4 : χ^4=1) (x : F) :
    2*(mark (labels χ) x:ℂ) = (1:C) x+(χ^2) x ∧
    2*(sign χ x:ℂ) = χ x+χ⁻¹ x ∧
    sign χ x ^ 2=mark (labels χ) x ∧ |sign χ x| ≤ mark (labels χ) x := by
  classical
  by_cases h0 : x=0
  · subst x; norm_num [sign,mark,labels,MulChar.map_zero]
  have one := MulChar.one_apply (R' := ℂ) (isUnit_iff_ne_zero.mpr h0)
  have four : χ x^4=1 := by rw [← MulChar.pow_apply' χ (by decide : 4≠0),h4,one]
  have hs : (χ x^2)^2=1 := by convert four using 1; ring
  rw [MulChar.pow_apply' χ two_ne_zero,MulChar.inv_apply_eq_inv',one]
  rcases sq_eq_one_iff.mp hs with e|e
  · rcases sq_eq_one_iff.mp e with h|h <;> norm_num [h,mark,labels,sign]
  · have h₁ : χ x ≠ 1 := by intro h; rw [h] at e; norm_num at e
    have h₂ : χ x ≠ -1 := by intro h; rw [h] at e; norm_num at e
    have nz : χ x ≠ 0 := by intro h; rw [h] at e; norm_num at e
    have inv : (χ x)⁻¹= -χ x := by
      rw [← one_div, div_eq_iff nz]
      linear_combination e
    norm_num [h₁,h₂,mark,labels,sign,e,inv]

private noncomputable def cell (χ ψ : C) (z : F) : ℂ := ∑ x, χ x*ψ (z-x)

private lemma scale (χ ψ : C) {z : F} (hz : z ≠ 0) :
    cell χ ψ z = (χ z*ψ z)*jacobiSum χ ψ := by
  rw [cell,jacobiSum,mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft₀ z hz).symm _ _ ?_
  intro i
  obtain ⟨j,rfl⟩ := (Equiv.mulLeft₀ z hz).surjective i
  simp only [Equiv.symm_apply_apply]
  change χ (z*j)*ψ (z-z*j)=_
  rw [show z-z*j=z*(1-j) by ring,map_mul,map_mul]
  ring

private lemma expandRow (s : F → ℤ) (a b : C) (H : ∀ x, 2*(s x:ℂ)=a x+b x) (z : F) :
    4*(signedRow s z:ℂ) = cell a a z+cell a b z+cell b a z+cell b b z := by
  simp only [signedRow,Int.cast_sum,Int.cast_mul,mul_sum,cell,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  calc
    _ = (2*(s i:ℂ))*(2*(s (z-i):ℂ)) := by ring
    _ = _ := by rw [H,H]; ring

private lemma count_labels (χ : C) (h4 : χ^4=1) (h2 : χ^2≠1) :
    2*(labels χ).card+1=p.val := by
  classical
  have a := congrArg (fun f : F → ℂ => ∑ x, f x)
    (funext fun x => (point χ h4 x).1)
  simp only [sum_add_distrib,← mul_sum,MulChar.sum_eq_zero_of_ne_one h2,
    add_zero,MulChar.sum_one_eq_card_units] at a
  have count : (∑ x, (mark (labels χ) x:ℂ)) = (labels χ).card := by
    simp [mark]
  rw [count] at a
  have eq : 2*(labels χ).card=Fintype.card Fˣ := by exact_mod_cast a
  rw [eq,← Fintype.card_eq_card_units_add_one,ZMod.card]

private lemma center (χ : C) (h4 : χ^4=1) (hm : χ (-1)=1) :
    signedRow (mark (labels χ)) 0=(labels χ).card ∧ signedRow (sign χ) 0=(labels χ).card := by
  classical
  have neg (x : F) : χ (-x)=χ x := by rw [← neg_one_mul x,map_mul,hm,one_mul]
  have mm (x : F) : mark (labels χ) x * mark (labels χ) (-x) = mark (labels χ) x := by
    simp only [mark,labels,mem_filter,mem_univ,true_and,neg]
    split <;> norm_num
  have ss (x : F) : sign χ x * sign χ (-x)= mark (labels χ) x := by
    have e : sign χ (-x)=sign χ x := by simp only [sign,neg]
    rw [e,← pow_two];exact (point χ h4 x).2.2.1
  simp only [signedRow,zero_sub,mm,ss]
  simp [mark]

omit [Fact p.val.Prime] in
private lemma inv_square (χ : C) (h4 : χ^4=1) : (χ^2)⁻¹=χ^2 := by
  apply inv_eq_of_mul_eq_one_right
  convert h4 using 1; group

private lemma unsigned (χ : C) (h4 : χ^4=1) (h2 : χ^2≠1) (hm : χ (-1)=1)
    (z : F) (hz : z≠0) :
    4*signedRow (mark (labels χ)) z=(p.val:ℤ)-1-4*mark (labels χ) z := by
  have e := expandRow _ _ _ (fun x => (point χ h4 x).1) z
  have sq : (χ^2) z*(χ^2) z = 1 := by
    rw [← MulChar.mul_apply,← pow_add,show 2+2=4 by decide,h4,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)]
  have J : jacobiSum (χ^2) (χ^2)= -1 := by
    have j := jacobiSum_nontrivial_inv h2
    rw [inv_square χ h4,MulChar.pow_apply' _ two_ne_zero,hm] at j
    simpa using j
  have one := MulChar.one_apply (R' := ℂ) (isUnit_iff_ne_zero.mpr hz)
  rw [scale _ _ hz,scale _ _ hz,scale _ _ hz,scale _ _ hz,one,sq,J,
    jacobiSum_one_one,jacobiSum_comm (χ^2) 1,jacobiSum_one_nontrivial h2,ZMod.card] at e
  have az := (point χ h4 z).1
  rw [one] at az
  have ee : 4*(signedRow (mark (labels χ)) z:ℂ)=(p.val:ℂ)-1-4*(mark (labels χ) z:ℂ) := by
    linear_combination e+2*az
  exact_mod_cast ee

omit [Fact p.val.Prime] in
private lemma conj_jacobi (χ : C) : jacobiSum χ⁻¹ χ⁻¹=starRingEnd ℂ (jacobiSum χ χ) := by
  simp only [jacobiSum,map_sum,map_mul,starRingEnd_apply,MulChar.star_apply']

private lemma signed (χ : C) (h4 : χ^4=1) (h2 : χ^2≠1) (hm : χ (-1)=1)
    (z : F) (hz : z≠0) :
    2*(signedRow (sign χ) z:ℂ) = (χ^2) z*((jacobiSum χ χ).re:ℂ)-1 := by
  have hχ : χ≠1 := by intro h; apply h2; simp [h]
  have mix := jacobiSum_nontrivial_inv hχ
  rw [hm] at mix
  have s := expandRow _ _ _ (fun x => (point χ h4 x).2.1) z
  have abs1 : χ z*χ⁻¹ z=1 := by
    rw [← MulChar.mul_apply,mul_inv_cancel,MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)]
  have u : χ z*χ z=(χ^2) z := by rw [pow_two,MulChar.mul_apply]
  have v : χ⁻¹ z*χ⁻¹ z=(χ^2) z := by
    rw [← MulChar.mul_apply,← pow_two,inv_pow,inv_square χ h4]
  rw [scale _ _ hz,scale _ _ hz,scale _ _ hz,scale _ _ hz,u,v,abs1,
    mul_comm (χ⁻¹ z) (χ z),abs1,jacobiSum_comm χ⁻¹ χ,mix,conj_jacobi] at s
  have add := Complex.add_conj (jacobiSum χ χ)
  push_cast at add
  linear_combination s/2 + ((χ^2) z/2)*add

/-- The signed row at one is an integer expression for the real part of
the quartic Jacobi sum. -/
noncomputable def parameter (χ : C) : ℤ := 2*signedRow (sign χ) 1+1

private lemma parameter_eq (χ : C) (h4 : χ^4=1) (h2 : χ^2≠1) (hm : χ (-1)=1) :
    (parameter χ:ℝ) = (jacobiSum χ χ).re := by
  have e := signed χ h4 h2 hm 1 one_ne_zero
  rw [map_one,one_mul] at e
  apply Complex.ofReal_injective
  push_cast [parameter]
  linear_combination e

private lemma jacobi_norm (χ : C) (h2 : χ^2≠1) : (jacobiSum χ χ).normSq = (p:ℝ) := by
  have hn : χ≠1 := by intro h; apply h2; simp [h]
  have hc : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]; exact p.pos.ne
  have e := jacobiSum_mul_jacobiSum_inv hc hn hn (by simpa [← pow_two] using h2)
  rw [conj_jacobi,Complex.mul_conj,ZMod.card] at e
  exact_mod_cast e

private lemma size_parameter (χ : C) (h4 : χ^4=1) (h2 : χ^2≠1) (hm : χ (-1)=1) :
    (parameter χ:ℝ)^2 < (p:ℝ) := by
  have hp : Nat.Prime p.val := Fact.out
  have norm := jacobi_norm χ h2
  rw [Complex.normSq_apply,← parameter_eq χ h4 h2 hm] at norm
  refine lt_of_le_of_ne (by nlinarith [sq_nonneg (jacobiSum χ χ).im]) ?_
  intro eq
  have ie : (parameter χ)^2=(p.val:ℤ) := by exact_mod_cast eq
  have ne := congrArg Int.natAbs ie
  rw [Int.natAbs_pow,Int.natAbs_natCast,pow_two] at ne
  exact (Nat.prime_iff.mp hp).not_isSquare ⟨_,ne.symm⟩

private lemma character_rows (χ : C) (h4 : χ^4=1) (h2 : χ^2≠1) (hm : χ (-1)=1) :
    RowCounts p (labels χ) (sign χ) (parameter χ) := by
  have card := count_labels χ h4 h2
  refine ⟨by simp [labels,MulChar.map_zero],card,fun x => (point χ h4 x).2.2.2,?_,?_⟩
  · obtain ⟨q,s⟩ := center χ h4 hm
    rw [q,s];omega
  · intro z hz
    refine ⟨unsigned χ h4 h2 hm z hz,?_⟩
    have e := signed χ h4 h2 hm z hz
    have s := (point χ h4 z).1
    rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hz)] at s
    rw [← parameter_eq χ h4 h2 hm] at e
    push_cast at e
    have ee : 2*(signedRow (sign χ) z:ℂ)=(parameter χ:ℂ)*(2*(mark (labels χ) z:ℂ)-1)-1 := by
      linear_combination e-(parameter χ:ℂ)*s
    exact_mod_cast ee

private lemma faithful : ∃ ψ : C, Function.Injective ψ := by
  classical
  let n := Fintype.card Fˣ
  let : NeZero n := ⟨Fintype.card_ne_zero⟩
  let U := rootsOfUnity n ℂ
  let e : Fˣ ≃* U := mulEquivOfCyclicCardEq (by
    rw [Complex.card_rootsOfUnity,Nat.card_eq_fintype_card])
  let f : Fˣ →* ℂˣ := (rootsOfUnity n ℂ).subtype.comp e.toMonoidHom
  let ψ : C := MulChar.ofUnitHom f
  refine ⟨ψ,?_⟩
  intro a b eq
  by_cases ha : a=0
  · subst a
    symm;simpa [MulChar.map_zero,MulChar.apply_eq_zero_iff,isUnit_iff_ne_zero] using eq.symm
  by_cases hb : b=0
  · subst b
    simpa [MulChar.map_zero,MulChar.apply_eq_zero_iff,isUnit_iff_ne_zero] using eq
  let A := Units.mk0 a ha
  let B := Units.mk0 b hb
  change ψ (A:F)=ψ (B:F) at eq
  rw [show ψ=MulChar.ofUnitHom f from rfl,MulChar.ofUnitHom_coe,MulChar.ofUnitHom_coe] at eq
  have t : e A=e B := Subtype.ext (Units.ext eq)
  exact congrArg Units.val (e.injective t)

private lemma realization (h8 : p.val%8=1) :
    ∃ χ : C, χ^4=1 ∧ χ^2≠1 ∧ χ (-1)=1 ∧ labels χ=squares p ∧ sign χ=signature p := by
  classical
  have pp : p.val.Prime := Fact.out
  have hp := pp.two_le
  let : Fact (2<p.val) := ⟨by omega⟩
  let n := p.val/4
  have hn : n≠0 := by dsimp [n]; omega
  have hhalf : n*2=p.val/2 := by dsimp [n];omega
  have hfull : n*4=p.val-1 := by dsimp [n];omega
  have hEven : Even n := ⟨p.val/8,by dsimp [n];omega⟩
  obtain ⟨ψ,inj⟩ := faithful (p := p)
  have neg : ψ (-1) = -1 := by
    have h : ψ (-1)^2=1 := by rw [← map_pow]; norm_num
    exact (sq_eq_one_iff.mp h).resolve_left fun e => ZMod.neg_one_ne_one (inj (e.trans ψ.map_one.symm))
  let χ := ψ^n
  have calcχ (x : F) : χ x=ψ (x^n) := by rw [show χ=ψ^n from rfl,MulChar.pow_apply' ψ hn,map_pow]
  have four : χ^4=1 := by
    change (ψ^n)^4=1
    rw [← pow_mul,hfull]
    simpa only [Fintype.card_units,ZMod.card] using ψ.pow_card_eq_one
  have two : χ^2≠1 := by
    intro h
    obtain ⟨g,hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    have c := DFunLike.congr_fun h (g:F)
    rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,calcχ,← map_pow,← pow_mul] at c
    have gp : g^(n*2)=1 := Units.ext (inj (c.trans ψ.map_one.symm))
    have dvd := orderOf_dvd_of_pow_eq_one gp
    rw [hg,Nat.card_eq_fintype_card,Fintype.card_units,ZMod.card,hhalf] at dvd
    have small := Nat.le_of_dvd (show 0<p.val/2 by omega) dvd
    omega
  refine ⟨χ,four,two,?_,?_,?_⟩
  · rw [calcχ,hEven.neg_one_pow,map_one]
  · ext x
    simp only [labels,squares,mem_filter,mem_univ,true_and,← sq_eq_one_iff]
    rw [calcχ,← map_pow,← pow_mul,hhalf,← ψ.map_one]
    exact inj.eq_iff
  · funext x
    simp only [sign,signature,calcχ]
    have oneEq : ψ (x^n)=1 ↔ x^n=1 := ψ.map_one ▸ inj.eq_iff
    have negEq : ψ (x^n)= -1 ↔ x^n= -1 := neg ▸ inj.eq_iff
    simp only [oneEq,negEq]; rfl

/-- Every prime equal to one modulo eight has the required rows on the
actual quadratic residues, with its signed row at one as the parameter. -/
theorem residue_rows (h8 : p.val%8=1) :
    let K := 2*signedRow (signature p) 1+1
    RowCounts p (squares p) (signature p) K ∧ (K:ℝ)^2 < p := by
  obtain ⟨χ,h4,h2,hm,hl,hs⟩ := realization h8
  have u := character_rows χ h4 h2 hm
  have v := size_parameter χ h4 h2 hm
  simpa only [parameter,hs,hl] using And.intro u v

/-- A single signed integer row suffices to certify optimality of the exact
common support at any prime equal to one modulo eight. -/
theorem exact_of_signed_row (h8 : p.val%8=1) (h : -1 ≤ signedRow (signature p) 1) :
    ExactSeed p (insert 0 (squares p)) ∧ minimumBudget p=(p.val+1)/2 := by
  obtain ⟨rows,small⟩ := residue_rows h8
  obtain ⟨seed,m⟩ := exact_of_rows p _ _ _ rows small (by omega)
  have := rows.size
  exact ⟨seed,by omega⟩

/-- The signed parameter is the odd coordinate, congruent to three modulo
four, of a representation of the prime as a sum of two squares. -/
theorem gaussian_coordinates (h8 : p.val%8=1) :
    let K := 2*signedRow (signature p) 1+1
    K%4=3 ∧ ∃ b : ℤ, K^2+b^2=p.val := by
  obtain ⟨χ,h4,h2,hm,hl,hs⟩ := realization h8
  have member : (1:F) ∈ labels χ := by simp [labels]
  have forms := character_rows χ h4 h2 hm
  have row := (forms.off_zero 1 one_ne_zero).1
  rw [mark,if_pos member] at row
  let q := mark (labels χ)
  have par (x : F) : (sign χ x : ZMod 2)=(q x : ZMod 2) := by
    have eq := (point χ h4 x).2.2.1
    have cast := congrArg (fun n : ℤ => (n : ZMod 2)) eq
    push_cast at cast
    rwa [ZMod.pow_card] at cast
  have mod2 : (signedRow (sign χ) 1:ZMod 2)=(signedRow q 1:ZMod 2) := by
    simp only [signedRow,Int.cast_sum,Int.cast_mul,par]
  have modEq := (ZMod.intCast_eq_intCast_iff _ _ _).1 mod2
  have pp : (p.val:ℤ)%8=1 := by exact_mod_cast h8
  have Kmod : parameter χ%4=3 := by
    change signedRow (sign χ) 1 % 2 = signedRow (mark (labels χ)) 1 % 2 at modEq
    dsimp [parameter]; omega
  have norm := jacobi_norm χ h2
  have integral (x : F) : ∃ b : ℤ, (χ x).im=(b:ℝ) := by
    by_cases hx : x=0
    · subst x;exact ⟨0,by simp [MulChar.map_zero]⟩
    obtain ⟨k,hk,eq⟩ := MulChar.exists_apply_eq_pow h4 Complex.isPrimitiveRoot_I hx
    rw [eq]
    interval_cases k
    · exact ⟨0,by norm_num⟩
    · exact ⟨1,by norm_num⟩
    · exact ⟨0,by norm_num⟩
    · exact ⟨-1,by norm_num [pow_succ]⟩
  choose B hB using integral
  have imag : (jacobiSum χ χ).im=(∑ x, B (x*(1-x)):ℤ) := by
    simp [jacobiSum,← map_mul,Complex.im_sum,hB]
  rw [Complex.normSq_apply,← parameter_eq χ h4 h2 hm,imag] at norm
  have eq : (parameter χ)^2+(∑ x, B (x*(1-x)))^2=(p.val:ℤ) := by
    exact_mod_cast (show (parameter χ:ℝ)^2+((∑ x, B (x*(1-x)):ℤ):ℝ)^2=(p:ℝ) by simpa [pow_two] using norm)
  refine ⟨by simpa only [parameter,hs] using Kmod,∑ x, B (x*(1-x)),?_⟩
  simpa only [parameter,hs] using eq

private lemma coordinates_aux {P a b r t : ℤ} (pos : 0<P)
    (h₁ : a^2+b^2=P) (h₂ : r^2+t^2=P) (hd : P ∣ a*t-b*r) :
    a^2=r^2 ∨ a^2=t^2 := by
  obtain ⟨k,hk⟩ := hd
  have norm : (a*t-b*r)^2+(a*r+b*t)^2=P^2 := by
    linear_combination (r^2+t^2)*h₁+P*h₂
  have first : (a*t-b*r)*(a*t+b*r)=P*(a^2-r^2) := by
    linear_combination a^2*h₂-r^2*h₁
  have second : (a*r+b*t)*(a*r-b*t)=P*(a^2-t^2) := by
    linear_combination a^2*h₂-t^2*h₁
  rw [hk,mul_pow] at norm
  have small : k^2≤1 := by
    by_contra! big
    nlinarith [mul_pos (sub_pos.mpr big) (sq_pos_of_pos pos),sq_nonneg (a*r+b*t)]
  by_cases zero : k=0
  · simp [zero] at hk
    rw [hk,zero_mul] at first
    exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp first.symm).resolve_left pos.ne'))
  · have lower : 1≤k^2 := by have := sq_pos_of_ne_zero zero;omega
    rw [le_antisymm small lower,mul_one] at norm
    have z : a*r+b*t=0 := by nlinarith [sq_nonneg (a*r+b*t)]
    rw [z,zero_mul] at second
    exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp second.symm).resolve_left pos.ne'))

private lemma coordinates_unique {P a b r t : ℤ} (hp : Prime P) (pos : 0<P)
    (h₁ : a^2+b^2=P) (h₂ : r^2+t^2=P) : a^2=r^2 ∨ a^2=t^2 := by
  have prodD : P ∣ (a*t-b*r)*(a*t+b*r) := ⟨a^2-r^2,by
    linear_combination a^2*h₂-r^2*h₁⟩
  rcases hp.dvd_or_dvd prodD with d|d
  · exact coordinates_aux pos h₁ h₂ d
  · apply coordinates_aux (b := -b) pos (by simpa using h₁) h₂
    simpa using d

/-- The two-square representation with odd coordinate congruent to three
modulo four gives the signed row, including its sign. -/
theorem signed_coordinate (h8 : p.val%8=1) {a b : ℤ} (primary : a%4=3)
    (repr : a^2+b^2=p.val) :
    2*signedRow (signature p) 1+1=a := by
  obtain ⟨mod4,t,norm⟩ := gaussian_coordinates h8
  let K := 2*signedRow (signature p) 1+1
  change K%4=3 at mod4
  change K^2+t^2=p.val at norm
  have pp : p.val.Prime := Fact.out
  have hP : (p.val:ℤ)%8=1 := by exact_mod_cast h8
  have par : t%2=0 := by
    have sum := congrArg (fun n : ℤ => n%2) norm
    have square (x : ℤ) : x^2%2=x%2 := by
      rw [pow_two,Int.mul_emod]; rcases Int.emod_two_eq_zero_or_one x with h|h <;> rw [h] <;> decide
    change (K^2+t^2)%2=(p.val:ℤ)%2 at sum
    rw [Int.add_emod,square,square] at sum
    omega
  change K=a
  rcases coordinates_unique (Nat.prime_iff_prime_int.mp pp) (by exact_mod_cast p.pos) repr norm with e|e
  · rcases eq_or_eq_neg_of_sq_eq_sq a K e with e|e <;> omega
  · rcases eq_or_eq_neg_of_sq_eq_sq a t e with e|e <;> omega

/-- The absolute support minimum is attained whenever the signed odd
two-square coordinate is at least minus one. -/
theorem exact_of_two_squares (h8 : p.val%8=1) {a b : ℤ} (primary : a%4=3)
    (repr : a^2+b^2=p.val) (positive : -1≤a) :
    ExactSeed p (insert 0 (squares p)) ∧ minimumBudget p=(p.val+1)/2 := by
  have := signed_coordinate h8 primary repr
  exact exact_of_signed_row h8 (by omega)

/-- Constant convolution for the pair with a common central mass and opposite
perturbations of the two quartic classes. -/
def HasQuarticWeights (p : ℕ+) : Prop :=
  let w := residueWeight (squares p) (signature p)
  ∃ r c : ℝ, 0<r ∧ r<1 ∧ 0<c ∧ ∀ z, conv (w r c) (w (-r) c) z=conv (w r c) (w (-r) c) 0

/-- Complete sign test for this specific pair of weights. -/
theorem weights_iff_two_squares (h8 : p.val%8=1) {a b : ℤ} (primary : a%4=3)
    (repr : a^2+b^2=p.val) : HasQuarticWeights p ↔ -1≤a := by
  obtain ⟨h,small⟩ := residue_rows h8
  rw [← signed_coordinate h8 primary repr]
  exact flat_weights_iff p _ _ _ h small (by simp [squares])

/-- Both minima concern all choices of common labels and both input laws. -/
theorem minimum_seventeen : minimumBudget 17=9 := by
  let : Fact (17:ℕ+).val.Prime := ⟨by decide⟩
  exact (exact_of_two_squares (p := 17) (a := -1) (b := 4) (by decide) (by decide)
    (by decide) (by decide)).2

theorem minimum_seventy_three : minimumBudget 73=37 := by
  let : Fact (73:ℕ+).val.Prime := ⟨by decide⟩
  exact (exact_of_two_squares (p := 73) (a := 3) (b := 8) (by decide) (by decide)
    (by decide) (by decide)).2

/-- At order forty-one the sign test rules out all parameters in this family. -/
theorem forty_one : ¬ HasQuarticWeights 41 := by
  let : Fact (41:ℕ+).val.Prime := ⟨by decide⟩
  rw [weights_iff_two_squares (p := 41) (a := -5) (b := 4) (by decide) (by decide) (by decide)]
  decide

#print axioms residue_rows
#print axioms exact_of_signed_row
#print axioms gaussian_coordinates
#print axioms signed_coordinate
#print axioms exact_of_two_squares
#print axioms weights_iff_two_squares
#print axioms minimum_seventeen
#print axioms minimum_seventy_three
#print axioms forty_one
end Green33QuarticJacobi
