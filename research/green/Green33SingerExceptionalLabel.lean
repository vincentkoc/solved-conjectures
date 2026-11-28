import Green33SingerCubicFibers
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! The geometric-square exception in the discriminant of a cubic pencil. -/

open Polynomial Finset
open scoped Polynomial

namespace Green33SingerExceptionalLabel

variable {F : Type*} [Field F]

/-- Three simultaneous values determine a polynomial of degree at most two. -/
private theorem quadratic_unique {P Q : F[X]} {r s t : F}
    (rs : r≠s) (st : s≠t) (tr : t≠r) (dp : P.natDegree≤2) (dq : Q.natDegree≤2)
    (er : P.eval r=Q.eval r) (es : P.eval s=Q.eval s) (et : P.eval t=Q.eval t) : P=Q := by
  classical
  apply sub_eq_zero.mp
  by_contra ne
  let G := P-Q
  have incl : {r,s,t}⊆G.roots.toFinset := by
    intro z hz
    apply Multiset.mem_toFinset.mpr
    apply (mem_roots ne).mpr
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with h|h|h <;> subst z <;> simp [IsRoot,er,es,et]
  have cap := (card_le_card incl).trans (G.roots.toFinset_card_le.trans (card_roots' G))
  have d : G.natDegree≤2 := (natDegree_sub_le ..).trans (max_le dp dq)
  have three : ({r,s,t} : Finset F).card=3 := by simp [rs,st,tr.symm]
  omega

section Scalar

variable {R : Type*} [CommRing R]

/-- The discriminant of a linear combination of the three pairwise products
of linear factors, viewed in the residual variable. -/
private def det (r s t a b c : R) :=
  (a*(s+t)+b*(t+r)+c*(r+s))^2-4*(a+b+c)*(a*s*t+b*t*r+c*r*s)

private theorem disc_all (r s t a b c : R) :
    det r s t a b c-(a*(s-t)+b*(t-r)+c*(r-s))^2 =
      -4*(a*b*(s-t)*(t-r)+b*c*(t-r)*(r-s)+c*a*(r-s)*(s-t)) := by
  unfold det;ring

private theorem disc_mixed (r s t a b c : R) :
    det r s t a b c-(a*(s-t)+b*(t-r)-c*(r-s))^2 =
      -4*a*b*(s-t)*(t-r) := by
  unfold det;ring

private theorem coefficient_ratios {r s t a b c : F} (na : a≠0) (nc : c≠0)
    (first : a*b+b*c+c*a=0) (second : t*a*b+r*b*c+s*c*a=0) :
    (s-t)*a=(t-r)*b ∧ (t-r)*b=(r-s)*c := by
  constructor
  · apply mul_right_cancel₀ nc
    linear_combination second-t*first
  · apply mul_right_cancel₀ na
    linear_combination second-r*first

end Scalar

private noncomputable def pairLine (s t : F) : F[X] := (X-C s)*(X-C t)

private noncomputable def component (a s t : F) : F[X] := C a*pairLine s t

private noncomputable def discriminant (r s t a b c : F) : F[X] :=
  det (C r) (C s) (C t) (component a s t) (component b t r) (component c r s)

private noncomputable def candidate (r s t a b c : F) : F[X] :=
  component a s t*C (s-t)+component b t r*C (t-r)+component c r s*C (r-s)

private theorem candidate_degree (r s t a b c : F) :
    (candidate r s t a b c).natDegree≤2 := by
  unfold candidate component pairLine
  compute_degree

private theorem discriminant_degree (r s t a b c : F) :
    (discriminant r s t a b c).natDegree≤4 := by
  unfold discriminant component pairLine det
  compute_degree

private theorem reduced (r s t a b c : F) :
    discriminant r s t a b c-(candidate r s t a b c)^2 =
      C (-4: F)*(X-C r)*(X-C s)*(X-C t)*
        (C (a*(s-t)*(b*(t-r)))*(X-C t)+C (b*(t-r)*(c*(r-s)))*(X-C r)+
          C (c*(r-s)*(a*(s-t)))*(X-C s)) := by
  unfold discriminant candidate
  simp only [map_sub,map_mul,map_neg,map_ofNat]
  rw [disc_all]
  unfold component pairLine
  ring

private theorem reduced_mixed (r s t a b c : F) :
    discriminant r s t a b c-(candidate r s t a b (-c))^2 =
       C (-4: F)*component a s t*component b t r*C (s-t)*C (t-r) := by
  unfold discriminant candidate
  simp only [component, map_neg,neg_mul,map_sub,map_ofNat]
  rw [show ∀ x y : F[X], x + -y=x-y by intros;abel]
  simpa only [component,map_sub,map_neg,map_ofNat,neg_mul] using disc_mixed (C r) (C s) (C t) (component a s t) (component b t r) (component c r s)

private theorem candidate_eval (r s t a b c : F) :
    (candidate r s t a b c).eval r=a*(r-s)*(r-t)*(s-t) ∧
    (candidate r s t a b c).eval s=b*(s-t)*(s-r)*(t-r) ∧
    (candidate r s t a b c).eval t=c*(t-r)*(t-s)*(r-s) := by
  simp [candidate,component,pairLine,mul_assoc]

private theorem square_signs {r s t a b c : F} {H : F[X]}
    (sq : discriminant r s t a b c=H^2) :
    ∃ A B C : F, (A=a ∨ A= -a) ∧ (B=b ∨ B= -b) ∧ (C=c ∨ C= -c) ∧
      H.eval r=A*(r-s)*(r-t)*(s-t) ∧ H.eval s=B*(s-t)*(s-r)*(t-r) ∧
      H.eval t=C*(t-r)*(t-s)*(r-s) := by
  have sign (v j k l : F) (eq : v^2=(j*k*l)^2) :
      ∃ J : F, (J=j ∨ J= -j) ∧ v=J*k*l := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp eq with h|h
    · exact ⟨j,Or.inl rfl,h⟩
    · exact ⟨-j,Or.inr rfl,by rw [h];ring⟩
  have w (x : F) (hx : x=r ∨ x=s ∨ x=t) :
      (H.eval x)^2=((candidate r s t a b c).eval x)^2 := by
    have e := congrArg (Polynomial.eval x) (reduced r s t a b c)
    rw [sq] at e
    rcases hx with h|h|h <;> subst x <;>
      simpa [sub_eq_zero] using e
  obtain ⟨A,hA,eA⟩ := sign (H.eval r) a ((r-s)*(r-t)) (s-t)
    (by simpa only [(candidate_eval ..).1,mul_assoc] using w r (Or.inl rfl))
  obtain ⟨B,hB,eB⟩ := sign (H.eval s) b ((s-t)*(s-r)) (t-r)
    (by simpa only [(candidate_eval ..).2.1,mul_assoc] using w s (Or.inr (Or.inl rfl)))
  obtain ⟨C,hC,eC⟩ := sign (H.eval t) c ((t-r)*(t-s)) (r-s)
    (by simpa only [(candidate_eval ..).2.2,mul_assoc] using w t (Or.inr (Or.inr rfl)))
  exact ⟨A,B,C,hA,hB,hC,by simpa only [mul_assoc] using eA,
    by simpa only [mul_assoc] using eB,by simpa only [mul_assoc] using eC⟩

private theorem not_mixed {r s t a b c : F} (four : (-4:F)≠0)
    (st : s≠t) (tr : t≠r) (ha : a≠0) (hb : b≠0) :
    discriminant r s t a b c≠(candidate r s t a b (-c))^2 := by
  intro h
  have e:=reduced_mixed r s t a b c
  rw [h,sub_self] at e
  have nz : C (-4:F)*component a s t*component b t r*C (s-t)*C (t-r)≠0 := by
    unfold component pairLine
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr four)
      (mul_ne_zero (C_ne_zero.mpr ha) (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))))
      (mul_ne_zero (C_ne_zero.mpr hb) (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))))
      (C_ne_zero.mpr (sub_ne_zero.mpr st))) (C_ne_zero.mpr (sub_ne_zero.mpr tr))
  exact (nz e.symm).elim

private theorem candidate_rotate (r s t a b c : F) :
    candidate r s t a b c=candidate s t r b c a := by
  unfold candidate;abel

private theorem discriminant_rotate (r s t a b c : F) :
    discriminant r s t a b c=discriminant s t r b c a := by
  unfold discriminant det;ring

private theorem candidate_neg (r s t a b c : F) :
    candidate r s t (-a) (-b) (-c)= -candidate r s t a b c := by
  unfold candidate component
  simp only [map_neg];ring

private theorem mixed_impossible {r s t a b c : F}
    (four : (-4:F)≠0) (rs : r≠s) (st : s≠t) (tr : t≠r)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    discriminant r s t a b c≠(candidate r s t (-a) b c)^2 ∧
    discriminant r s t a b c≠(candidate r s t a (-b) c)^2 ∧
    discriminant r s t a b c≠(candidate r s t a b (-c))^2 := by
  refine ⟨?_,?_,not_mixed four st tr ha hb⟩
  · rw [discriminant_rotate,candidate_rotate]
    exact not_mixed four tr rs hb hc
  · rw [← discriminant_rotate t r s c a b,← candidate_rotate t r s c a (-b)]
    exact not_mixed four rs st hc ha

private theorem uniform_sign {r s t a b c : F} (four : (-4:F)≠0)
    (rs : r≠s) (st : s≠t) (tr : t≠r) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    {H : F[X]} (sq : discriminant r s t a b c=H^2) :
    discriminant r s t a b c=(candidate r s t a b c)^2 := by
  obtain ⟨A,B,C,hA,hB,hC,eA,eB,eC⟩ := square_signs sq
  have deg := discriminant_degree r s t a b c
  rw [sq,natDegree_pow] at deg
  have h := quadratic_unique rs st tr (show H.natDegree≤2 by omega)
    (candidate_degree r s t A B C) (eA.trans (candidate_eval ..).1.symm)
    (eB.trans (candidate_eval ..).2.1.symm) (eC.trans (candidate_eval ..).2.2.symm)
  rw [h] at sq
  have flip : discriminant r s t a b c=(candidate r s t (-A) (-B) (-C))^2 := by
    simpa [candidate_neg] using sq
  obtain ⟨m₁,m₂,m₃⟩ := mixed_impossible four rs st tr ha hb hc
  rcases hA with hA|hA <;> rcases hB with hB|hB <;> rcases hC with hC|hC <;>
    subst A <;> subst B <;> subst C
  · exact sq
  · exact (m₃ sq).elim
  · exact (m₂ sq).elim
  · exact (m₁ (by simpa only [neg_neg] using flip)).elim
  · exact (m₁ sq).elim
  · exact (m₂ (by simpa only [neg_neg] using flip)).elim
  · exact (m₃ (by simpa only [neg_neg] using flip)).elim
  · simpa only [neg_neg] using flip

private theorem linear_coefficients {r s t a b c : F}
    (z : C (a*b)*(X-C t)+C (b*c)*(X-C r)+C (c*a)*(X-C s)=0) :
    a*b+b*c+c*a=0 ∧ t*a*b+r*b*c+s*c*a=0 := by
  constructor
  · have h := congrArg (fun P : F[X] => P.coeff 1) z
    simpa only [coeff_add,coeff_zero,coeff_C_mul,coeff_sub,coeff_X_one,coeff_C,one_ne_zero,if_false,sub_zero,mul_one] using h
  · have h := congrArg (Polynomial.eval 0) z
    simp at h
    linear_combination -h

/-- A geometric square forces a single projective triple of interpolation weights. -/
private theorem square_weights {r s t a b c : F} (four : (-4:F)≠0)
    (rs : r≠s) (st : s≠t) (tr : t≠r) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (sq : ∃ H : F[X], discriminant r s t a b c=H^2) :
    a*(s-t)^2=b*(t-r)^2 ∧ b*(t-r)^2=c*(r-s)^2 := by
  obtain ⟨H,hH⟩:=sq
  have e:=reduced r s t a b c
  rw [uniform_sign four rs st tr ha hb hc hH,sub_self] at e
  have nz : C (-4:F)*(X-C r)*(X-C s)*(X-C t)≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (C_ne_zero.mpr four) (X_sub_C_ne_zero _))
      (X_sub_C_ne_zero _)) (X_sub_C_ne_zero _)
  obtain ⟨h₁,h₂⟩:=linear_coefficients ((mul_eq_zero.mp e.symm).resolve_left nz)
  obtain ⟨g₁,g₂⟩ := coefficient_ratios (mul_ne_zero ha (sub_ne_zero.mpr st))
    (mul_ne_zero hc (sub_ne_zero.mpr rs)) h₁ h₂
  constructor <;> first | linear_combination g₁ | linear_combination g₂

open Green33SingerCubicFibers

private def weight (P : Pencil F) (r s t : F) := P.quad r/((r-s)*(r-t))

private theorem weight_coefficients (P : Pencil F) {r s t : F}
    (rs : r≠s) (st : s≠t) (tr : t≠r) :
    let a:=weight P r s t; let b:=weight P s t r; let c:=weight P t r s
    P.a=a+b+c ∧ P.b= -(a*(s+t)+b*(t+r)+c*(r+s)) ∧
    P.c=a*s*t+b*t*r+c*r*s := by
  let a:=weight P r s t
  let b:=weight P s t r
  let c:=weight P t r s
  let p : F[X] := C P.a*X^2+C P.b*X+C P.c
  let q := component a s t+component b t r+component c r s
  have d₁ : p.natDegree≤2 := by dsimp [p];compute_degree
  have d₂ : q.natDegree≤2 := by dsimp [q,component,pairLine];compute_degree
  have val (x : F) (hx : x=r ∨ x=s ∨ x=t) : p.eval x=q.eval x := by
    rcases hx with h|h|h <;> subst x <;>
      simp [p,q,component,pairLine,a,b,c,weight,Pencil.quad,
        sub_ne_zero.mpr rs,sub_ne_zero.mpr rs.symm,sub_ne_zero.mpr st,sub_ne_zero.mpr st.symm,
        sub_ne_zero.mpr tr,sub_ne_zero.mpr tr.symm]
  have eq := quadratic_unique rs st tr d₁ d₂ (val r (Or.inl rfl)) (val s (Or.inr (Or.inl rfl)))
    (val t (Or.inr (Or.inr rfl)))
  have split (v w : F) : pairLine v w=X^2-C (v+w)*X+C (v*w) := by
    unfold pairLine;simp only [map_add,map_mul];ring
  have expanded : q=C (a+b+c)*X^2+C (-(a*(s+t)+b*(t+r)+c*(r+s)))*X+C (a*s*t+b*t*r+c*r*s) := by
    simp only [q,component,split,map_add,map_neg,map_mul]
    ring
  rw [expanded] at eq
  change P.a=a+b+c ∧ P.b= -(a*(s+t)+b*(t+r)+c*(r+s)) ∧ P.c=a*s*t+b*t*r+c*r*s
  have h (n : ℕ) := congrArg (fun f : F[X] => f.coeff n) eq
  refine ⟨?_,?_,?_⟩
  · have e:=h 2
    simp only [p,coeff_add,coeff_X_pow,coeff_C_mul,coeff_X,coeff_C] at e
    norm_num at e
    exact e
  · have e:=h 1
    simp only [p,coeff_add,coeff_X_pow,coeff_C_mul,coeff_X,coeff_C] at e
    norm_num at e
    linear_combination e
  · have e:=h 0
    simp only [p,coeff_add,coeff_X_pow,coeff_C_mul,coeff_X,coeff_C] at e
    norm_num at e
    exact e

private theorem polynomial_natural {E : Type*} [Field E] (P : Pencil F) (φ : F→+*E) :
    P.polynomial.map φ=(P.map φ).polynomial := by
  simp [Pencil.polynomial,Pencil.disc,Pencil.middle,Pencil.quad,Pencil.last,Pencil.map]

private theorem polynomial_weights (P : Pencil F) {r s t : F}
    (rs : r≠s) (st : s≠t) (tr : t≠r) (one : P.i= -(r+s+t))
    (two : P.j=r*s+r*t+s*t) (three : P.k= -(r*s*t)) :
    P.polynomial=discriminant r s t (weight P r s t) (weight P s t r) (weight P t r s) := by
  let a:=weight P r s t
  let b:=weight P s t r
  let c:=weight P t r s
  obtain ⟨A,B,D⟩ := weight_coefficients P rs st tr
  change P.a=a+b+c at A
  change P.b= -(a*(s+t)+b*(t+r)+c*(r+s)) at B
  change P.c=a*s*t+b*t*r+c*r*s at D
  change P.polynomial=discriminant r s t a b c
  let u:=component a s t
  let v:=component b t r
  let w:=component c r s
  have lead : (P.map C).quad X=u+v+w := by
    simp only [Pencil.quad,Pencil.map,u,v,w,component,pairLine,A,B,D,map_add,map_mul,map_neg]
    ring
  have mid : (P.map C).middle X= -(u*(C s+C t)+v*(C t+C r)+w*(C r+C s)) := by
    simp only [Pencil.middle,Pencil.map,u,v,w,component,pairLine,A,B,D,one,two,three,map_add,map_mul,map_neg]
    ring
  have last : (P.map C).last X=u*C s*C t+v*C t*C r+w*C r*C s := by
    simp only [Pencil.last,Pencil.map,u,v,w,component,pairLine,A,B,D,one,two,three,map_add,map_mul,map_neg]
    ring
  change (P.map C).middle X ^ 2-4*(P.map C).quad X*(P.map C).last X=_
  rw [lead,mid,last,neg_sq]
  rfl

private theorem weight_transition {r s t a b : F} (h : a*(s-t)^2=b*(t-r)^2) :
    a*((s-t)*(s-r))^2=b*((r-s)*(r-t))^2 := by
  linear_combination (r-s)^2*h

private theorem derivative_samples {r s t a b c : F} (rs : r≠s) (tr : t≠r)
    (one : a*(s-t)^2=b*(t-r)^2) (two : b*(t-r)^2=c*(r-s)^2) :
    ∃ e : F, a=e*((r-s)*(r-t))^2 ∧ b=e*((s-t)*(s-r))^2 ∧
      c=e*((t-r)*(t-s))^2 := by
  let d := (r-s)*(r-t)
  have dn : d≠0 := mul_ne_zero (sub_ne_zero.mpr rs) (sub_ne_zero.mpr tr.symm)
  refine ⟨a/d^2,?_,?_,?_⟩
  · exact (div_mul_cancel₀ _ (pow_ne_zero 2 dn)).symm
  · have eq:=weight_transition one
    field_simp [dn]
    simpa only [d,mul_pow,mul_assoc] using eq.symm
  · have eq := weight_transition (r:=t) (s:=r) (t:=s) (one.trans two).symm
    field_simp [dn]
    simpa only [d,mul_pow,mul_assoc] using eq

private theorem square_for_samples (r s t e : F) :
    ∃ H : F[X], discriminant r s t (e*((r-s)*(r-t))^2) (e*((s-t)*(s-r))^2)
      (e*((t-r)*(t-s))^2)=H^2 := by
  let a:=e*((r-s)*(r-t))^2
  let b:=e*((s-t)*(s-r))^2
  let c:=e*((t-r)*(t-s))^2
  refine ⟨candidate r s t a b c,sub_eq_zero.mp ?_⟩
  rw [reduced]
  suffices z : C (a*(s-t)*(b*(t-r)))*(X-C t)+C (b*(t-r)*(c*(r-s)))*(X-C r)+
      C (c*(r-s)*(a*(s-t)))*(X-C s)=0 by rw [z,mul_zero]
  let A:=a*(s-t)
  let B:=b*(t-r)
  let D:=c*(r-s)
  have lead : A*B+B*D+D*A=0 := by dsimp [A,B,D,a,b,c];ring
  have const : t*A*B+r*B*D+s*D*A=0 := by dsimp [A,B,D,a,b,c];ring
  change C (A*B)*(X-C t)+C (B*D)*(X-C r)+C (D*A)*(X-C s)=0
  calc _ = C (A*B+B*D+D*A)*X-C (t*A*B+r*B*D+s*D*A) := by
              simp only [map_add,map_mul];ring
       _ = 0 := by rw [lead,const];simp

/-- With the three distinct cubic poles fixed, the square-discriminant
numerators have values proportional to the cubes of the derivatives there. -/
theorem square_pencil_iff (P : Pencil F) {r s t : F} (four : (-4:F)≠0)
    (rs : r≠s) (st : s≠t) (tr : t≠r) (one : P.i= -(r+s+t))
    (two : P.j=r*s+r*t+s*t) (three : P.k= -(r*s*t))
    (nr : P.quad r≠0) (ns : P.quad s≠0) (nt : P.quad t≠0) :
    (∃ H : F[X], P.polynomial=H^2) ↔
      ∃ e : F, P.quad r=e*((r-s)*(r-t))^3 ∧ P.quad s=e*((s-t)*(s-r))^3 ∧
        P.quad t=e*((t-r)*(t-s))^3 := by
  let d:= (r-s)*(r-t)
  let f:= (s-t)*(s-r)
  let g:= (t-r)*(t-s)
  have dn : d≠0 := mul_ne_zero (sub_ne_zero.mpr rs) (sub_ne_zero.mpr tr.symm)
  have fnz : f≠0 := mul_ne_zero (sub_ne_zero.mpr st) (sub_ne_zero.mpr rs.symm)
  have gn : g≠0 := mul_ne_zero (sub_ne_zero.mpr tr) (sub_ne_zero.mpr st.symm)
  have conv (x j e : F) (z : j≠0) : x/j=e*j^2 ↔ x=e*j^3 := by
    rw [div_eq_iff z];ring_nf
  rw [polynomial_weights P rs st tr one two three]
  constructor
  · intro h
    obtain ⟨h₁,h₂⟩ := square_weights four rs st tr (div_ne_zero nr dn) (div_ne_zero ns fnz)
      (div_ne_zero nt gn) h
    obtain ⟨e,er,es,et⟩ := derivative_samples rs tr h₁ h₂
    exact ⟨e,(conv _ _ e dn).mp er,(conv _ _ e fnz).mp es,(conv _ _ e gn).mp et⟩
  · rintro ⟨e,er,es,et⟩
    have a : weight P r s t=e*d^2 := (conv _ _ e dn).mpr er
    have b : weight P s t r=e*f^2 := (conv _ _ e fnz).mpr es
    have c : weight P t r s=e*g^2 := (conv _ _ e gn).mpr et
    rw [a,b,c]
    exact square_for_samples r s t e

#print axioms square_pencil_iff

private theorem scalar_descent {K : Type*} [Field K] (φ : F→+*K) (P Q : F[X]) (nq : Q≠0)
    {e : K} (proportional : P.map φ=C e*Q.map φ) :
    ∃ c : F, P=C c*Q ∧ φ c=e := by
  let j:=Q.natDegree
  have nz : Q.coeff j≠0 := leadingCoeff_ne_zero.mpr nq
  have atIndex := congrArg (fun f : K[X] => f.coeff j) proportional
  simp only [coeff_map,coeff_C_mul] at atIndex
  refine ⟨P.coeff j/Q.coeff j,?_,?_⟩
  · apply Polynomial.map_injective φ φ.injective
    rw [Polynomial.map_mul,map_C,map_div₀,(div_eq_iff ((map_ne_zero φ).mpr nz)).mpr atIndex]
    exact proportional
  · rw [map_div₀]
    exact (div_eq_iff ((map_ne_zero φ).mpr nz)).mpr atIndex

/-- The monic cubic defining the pencil. -/
noncomputable def denominator (P : Pencil F) : F[X] := X^3+C P.i*X^2+C P.j*X+C P.k

/-- Its numerator, in the coefficient convention of the affine chart. -/
noncomputable def numerator (P : Pencil F) : F[X] := C P.a*X^2+C P.b*X+C P.c

/-- The unique projective candidate for a square discriminant in this chart. -/
noncomputable def exceptional (P : Pencil F) : F[X] :=
  ((denominator P).derivative^3) %ₘ (denominator P)

private theorem cubic_shape (P : Pencil F) :
    (denominator P).Monic ∧ (denominator P).natDegree=3 := by
  unfold denominator
  constructor
  · monicity <;> decide
  · compute_degree!

/-- Over the base field the exceptional projective class is the cube of the
derivative reduced modulo the cubic. -/
theorem exceptional_class {K : Type*} [Field K] [Algebra F K]
    (P : Pencil F) {r s t : K} (four : (-4:K)≠0) (rs : r≠s) (st : s≠t) (tr : t≠r)
    (one : algebraMap F K P.i= -(r+s+t)) (two : algebraMap F K P.j=r*s+r*t+s*t)
    (three : algebraMap F K P.k= -(r*s*t))
    (nr : (P.map (algebraMap F K)).quad r≠0)
    (ns : (P.map (algebraMap F K)).quad s≠0)
    (nt : (P.map (algebraMap F K)).quad t≠0) :
    (∃ H : K[X], P.polynomial.map (algebraMap F K)=H^2) ↔
      ∃ c : F, numerator P=C c*exceptional P := by
  let φ:=algebraMap F K
  let m:=denominator P
  let q:=numerator P
  let z:=exceptional P
  have mon : m.Monic := (cubic_shape P).1
  have deg : m.natDegree=3 := (cubic_shape P).2
  have ne : m≠1 := by intro h;rw [h,natDegree_one] at deg;omega
  have zdeg : z.natDegree≤2 := by
    have h := natDegree_modByMonic_lt (m.derivative^3) mon ne
    change z.natDegree<m.natDegree at h
    omega
  have qdeg : q.natDegree≤2 := by unfold q numerator;compute_degree
  have cubic (x : K) : aeval x m=(x-r)*(x-s)*(x-t) := by
    simp only [m,denominator,map_add,map_mul,map_pow,aeval_X,aeval_C,one,two,three]
    ring
  have deriv (x : K) : aeval x m.derivative=(x-s)*(x-t)+(x-r)*(x-t)+(x-r)*(x-s) := by
    simp [m,denominator,one,two]
    ring_nf
    simp [map_ofNat]
    ring
  have values (x : K) (h : x=r ∨ x=s ∨ x=t) :
      (z.map φ).eval x=((x-s)*(x-t)+(x-r)*(x-t)+(x-r)*(x-s))^3 := by
    have zero : aeval x m=0 := by
      rw [cubic];rcases h with h|h|h <;> subst x <;> simp
    calc _ = aeval x z := by rw [eval_map,aeval_def]
         _ = (aeval x m.derivative)^3 := by
               change aeval x (m.derivative^3 %ₘ m)=_
               rw [aeval_modByMonic_eq_self_of_root zero,map_pow]
         _ = _ := by rw [deriv]
  have vr : (z.map φ).eval r=((r-s)*(r-t))^3 := by simpa using values r (Or.inl rfl)
  have vs : (z.map φ).eval s=((s-t)*(s-r))^3 := by simpa [mul_comm] using values s (Or.inr (Or.inl rfl))
  have vt : (z.map φ).eval t=((t-r)*(t-s))^3 := by simpa using values t (Or.inr (Or.inr rfl))
  have nval (x : K) : (q.map φ).eval x=(P.map φ).quad x := by simp [q,numerator,Pencil.map,Pencil.quad]
  rw [polynomial_natural, square_pencil_iff (P.map φ) four rs st tr one two three nr ns nt]
  constructor
  · rintro ⟨e,er,es,et⟩
    have combine : q.map φ=C e*z.map φ := by
      apply quadratic_unique rs st tr ((natDegree_map φ).le.trans qdeg)
        ((natDegree_C_mul_le ..).trans ((natDegree_map φ).le.trans zdeg))
      · simpa only [nval,eval_mul,eval_C,vr] using er
      · simpa only [nval,eval_mul,eval_C,vs] using es
      · simpa only [nval,eval_mul,eval_C,vt] using et
    have nz : z≠0 := by
      intro hz
      have bad : ((r-s)*(r-t))^3=0 := by simpa [hz] using vr.symm
      exact (pow_ne_zero 3 (mul_ne_zero (sub_ne_zero.mpr rs) (sub_ne_zero.mpr tr.symm))) bad
    obtain ⟨c,hc,_⟩:=scalar_descent φ q z nz combine
    exact ⟨c,hc⟩
  · rintro ⟨c,hc⟩
    change q=C c*z at hc
    have prop (x : K) : (P.map φ).quad x=φ c*(z.map φ).eval x := by rw [←nval,hc];simp
    exact ⟨φ c,vr ▸ prop r,vs ▸ prop s,vt ▸ prop t⟩

#print axioms exceptional_class

end Green33SingerExceptionalLabel
