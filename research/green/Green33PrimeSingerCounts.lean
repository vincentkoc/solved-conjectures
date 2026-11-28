import Green33SingerExceptionalLabel
import Green33PrimeSingerTriples

/-! Two-sided triple counts and reflected sumset limits on prime Singer lines. -/

open Polynomial Finset Green33SingerCubicFibers Green33SingerExceptionalLabel
open scoped Polynomial Pointwise

namespace Green33PrimeSingerCounts

private theorem coefficients_zero {F K : Type*} [Field F] [Field K] [Algebra F K]
    (r : K) (degree : (minpoly F r).natDegree=3) (a b c : F)
    (value : algebraMap F K a*r^2+algebraMap F K b*r+algebraMap F K c=0) :
    a=0 ∧ b=0 ∧ c=0 := by
  let Q : F[X] := C a*X^2+C b*X+C c
  have div : minpoly F r ∣ Q := minpoly.dvd F r (by simpa [Q] using value)
  have size : Q.natDegree≤2 := by unfold Q;compute_degree
  have zero : Q=0 := by
    by_contra ne
    have bound := natDegree_le_of_dvd div ne
    omega
  have h (n : ℕ) := congrArg (fun f : F[X] => f.coeff n) zero
  refine ⟨?_,?_,?_⟩
  · simpa [Q,coeff_X_pow] using h 2
  · simpa [Q,coeff_X_pow] using h 1
  · simpa [Q,coeff_X_pow] using h 0

private theorem affine_reverse {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K : Type*} [Field K] [Algebra F K]
    (P : Pencil F) (r : K) (degree : (minpoly F r).natDegree=3)
    (noPole : ∀ x, P.cubic x≠0) (pole : (P.map (algebraMap F K)).cubic r=0)
    (x y z k : F) (product :
      (r-algebraMap F K x)*(r-algebraMap F K y)*(r-algebraMap F K z)=
        algebraMap F K k*(P.map (algebraMap F K)).quad r) :
    y∈fiberOver P x := by
  let φ:=algebraMap F K
  let a:= -(x+y+z)-P.i-k*P.a
  let b:=x*y+x*z+y*z-P.j-k*P.b
  let c:= -(x*y*z)-P.k-k*P.c
  have value : φ a*r^2+φ b*r+φ c=0 := by
    unfold a b c
    simp only [map_sub,map_mul,map_neg,map_add]
    unfold Pencil.cubic Pencil.map at pole
    unfold Pencil.quad Pencil.map at product
    change (r-φ x)*(r-φ y)*(r-φ z)=φ k*(φ P.a*r^2+φ P.b*r+φ P.c) at product
    change r^3+φ P.i*r^2+φ P.j*r+φ P.k=0 at pole
    linear_combination product-pole
  obtain ⟨h₁,h₂,h₃⟩ := coefficients_zero r degree a b c value
  have one : P.i= -(x+y+z)-k*P.a := by dsimp [a] at h₁;linear_combination -h₁
  have two : P.j=x*y+x*z+y*z-k*P.b := by dsimp [b] at h₂;linear_combination -h₂
  have three : P.k= -(x*y*z)-k*P.c := by dsimp [c] at h₃;linear_combination -h₃
  have atX : P.cubic x+k*P.quad x=0 := by unfold Pencil.cubic Pencil.quad;rw [one,two,three];ring
  have nonzero : P.quad x≠0 := fun e => noPole x (by simpa [e] using atX)
  apply (mem_fiberOver P x y).mpr
  refine ⟨nonzero,?_⟩
  unfold Pencil.quad Pencil.middle Pencil.last
  rw [one,two,three]
  ring

open Green33ReflectedLayers (paths walk)

private def triples {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) (c : G) :
    Finset (G×G×G) := (A ×ˢ (A ×ˢ A)).filter (fun v => v.1+v.2.1+v.2.2=c)

private theorem triple_mem {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    {c a b d : G} : (a,b,d)∈triples A c ↔ a∈A ∧ b∈A ∧ d∈A ∧ a+b+d=c := by
  simp [triples,and_assoc]

private theorem triple_count {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A : Finset G) (c : G) : paths A 3 c=((triples A c).card:ℝ) := by
  classical
  simp only [paths,walk,triples,card_eq_sum_ones,Nat.cast_sum,sum_filter,sum_product]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  have eq : c-x-y-z=0 ↔ x+y+z=c := by
    constructor
    · intro h
      calc x+y+z = c-(c-x-y-z) := by abel
           _ = c := by rw [h,sub_zero]
    · intro h;rw [←h];abel
  simp [eq]

private theorem pair_cap {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (sid : IsSidon (A : Set G)) (v : G) :
    (A.filter (fun x => v-x∈A)).card≤2 := by
  classical
  let J:=A.filter (fun x => v-x∈A)
  by_cases ne : J.Nonempty
  · obtain ⟨u,hu⟩:=ne
    obtain ⟨au,bu⟩:=mem_filter.mp hu
    have sub : J⊆{u,v-u} := by
      intro x hx
      obtain ⟨ax,bx⟩:=mem_filter.mp hx
      rcases sid x ax u au (v-x) bx (v-u) bu (by abel) with h|h <;> simp [h.1]
    exact (card_le_card sub).trans card_le_two
  · have empty:=not_nonempty_iff_eq_empty.mp ne
    change J.card≤2
    simp [empty]

private theorem chart_upper {G E : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    [Fintype E] [DecidableEq E] (D : Finset G) (sid : IsSidon (D : Set G)) (c u : G)
    (e : E ↪ G) (cover : ∀ d∈D, d=u ∨ ∃ x, e x=d) (S : E→Finset E)
    (reverse : ∀ x y z, e x+e y+e z=c → y∈S x) :
    paths D 3 c≤(∑ x,((S x).card:ℝ))+6 := by
  classical
  let J:=D.filter (fun d => c-u-d∈D)
  let I:=univ.biUnion fun x : E => (S x).image (fun y => (e x,e y,c-e x-e y))
  let U:=J.image (fun x => (u,x,c-u-x))
  let V:=J.image (fun x => (x,u,c-u-x))
  let W:=J.image (fun x => (x,c-u-x,u))
  have cap : J.card≤2 := pair_cap sid (c-u)
  have capI : I.card≤∑ x,(S x).card := card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le)
  have capU : U.card≤2 := card_image_le.trans cap
  have capV : V.card≤2 := card_image_le.trans cap
  have capW : W.card≤2 := card_image_le.trans cap
  have sub : triples D c⊆I ∪ U ∪ V ∪ W := by
    rintro ⟨x,y,z⟩ hin
    obtain ⟨hx,hy,hz,eq⟩:=triple_mem.mp hin
    simp only [mem_union]
    rcases cover x hx with h|⟨i,hi⟩
    · subst x
      have ez : c-u-y=z := by rw [←eq];abel
      exact Or.inl (Or.inl (Or.inr (mem_image.mpr ⟨y,mem_filter.mpr ⟨hy,ez ▸ hz⟩,by simp [ez]⟩)))
    rcases cover y hy with h|⟨j,hj⟩
    · subst y
      have ez : c-u-x=z := by rw [←eq];abel
      exact Or.inl (Or.inr (mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,ez ▸ hz⟩,by simp [ez]⟩))
    rcases cover z hz with h|⟨k,hk⟩
    · subst z
      have ey : c-u-x=y := by rw [←eq];abel
      exact Or.inr (mem_image.mpr ⟨x,mem_filter.mpr ⟨hx,ey ▸ hy⟩,by simp [ey]⟩)
    · have ej:=reverse i j k (by simpa only [hi,hj,hk] using eq)
      have ez : c-x-y=z := by rw [←eq];abel
      exact Or.inl (Or.inl (Or.inl (mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr
        ⟨j,ej,by simp only [hi,hj,ez]⟩⟩)))
  have size := card_le_card sub
  have e₁:=card_union_le I U
  have e₂:=card_union_le (I ∪ U) V
  have e₃:=card_union_le (I ∪ U ∪ V) W
  rw [triple_count]
  exact_mod_cast (show (triples D c).card≤(∑ x,(S x).card)+6 by omega)

private theorem nonzero_conjugates {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : Pencil F) (r : K) (degree : (minpoly F r).natDegree=3)
    (pole : (P.map (algebraMap F K)).cubic r=0)
    (nz : (P.map (algebraMap F K)).quad r≠0) (s : K)
    (hs : (P.map (algebraMap F K)).cubic s=0) :
    (P.map (algebraMap F K)).quad s≠0 := by
  let m:=denominator P
  let q:=numerator P
  have cub (x : K) : aeval x m=(P.map (algebraMap F K)).cubic x := by
    simp [m,denominator,Pencil.cubic,Pencil.map]
  have val (x : K) : aeval x q=(P.map (algebraMap F K)).quad x := by
    simp [q,numerator,Pencil.quad,Pencil.map]
  have mon : m.Monic := by unfold m denominator;monicity <;> decide
  have md : m.natDegree=3 := by unfold m denominator;compute_degree!
  have ir : IsIntegral F r:=⟨m,mon,(cub r).trans pole⟩
  have eq : m=minpoly F r:=eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ir) mon
    (minpoly.dvd F r ((cub r).trans pole)) (md.trans degree.symm).le
  have other : m=minpoly F s:=minpoly.eq_of_irreducible_of_monic (eq ▸ minpoly.irreducible ir)
    ((cub s).trans hs) mon
  intro zero
  have div : minpoly F s∣q:=minpoly.dvd F s ((val s).trans zero)
  rw [←other,eq] at div
  obtain ⟨k,hk⟩:=div
  exact nz (by rw [←val,hk,map_mul,minpoly.aeval,zero_mul])

private theorem twist_square {F K : Type*} [Field F] [Field K] (φ : F→+*K) (g : F[X])
    (r b : K) (nz : b≠0) (atPole : (g.map φ).eval r=b^2)
    (twist : ∃ c : F, ∃ q : F[X], g=C c*q^2) : ∃ H : K[X], g.map φ=H^2 := by
  obtain ⟨c,q,fac⟩:=twist
  let a:=(q.map φ).eval r
  have val : φ c*a^2=b^2 := by simpa [fac,a,Polynomial.map_mul,Polynomial.map_pow] using atPole
  have an : a≠0 := by intro hn;rw [hn,zero_pow (by decide : 2≠0),mul_zero] at val;exact (pow_ne_zero 2 nz) val.symm
  have scalar : φ c=(b/a)^2 := by field_simp [an];exact val
  refine ⟨C (b/a)*q.map φ,?_⟩
  rw [fac,Polynomial.map_mul,Polynomial.map_pow,map_C,scalar,map_pow,mul_pow]

private theorem value_at_exception {F K : Type*} [Field F] [Field K] [Algebra F K]
    (P : Pencil F) {r s t : K} (four : (-4:K)≠0) (rs : r≠s) (st : s≠t) (tr : t≠r)
    (one : r+s+t= -algebraMap F K P.i) (two : r*s+r*t+s*t=algebraMap F K P.j)
    (three : r*s*t= -algebraMap F K P.k)
    (degree : (minpoly F r).natDegree=3) (nr : (P.map (algebraMap F K)).quad r≠0)
    (twist : ∃ c : F, ∃ q : F[X], P.polynomial=C c*q^2) :
    ∃ c : F, (P.map (algebraMap F K)).quad r=algebraMap F K c*((r-s)*(r-t))^3 := by
  let φ:=algebraMap F K
  have i : φ P.i= -(r+s+t) := by dsimp [φ];linear_combination one
  have k : φ P.k= -(r*s*t) := by dsimp [φ];linear_combination three
  have m (x : K) : (P.map φ).cubic x=(x-r)*(x-s)*(x-t) := by
    unfold Pencil.cubic Pencil.map;dsimp only
    rw [i,←two,k];ring
  have root : (P.map φ).cubic r=0 := by rw [m];simp
  have ns:=nonzero_conjugates P r degree root nr s (by rw [m];simp)
  have nt:=nonzero_conjugates P r degree root nr t (by rw [m];simp)
  have atPole := (P.eval_polynomial φ r).trans ((P.map φ).pole_value one two three)
  have square:=twist_square φ P.polynomial r _ (mul_ne_zero nr (sub_ne_zero.mpr st)) atPole twist
  obtain ⟨c,hc⟩:=(exceptional_class P four rs st tr i two.symm k nr ns nt).mp square
  refine ⟨c,?_⟩
  have val (q : F[X]) := aeval_modByMonic_eq_self_of_root (p:=q)
    (show aeval r (denominator P)=0 by simpa [denominator,Pencil.cubic,Pencil.map] using root)
  have h:=congrArg (aeval r) hc
  change aeval r (numerator P)=aeval r (C c*((denominator P).derivative^3 %ₘ denominator P)) at h
  rw [map_mul,aeval_C,val,map_pow] at h
  have deriv : aeval r (denominator P).derivative=(r-s)*(r-t) := by
    have i₀ : algebraMap F K P.i= -(r+s+t):=i
    simp [denominator,i₀,←two]
    ring_nf
    simp [map_ofNat]
    ring
  rw [deriv] at h
  simpa [numerator,Pencil.map,Pencil.quad] using h

open Green33PrimeSingerIncidence Green33PrimeSingerTriples

/-- Every target except one projective label has at most (p+O(√p)) ordered
three-term representations. The constant is uniform in the cubic Singer chart. -/
theorem triple_upper_field {F : Type*} [Field F] [Fintype F] [DecidableEq F] (odd : ringChar F≠2) {K G : Type*} [Field K] [Fintype K]
    [Algebra F K] [AddCommGroup G] [DecidableEq G] [Fintype G]
    (D : Finset G) (S : SingerMap F K D) (sid : IsSidon (D : Set G))
    (size : D.card=Fintype.card F+1) (card : Fintype.card K=(Fintype.card F)^3) :
    ∃ exception : G, ∀ c≠exception,
      paths D 3 c≤(Fintype.card F:ℝ)+80*(((Fintype.card F).sqrt:ℝ)+1)+10 := by
  classical
  let φ:=algebraMap F K
  obtain ⟨C⟩:=line_chart_field D S (by have := Fintype.one_lt_card (α:=F);omega) card
  let U:=C.base
  let θ:=C.theta
  let e:=C.embedding
  obtain ⟨i,j,k,s,t,st,rs,tr,one,two,three,irr,root⟩:=cubic_poles θ C.degree
  let v:=((θ-s)*(θ-t))^3
  have vn : v≠0 := pow_ne_zero 3 (mul_ne_zero (sub_ne_zero.mpr rs) (sub_ne_zero.mpr tr.symm))
  let E:=Units.mk0 ((U:K)^3*v) (mul_ne_zero (pow_ne_zero 3 U.ne_zero) vn)
  refine ⟨S.tag E,?_⟩
  intro c ne
  obtain ⟨W,wc⟩:=S.surj c
  obtain ⟨a,b,d,eq⟩:=span_quadratics θ card C.degree ((W:K)/(U:K)^3)
  let P : Pencil F:=⟨i,j,k,a,b,d⟩
  have val : (P.map φ).quad θ=(W:K)/(U:K)^3:=eq
  have prod : (P.map φ).quad θ*(U:K)^3=(W:K):=(eq_div_iff (pow_ne_zero 3 U.ne_zero)).mp val
  have four : (-4:K)≠0 := by
    have twoK : (2:K)≠0 := Ring.two_ne_zero (by rwa [←Algebra.ringChar_eq F K])
    exact neg_ne_zero.mpr (by simpa only [show (4:K)=2*2 by norm_num] using mul_ne_zero twoK twoK)
  have count : (∑ x : F,(fiberOver P x).card)≤Fintype.card F+80*((Fintype.card F).sqrt+1)+4 := by
    rcases pairs_or_twist_field odd P with q|twist
    · exact q
    · obtain ⟨j,ej⟩:=value_at_exception P four rs st tr one two three C.degree
        (val.trans_ne (div_ne_zero W.ne_zero (pow_ne_zero 3 U.ne_zero))) twist
      apply (ne (wc ▸ (S.same W E).mpr ⟨j,?_⟩)).elim
      rw [Algebra.smul_def]
      change (W:K)=φ j*((U:K)^3*v)
      change (P.map φ).quad θ=φ j*v at ej
      rw [←prod,ej];ring
  have rev (x y z : F) (he : e x+e y+e z=c) : y∈fiberOver P x := by
    have tags : S.tag (C.parameter x*C.parameter y*C.parameter z)=S.tag W := by
      rw [S.mul,S.mul,←C.tagged,←C.tagged,←C.tagged,wc];exact he
    obtain ⟨m,hm⟩:=(S.same _ _).mp tags
    rw [Algebra.smul_def] at hm
    change ((C.parameter x:K)*(C.parameter y:K))*(C.parameter z:K)=φ m*W at hm
    rw [C.coordinates,C.coordinates,C.coordinates] at hm
    change ((U:K)*(θ-φ x))*((U:K)*(θ-φ y))*((U:K)*(θ-φ z))=φ m*(W:K) at hm
    apply affine_reverse P θ C.degree irr root x y z m
    apply mul_right_cancel₀ (pow_ne_zero 3 U.ne_zero)
    change ((θ-φ x)*(θ-φ y)*(θ-φ z))*(U:K)^3=φ m*(P.map φ).quad θ*(U:K)^3
    rw [mul_assoc (φ m),prod]
    linear_combination hm
  have inside : univ.map e⊆D := by
    intro z hz
    obtain ⟨x,_,rfl⟩:=mem_map.mp hz
    exact C.inside x
  have diff : (D \ univ.map e).card=1 := by rw [card_sdiff_of_subset inside,card_map,card_univ,size];omega
  obtain ⟨u,hu⟩:=card_eq_one.mp diff
  have cover (d) (hd : d∈D) : d=u ∨ ∃ x,e x=d := by
    by_cases h : d∈univ.map e
    · obtain ⟨x,_,hx⟩:=mem_map.mp h
      exact Or.inr ⟨x,hx⟩
    · have hv:=mem_sdiff.mpr ⟨hd,h⟩
      rw [hu,mem_singleton] at hv
      exact Or.inl hv
  have upper:=chart_upper D sid c u e cover (fiberOver P) rev
  have q : (∑ x : F,((fiberOver P x).card:ℝ))≤(Fintype.card F:ℝ)+80*(((Fintype.card F).sqrt:ℝ)+1)+4 := by exact_mod_cast count
  linarith

#print axioms triple_upper_field

theorem triple_upper {p : ℕ} [Fact p.Prime] {K G : Type*} [Field K] [Fintype K]
    [Algebra (ZMod p) K] [AddCommGroup G] [DecidableEq G] [Fintype G]
    (D : Finset G) (S : SingerMap (ZMod p) K D) (sid : IsSidon (D : Set G))
    (size : D.card=p+1) (card : Fintype.card K=(Fintype.card (ZMod p))^3) (big : 400≤p) :
    ∃ exception : G, ∀ c≠exception,
      paths D 3 c≤(p:ℝ)+80*((p.sqrt:ℝ)+1)+10 := by
  have odd : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  simpa only [ZMod.card] using triple_upper_field odd D S sid (by simpa only [ZMod.card] using size) card

#print axioms triple_upper

private theorem triple_cap {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (D : Finset G) (sid : IsSidon (D : Set G)) (c : G) : paths D 3 c≤2*(D.card:ℝ) := by
  classical
  have one (t : G) : paths D 1 t=if t∈D then 1 else 0 := by
    simp only [paths,walk,sub_eq_zero,sum_ite_eq]
  have two (t : G) : paths D 2 t≤2 := by
    change (∑ x∈D,paths D 1 (t-x))≤2
    simp only [one,sum_boole]
    exact_mod_cast pair_cap sid t
  change (∑ x∈D,paths D 2 (c-x))≤_
  calc _ ≤ ∑ _x∈D,(2:ℝ) := sum_le_sum fun x _ => two (c-x)
       _ = _ := by simp [mul_comm]

open Green33SingerAllCharacteristics Green33PrimeSingerBasisGap Green33PerfectDifferenceCenters
open Green33ReflectedLayers (overlap)
open Green33SingerKloosterman (cubic_parameters)

section FiniteFields

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra F K]

/-- Two-sided uniform finite error for the reflected overlap, with the one
exceptional three-term target charged at most once. -/
theorem overlap_error_field (odd : ringChar F≠2) (card : Fintype.card K=(Fintype.card F)^3)
    (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (c : ZMod (order F)) :
    |4*(overlap (labels card L) c:ℝ)-(order F:ℝ)|≤
      (((Fintype.card F):ℝ)+1)*(80*(((Fintype.card F).sqrt:ℝ)+1)+16)+1 := by
  classical
  let D:=labels card L
  have size : D.card=(Fintype.card F)+1 := by change (labels card L).card=_;rw [labels,card_map,(cubic_parameters L onto card).1]
  have hd:=(perfect_labels card L onto).sidon
  obtain ⟨S⟩:=singer_map card L onto
  obtain ⟨z,hz⟩:=triple_upper_field odd D S hd size card
  let E : ℝ:=80*(((Fintype.card F).sqrt:ℝ)+1)+10
  have low (a : ZMod (order F)) : ((Fintype.card F):ℝ)-E≤paths D 3 (c-a) := by
    have h:=label_triples_field odd card L onto (c-a)
    dsimp [D,E];linarith
  have upper (a : ZMod (order F)) :
      paths D 3 (c-a)≤((Fintype.card F):ℝ)+E+if a=c-z then 2*(((Fintype.card F):ℝ)+1) else 0 := by
    by_cases hit : a=c-z
    · rw [if_pos hit]
      have h:=triple_cap D hd (c-a)
      rw [size,Nat.cast_add,Nat.cast_one] at h
      have e : 0≤E := by dsimp [E];positivity
      linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card F)]
    · rw [if_neg hit,add_zero]
      simpa only [E,add_assoc] using hz (c-a) (fun e => hit (by rw [←e];abel))
  have low_sum:=sum_le_sum (s:=D) (fun x _ => low x)
  have up_sum:=sum_le_sum (s:=D) (fun x _ => upper x)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,sum_ite_eq',size,Nat.cast_add,Nat.cast_one] at up_sum low_sum
  have loss : (if c-z∈D then 2*(((Fintype.card F):ℝ)+1) else 0)≤2*(((Fintype.card F):ℝ)+1) := by split <;> first | exact le_rfl | positivity
  change (((Fintype.card F):ℝ)+1)*(((Fintype.card F):ℝ)-E)≤paths D 4 c at low_sum
  change paths D 4 c≤(((Fintype.card F):ℝ)+1)*(Fintype.card F)+(((Fintype.card F):ℝ)+1)*E+_ at up_sum
  have ov:=Green33ReflectedLayers.two_walk_overlap hd c
  change paths D 4 c≤4*(overlap D c:ℝ) ∧ 4*(overlap D c:ℝ)≤paths D 4 c+4*(D.card:ℝ) at ov
  rw [size,Nat.cast_add,Nat.cast_one] at ov
  have v : (order F:ℝ)=((Fintype.card F):ℝ)^2+(Fintype.card F)+1 := by simp [Green33SingerAllCharacteristics.order]
  change |4*(overlap D c:ℝ)-(order F:ℝ)|≤_
  rw [v,abs_le]
  dsimp [E] at low_sum up_sum
  constructor <;> nlinarith only [up_sum,low_sum,ov.1,ov.2,loss,Nat.cast_nonneg (α:=ℝ) (Fintype.card F)]

#print axioms overlap_error_field

/-- The ordinary sumset in the doubled cyclic group has density (7/8) up
to a uniform (O(Q^{-1/2})) relative error. -/
theorem doubled_error_field (odd : ringChar F≠2) (card : Fintype.card K=(Fintype.card F)^3)
    (L : K→ₗ[F] F) (onto : Function.Surjective L)
    (t : ZMod (order F)) :
    |4*((reflected card L t+reflected card L t).card:ℝ)-7*(order F:ℝ)|≤
      (((Fintype.card F):ℝ)+1)*(80*(((Fintype.card F).sqrt:ℝ)+1)+24)+5 := by
  classical
  let c:=1+t+t
  have size : (labels card L).card=(Fintype.card F)+1 := by rw [labels,card_map,(cubic_parameters L onto card).1]
  have ne : (labels card L).Nonempty:=card_pos.mp (by omega)
  have h:=doubled_count (m:=positiveOrder F) (perfect_labels card L onto) ne t
  have eq:=congrArg (Nat.cast (R:=ℝ)) h
  push_cast at eq
  change ((reflected card L t+reflected card L t).card:ℝ)+(overlap (labels card L) c:ℝ)+1=
    2*(order F:ℝ)+2*((labels card L).card:ℝ) at eq
  have realSize : ((labels card L).card:ℝ)=((Fintype.card F):ℝ)+1 := by exact_mod_cast size
  rw [realSize] at eq
  have b:=abs_le.mp (overlap_error_field odd card L onto c)
  rw [abs_le]
  constructor <;> nlinarith only [eq,b.1,b.2,Nat.cast_nonneg (α:=ℝ) (Fintype.card F)]

#print axioms doubled_error_field


end FiniteFields

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K]

theorem overlap_error (card : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 400≤p)
    (c : ZMod (order (ZMod p))) :
    |4*(overlap (labels card L) c:ℝ)-(order (ZMod p):ℝ)|≤
      ((p:ℝ)+1)*(80*((p.sqrt:ℝ)+1)+16)+1 := by
  have odd : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  simpa only [ZMod.card] using overlap_error_field odd card L onto c

#print axioms overlap_error

theorem doubled_error (card : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 400≤p)
    (t : ZMod (order (ZMod p))) :
    |4*((reflected card L t+reflected card L t).card:ℝ)-7*(order (ZMod p):ℝ)|≤
      ((p:ℝ)+1)*(80*((p.sqrt:ℝ)+1)+24)+5 := by
  have odd : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  simpa only [ZMod.card] using doubled_error_field odd card L onto t

#print axioms doubled_error

open Filter
open scoped Topology

private theorem normalized (q : ℕ→ℕ) (v u : ℕ→ℝ) (b : ℝ) (hv : ∀ i,(q i:ℝ)^2≤v i)
    (grow : Tendsto q atTop atTop)
    (err : ∀ᶠ i in atTop, |u i-b*v i|≤
      ((q i:ℝ)+1)*(80*(((q i).sqrt:ℝ)+1)+24)+5) :
    Tendsto (fun i => u i/v i) atTop (𝓝 b) := by
  have large : Tendsto (fun i => (q i:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp grow
  have small:=((tendsto_const_nhds (x:=(160:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp large)).add
    ((tendsto_const_nhds (x:=(220:ℝ))).div_atTop large)
  rw [add_zero] at small
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ small
  filter_upwards [grow.eventually_ge_atTop 400,err] with i big ei
  let x:ℝ:=q i
  let y:ℝ:=(q i).sqrt
  have largeX : (400:ℝ)≤x := by dsimp [x];exact_mod_cast big
  have xp : 0<x:=by linarith
  have vp:= (sq_pos_of_pos xp).trans_le (hv i)
  have yp : 0≤y := by dsimp [y];positivity
  have ybound : y≤Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    dsimp [y,x]
    exact_mod_cast (show ((q i).sqrt)^2≤q i by simpa [pow_two] using Nat.sqrt_le (q i))
  have coarse : (x+1)*(80*(y+1)+24)+5≤x*(160*Real.sqrt x+220) := by
    have cmp:=mul_le_mul (show x+1≤2*x by linarith)
      (show 80*(y+1)+24≤80*(Real.sqrt x+1)+24 by linarith) (by linarith : 0≤80*(y+1)+24)
      (by linarith : 0≤2*x)
    linarith
  have bound:=ei.trans coarse
  have rt:=Real.sqrt_pos.mpr xp
  change ‖u i/v i-b‖≤160/Real.sqrt x+220/x
  rw [show u i/v i-b=(u i-b*v i)/v i by field_simp,Real.norm_eq_abs,abs_div,abs_of_pos vp]
  calc
    _ ≤ (x*(160*Real.sqrt x+220))/v i := (div_le_div_iff_of_pos_right vp).mpr bound
    _ ≤ (x*(160*Real.sqrt x+220))/x^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos xp) (hv i)
    _ = _ := by field_simp [xp.ne',rt.ne'];nlinarith only [Real.sq_sqrt xp.le]

section OddFieldLimits

variable (F : ℕ→Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (odd : ∀ᶠ i in atTop, ringChar (F i)≠2) (K : ℕ→Type*) [∀ i, Field (K i)]
    [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)] [∀ i, Algebra (F i) (K i)]
    (h : ∀ i, Fintype.card (K i)=(Fintype.card (F i))^3)
    (L : ∀ i, K i→ₗ[F i] F i) (onto : ∀ i, Function.Surjective (L i))
    (t : ∀ i, ZMod (order (F i))) (grow : Tendsto (fun i => Fintype.card (F i)) atTop atTop)

include onto odd grow

/-- All choices of centers have limiting reflected overlap one quarter over
growing odd finite fields. -/
theorem quarter_field :
    Tendsto (fun i => (overlap (labels (h i) (L i)) (t i):ℝ)/(order (F i):ℝ))
      atTop (𝓝 (1/4)) := by
  let v i : ℝ:=order (F i)
  let I i : ℝ:=overlap (labels (h i) (L i)) (t i)
  have hv (i) : (Fintype.card (F i):ℝ)^2≤v i := by dsimp [v,order];simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow];linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (F i))]
  have z:=normalized (fun i => Fintype.card (F i)) v (fun i => 4*I i) 1 hv grow (by
    filter_upwards [odd] with i oi
    rw [one_mul]
    have hh:= overlap_error_field oi (h i) (L i) (onto i) (t i)
    change |4*I i-v i|≤_ at hh
    exact hh.trans (by nlinarith only [Nat.cast_nonneg (α:=ℝ) (Fintype.card (F i))]))
  apply (z.div_const 4).congr
  intro i
  change 4*I i/v i/4=I i/v i
  ring

/-- Seven-eighths coverage by the ordinary doubled Singer construction for
every sequence of reflection axes over growing odd finite fields. -/
theorem seven_eighths_field :
    Tendsto (fun i => ((reflected (h i) (L i) (t i)+reflected (h i) (L i) (t i)).card:ℝ)/
      (2*(order (F i):ℝ))) atTop (𝓝 (7/8)) := by
  let v i : ℝ:=order (F i)
  let A i : ℝ:=(reflected (h i) (L i) (t i)+reflected (h i) (L i) (t i)).card
  have hv (i) : (Fintype.card (F i):ℝ)^2≤v i := by dsimp [v,order];simp only [Nat.cast_add,Nat.cast_one,Nat.cast_pow];linarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (F i))]
  have z:=normalized (fun i => Fintype.card (F i)) v (fun i => 4*A i) 7 hv grow (odd.mono fun i oi => doubled_error_field oi (h i) (L i) (onto i) (t i))
  apply (z.div_const 8).congr
  intro i
  change 4*A i/v i/8=A i/(2*v i)
  ring

#print axioms quarter_field
#print axioms seven_eighths_field

open Green33ReflectedLayers (doubleHom double_coordinates)

/-- Any ordinary full basis containing both reflected odd-field Singer layers has
eventual normalized size above every value below `(3+√3)/(2√2)`. -/
theorem repair_floor_field (B : ∀ i, Finset (ZMod (2*order (F i))))
    (sub : ∀ i, reflected (h i) (L i) (t i)⊆B i) (full : ∀ i,B i+B i=univ)
    {s : ℝ} (below : s<(3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, s<((B i).card:ℝ)/Real.sqrt (2*(order (F i):ℝ)) := by
  classical
  let v i:=positiveOrder (F i)
  let D (i : ℕ) : Finset (ZMod (v i)):=labels (h i) (L i)
  let T (i : ℕ) : ZMod (v i):=t i
  have ne i : (D i).Nonempty := by
    apply card_pos.mp
    change 0<(labels (h i) (L i)).card
    rw [labels,card_map,(cubic_parameters (L i) (onto i) (h i)).1];omega
  have hd i : Perfect (D i):=perfect_labels (h i) (L i) (onto i)
  have vg : Tendsto (fun i => Fintype.card (ZMod (v i))) atTop atTop := by
    simp only [ZMod.card]
    exact tendsto_atTop_mono (fun i => by dsimp [v,positiveOrder,order];omega) grow
  have inter : Tendsto (fun i => (overlap (D i) (1+T i+T i):ℝ)/Fintype.card (ZMod (v i)))
      atTop (𝓝 (1/4)) := by
    simp only [ZMod.card]
    exact quarter_field F odd K h L onto (fun i => 1+t i+t i) grow
  have res:=Green33SidonLayerRepairs.overlap_extension_lower D (fun i => (hd i).sidon) ne
    (fun i => doubleHom (v i)) (fun i => (double_coordinates (v i) (T i)).1)
    (fun i => 1+doubleHom (v i) (T i)) (fun i => (double_coordinates (v i) (T i)).2.1)
    (by intro i;simp only [ZMod.card]) (fun i => 1+T i+T i)
    (fun i => (double_coordinates (v i) (T i)).2.2) vg (perfect_size_limit D hd vg) inter B sub full below
  simp only [ZMod.card,Nat.cast_mul,Nat.cast_ofNat] at res
  exact res

#print axioms repair_floor_field

end OddFieldLimits

section Limits

variable (q : ℕ→ℕ) [∀ i, Fact (q i).Prime] (K : ℕ→Type*) [∀ i, Field (K i)]
    [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)] [∀ i, Algebra (ZMod (q i)) (K i)]
    (h : ∀ i, Fintype.card (K i)=(Fintype.card (ZMod (q i)))^3)
    (L : ∀ i, K i→ₗ[ZMod (q i)] ZMod (q i)) (onto : ∀ i, Function.Surjective (L i))
    (t : ∀ i, ZMod (order (ZMod (q i)))) (grow : Tendsto q atTop atTop)

include onto grow

omit onto in
private theorem prime_eventually_odd : ∀ᶠ i in atTop, ringChar (ZMod (q i))≠2 := by
  filter_upwards [grow.eventually_ge_atTop 3] with i hi
  rw [ringChar.eq (ZMod (q i)) (q i)]
  omega

theorem quarter :
    Tendsto (fun i => (overlap (labels (h i) (L i)) (t i):ℝ)/(order (ZMod (q i)):ℝ))
      atTop (𝓝 (1/4)) := by
  exact quarter_field (fun i => ZMod (q i)) (prime_eventually_odd q grow) K h L onto t
    (by simpa only [ZMod.card] using grow)

#print axioms quarter

theorem seven_eighths :
    Tendsto (fun i => ((reflected (h i) (L i) (t i)+reflected (h i) (L i) (t i)).card:ℝ)/
      (2*(order (ZMod (q i)):ℝ))) atTop (𝓝 (7/8)) := by
  exact seven_eighths_field (fun i => ZMod (q i)) (prime_eventually_odd q grow) K h L onto t
    (by simpa only [ZMod.card] using grow)

#print axioms seven_eighths

theorem repair_floor (B : ∀ i, Finset (ZMod (2*order (ZMod (q i)))))
    (sub : ∀ i, reflected (h i) (L i) (t i)⊆B i) (full : ∀ i,B i+B i=univ)
    {s : ℝ} (below : s<(3+Real.sqrt 3)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop, s<((B i).card:ℝ)/Real.sqrt (2*(order (ZMod (q i)):ℝ)) := by
  exact repair_floor_field (fun i => ZMod (q i)) (prime_eventually_odd q grow) K h L onto t
    (by simpa only [ZMod.card] using grow) B sub full below

#print axioms repair_floor

end Limits

end Green33PrimeSingerCounts
