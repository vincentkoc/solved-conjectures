import Green33BaerSidonPencil
import Green33BaerCyclicCertificate
/-! Factor pairs in square-order projective coordinates. -/
open Matrix Submodule Green33BaerSidonPencil Green33BaerForms
open scoped Pointwise IntermediateField
namespace Green33BaerSidonFibers

section Cubic
variable {E K:Type*} [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]

private theorem cubic_powers (s:K) (rank:Module.finrank E K=3) (off:s∉Set.range (algebraMap E K)) :
    LinearIndependent E (fun i:Fin 3 => s^(i:ℕ)) := by
  have d : Module.finrank E E⟮s⟯∣3 := ⟨Module.finrank E⟮s⟯ K,rank ▸ (Module.finrank_mul_finrank E E⟮s⟯ K).symm⟩
  have no : Module.finrank E E⟮s⟯≠1 := fun h => off
    (IntermediateField.mem_bot.mp (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp h))
  have degree:(minpoly E s).natDegree=3 := by
    rw [←IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral s)]
    exact ((by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ d).resolve_left no
  exact degree ▸ linearIndependent_pow (K:=E) s

/-- A product of two binary linear forms proportional to the product of
the coordinate vectors has one factor proportional to the second vector. -/
private theorem binary_factor {a b:K} (an:a≠0) (rank:Module.finrank E K=3)
    (off:b/a∉Set.range (algebraMap E K)) (x y z w r:E)
    (eq:(x • a+y • b)*(z • a+w • b)=r • (a*b)) : x=0 ∨ z=0 := by
  let s:=b/a
  let cf:Fin 3→E:=![x*z,x*w+y*z-r,y*w]
  have rel : ∑ i:Fin 3,cf i • (s^(i:ℕ))=0 := by
    dsimp only [cf,s]
    simp [Fin.sum_univ_succ,Algebra.smul_def]
    simp only [Algebra.smul_def] at eq
    field_simp [an]
    linear_combination eq
  have c:=Fintype.linearIndependent_iff.mp (cubic_powers s rank off) cf rel 0
  exact mul_eq_zero.mp c
end Cubic

section Frames
variable {F E K G:Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] [FiniteDimensional F K] [FiniteDimensional E K]

private theorem span_frame {W:Submodule F K} (dim:Module.finrank F W=3)
    (b:Fin 3→K) (inside:∀ i,b i∈W) (ind:LinearIndependent F b) :
    span F (Set.range b)=W := by
  apply Submodule.eq_of_le_of_finrank_le (span_le.mpr (by rintro _ ⟨i,rfl⟩;exact inside i))
  rw [dim,finrank_span_eq_card ind]
  rfl

/-- Rank six excludes each inequivalent small-field product collision.
A collision would put a full three-term progression in W, and the two
middle quadratic products of that progression agree. -/
theorem rank_sidon (frame:K≃ₗ[E](Fin 3→E))
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    (a b c d:Kˣ) (aw:(a:K)∈rationalForm F frame) (bw:(b:K)∈rationalForm F frame)
    (cw:(c:K)∈rationalForm F frame) (dw:(d:K)∈rationalForm F frame)
    (eq:(a:K)*b=c*(d:K)) : (a:K)∈F ∙ (c:K) ∨ (a:K)∈F ∙ (d:K) := by
  by_contra! bad
  obtain ⟨s,y,off,yn,wy,wsy,wss⟩:=Green33BaerProgressions.collision_progression _
    (form_rank frame) a b c d aw bw cw dw eq bad.1 bad.2
  have ns : s∉Set.range (algebraMap E K) := by
    rintro ⟨r,hr⟩
    have h : r • y∈rationalForm F frame := by rwa [Algebra.smul_def,hr]
    obtain ⟨u,hu⟩:=form_scattered frame wy yn r h
    exact off ⟨u,by rw [IsScalarTower.algebraMap_apply F E K,hu,hr]⟩
  have cub:Module.finrank E K=3 := by rw [frame.finrank_eq];simp
  let g (i:Fin 3):=y*s^(i:ℕ)
  have inside i : g i∈rationalForm F frame := by
    fin_cases i
    · simpa [g] using wy
    · simpa [g,mul_comm] using wsy
    · simpa [g,pow_two,mul_comm,mul_left_comm,mul_assoc] using wss
  have ind : LinearIndependent F g := ((cubic_powers s cub ns).restrict_scalars' F).map'
    (Algebra.lmul F K y) (LinearMap.ker_eq_bot.mpr fun _ _ h => mul_left_cancel₀ yn h)
  have sq:=independent_squares rank g (span_frame (form_rank frame) g inside ind)
  have same : squares g 1=squares g 4 := by simp [squares,g];ring
  exact (by decide : (1:Fin 6)≠4) (sq.injective same)
#print axioms rank_sidon

omit [FiniteDimensional F K] [FiniteDimensional E K] in
private theorem tag_small (tag:Kˣ→G)
    (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K)) (u v:Kˣ)
    (h:(u:K)∈F ∙ (v:K)) : tag u=tag v := by
  obtain ⟨r,hr⟩:=mem_span_singleton.mp h
  exact (same _ _).mpr ⟨algebraMap F E r,by rw [←hr,Algebra.smul_def,Algebra.smul_def,←IsScalarTower.algebraMap_apply]⟩

private theorem small_factors (frame:K≃ₗ[E](Fin 3→E))
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    (tag:Kˣ→G) (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (a b c d:Kˣ) (aw:(a:K)∈rationalForm F frame) (bw:(b:K)∈rationalForm F frame)
    (cw:(c:K)∈rationalForm F frame) (dw:(d:K)∈rationalForm F frame)
    {r:F} (eq:(a:K)*b=r • ((c:K)*d)) : tag a=tag c ∨ tag a=tag d := by
  have nz:r≠0 := by rintro rfl;rw [zero_smul] at eq;exact mul_ne_zero a.ne_zero b.ne_zero eq
  let d':Kˣ:=Units.mk0 (r • (d:K)) (smul_ne_zero nz d.ne_zero)
  have eq' : (a:K)*b=c*(d':K) := by change (a:K)*b=c*(r • (d:K));rw [eq,mul_smul_comm]
  have td : tag d'=tag d := tag_small tag same _ _ (mem_span_singleton.mpr ⟨r,rfl⟩)
  rcases rank_sidon frame rank a b c d' aw bw cw ((rationalForm F frame).smul_mem r dw) eq' with h|h
  · exact Or.inl (tag_small tag same _ _ h)
  · exact Or.inr ((tag_small tag same _ _ h).trans td)
end Frames

section Pencil
variable {F E K G:Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] [FiniteDimensional F E] [FiniteDimensional F K] [FiniteDimensional E K]

private theorem quadratic_scalars (two:Module.finrank F E=2) {h:E} (ns:h∉Set.range (algebraMap F E))
    (k:E) : ∃ α β:F,k=algebraMap F E α+algebraMap F E β*h := by
  let b:Fin 2→E:=![h,1]
  have ind:LinearIndependent F b := linearIndependent_fin2.mpr ⟨one_ne_zero,fun a e =>
    ns ⟨a,by simpa [b,Algebra.smul_def] using e⟩⟩
  have top:span F (Set.range b)=⊤ := Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card ind,two];rfl)
  have mem:k∈span F (Set.range b) := top ▸ mem_top
  obtain ⟨f,hf⟩:= (mem_span_range_iff_exists_fun F).mp mem
  exact ⟨f 1,f 0,by simpa [b,Fin.sum_univ_succ,Algebra.smul_def,add_comm] using hf.symm⟩

omit [FiniteDimensional F E] [FiniteDimensional F K] in
private theorem outside_pair (tag:Kˣ→G) (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (cub:Module.finrank E K=3) (a b c d:Kˣ) (ab:tag a≠tag b)
    (bc:tag b≠tag c) (bd:tag b≠tag d) {h:E} (eq:(c:K)*d=h • ((a:K)*b)) :
    (c:K)∉span F {(a:K),(b:K)} ∨ (d:K)∉span F {(a:K),(b:K)} := by
  by_contra! both
  obtain ⟨x,y,xc⟩:=mem_span_pair.mp both.1
  obtain ⟨z,w,zd⟩:=mem_span_pair.mp both.2
  have off:(b:K)/a∉Set.range (algebraMap E K) := by
    rintro ⟨r,hr⟩
    exact ab ((same b a).mpr ⟨r,by rw [Algebra.smul_def,(eq_div_iff a.ne_zero).mp hr]⟩).symm
  have lift (i:F) (v:K) : (algebraMap F E i) • v = i • v := by simp only [Algebra.smul_def,←IsScalarTower.algebraMap_apply]
  have bin:=binary_factor a.ne_zero cub off (algebraMap F E x) (algebraMap F E y)
    (algebraMap F E z) (algebraMap F E w) h (by simpa only [lift,xc,zd] using eq)
  rcases bin with left|right
  · have zero:= (map_eq_zero (algebraMap F E)).mp left
    rw [zero,zero_smul,zero_add] at xc
    exact bc (tag_small tag same c b (mem_span_singleton.mpr ⟨y,xc⟩)).symm
  · have zero:= (map_eq_zero (algebraMap F E)).mp right
    rw [zero,zero_smul,zero_add] at zd
    exact bd (tag_small tag same d b (mem_span_singleton.mpr ⟨w,zd⟩)).symm

omit [FiniteDimensional F E] [FiniteDimensional E K] in
private theorem spanning_three {W:Submodule F K} (dim:Module.finrank F W=3)
    (a b c:K) (bn:b≠0) (ab:a∉F ∙ b) (out:c∉span F {a,b}) (aw:a∈W) (bw:b∈W) (cw:c∈W) :
    span F (Set.range ![a,b,c])=W := by
  let U:=span F {a,b}
  let V:=span F (Set.range ![a,b,c])
  have ind:LinearIndependent F ![a,b] := linearIndependent_fin2.mpr ⟨bn,fun r h => ab (mem_span_singleton.mpr ⟨r,h⟩)⟩
  have two:Module.finrank F U=2 := by
    have rr : Set.range ![a,b]=({a,b}:Set K) := by ext x;simp [eq_comm,or_comm]
    change Module.finrank F (span F {a,b})=2
    rw [←rr]
    exact finrank_span_eq_card ind
  have uv:U≤V := span_le.mpr (by
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl|h
    · exact subset_span ⟨0,rfl⟩
    · exact Set.mem_singleton_iff.mp h ▸ subset_span ⟨1,rfl⟩)
  have lt:U<V := lt_of_le_of_ne uv (fun h => out (show c∈U from h.symm ▸ (show c∈V from subset_span ⟨2,rfl⟩)))
  have small:V≤W := span_le.mpr (by rintro _ ⟨i,rfl⟩;fin_cases i <;> assumption)
  apply Submodule.eq_of_le_of_finrank_le small
  have hd:=Submodule.finrank_lt_finrank_of_lt lt
  omega
end Pencil

section Parameters
variable {F E K G:Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] [FiniteDimensional F E] [FiniteDimensional F K] [FiniteDimensional E K]
private theorem extra_parameter (frame:K≃ₗ[E](Fin 3→E)) (two:Module.finrank F E=2)
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    (tag:Kˣ→G) (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (a b c d e f:Kˣ) (inside:∀ x∈([a,b,c,d,e,f]:List Kˣ),(x:K)∈rationalForm F frame)
    (spans:span F (Set.range ![(a:K),b,c])=rationalForm F frame)
    (u v w:F) (valD:(d:K)=u • (a:K)+v • (b:K)+w • (c:K))
    {h k:E} (qeq:(c:K)*d=h • ((a:K)*b)) (eeq:(e:K)*f=k • ((a:K)*b))
    (ca:tag c≠tag a) (cb:tag c≠tag b) (ea:tag e≠tag a) (eb:tag e≠tag b)
    (ec:tag e≠tag c) (ed:tag e≠tag d) :
    ∃ α r:F,α≠0 ∧ r*u*v=w ∧ (e:K)*f=α • ((a:K)*b+r • ((c:K)*d)) := by
  have sep (i j m n:Kˣ) (wi:(i:K)∈rationalForm F frame) (wj:(j:K)∈rationalForm F frame)
      (wm:(m:K)∈rationalForm F frame) (wn:(n:K)∈rationalForm F frame)
      (im:tag i≠tag m) (inn:tag i≠tag n) (l:F) : (i:K)*j≠l • ((m:K)*n) := by
    intro hit
    exact (small_factors frame rank tag same i j m n wi wj wm wn hit).elim im inn
  have ns:h∉Set.range (algebraMap F E) := by
    rintro ⟨m,rfl⟩
    exact sep c d a b (inside _ (by simp)) (inside _ (by simp)) (inside _ (by simp)) (inside _ (by simp))
      ca cb m (by simpa only [Algebra.smul_def,←IsScalarTower.algebraMap_apply] using qeq)
  obtain ⟨α,β,eq⟩:=quadratic_scalars two ns k
  have add:(e:K)*f=α • ((a:K)*b)+β • ((c:K)*d) := by
    rw [eeq,eq,qeq]
    simp only [Algebra.smul_def,map_add,map_mul,←IsScalarTower.algebraMap_apply]
    ring
  have an:α≠0 := by
    rintro rfl
    exact sep e f c d (inside _ (by simp)) (inside _ (by simp)) (inside _ (by simp)) (inside _ (by simp))
      ec ed β (by simpa only [zero_smul,zero_add] using add)
  have bn:β≠0 := by
    rintro rfl
    exact sep e f a b (inside _ (by simp)) (inside _ (by simp)) (inside _ (by simp)) (inside _ (by simp))
      ea eb α (by simpa only [zero_smul,add_zero] using add)
  let r:F:=β/α
  have eqr:(e:K)*f=α • ((a:K)*b+r • ((c:K)*d)) := by
    rw [add,smul_add,smul_smul,show α*r=β by dsimp [r];field_simp]
  have rep (z:K) (hz:z∈rationalForm F frame) :
      ∃ ξ:Fin 3→F,Fintype.linearCombination F ![(a:K),b,c] ξ=z :=
    (mem_span_range_iff_exists_fun F).mp (spans.symm ▸ hz)
  obtain ⟨x,hx⟩:=rep _ ((rationalForm F frame).smul_mem α⁻¹ (inside e (by simp)))
  obtain ⟨y,hy⟩:=rep _ (inside f (by simp))
  refine ⟨α,r,an,field_parameter ![(a:K),b,c] (independent_squares rank _ spans) (div_ne_zero bn an) x y ?_,eqr⟩
  rw [hx,hy,smul_mul_assoc,eqr,inv_smul_smul₀ an]
  change _=(a:K)*b+r • ((c:K)*(u • (a:K)+v • (b:K)+w • (c:K)))
  rw [←valD]
end Parameters

section FourPairs
variable {F E K G:Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] [FiniteDimensional F E] [FiniteDimensional F K] [FiniteDimensional E K]

private structure Pair (W:Submodule F K) where
  a : Kˣ
  b : Kˣ
  aw : (a:K)∈W
  bw : (b:K)∈W

private def Pair.flip {W:Submodule F K} (p:Pair W) : Pair W := ⟨p.b,p.a,p.bw,p.aw⟩
private def Pair.separate {W:Submodule F K} (p:Pair W) (tag:Kˣ→G) (q:Pair W) :=
  tag p.a≠tag q.a ∧ tag p.a≠tag q.b ∧ tag p.b≠tag q.a ∧ tag p.b≠tag q.b

private theorem no_four_adapted (frame:K≃ₗ[E](Fin 3→E)) (two:Module.finrank F E=2)
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    (tag:Kˣ→G) (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (p q j k:Pair (rationalForm F frame)) (different:tag p.a≠tag p.b)
    (qp:q.separate tag p) (jp:j.separate tag p) (jq:j.separate tag q)
    (kp:k.separate tag p) (kq:k.separate tag q) (kj:k.separate tag j)
    (out:(q.a:K)∉span F {(p.a:K),(p.b:K)})
    {h l m:E} (qh:(q.a:K)*q.b=h • ((p.a:K)*p.b)) (jl:(j.a:K)*j.b=l • ((p.a:K)*p.b))
    (km:(k.a:K)*k.b=m • ((p.a:K)*p.b)) : False := by
  have non:(p.a:K)∉F ∙ (p.b:K) := fun v => different (tag_small tag same _ _ v)
  have spans:=spanning_three (form_rank frame) _ _ _ p.b.ne_zero non out p.aw p.bw q.aw
  have dw:(q.b:K)∈span F (Set.range ![(p.a:K),p.b,q.a]) := spans.symm ▸ q.bw
  obtain ⟨f,hd⟩:=(mem_span_range_iff_exists_fun F).mp dw
  let u:=f 0
  let v:=f 1
  let w:=f 2
  have valD:(q.b:K)=u • (p.a:K)+v • (p.b:K)+w • (q.a:K) := by
    simpa [u,v,w,Fin.sum_univ_succ,add_assoc] using hd.symm
  have co (o:Pair (rationalForm F frame)) (op:o.separate tag p) (oq:o.separate tag q)
      (l:E) (ol:(o.a:K)*o.b=l • ((p.a:K)*p.b)) :=
    extra_parameter frame two rank tag same p.a p.b q.a q.b o.a o.b
      (by intro x hx;simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
          rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> first | exact p.aw | exact p.bw | exact q.aw | exact q.bw | exact o.aw | exact o.bw)
      spans u v w valD qh ol qp.1 qp.2.1 op.1 op.2.1 oq.1 oq.2.1
  obtain ⟨α,r,an,ruv,qr⟩:=co j jp jq l jl
  obtain ⟨β,s,bn,suv,qs⟩:=co k kp kq m km
  have uv:u*v≠0 := by
    intro zero
    have wm:w=0 := by rw [mul_assoc,zero,mul_zero] at ruv;exact ruv.symm
    rw [wm,zero_smul,add_zero] at valD
    rcases mul_eq_zero.mp zero with zu|zv
    · rw [zu,zero_smul,zero_add] at valD
      exact qp.2.2.2 (tag_small tag same _ _ (mem_span_singleton.mpr ⟨v,valD.symm⟩))
    · rw [zv,zero_smul,add_zero] at valD
      exact qp.2.2.1 (tag_small tag same _ _ (mem_span_singleton.mpr ⟨u,valD.symm⟩))
  rw [mul_assoc] at ruv suv
  have rs:r=s := mul_right_cancel₀ uv (ruv.trans suv.symm)
  have final:(k.a:K)*k.b=(β/α) • ((j.a:K)*j.b) := by
    rw [qs,qr,rs,smul_smul,div_mul_cancel₀ _ an]
  exact (small_factors frame rank tag same k.a k.b j.a j.b k.aw k.bw j.aw j.bw final).elim kj.1 kj.2.1

private theorem no_four (frame:K≃ₗ[E](Fin 3→E)) (two:Module.finrank F E=2)
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    (tag:Kˣ→G) (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (p q j k:Pair (rationalForm F frame)) (different:tag p.a≠tag p.b)
    (qp:q.separate tag p) (jp:j.separate tag p) (jq:j.separate tag q)
    (kp:k.separate tag p) (kq:k.separate tag q) (kj:k.separate tag j)
    (qeq:tag (q.a*q.b)=tag (p.a*p.b)) (jeq:tag (j.a*j.b)=tag (p.a*p.b))
    (keq:tag (k.a*k.b)=tag (p.a*p.b)) : False := by
  obtain ⟨h,qh⟩:=(same _ _).mp qeq
  obtain ⟨l,jl⟩:=(same _ _).mp jeq
  obtain ⟨m,km⟩:=(same _ _).mp keq
  have cub:Module.finrank E K=3 := by rw [frame.finrank_eq];simp
  rcases outside_pair (F:=F) tag same cub p.a p.b q.a q.b different qp.2.1.symm qp.2.2.2.symm qh with out|out
  · exact no_four_adapted frame two rank tag same p q j k different qp jp jq kp kq kj out qh jl km
  · apply no_four_adapted frame two rank tag same p q.flip j k different
      ⟨qp.2.2.1,qp.2.2.2,qp.1,qp.2.1⟩ jp ⟨jq.2.1,jq.1,jq.2.2.2,jq.2.2.1⟩ kp
      ⟨kq.2.1,kq.1,kq.2.2.2,kq.2.2.1⟩ kj out (h:=h) _ jl km
    change (q.b:K)*q.a=_
    simpa only [Units.val_mul,mul_comm (q.a:K) (q.b:K)] using qh
end FourPairs

section Count
open Finset Green33Multiplicity
variable {G:Type*} [AddCommGroup G] [DecidableEq G]

private def orbit (s x:G) : Finset G := {x,s-x}
private theorem reflected_out {s x y:G} (h:x∉orbit s y) : s-x∉orbit s y := by
  simp only [orbit,mem_insert,mem_singleton,not_or] at h ⊢
  exact ⟨fun e => h.2 (by rw [←e]; abel),fun e => h.1 (sub_right_inj.mp e)⟩

private theorem six_of_forbidden (A:Finset G) (s:G)
    (diag:∀ x∈A,∀ y∈A,x+x=y+y → x=y)
    (ban:∀ (x y u v:G), (∀ z∈([x,y,u,v]:List G),z∈A ∧ s-z∈A) →
      x≠s-x → y∉orbit s x → u∉orbit s x → u∉orbit s y →
      v∉orbit s x → v∉orbit s y → v∉orbit s u → False) :
    reps A s≤6 := by
  classical
  let U:=A.filter fun x => s-x∈A
  have inject : reps A s≤U.card := by
    apply card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hw,eq⟩:=mem_filter.mp hp
      exact mem_filter.mpr ⟨(mem_product.mp hw).1,(sub_eq_of_eq_add' eq.symm) ▸ (mem_product.mp hw).2⟩
    · rintro ⟨a,b⟩ ab ⟨c,d⟩ cd h
      change a=c at h
      subst c
      exact Prod.ext rfl (add_left_cancel ((mem_filter.mp ab).2.trans (mem_filter.mp cd).2.symm))
  apply inject.trans
  by_contra! many
  obtain ⟨x,hx,nx⟩:∃ x∈U,x≠s-x := by
    by_contra! fixed
    have atmost:U.card≤1 := by
      apply card_le_one_iff.mpr
      intro a b ha hb
      exact diag a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
        ((eq_sub_iff_add_eq.mp (fixed a ha)).trans (eq_sub_iff_add_eq.mp (fixed b hb)).symm)
    omega
  have fresh (B:Finset G) (size:B.card≤6) : ∃ y∈U,y∉B := by
    by_contra! sub
    exact (not_lt_of_ge ((card_le_card sub).trans size)) many
  let P:=orbit s x
  have p2:P.card≤2:=card_le_two
  obtain ⟨y,hy,yp⟩:=fresh P (by omega)
  let Q:=orbit s y
  have q2:Q.card≤2:=card_le_two
  obtain ⟨u,hu,uo⟩:=fresh (P∪Q) (by have h:=card_union_le P Q;omega)
  let R:=orbit s u
  have r2:R.card≤2:=card_le_two
  obtain ⟨v,hv,vo⟩:=fresh (P∪Q∪R) (by have h:=card_union_le P Q;have h':=card_union_le (P∪Q) R;omega)
  simp only [mem_union,not_or] at uo vo
  apply ban x y u v _ nx yp uo.1 uo.2 vo.1.1 vo.1.2 vo.2
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> apply mem_filter.mp <;> assumption
end Count

section Labels
open Finset Green33Multiplicity Green33BaerSubline
variable {F E K G:Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] [FiniteDimensional F E] [FiniteDimensional F K] [FiniteDimensional E K]
    [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] [AddCommGroup G] in
/-- Squaring preserves distinct projective labels in a cubic extension. -/
theorem diagonal_tag (cub:Module.finrank E K=3) (tag:Kˣ→G)
    (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (a b:Kˣ) (eq:tag (a*a)=tag (b*b)) : tag a=tag b := by
  by_contra different
  let s:K:=(a:K)/b
  have off:s∉Set.range (algebraMap E K) := by
    rintro ⟨r,hr⟩
    apply different ((same _ _).mpr ⟨r,?_⟩)
    rw [Algebra.smul_def,(eq_div_iff b.ne_zero).mp hr]
  obtain ⟨r,hr⟩:=(same _ _).mp eq
  change (a:K)*a=r • ((b:K)*b) at hr
  let c:Fin 3→E:=![-r,0,1]
  have zero:∑ i:Fin 3,c i • s^(i:ℕ)=0 := by
    simp [c,s,Fin.sum_univ_succ,Algebra.smul_def]
    rw [Algebra.smul_def] at hr
    field_simp [b.ne_zero]
    linear_combination hr
  exact one_ne_zero (Fintype.linearIndependent_iff.mp (cubic_powers s cub off) c zero 2)

/-- In a rational subplane with six-dimensional product span there are at
most six ordered pairs at each label. All fields may have characteristic two. -/
theorem six_ordered (frame:K≃ₗ[E](Fin 3→E)) (two:Module.finrank F E=2)
    (rank:Module.finrank F ((rationalForm F frame)*(rationalForm F frame))=6)
    (tag:Kˣ→G) (same:∀ u v,tag u=tag v ↔ ∃ r:E,(u:K)=r • (v:K))
    (law:∀ a b c d,tag a+tag b=tag c+tag d → tag (a*b)=tag (c*d))
    (A:Finset G) (lifts:∀ x∈A,∃ u:Kˣ,(u:K)∈rationalForm F frame ∧ tag u=x) (s:G) :
    reps A s≤6 := by
  classical
  choose pick inside value using (fun x:↥A => lifts x.val x.property)
  have cub:Module.finrank E K=3 := by rw [frame.finrank_eq];simp
  apply six_of_forbidden A s
  · intro x hx y hy eq
    let a:↥A:=⟨x,hx⟩
    let b:↥A:=⟨y,hy⟩
    change a.val+a.val=b.val+b.val at eq
    change a.val=b.val
    rw [←value a,←value b] at eq ⊢
    exact diagonal_tag cub tag same _ _ (law _ _ _ _ eq)
  · intro x y u v hit xd yx ux uy vx vy vu
    let pair (z:G) (h:z∈A ∧ s-z∈A) : Pair (rationalForm F frame) :=
      ⟨pick ⟨z,h.1⟩,pick ⟨s-z,h.2⟩,inside _,inside _⟩
    have pval (z:G) (h:z∈A ∧ s-z∈A) : tag (pair z h).a=z ∧ tag (pair z h).b=s-z := ⟨value _,value _⟩
    have sep {a b:G} (ia:a∈A ∧ s-a∈A) (ib:b∈A ∧ s-b∈A) (ab:a∉orbit s b) :
        (pair a ia).separate tag (pair b ib) := by
      have ba:=reflected_out ab
      simp only [orbit,mem_insert,mem_singleton,not_or] at ab ba
      simpa only [Pair.separate,(pval a ia).1,(pval a ia).2,(pval b ib).1,(pval b ib).2] using
        (show a≠b ∧ a≠s-b ∧ s-a≠b ∧ s-a≠s-b from ⟨ab.1,ab.2,ba.1,ba.2⟩)
    have eq {a b:G} (ia:a∈A ∧ s-a∈A) (ib:b∈A ∧ s-b∈A) :
        tag ((pair a ia).a*(pair a ia).b)=tag ((pair b ib).a*(pair b ib).b) := by
      apply law
      rw [(pval a ia).1,(pval a ia).2,(pval b ib).1,(pval b ib).2]
      abel
    have hx:=hit x (by simp)
    have hy:=hit y (by simp)
    have hu:=hit u (by simp)
    have hv:=hit v (by simp)
    exact no_four frame two rank tag same (pair x hx) (pair y hy) (pair u hu) (pair v hv)
      (by rwa [(pval x hx).1,(pval x hx).2]) (sep hy hx yx) (sep hu hx ux) (sep hu hy uy)
      (sep hv hx vx) (sep hv hy vy) (sep hv hu vu) (eq hy hx) (eq hu hx) (eq hv hx)
#print axioms diagonal_tag
#print axioms six_ordered
end Labels

end Green33BaerSidonFibers
