import Green33PrimeSingerCounts
import Green33SingerBlockingLayers
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.PGroup

/-! Planar multipliers and the ordered triple count at a canonical center. -/

open Finset Green33PerfectDifferenceCenters Green33SingerBlockingLayers
open scoped Pointwise

namespace Green33PlanarMultipliers

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

private noncomputable def word (p : ℕ) (D : Finset G) (f : G→G) : AddMonoidAlgebra (ZMod p) G :=
  ∑ x∈D,AddMonoidAlgebra.single (f x) 1

omit [Fintype G] in
private theorem prod_coeff (p : ℕ) (D : Finset G) (f g : G→G) (t : G) :
    ((word p D f)*(word p D g)).coeff t=
      (((D ×ˢ D).filter (fun v => f v.1+g v.2=t)).card:ZMod p) := by
  classical
  simp only [word,sum_mul,mul_sum,AddMonoidAlgebra.single_mul_single,one_mul,
    AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply,card_eq_sum_ones,sum_filter,sum_product,Nat.cast_sum]
  rw [sum_comm]
  simp

omit [AddCommGroup G] in
private theorem univ_coeff (p : ℕ) (t : G) : (word p univ id).coeff t=1 := by
  classical
  simp [word,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Finsupp.single_apply]

private theorem uniform_mul (p : ℕ) (D : Finset G) :
    word p D id*word p univ id=(D.card:ZMod p) • word p univ id := by
  apply AddMonoidAlgebra.ext
  ext t
  unfold word
  rw [sum_mul,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
  change (∑ i∈D,(AddMonoidAlgebra.single (id i) 1*word p univ id).coeff t)=_
  simp only [AddMonoidAlgebra.coeff_single_mul_apply,univ_coeff,sum_const,nsmul_eq_mul,mul_one]
  change _=((D.card:ZMod p) • (word p univ id)).coeff t
  simp [univ_coeff]

private theorem perfect_mod (p : ℕ) [Fact p.Prime] (D : Finset G) (perfect : Perfect D)
    {q : ℕ} (size : D.card=q+1) (divide : p∣q) : word p D id*word p D Neg.neg=word p univ id := by
  apply AddMonoidAlgebra.ext
  ext t
  rw [prod_coeff,univ_coeff]
  simp only [id_eq,←sub_eq_add_neg]
  change ((Green33TailEnergy.diffReps D t:ℕ):ZMod p)=1
  by_cases zero : t=0
  · subst t
    simp only [Green33TailEnergy.diffReps,sub_eq_zero,←diag_eq_filter,diag_card]
    rw [size,Nat.cast_add,(ZMod.natCast_eq_zero_iff ..).mpr divide]
    simp
  · rw [perfect t zero,Nat.cast_one]

omit [DecidableEq G] [Fintype G] in
private theorem frobenius_word (p : ℕ) [Fact p.Prime] (D : Finset G) :
    (word p D id)^p=word p D (fun d => p • d) := by
  let φ : ZMod p →+* AddMonoidAlgebra (ZMod p) G:=AddMonoidAlgebra.singleZeroRingHom
  let _ : CharP (AddMonoidAlgebra (ZMod p) G) p:=charP_of_injective_ringHom φ.injective p
  unfold word
  rw [sum_pow_char]
  simp only [AddMonoidAlgebra.single_pow,id_eq,one_pow]

/-- Every difference from the prime multiple has multiplicity one modulo the
prime. Hall's planar multiplier argument uses only the resulting full support. -/
private theorem cross_mod (p : ℕ) [Fact p.Prime] (D : Finset G) (perfect : Perfect D)
    {q : ℕ} (size : D.card=q+1) (divide : p∣q) (t : G) :
    (((D ×ˢ D).filter (fun v => p • v.1-v.2=t)).card:ZMod p)=1 := by
  let A:=word p D id
  let B:=word p D Neg.neg
  let J : AddMonoidAlgebra (ZMod p) G:=word p univ id
  have C : (D.card:ZMod p)=1 := by rw [size,Nat.cast_add,(ZMod.natCast_eq_zero_iff ..).mpr divide];simp
  have AJ : A*J=J := (uniform_mul p D).trans (by rw [C,one_smul])
  have all (n : ℕ) : A^n*J=J := by
    induction n with
    | zero => simp
    | succ n h => rw [pow_succ,mul_assoc,AJ,h]
  have AB : A*B=J := perfect_mod p D perfect size divide
  have key : A^p*B=J := calc
    _ = (A^(p-1)*A)*B := by rw [←pow_succ,Nat.sub_add_cancel (Fact.out : Nat.Prime p).one_le]
    _ = J := by rw [mul_assoc,AB,all]
  change (word p D id)^p*word p D Neg.neg=word p univ id at key
  rw [frobenius_word] at key
  have co:=congrArg (fun v : AddMonoidAlgebra (ZMod p) G => v.coeff t) key
  simpa only [prod_coeff,univ_coeff,sub_eq_add_neg] using co

private theorem order_formula (D : Finset G) (perfect : Perfect D) {q : ℕ} (size : D.card=q+1) :
    Fintype.card G=q*(q+1)+1 := by
  have h:=parameters D perfect
  rw [size] at h
  push_cast at h
  exact_mod_cast (show (Fintype.card G:ℝ)=(q:ℝ)*(q+1)+1 by nlinarith only [h])

omit [DecidableEq G] in
private theorem scalar_injective (p : ℕ) {q : ℕ} (divide : p∣q)
    (order : Fintype.card G=q*(q+1)+1) : Function.Injective (fun x : G => p • x) := by
  obtain ⟨u,hu⟩:=divide
  have pq : p*(u*(q+1))=q*(q+1) := by rw [hu];ring
  have cancel (x : G) : (q*(q+1)) • x= -x := by
    have e:=card_nsmul_eq_zero (x:=x)
    rw [order,add_nsmul,one_nsmul] at e
    exact eq_neg_of_add_eq_zero_left e
  intro x y eq
  have h:=congrArg (fun g : G => (u*(q+1)) • g) eq
  change (u*(q+1)) • (p • x)=(u*(q+1)) • (p • y) at h
  rw [←mul_nsmul,←mul_nsmul,pq,cancel,cancel] at h
  exact neg_injective h

/-- Hall's prime multiplier theorem for planar difference sets in a finite
abelian group. Every prime divisor of the plane order acts by a translate. -/
theorem prime_multiplier (p : ℕ) [hp : Fact p.Prime] (D : Finset G) (perfect : Perfect D)
    {q : ℕ} (positive : 0<q) (size : D.card=q+1) (divide : p∣q) :
    ∃ c : G, D.image (fun x => p • x)=D.image (fun x => x+c) := by
  classical
  let B:=D.image (fun x => -(p • x))
  have inj:=scalar_injective p divide (order_formula D perfect size)
  have neginj : Function.Injective (fun x : G => -(p • x)):=neg_injective.comp inj
  have budget : B.card=q+1+0 := by rw [add_zero,←size];exact card_image_of_injective D neginj
  have full : D+B=univ := by
    apply eq_univ_of_forall
    intro t
    let T:=(D ×ˢ D).filter (fun v => p • v.1-v.2= -t)
    have nz : T.Nonempty := by
      by_contra empty
      have zero:=not_nonempty_iff_eq_empty.mp empty
      have h:=cross_mod p D perfect size divide (-t)
      change (T.card:ZMod p)=1 at h
      simp [zero] at h
    obtain ⟨⟨a,b⟩,hab⟩:=nz
    obtain ⟨h,eq⟩:=mem_filter.mp hab
    obtain ⟨ha,hb⟩:=mem_product.mp h
    refine mem_add.mpr ⟨b,hb,-(p • a),mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
    change p • a-b= -t at eq
    calc b+ -(p • a) = -(p • a-b) := by abel
         _ = t := by rw [eq,neg_neg]
  rcases blocking_alternative D B perfect size budget full with line|impossible
  · obtain ⟨c,hc⟩:=line
    refine ⟨-c,Eq.symm (eq_of_subset_of_card_le ?_ ?_)⟩
    · intro z hz
      obtain ⟨d,hd,rfl⟩:=mem_image.mp hz
      obtain ⟨a,ha,he⟩:=mem_image.mp (hc d hd)
      refine mem_image.mpr ⟨a,ha,?_⟩
      change -(p • a)=c-d at he
      calc p • a = -(-(p • a)) := (neg_neg _).symm
           _ = d+ -c := by rw [he];abel
    · rw [card_image_of_injective D inj,card_image_of_injective D (add_left_injective (-c))]
  · simp at impossible;omega

#print axioms prime_multiplier

private theorem centroid_motion {q n : ℕ} (D : Finset G) (size : D.card=q+1)
    (order : Fintype.card G=q*(q+1)+1) (divide : n∣q) {t : G}
    (moves : D.image (fun x => n • x)=D.image (fun x => x+t)) :
    n • (-(q • ∑ d∈D,d))= -(q • ∑ d∈D,d)+t := by
  let S:=∑ d∈D,d
  have I:=scalar_injective n divide order
  have sumN : (∑ x∈D.image (fun d => n • d),x)=n • S := by
    rw [sum_image (fun a _ b _ eq => I eq),smul_sum]
  have sumT : (∑ x∈D.image (fun d => d+t),x)=S+(q+1) • t := by
    rw [sum_image (fun a _ b _ eq => add_right_cancel eq),sum_add_distrib,sum_const,size]
  rw [moves,sumT] at sumN
  have plus : (q*(q+1)) • t+t=0 := by
    have h:=card_nsmul_eq_zero (x:=t)
    rwa [order,add_nsmul,one_nsmul] at h
  have comp : q • ((q+1) • t)= -t := by
    rw [←mul_nsmul,Nat.mul_comm (q+1) q]
    exact eq_neg_of_add_eq_zero_left plus
  change n • (-(q • S))= -(q • S)+t
  rw [smul_neg,smul_comm n q,←sumN,smul_add,comp]
  abel

/-- The same canonical translate is fixed by every prime divisor of the plane
order, hence by the plane order itself. -/
theorem normalized_line (D : Finset G) (perfect : Perfect D) {q : ℕ}
    (positive : 0<q) (size : D.card=q+1) :
    let center:= -(q • ∑ d∈D,d)
    ∀ n : ℕ, n∣q → ∀ x∈D.image (fun d => d-center), n • x∈D.image (fun d => d-center) := by
  classical
  let center:= -(q • ∑ d∈D,d)
  let B:=D.image (fun d => d-center)
  change ∀ n : ℕ, n∣q → ∀ x∈B,n • x∈B
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h;simp at h;omega
  | one => simp
  | prime p prime =>
    intro divide x hx
    let _ : Fact p.Prime:=⟨prime⟩
    obtain ⟨t,translates⟩:=prime_multiplier p D perfect positive size divide
    have moves:=centroid_motion D size (order_formula D perfect size) divide translates
    change p • center=center+t at moves
    obtain ⟨d,hd,rfl⟩:=mem_image.mp hx
    have mem : p • d∈D.image (fun a => p • a):=mem_image_of_mem _ hd
    rw [translates] at mem
    obtain ⟨a,ha,eq⟩:=mem_image.mp mem
    refine mem_image.mpr ⟨a,ha,?_⟩
    rw [smul_sub,moves,←eq];abel
  | mul a b ih jh =>
    intro divide x hx
    have h₁:=ih ((dvd_mul_right a b).trans divide) x hx
    have h₂:=jh ((dvd_mul_left b a).trans divide) _ h₁
    simpa only [mul_nsmul] using h₂

#print axioms normalized_line

omit [DecidableEq G] in
private theorem orbit_sum {q : ℕ} (order : Fintype.card G=q*(q+1)+1) (x : G) :
    x+q • x+q • (q • x)=0 := by
  have h:=card_nsmul_eq_zero (x:=x)
  rw [order,show q*(q+1)+1=1+q+q*q by ring,add_nsmul,add_nsmul,one_nsmul,mul_nsmul] at h
  exact h

omit [DecidableEq G] in
private theorem orbit_three {q : ℕ} (order : Fintype.card G=q*(q+1)+1) (x : G) :
    q • (q • (q • x))=x := by
  have s:=orbit_sum order x
  have t:=orbit_sum order (q • x)
  apply add_left_cancel (a:=q • x+q • (q • x))
  rw [t]
  calc 0 = x+q • x+q • (q • x) := s.symm
       _ = q • x+q • (q • x)+x := by abel

open Green33ReflectedLayers (paths walk)

omit [Fintype G] in
private theorem paths_pair {D : Finset G} (sid : IsSidon (D : Set G)) {a b : G}
    (ha : a∈D) (hb : b∈D) :
    paths D 2 (a+b)=if a=b then 1 else 2 := by
  classical
  have one (t : G) : paths D 1 t=if t∈D then 1 else 0 := by
    simp only [paths,walk,sub_eq_zero,sum_ite_eq]
  have filter : (D.filter (fun x => a+b-x∈D))={a,b} := by
    ext x
    constructor
    · intro hx
      obtain ⟨h,j⟩:=mem_filter.mp hx
      rcases sid x h a ha (a+b-x) j b hb (by abel) with e|e <;> simp [e.1]
    · intro hx
      rcases mem_insert.mp hx with e|e
      · subst x;simpa [ha] using hb
      · obtain rfl:=mem_singleton.mp e
        simp [ha,hb]
  change (∑ x∈D,paths D 1 (a+b-x))=_
  simp only [one,sum_boole,filter]
  by_cases eq : a=b
  · subst b;simp
  · simp [eq]

omit [Fintype G] in
private theorem shifted_sidon {D : Finset G} (h : IsSidon (D : Set G)) (c : G) :
    IsSidon ((D.image (fun d => d-c)) : Set G) := by
  rintro v hv w hw z hz t ht eq
  obtain ⟨a,ha,rfl⟩:=mem_image.mp hv
  obtain ⟨b,hb,rfl⟩:=mem_image.mp hw
  obtain ⟨x,hx,rfl⟩:=mem_image.mp hz
  obtain ⟨y,hy,rfl⟩:=mem_image.mp ht
  have cancel : a+x=b+y := by
    apply add_right_cancel (b:=-c-c)
    calc a+x+(-c-c) = (a-c)+(x-c) := by abel
         _ = _ := eq
         _ = b+y+(-c-c) := by abel
  rcases h a ha b hb x hx y hy cancel with u|u
  · exact Or.inl ⟨by rw [u.1],by rw [u.2]⟩
  · exact Or.inr ⟨by rw [u.1],by rw [u.2]⟩

private theorem peak_sum {q : ℕ} (B : Finset G) (sid : IsSidon (B : Set G))
    (order : Fintype.card G=q*(q+1)+1) (stable : ∀ x∈B, q • x∈B) :
    paths B 3 0=2*(B.card:ℝ)-((B.filter (fun x => q • x=x)).card:ℝ) := by
  classical
  have inj:=scalar_injective q (dvd_refl q) order
  have each (x : G) (hx : x∈B) : paths B 2 (0-x)=2-if q • x=x then 1 else 0 := by
    let y:=q • x
    let z:=q • y
    have pair:=paths_pair sid (stable x hx) (stable y (stable x hx))
    have eq : 0-x=y+z := by
      rw [zero_sub]
      exact neg_eq_of_add_eq_zero_left ((by abel : y+z+x=x+y+z).trans (orbit_sum order x))
    have same : y=z ↔ q • x=x := by
      change q • x=q • (q • x) ↔ q • x=x
      constructor
      · intro e;exact (inj e).symm
      · intro e;exact (congrArg (fun a : G => q • a) e).symm
    change paths B 2 (y+z)=if y=z then 1 else 2 at pair
    rw [eq,pair]
    by_cases h : q • x=x
    · rw [if_pos h,if_pos (same.mpr h)];norm_num
    · rw [if_neg h,if_neg (mt same.mp h)];norm_num
  change (∑ x∈B,paths B 2 (0-x))=_
  rw [sum_congr rfl each,sum_sub_distrib,sum_const,sum_boole,nsmul_eq_mul,mul_comm]


private theorem fixed_capacity {q : ℕ} (order : Fintype.card G=q*(q+1)+1) (B : Finset G) :
    (B.filter (fun x => q • x=x)).card ≤ (if q%3=1 then 3 else 1) := by
  classical
  let T : AddSubgroup G:=(nsmulAddMonoidHom 3).ker
  let _ : Fact (Nat.Prime 3):=⟨by decide⟩
  have powG : IsPGroup 3 (Multiplicative T) := by
    intro g
    refine ⟨1,?_⟩
    let a : T:=Multiplicative.toAdd g
    change ((3^1:ℕ) • a:T)=0
    apply Subtype.ext
    change (3^1:ℕ) • (a:G)=0
    simpa only [pow_one] using (show 3 • (a:G)=0 from a.property)
  obtain ⟨k,hk⟩:=IsPGroup.iff_card.mp powG
  change Nat.card T=3^k at hk
  have divides:=T.card_addSubgroup_dvd_card
  rw [hk,Nat.card_eq_fintype_card,order] at divides
  have no9 : ¬ 9∣q*(q+1)+1 := by
    rw [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod,Nat.add_mod q 1 9]
    have v : q%9<9:=Nat.mod_lt _ (by decide)
    interval_cases (q%9) <;> decide
  have small : k≤1 := by
    by_contra! e
    exact no9 ((Nat.pow_dvd_pow 3 (show 2≤k by omega)).trans divides)
  let J:=B.filter (fun x => q • x=x)
  have killed (x : J) : 3 • (x:G)=0 := by
    have h:=(mem_filter.mp x.property).2
    have h₃:=orbit_sum order (x:G)
    rw [h,h] at h₃
    simpa only [three_nsmul,add_assoc] using h₃
  let f (x : J) : T:=⟨x,killed x⟩
  have inj : Function.Injective f := by
    intro a b e;exact Subtype.ext (congrArg (fun t : T => (t:G)) e)
  have cap:=Nat.card_le_card_of_injective f inj
  rw [hk,Nat.card_eq_fintype_card,Fintype.card_coe] at cap
  by_cases one : q%3=1
  · rw [if_pos one]
    exact cap.trans (by interval_cases k <;> decide)
  · rw [if_neg one]
    have n3 : ¬3∣q*(q+1)+1 := by
      rw [Nat.dvd_iff_mod_eq_zero,Nat.add_mod,Nat.mul_mod,Nat.add_mod q 1 3]
      have v : q%3<3:=Nat.mod_lt _ (by decide)
      interval_cases (q%3) <;> first | decide | contradiction
    have z : k=0 := by by_contra ne;exact n3 ((Nat.pow_dvd_pow 3 (show 1≤k by omega)).trans divides)
    simpa only [z,pow_zero] using cap

private theorem fixed_number {q : ℕ} (B : Finset G) (size : B.card=q+1)
    (order : Fintype.card G=q*(q+1)+1) (stable : ∀ x∈B,q • x∈B) :
    (B.filter (fun x => q • x=x)).card=(if q%3=0 then 1 else if q%3=1 then 2 else 0) := by
  classical
  let _ : Fact (Nat.Prime 3):=⟨by decide⟩
  let f : Function.End B:=fun x => ⟨q • x.val,stable x x.property⟩
  have cube : f^((3:ℕ)^1)=1 := by
    funext x;apply Subtype.ext
    change q • (q • (q • x.val))=x.val
    exact orbit_three order _
  let J:=B.filter (fun x => q • x=x)
  let e : Function.fixedPoints f ≃ J := {
    toFun := fun a => ⟨(a.val:G),mem_filter.mpr ⟨a.val.property,congrArg (fun t : B => (t:G)) a.property⟩⟩
    invFun := fun a => ⟨⟨a.val,(mem_filter.mp a.property).1⟩,Subtype.ext (mem_filter.mp a.property).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have h:=Equiv.Perm.card_fixedPoints_modEq cube
  rw [Fintype.card_congr e,Fintype.card_coe,Fintype.card_coe,size] at h
  change (q+1)%3=J.card%3 at h
  have cap:=fixed_capacity order B
  change J.card≤(if q%3=1 then 3 else 1) at cap
  change J.card=_
  by_cases one : q%3=1
  · rw [if_pos one] at cap
    rw [if_neg (by omega : ¬q%3=0),if_pos one]
    omega
  · rw [if_neg one] at cap ⊢
    split <;> omega

/-- At three times the canonical centroid the ordered three-sum count is
`2(q+1)−f`, where `f` is 1, 2 or 0 according as `q` is 0, 1 or 2 modulo
three. This holds for every abelian planar difference set of positive order. -/
theorem centroid_peak (D : Finset G) (perfect : Perfect D) {q : ℕ}
    (positive : 0<q) (size : D.card=q+1) :
    paths D 3 ((3:ℕ) • (-(q • ∑ d∈D,d)))=
      2*((q:ℝ)+1)-(if q%3=0 then 1 else if q%3=1 then 2 else 0) := by
  classical
  let c:= -(q • ∑ d∈D,d)
  let B:=D.image (fun d => d-c)
  have order:=order_formula D perfect size
  have sb : B.card=q+1 := (card_image_of_injective D (fun _ _ eq => sub_left_injective eq)).trans size
  have stable : ∀ x∈B,q • x∈B:=normalized_line D perfect positive size q (dvd_refl q)
  have fixed:=fixed_number B sb order stable
  have paths0:=peak_sum B (shifted_sidon perfect.sidon c) order stable
  have shift:=Green33ReflectedLayers.paths_affine D (AddEquiv.refl G) (-c) 3 ((3:ℕ) • c)
  change paths (D.image (fun a => a+ -c)) 3 ((3:ℕ) • c+3 • (-c))=paths D 3 ((3:ℕ) • c) at shift
  simp only [smul_neg,add_neg_cancel,←sub_eq_add_neg] at shift
  change paths B 3 0=paths D 3 ((3:ℕ) • c) at shift
  change paths D 3 ((3:ℕ) • c)=_
  rw [←shift,paths0,fixed,sb,Nat.cast_add,Nat.cast_one]
  split_ifs <;> norm_num

#print axioms centroid_peak

open Green33SingerAllCharacteristics Green33SingerKloosterman Green33PrimeSingerIncidence Green33PrimeSingerBasisGap

/-- Over an odd field of order at least ten thousand the centroid gives the unique
global maximum of ordered triple counts for a cubic Singer line. -/
theorem singer_unique_peak_field {F : Type*} [Field F] [Fintype F] [DecidableEq F] (odd : ringChar F≠2) {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra F K] (h : Fintype.card K=(Fintype.card F)^3)
    (L : K→ₗ[F] F) (onto : Function.Surjective L) (big : 10000≤(Fintype.card F)) :
    let D:=labels h L
    let z:=(3:ℕ) • (-((Fintype.card F) • ∑ d∈D,d))
    ∀ t≠z, paths D 3 t<paths D 3 z := by
  classical
  let D:=labels h L
  let z:=(3:ℕ) • (-((Fintype.card F) • ∑ d∈D,d))
  change ∀ t≠z,paths D 3 t<paths D 3 z
  have hd : Perfect D:=perfect_labels h L onto
  have size : D.card=(Fintype.card F)+1 := by change (labels h L).card=_;rw [labels,card_map,(cubic_parameters L onto h).1]
  have eq:=centroid_peak D hd (by omega : 0<(Fintype.card F)) size
  change paths D 3 z=_ at eq
  have peak : 2*((Fintype.card F):ℝ)≤paths D 3 z := by rw [eq];split_ifs <;> linarith
  have large : 100≤(Fintype.card F).sqrt:=Nat.le_sqrt.mpr big
  have margin : 80*((Fintype.card F).sqrt+1)+10<(Fintype.card F) := by
    nlinarith only [Nat.sqrt_le (Fintype.card F),Nat.mul_le_mul_right (Fintype.card F).sqrt large,large]
  have marginR : ((Fintype.card F):ℝ)+80*(((Fintype.card F).sqrt:ℝ)+1)+10<2*(Fintype.card F) := by
    have real : 80*(((Fintype.card F).sqrt:ℝ)+1)+10<((Fintype.card F):ℝ) := by exact_mod_cast margin
    linarith
  obtain ⟨S⟩:=singer_map h L onto
  obtain ⟨w,hw⟩:=Green33PrimeSingerCounts.triple_upper_field odd D S hd.sidon size h
  have name : z=w := by
    by_contra ne
    exact (not_lt_of_ge peak) ((hw z ne).trans_lt marginR)
  intro t nt
  exact ((hw t (name ▸ nt)).trans_lt marginR).trans_le peak

#print axioms singer_unique_peak_field

/-- For large prime Singer lines the unique maximum three-sum count occurs at
three times the centroid. Its exact value is given by `centroid_peak`. -/
theorem prime_singer_unique_peak {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] (h : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 10000≤p) :
    let D:=labels h L
    let z:=(3:ℕ) • (-(p • ∑ d∈D,d))
    ∀ t≠z, paths D 3 t<paths D 3 z := by
  have odd : ringChar (ZMod p)≠2 := by rw [ringChar.eq (ZMod p) p];omega
  simpa only [ZMod.card] using singer_unique_peak_field odd h L onto (by simpa only [ZMod.card] using big)

#print axioms prime_singer_unique_peak

end Green33PlanarMultipliers
