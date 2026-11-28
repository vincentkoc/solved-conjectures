import Green33PlanarMultipliers
/-! Baer cosets in square-order planar difference sets. -/
open Finset Green33PerfectDifferenceCenters Green33TailEnergy
open scoped Pointwise

namespace Green33BaerLayers
variable {G H J : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup H] [Fintype H] [DecidableEq H] [AddCommGroup J] [Fintype J] [DecidableEq J]

omit [Fintype G] in
private theorem unique_difference (D : Finset G) (s : G) :
    diffReps D s=1 ↔ ∃! ab : G×G, ab.1∈D ∧ ab.2∈D ∧ ab.1-ab.2=s := by
  classical
  rw [diffReps,card_eq_one]
  constructor
  · rintro ⟨v,hv⟩
    have mem (u : G×G) : u.1∈D ∧ u.2∈D ∧ u.1-u.2=s ↔ u=v := by
      have w := Finset.ext_iff.mp hv u
      simpa only [mem_filter,mem_product,mem_singleton,and_assoc] using w
    exact ⟨v,(mem _).mpr rfl,fun u hu => (mem _).mp hu⟩
  · rintro ⟨v,hv,unique⟩
    refine ⟨v,?_⟩
    ext u
    simp only [mem_filter,mem_product,mem_singleton,and_assoc]
    exact ⟨unique _,fun e => e ▸ hv⟩

/-- The horizontal coordinates above one quotient element. -/
def row (D : Finset (H×J)) (j : J) : Finset H := univ.filter fun a => (a,j)∈D
omit [AddCommGroup H] [AddCommGroup J] [Fintype J] in
@[simp] private theorem mem_row {D : Finset (H×J)} {j : J} {a : H} :
    a∈row D j ↔ (a,j)∈D := by simp [row]

omit [Fintype H] [Fintype J] in
private theorem fixed_pair (D : Finset (H×J)) (perfect : Perfect D)
    (stable : ∀ z∈D,(z.1,-z.2)∈D) (odd : ∀ j : J,-j=j → j=0)
    {a b : H×J} (ha : a∈D) (hb : b∈D) (eq : a.2=b.2) (ne : a≠b) :
    a.2=0 := by
  have nz : a-b≠0 := sub_ne_zero.mpr ne
  obtain ⟨w,_,only⟩ := (unique_difference D _).mp (perfect (a-b) nz)
  have orig:=only (a,b) ⟨ha,hb,rfl⟩
  let u:H×J:=(a.1,-a.2)
  let v:H×J:=(b.1,-b.2)
  have delta : u-v=a-b := by ext <;> simp [u,v,eq]
  have other:=only (u,v) ⟨stable a ha,stable b hb,delta⟩
  exact odd _ (congrArg (fun z : (H×J)×(H×J) => z.1.2) (other.trans orig.symm))

omit [Fintype J] in
/-- Unique differences place every repeated row coordinate in the fixed subgroup. -/
theorem subplane (D : Finset (H×J)) (perfect : Perfect D)
    (stable : ∀ z∈D,(z.1,-z.2)∈D) (odd : ∀ j : J,-j=j → j=0) :
    Perfect (row D 0) ∧ ∀ j≠0,(row D j).card≤1 := by
  constructor
  · intro s ns
    have nonzero : (s,(0:J))≠0 := fun e => ns (congrArg Prod.fst e)
    obtain ⟨⟨a,b⟩,⟨ha,hb,diff⟩,only⟩ := (unique_difference D _).mp (perfect _ nonzero)
    have eq : a.2=b.2 := sub_eq_zero.mp (congrArg Prod.snd diff)
    have ne : a≠b := fun h => nonzero (diff.symm.trans (sub_eq_zero.mpr h))
    have az:=fixed_pair D perfect stable odd ha hb eq ne
    have bz:=eq.symm.trans az
    apply (unique_difference _ _).mpr
    refine ⟨(a.1,b.1),⟨mem_row.mpr ?_,mem_row.mpr ?_,congrArg Prod.fst diff⟩,?_⟩
    · simpa only [←az,Prod.mk.eta] using ha
    · simpa only [←bz,Prod.mk.eta] using hb
    · rintro ⟨x,y⟩ ⟨hx,hy,he⟩
      have u:=only ((x,0),(y,0)) ⟨mem_row.mp hx,mem_row.mp hy,Prod.ext he (sub_zero _)⟩
      exact congrArg (fun z : (H×J)×(H×J) => (z.1.1,z.2.1)) u
  · intro j nz
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra ne
    have neq : (x,j)≠(y,j) := fun e => ne (congrArg Prod.fst e)
    exact nz (fixed_pair D perfect stable odd (mem_row.mp hx) (mem_row.mp hy) rfl neq)

#print axioms subplane
omit [AddCommGroup H] [AddCommGroup J] in
private theorem sum_rows (D : Finset (H×J)) : ∑ j,(row D j).card=D.card := by
  classical
  calc ∑ j,(row D j).card = ∑ j,∑ a : H, if (a,j)∈D then 1 else 0 := by simp [row]
       _ = ∑ z : H×J, if z∈D then 1 else 0 := (Fintype.sum_prod_type_right (fun z : H×J => if z∈D then (1:ℕ) else 0)).symm
       _ = D.card := by simp

/-- The fixed row has `t + 1` points. Every other row is a singleton. -/
theorem row_sizes (D : Finset (H×J)) (perfect : Perfect D)
    (stable : ∀ z∈D,(z.1,-z.2)∈D) (odd : ∀ j : J,-j=j → j=0)
    {t : ℕ} (pos : 0<t) (size : D.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1) :
    ∀ j : J,(row D j).card=(if j=0 then t else 0)+1 := by
  classical
  obtain ⟨subplane,cap⟩:=subplane D perfect stable odd
  have equation:=parameters (row D 0) subplane
  rw [left] at equation
  push_cast at equation
  have center : (row D 0).card=t+1 := by
    have product : (((row D 0).card:ℝ)-(t+1))*((row D 0).card+t)=0 := by nlinarith
    have nn : (0:ℝ)<(row D 0).card+t := by positivity
    have z:=(mul_eq_zero.mp product).resolve_right nn.ne'
    exact_mod_cast (sub_eq_zero.mp z)
  let limit (j:J):=(if j=0 then t else 0)+1
  have bound (j:J) : (row D j).card≤limit j := by
    by_cases eq:j=0
    · simp [limit,eq,center]
    · simpa [limit,eq] using cap j eq
  have total : (∑ j,limit j)=D.card := by
    simp only [limit,sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,nsmul_eq_mul,mul_one,Nat.cast_id]
    omega
  intro j
  apply (bound j).antisymm
  by_contra! small
  have strict : (∑ j,(row D j).card)<∑ j,limit j := by
    apply sum_lt_sum (fun i _ => bound i)
    exact ⟨j,mem_univ _,small⟩
  rw [sum_rows,total] at strict
  omega

#print axioms row_sizes
omit [Fintype G] in
private theorem shifted_perfect (D : Finset G) (hd : Perfect D) (c : G) :
    Perfect (D.image (fun d => d-c)) := by
  intro x nz
  obtain ⟨⟨a,b⟩,⟨ha,hb,diff⟩,only⟩:=(unique_difference D x).mp (hd x nz)
  apply (unique_difference _ x).mpr
  refine ⟨(a-c,b-c),⟨mem_image_of_mem _ ha,mem_image_of_mem _ hb,?_⟩,?_⟩
  · change a-c-(b-c)=x
    rw [←diff];abel
  · rintro ⟨u,v⟩ ⟨hu,hv,eq⟩
    obtain ⟨i,hi,rfl⟩:=mem_image.mp hu
    obtain ⟨j,hj,rfl⟩:=mem_image.mp hv
    have eq' : i-j=x := by
      change i-c-(j-c)=x at eq
      rw [←eq];abel
    have pair:=only (i,j) ⟨hi,hj,eq'⟩
    exact congrArg (fun z : G×G => (z.1-c,z.2-c)) pair

omit [DecidableEq H] [DecidableEq J] in
private theorem conjugate_scalar {t : ℕ} (pos : 0<t) (h : Fintype.card H=t^2+t+1)
    (j : Fintype.card J+t=t^2+1) (a : H×J) : (t^3) • a=(a.1,-a.2) := by
  obtain ⟨u,eu⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
  have hmul : t^3=u*Fintype.card H+1 := by rw [h,eu,Nat.succ_eq_add_one];ring
  have jmul : t^3+1=(t+1)*Fintype.card J := by nlinarith only [j,congrArg (·*t) j]
  have first : t^3 • a.1=a.1 := by simp only [hmul,add_nsmul,mul_nsmul,card_nsmul_eq_zero,one_nsmul,zero_add]
  have last : t^3 • a.2+a.2=0 := by
    calc _ = (t^3+1) • a.2 := by rw [add_nsmul,one_nsmul]
         _ = 0 := by simp only [jmul,mul_nsmul,card_nsmul_eq_zero]
  exact Prod.ext first (eq_neg_of_add_eq_zero_left last)

omit [DecidableEq J] in
private theorem quotient_double {t : ℕ} (right : Fintype.card J+t=t^2+1) :
    Function.Bijective (fun z : J => z+z) := by
  apply Finite.injective_iff_bijective.mp
  intro a b eq
  have even : 2 • (a-b)=0 := by
    calc 2 • (a-b)=(a+a)-(b+b) := by rw [two_nsmul];abel
         _=0 := sub_eq_zero.mpr eq
  have congr:=congrArg (·%2) right
  have rem : Fintype.card J%2=1 := by
    rw [Nat.add_mod (Fintype.card J) t,Nat.add_mod (t^2) 1,pow_two,Nat.mul_mod t t] at congr
    rcases Nat.mod_two_eq_zero_or_one t with h|h <;> rw [h] at congr <;> omega
  obtain ⟨k,ord⟩:=Nat.odd_iff.mpr rem
  have zero:=card_nsmul_eq_zero (x:=a-b)
  simp only [ord,add_nsmul,mul_nsmul,even,smul_zero,one_nsmul,zero_add] at zero
  exact sub_eq_zero.mp zero

/-- The Hall–Menon multiplier puts every perfect set into Baer coordinates at its centroid. -/
theorem normalized_rows (D : Finset (H×J)) (perfect : Perfect D) {t : ℕ} (positive : 0<t)
    (size : D.card=t^2+1) (left : Fintype.card H=t^2+t+1)
    (right : Fintype.card J+t=t^2+1) :
    let c:= -(t^2 • ∑ d∈D,d)
    let A:=D.image (fun d => d-c)
    Perfect (row A 0) ∧ ∀ j : J,(row A j).card=(if j=0 then t else 0)+1 := by
  classical
  let c:= -(t^2 • ∑ d∈D,d)
  let A:=D.image (fun d => d-c)
  change Perfect (row A 0) ∧ ∀ j : J,(row A j).card=_
  have valid : Perfect A:=shifted_perfect D perfect c
  have sc : A.card=t^2+1 := (card_image_of_injective D (fun _ _ eq => sub_left_injective eq)).trans size
  have closed : ∀ z∈A,t • z∈A := Green33PlanarMultipliers.normalized_line D perfect
    (pow_pos positive 2) size t (by rw [pow_two];exact dvd_mul_right ..)
  have flip (z : H×J) (hz : z∈A) : (z.1,-z.2)∈A := by
    rw [←conjugate_scalar positive left right z,pow_succ,pow_two,mul_nsmul,mul_nsmul]
    exact closed _ (closed _ (closed _ hz))
  have odd (z : J) (fix : -z=z) : z=0 := by
    apply (quotient_double right).injective
    change z+z=(0:J)+0
    calc z+z = (-z)+z := congrArg (·+z) fix.symm
         _ = 0+0 := by simp
  exact ⟨(subplane A valid flip odd).1,row_sizes A valid flip odd positive sc left right⟩

#print axioms normalized_rows
/-- A set supported on the coset with prescribed second coordinate. -/
def layer (B : Finset H) (r : J) : Finset (H×J) := B.image fun b => (b,r)

omit [Fintype J] in
private theorem mixed_row (A : Finset (H×J)) (B : Finset H) (r j : J) :
    row (A+layer B r) j=row A (j-r)+B := by
  ext x
  rw [mem_row]
  constructor
  · intro mem
    obtain ⟨⟨a,k⟩,ak,v,hv,eq⟩:=mem_add.mp mem
    obtain ⟨b,hb,rfl⟩:=mem_image.mp hv
    have first : a+b=x := congrArg Prod.fst eq
    have last : k+r=j := congrArg Prod.snd eq
    exact mem_add.mpr ⟨a,mem_row.mpr (by rwa [←last,add_sub_cancel_right]),b,hb,first⟩
  · intro mem
    obtain ⟨a,ha,b,hb,eq⟩:=mem_add.mp mem
    exact mem_add.mpr ⟨(a,j-r),mem_row.mp ha,(b,r),mem_image_of_mem _ hb,Prod.ext eq (sub_add_cancel ..)⟩

private theorem full_add (E B : Finset H) (large : Fintype.card H<E.card+B.card) : E+B=univ := by
  apply eq_univ_of_forall
  intro x
  by_contra missing
  let R:=B.image (fun b => x-b)
  have sep : Disjoint E R := by
    apply Finset.disjoint_left.mpr
    intro a ha h
    obtain ⟨b,hb,rfl⟩:=mem_image.mp h
    exact missing (mem_add.mpr ⟨x-b,ha,b,hb,sub_add_cancel ..⟩)
  have cap:=card_le_univ (E∪R)
  rw [card_union_of_disjoint sep,show R.card=B.card from card_image_of_injective _ (fun _ _ eq => sub_right_inj.mp eq)] at cap
  omega

omit [Fintype J] in
/-- Mixed sums fill the exceptional coset and omit exactly the deletion budget on every other coset. -/
theorem mixed_profile (A : Finset (H×J)) (B : Finset H) (r : J)
    {t : ℕ} (left : Fintype.card H=t^2+t+1) (size : B.card=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) :
    ∀ j : J,(row (A+layer B r) j).card=(if j=r then t else 0)+(t^2+1) := by
  intro j
  rw [mixed_row]
  by_cases eq:j=r
  · subst j
    simp only [sub_self]
    have large : Fintype.card H<(row A 0).card+B.card := by rw [left,rows,size,if_pos rfl];omega
    rw [full_add _ _ large,card_univ,left];simp;omega
  · rw [if_neg eq,zero_add]
    have singleton : (row A (j-r)).card=1 := by rw [rows,if_neg (sub_ne_zero.mpr eq),zero_add]
    obtain ⟨a,ha⟩:=card_eq_one.mp singleton
    rw [ha,add_comm,card_add_singleton,size]

#print axioms mixed_profile
/-- The mixed parity layer misses exactly `t · (card J - 1)` residues,
regardless of which `t` points the balanced layer deletes from its coset. -/
theorem mixed_holes (A : Finset (H×J)) (B : Finset H) (r : J)
    {t : ℕ} (left : Fintype.card H=t^2+t+1) (size : B.card=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) :
    (A+layer B r)ᶜ.card+t=t*Fintype.card J := by
  have total:=sum_rows (A+layer B r)
  simp_rw [mixed_profile A B r left size rows] at total
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at total
  have m:=card_add_card_compl (A+layer B r)
  rw [Fintype.card_prod,left] at m
  nlinarith only [total,m]

#print axioms mixed_holes
omit [AddCommGroup H] [AddCommGroup J] in
private theorem row_weight (A : Finset (H×J)) (f : J→ℝ) :
    (∑ x∈A,f x.2)=∑ j,(row A j).card*f j := by
  classical
  calc (∑ x∈A,f x.2) = ∑ x : H×J, if x∈A then f x.2 else 0 := by simp
       _ = ∑ j,∑ a:H, if (a,j)∈A then f j else 0 := Fintype.sum_prod_type_right _
       _ = _ := by
         apply sum_congr rfl
         intro j _
         rw [←sum_filter]
         simp [row]

omit [AddCommGroup H] in
private theorem mass_weight (A : Finset (H×J)) {t : ℕ}
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) (f : J→ℝ) :
    (∑ x∈A,f x.2)=(∑ j,f j)+t*f 0 := by
  rw [row_weight]
  simp_rw [rows]
  simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,apply_ite (Nat.cast : ℕ→ℝ),
    Nat.cast_zero,ite_mul,zero_mul,sum_add_distrib,sum_ite_eq',mem_univ,if_true]
  ring

private theorem pair_row {t : ℕ} (A : Finset (H×J))
    (sid : IsSidon (A : Set (H×J))) (size : A.card=t^2+1)
    (right : Fintype.card J+t=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) (c : J) :
    2*(row (A+A) c).card=t^2+1+(t+1)*(row A c).card := by
  classical
  let f (j : J) : ℝ:=if j=c then 1 else 0
  have unit : ∑ j,f j=1 := by simp [f]
  have count (S : Finset (H×J)) : (∑ a∈S,f a.2)=((row S c).card:ℝ) := by
    rw [row_weight]
    simp [f,mul_ite]
  have inside (a : H×J) : (∑ b∈A,f (a.2+b.2))=1+t*f a.2 := by
    have m:=mass_weight A rows (fun j => f (a.2+j))
    have move : (∑ j,f (a.2+j))=1 := (Equiv.sum_comp (Equiv.addLeft a.2) f).trans unit
    simpa only [move,add_zero] using m
  have pairs : (∑ a∈A,∑ b∈A,f (a.2+b.2))=(A.card:ℝ)+t*(row A c).card := by
    simp_rw [inside]
    rw [sum_add_distrib,←mul_sum,count]
    simp
  have twice : (∑ j,f (j+j))=1 := (Equiv.sum_comp (Equiv.ofBijective _ (quotient_double right)) f).trans unit
  have diag:=mass_weight A rows (fun j => f (j+j))
  rw [twice,zero_add] at diag
  have center : 1+(t:ℝ)*f 0=(row A c).card := by
    rw [rows]
    by_cases z:c=0 <;> simp [f,z,eq_comm,add_comm]
  have eq:=Green33ReflectedLayers.sidon_sum_weight sid (fun z => f z.2)
  change 2*(∑ z∈A+A,f z.2)=(∑ a∈A,∑ b∈A,f (a.2+b.2))+∑ a∈A,f (a.2+a.2) at eq
  rw [count,pairs,diag,center,size] at eq
  push_cast at eq
  exact_mod_cast (show 2*((row (A+A) c).card:ℝ)=(t:ℝ)^2+1+(t+1)*(row A c).card by linarith)
/-- The ordinary sumset fills its central Baer coset. Every other coset has
exactly half of its points rounded up. -/
theorem sumset_rows (A : Finset (H×J)) (sid : IsSidon (A : Set (H×J))) {t : ℕ}
    (size : A.card=t^2+1) (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) :
    row (A+A) 0=univ ∧ ∀ j≠0,2*(row (A+A) j).card=Fintype.card H+1 := by
  constructor
  · apply eq_univ_of_card
    have n:=pair_row A sid size right rows 0
    rw [rows,if_pos rfl] at n
    rw [left]
    nlinarith only [n]
  · intro j nz
    have n:=pair_row A sid size right rows j
    rw [rows,if_neg nz,zero_add,mul_one] at n
    omega

#print axioms sumset_rows
omit [Fintype G] in
private theorem mapped_perfect {G' : Type*} [AddCommGroup G'] [DecidableEq G']
    (e : G≃+G') (D : Finset G) (perf : Perfect D) : Perfect (D.image e) := by
  intro z nz
  have nonzero : e.symm z≠0 := fun h => nz (by simpa using congrArg e h)
  obtain ⟨⟨a,b⟩,⟨ha,hb,diff⟩,only⟩:=(unique_difference D _).mp (perf _ nonzero)
  apply (unique_difference _ z).mpr
  refine ⟨(e a,e b),⟨mem_image_of_mem _ ha,mem_image_of_mem _ hb,?_⟩,?_⟩
  · simpa only [map_sub,AddEquiv.apply_symm_apply] using congrArg e diff
  · rintro ⟨x,y⟩ ⟨hx,hy,he⟩
    obtain ⟨u,hu,rfl⟩:=mem_image.mp hx
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hy
    have src : u-v=e.symm z := e.injective (by simpa only [map_sub,AddEquiv.apply_symm_apply] using he)
    exact congrArg (fun ab : G×G => (e ab.1,e ab.2)) (only (u,v) ⟨hu,hv,src⟩)

private theorem baer_coprime (t h j : ℕ) (hl : h=t^2+t+1) (jr : j+t=t^2+1) :
    h.Coprime j := by
  apply Nat.coprime_of_dvd
  intro p prime ph pj
  have twice : p∣2*t := by
    have diff : h=j+2*t := by omega
    rw [diff] at ph
    exact (Nat.dvd_add_right pj).mp ph
  rcases prime.dvd_mul.mp twice with two|pt
  · have same : p=2 := (Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp two
    subst p
    have eq:=congrArg (·%2) jr
    rw [Nat.add_mod j t,Nat.add_mod (t^2) 1,pow_two,Nat.mul_mod t t,Nat.mod_eq_zero_of_dvd pj] at eq
    rcases Nat.mod_two_eq_zero_or_one t with ht|ht <;> rw [ht] at eq <;> omega
  · have q : p∣t^2+1 := jr ▸ dvd_add pj pt
    have one : p∣1 := (Nat.dvd_add_right ((pow_two t).symm ▸ dvd_mul_of_dvd_left pt t)).mp q
    exact prime.not_dvd_one one
/-- Translate by an additive displacement. -/
def shift (g : G) (A : Finset G) := A.image (fun a => g+a)

omit [Fintype G] in
private theorem shift_add (c d : G) (A B : Finset G) :
    shift c A+shift d B=shift (c+d) (A+B) := by
  ext z
  constructor
  · intro hz
    obtain ⟨_,ha,_,hb,rfl⟩:=mem_add.mp hz
    obtain ⟨a,h1,rfl⟩:=mem_image.mp ha
    obtain ⟨b,h2,rfl⟩:=mem_image.mp hb
    exact mem_image.mpr ⟨a+b,add_mem_add h1 h2,by abel⟩
  · intro hz
    obtain ⟨_,hp,rfl⟩:=mem_image.mp hz
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hp
    exact mem_add.mpr ⟨_,mem_image_of_mem _ ha,_,mem_image_of_mem _ hb,by abel⟩

omit [Fintype J] in
private theorem layer_saturates (B : Finset H) (r : J) {t : ℕ}
    (size : B.card=t^2+1) (left : Fintype.card H=t^2+t+1) (d : H×J) :
    shift d (layer B r+layer B r)=layer (univ : Finset H) (d.2+(r+r)) := by
  have full : B+B=univ:=full_add B B (by rw [size,left];nlinarith only [Nat.le_mul_self t])
  ext z
  constructor
  · intro hz
    obtain ⟨_,mem,rfl⟩:=mem_image.mp hz
    obtain ⟨_,ha,_,hb,rfl⟩:=mem_add.mp mem
    obtain ⟨a,_,rfl⟩:=mem_image.mp ha
    obtain ⟨b,_,rfl⟩:=mem_image.mp hb
    exact mem_image.mpr ⟨d.1+(a+b),mem_univ _,rfl⟩
  · intro hz
    obtain ⟨u,_,rfl⟩:=mem_image.mp hz
    have mem : u-d.1∈B+B := full.symm ▸ mem_univ _
    obtain ⟨a,ha,b,hb,hs⟩:=mem_add.mp mem
    exact mem_image.mpr ⟨(a,r)+(b,r),add_mem_add (mem_image_of_mem _ ha) (mem_image_of_mem _ hb),
      Prod.ext (by change d.1+(a+b)=u;rw [hs];abel) rfl⟩

omit [AddCommGroup H] [AddCommGroup J] [Fintype J] in
private theorem filled_row (S : Finset (H×J)) (c : J) :
    (S∪layer univ c).card+(row S c).card=S.card+Fintype.card H := by
  let i : H → H×J := fun a => (a,c)
  have eq : S∩layer univ c=(row S c).image i := by
    ext z
    constructor
    · intro h
      obtain ⟨a,_,rfl⟩:=mem_image.mp (mem_inter.mp h).2
      exact mem_image.mpr ⟨a,mem_row.mpr (mem_inter.mp h).1,rfl⟩
    · intro h
      obtain ⟨a,ha,rfl⟩:=mem_image.mp h
      exact mem_inter.mpr ⟨mem_row.mp ha,mem_image_of_mem _ (mem_univ _)⟩
  have inj : Function.Injective i:=fun _ _ e => congrArg Prod.fst e
  have n:=card_union_add_card_inter S (layer univ c)
  rw [eq,card_image_of_injective _ inj] at n
  have card : (layer (univ : Finset H) c).card=Fintype.card H := (card_image_of_injective _ inj).trans card_univ
  rwa [card] at n

private theorem sidon_card (A : Finset G) (sid : IsSidon (A : Set G)) :
    2*(A+A).card=A.card*(A.card+1) := by
  have eq:=Green33ReflectedLayers.sidon_sum_weight sid (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one] at eq
  exact_mod_cast (show 2*((A+A).card:ℝ)=A.card*(A.card+1) by linarith)

/-- The exact sum of the two parity counts before identifying the cyclic double. -/
theorem product_coverage (A : Finset (H×J)) (B : Finset H) {t : ℕ}
    (sid : IsSidon (A : Set (H×J))) (size : A.card=t^2+1) (bal : B.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) (r : J) (d : H×J) :
    let V:=layer B r
    let n:=(A+V).card+(A+A∪shift d (V+V)).card
    2*n=2*(t+Fintype.card J*(t^2+1))+(t^2+1)*(t^2+2)+
      (if d.2+(r+r)=0 then 0 else t^2+t) := by
  classical
  dsimp only
  rw [layer_saturates B r bal left d]
  have mixed:=sum_rows (A+layer B r)
  simp_rw [mixed_profile A B r left bal rows] at mixed
  simp only [sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at mixed
  have whole:=filled_row (A+A) (d.2+(r+r))
  have counts:=sumset_rows A sid size left right rows
  have pairs:=sidon_card A sid
  rw [size] at pairs
  by_cases hit:d.2+(r+r)=0
  · rw [hit,counts.1,card_univ] at whole
    rw [if_pos hit,hit]
    nlinarith only [whole,pairs,mixed]
  · have extra:=counts.2 _ hit
    rw [if_neg hit]
    nlinarith only [whole,pairs,mixed,extra,left]

#print axioms product_coverage
open Green33SingerBlockingLayers Green33ReflectedLayers

/-- In an index-two split, odd sums come from mixed pairs and even sums come from either layer. -/
theorem split_count {v : ℕ+} (A B : Finset (ZMod v)) :
    (split A B+split A B).card=(A+B).card+(A+A∪shift 1 (B+B)).card := by
  classical
  let f:=doubleHom v
  have two : f 1=1+1 := by simpa [f] using (double_coordinates v 0).2.2
  have shape (C E : Finset (ZMod v)) :
      split C E=shift 0 (C.image f) ∪ shift 1 (E.image f) := by
    simp [split,f,shift,image_image,Function.comp_def]
  have eq : split A B+split A B=split (A+A∪shift 1 (B+B)) (A+B) := by
    rw [shape,union_add,add_union,add_union,shift_add,shift_add,shift_add,shift_add]
    rw [shape]
    simp only [zero_add,add_zero,← Finset.image_add,image_union]
    simp only [shift,image_image,Function.comp_def,zero_add,Finset.image_id',map_add,two]
    rw [add_comm B A]
    ext z
    simp only [mem_union]
    tauto
  rw [eq,split_card,Nat.add_comm]

#print axioms split_count

private def frame {K : Type*} [AddCommGroup K] [DecidableEq K]
    (e : G≃+K) (c : K) (S : Finset G) := S.image fun z => e z-c

omit [Fintype G] [DecidableEq G] in
private theorem frame_card {K : Type*} [AddCommGroup K] [DecidableEq K]
    (e : G≃+K) (c : K) (S : Finset G) : (frame e c S).card=S.card :=
  card_image_of_injective _ (fun _ _ eq => e.injective (sub_left_injective eq))

omit [Fintype G] in
private theorem frame_sum {K : Type*} [AddCommGroup K] [DecidableEq K]
    (e : G≃+K) (c : K) (A B : Finset G) :
    frame e (c+c) (A+B)=frame e c A+frame e c B := by
  ext z
  constructor
  · intro hz
    obtain ⟨_,hab,rfl⟩:=mem_image.mp hz
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hab
    exact mem_add.mpr ⟨_,mem_image_of_mem _ ha,_,mem_image_of_mem _ hb,by
      rw [map_add]; abel⟩
  · intro hz
    obtain ⟨_,ha,_,hb,rfl⟩:=mem_add.mp hz
    obtain ⟨a,hA,rfl⟩:=mem_image.mp ha
    obtain ⟨b,hB,rfl⟩:=mem_image.mp hb
    exact mem_image.mpr ⟨a+b,add_mem_add hA hB,by rw [map_add]; abel⟩

omit [Fintype G] in
private theorem frame_shift {K : Type*} [AddCommGroup K] [DecidableEq K]
    (e : G≃+K) (c : K) (g : G) (A : Finset G) :
    frame e c (shift g A)=shift (e g) (frame e c A) := by
  simp only [frame,shift,image_image,Function.comp_def,map_add,add_sub_assoc]

omit [AddCommGroup H] [AddCommGroup J] [Fintype J] in
private theorem supported_layer (S : Finset (H×J)) (r : J)
    (supported : ∀ z∈S,z.2=r) : S=layer (row S r) r := by
  ext z
  constructor
  · intro hz
    exact mem_image.mpr ⟨z.1,mem_row.mpr (by simpa only [←supported z hz,Prod.mk.eta] using hz),
      Prod.ext rfl (supported z hz).symm⟩
  · intro hz
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hz
    exact mem_row.mp ha

/-- Exact coverage in the cyclic double. The relative coset index is measured
from the centroid of the planar set. -/
theorem cyclic_coverage {v : ℕ+} (e : ZMod v≃+H×J) (D B : Finset (ZMod v))
    {t : ℕ} (pos : 0<t) (perf : Perfect D) (size : D.card=t^2+1) (bal : B.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (s : J) (support : ∀ z∈B,(e z).2=s) :
    let c:= -(t^2 • ∑ z∈D.image e,z)
    let r:=s-c.2
    2*(split D B+split D B).card=2*(t+Fintype.card J*(t^2+1))+(t^2+1)*(t^2+2)+
      (if (e 1).2+(r+r)=0 then 0 else t^2+t) := by
  classical
  let c:= -(t^2 • ∑ z∈D.image e,z)
  let r:=s-c.2
  let A:=frame e c D
  let U:=frame e c B
  change _=_+ (if (e 1).2+(r+r)=0 then 0 else t^2+t)
  have mp:=mapped_perfect e D perf
  have ds : (D.image e).card=t^2+1 := (card_image_of_injective D e.injective).trans size
  have eqA : (D.image e).image (fun d => d-c)=A := by simp [A,frame,image_image,Function.comp_def]
  have pa:=shifted_perfect _ mp c
  rw [eqA] at pa
  have rows:= (normalized_rows _ mp pos ds left right).2
  change ∀ j, (row ((D.image e).image (fun d => d-c)) j).card=_ at rows
  rw [eqA] at rows
  have loc : U=layer (row U r) r := supported_layer U r (by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hz
    change (e x).2-c.2=s-c.2
    rw [support _ hx])
  have bs : (row U r).card=t^2+1 := by
    calc _ = (layer (row U r) r).card :=
           (card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq)).symm
         _ = U.card := congrArg card loc.symm
         _ = _ := (frame_card e c B).trans bal
  have counts:=product_coverage A (row U r) pa.sidon ((frame_card e c D).trans size)
    bs left right rows r (e 1)
  dsimp only at counts
  rw [←loc] at counts
  rw [split_count,←frame_card e (c+c) (D+B),←frame_card e (c+c) (D+D∪shift 1 (B+B))]
  have joined (S T : Finset (ZMod v)) : frame e (c+c) (S∪T)=frame e (c+c) S∪frame e (c+c) T :=
    image_union _ _
  rw [joined,frame_shift,frame_sum,frame_sum,frame_sum]
  exact counts

#print axioms cyclic_coverage

/-- The cyclic coordinates for a planar set of square order. -/
def chart (t : ℕ) (h j : ℕ+) (hl : h.val=t^2+t+1) (jr : j.val+t=t^2+1) :
    ZMod (h*j : ℕ+) ≃+ ZMod h × ZMod j :=
  (ZMod.chineseRemainder (baer_coprime t h j hl jr)).toAddEquiv

end Green33BaerLayers
