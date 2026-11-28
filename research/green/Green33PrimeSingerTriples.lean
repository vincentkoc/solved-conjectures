import Green33SingerCubicFibers
import Green33PrimeSingerBasisGap
import Mathlib.FieldTheory.Finite.GaloisField

/-! Three-term representations on a projective Singer line over a prime field. -/

open Polynomial Finset Green33SingerCubicFibers Green33PrimeSingerIncidence
open Green33ReflectedLayers (paths walk doubleHom overlap)
open scoped Polynomial Pointwise IntermediateField

namespace Green33PrimeSingerTriples

private theorem degree_three {F K : Type*} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {θ : K} (rank : Module.finrank F K=3)
    (ns : θ∉Set.range (algebraMap F K)) : (minpoly F θ).natDegree=3 := by
  have hi : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have one : Module.finrank F F⟮θ⟯ ≠ 1 := fun e =>
    ns (IntermediateField.mem_bot.mp (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp e))
  have div : Module.finrank F F⟮θ⟯ ∣ 3 :=
    ⟨Module.finrank F⟮θ⟯ K,rank.symm.trans (Module.finrank_mul_finrank F F⟮θ⟯ K).symm⟩
  rw [←IntermediateField.adjoin.finrank hi]
  exact ((by decide : Nat.Prime 3).eq_one_or_self_of_dvd _ div).resolve_left one

private noncomputable def low {F : Type*} [Field F] (a : Fin 3→F) : F[X] := by classical exact ofFn 3 a

private theorem span_quadratics {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype F] [Fintype K] (θ : K) (card : Fintype.card K=(Fintype.card F)^3)
    (degree : (minpoly F θ).natDegree=3) (z : K) :
    ∃ a b c : F, algebraMap F K a*θ^2+algebraMap F K b*θ+algebraMap F K c=z := by
  classical
  let values (w : Fin 3→F) := aeval θ (low w)
  have inj : Function.Injective values := by
    intro u v eq
    have div : minpoly F θ∣low u-low v := minpoly.dvd F θ (by rw [map_sub];exact sub_eq_zero.mpr eq)
    have zero : low u-low v=0 := by
      by_contra nz
      have cap := natDegree_le_of_dvd div nz
      have bound := natDegree_sub_le (low u) (low v)
      have du : (low u).natDegree<3 := ofFn_natDegree_lt (by decide) u
      have dv : (low v).natDegree<3 := ofFn_natDegree_lt (by decide) v
      omega
    have same := sub_eq_zero.mp zero
    funext i
    have co := congrArg (fun P : F[X] => P.coeff i.val) same
    simpa only [low,ofFn_coeff_eq_val_of_lt _ i.isLt] using co
  have bij := (Fintype.bijective_iff_injective_and_card values).mpr ⟨inj,by simp [card]⟩
  obtain ⟨w,eq⟩ := bij.2 z
  refine ⟨w 2,w 1,w 0,?_⟩
  have h : low w=C (w 2)*X^2+C (w 1)*X+C (w 0) := by
    rw [(low w).as_sum_range_C_mul_X_pow' (n:=3) (ofFn_natDegree_lt (by decide) w)]
    simp [low,sum_range_succ,ofFn_coeff_eq_val_of_lt,add_comm];ring
  change aeval θ (low w)=z at eq
  simpa only [h,map_add,map_mul,map_pow,aeval_X,aeval_C] using eq

private theorem path_nonnegative {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (D : Finset G) (n : ℕ) (c : G) : 0≤paths D n c := by
  induction n generalizing c with
  | zero => simp only [paths];split <;> norm_num
  | succ n ih => exact sum_nonneg fun x _ => ih (c-x)

private theorem paths_three {G F : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Fintype F] [DecidableEq F] (D : Finset G) (c : G) (e : F ↪ G)
    (inside : ∀ x, e x∈D) (S : F→Finset F)
    (triple : ∀ x y, y∈S x → c-e x-e y∈D) :
    (∑ x, ((S x).card:ℝ))≤paths D 3 c := by
  classical
  have one (t : G) : paths D 1 t=if t∈D then 1 else 0 := by
    simp only [paths,walk,sub_eq_zero,sum_ite_eq]
  have lower (x : F) : ((S x).card:ℝ)≤paths D 2 (c-e x) := by
    have sub : (S x).map e ⊆ D := by
      intro z hz
      obtain ⟨t,_,rfl⟩ := mem_map.mp hz
      exact inside t
    change _ ≤ ∑ d ∈ D,paths D 1 (c-e x-d)
    calc ((S x).card:ℝ) = ∑ d ∈ (S x).map e, paths D 1 (c-e x-d) := by
           rw [sum_map]
           simp only [one]
           rw [sum_congr rfl (fun y hy => if_pos (triple x y hy))]
           simp
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => path_nonnegative ..)
  change _ ≤ ∑ d ∈ D, paths D 2 (c-d)
  calc (∑ x, ((S x).card:ℝ)) ≤ ∑ x, paths D 2 (c-e x) := sum_le_sum fun x _ => lower x
       _ = ∑ d ∈ univ.map e, paths D 2 (c-d) := (sum_map univ e (fun d => paths D 2 (c-d))).symm
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
         intro d hd
         obtain ⟨x,_,rfl⟩ := mem_map.mp hd
         exact inside x) (fun d _ _ => path_nonnegative ..)

private theorem cubic_poles {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
    (θ : K) (deg : (minpoly F θ).natDegree=3) :
    ∃ i j k : F, ∃ s t : K, s≠t ∧ θ+s+t= -algebraMap F K i ∧
      θ*s+θ*t+s*t=algebraMap F K j ∧ θ*s*t= -algebraMap F K k ∧
      (∀ x : F, x^3+i*x^2+j*x+k≠0) ∧
      θ^3+algebraMap F K i*θ^2+algebraMap F K j*θ+algebraMap F K k=0 := by
  classical
  let φ := algebraMap F K
  let m := minpoly F θ
  have hi : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  have mon : m.Monic := minpoly.monic hi
  have c3 : m.coeff 3=1 := by change m.natDegree=3 at deg;rw [← deg];exact mon
  have shape : m=X^3+C (m.coeff 2)*X^2+C (m.coeff 1)*X+C (m.coeff 0) := by
    conv_lhs => rw [m.as_sum_range_C_mul_X_pow' (n:=4) (by change m.natDegree=3 at deg;omega)]
    simp [sum_range_succ,c3];ring
  let M := m.map φ
  have nm : M.Monic := mon.map φ
  have split : M.Splits := Normal.splits inferInstance θ
  have card : M.roots.card=3 := split.natDegree_eq_card_roots.symm.trans ((natDegree_map φ).trans deg)
  have sep : M.Separable := ((PerfectField.separable_iff_squarefree.mpr (minpoly.irreducible hi).squarefree).map)
  have root : M.eval θ=0 := by simpa [M,φ,m,eval_map,aeval_def] using minpoly.aeval F θ
  have mem : θ∈M.roots := (mem_roots nm.ne_zero).mpr root
  have erase : (M.roots.erase θ).card=2 := by rw [Multiset.card_erase_of_mem mem,card];rfl
  obtain ⟨s,t,es⟩ := Multiset.card_eq_two.mp erase
  have rr : M.roots=θ ::ₘ s ::ₘ {t} := (Multiset.cons_erase mem).symm.trans (by rw [es];rfl)
  have st : s≠t := by have n := nodup_roots sep;rw [rr] at n;simpa using (Multiset.nodup_cons.mp (Multiset.nodup_cons.mp n).2).1
  have fact : M=(X-C θ)*(X-C s)*(X-C t) := by
    rw [split.eq_prod_roots_of_monic nm,rr];simp;ring
  have target : φ (m.coeff 0)= -θ*s*t ∧ φ (m.coeff 1)=θ*s+θ*t+s*t ∧
      φ (m.coeff 2)= -(θ+s+t) := by
    have eq : M=X^3+C (φ (m.coeff 2))*X^2+C (φ (m.coeff 1))*X+C (φ (m.coeff 0)) := by
      change m.map φ=_
      conv_lhs => rw [shape]
      simp
    rw [eq] at fact
    have poly : (X-C θ)*(X-C s)*(X-C t) =
        X^3+C (-(θ+s+t))*X^2+C (θ*s+θ*t+s*t)*X+C (-θ*s*t) := by simp;ring
    rw [poly] at fact
    constructor
    · simpa [coeff_X_pow] using congrArg (fun z : K[X] => z.coeff 0) fact
    constructor
    · have hh := congrArg (fun z : K[X] => z.coeff 1) fact
      simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X] at hh
      norm_num at hh
      exact hh
    · have hh := congrArg (fun z : K[X] => z.coeff 2) fact
      simp only [coeff_add,coeff_C_mul,coeff_X_pow,coeff_C,coeff_X] at hh
      norm_num at hh
      linear_combination hh
  refine ⟨m.coeff 2,m.coeff 1,m.coeff 0,s,t,st,by rw [target.2.2];simp,target.2.1.symm,
    by rw [target.1];ring,?_,?_⟩
  · intro x zero
    have rx : m.IsRoot x := by change m.eval x=0;conv_lhs => rw [shape];simp [zero]
    have bad : m.natDegree=1 := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root (minpoly.irreducible hi) rx)
    change m.natDegree=3 at deg
    omega
  · have eq := root
    change (m.map φ).eval θ=0 at eq
    conv_lhs at eq => rw [shape]
    simpa [φ] using eq

/-- Uniform lower bound for ordered triple sums on a cubic Singer line over a
prime field. The proof counts only finite parameters in a projective chart. -/
theorem triple_lower {p : ℕ} [Fact p.Prime] {K G : Type*} [Field K] [Fintype K]
    [Algebra (ZMod p) K] [AddCommGroup G] [DecidableEq G] [Fintype G]
    (D : Finset G) (S : SingerMap (ZMod p) K D) (twoPts : 1<D.card)
    (card : Fintype.card K=(Fintype.card (ZMod p))^3) (big : 400≤p) (center : G) :
    (p:ℝ)≤paths D 3 center+80*((p.sqrt:ℝ)+1)+8 := by
  classical
  let φ := algebraMap (ZMod p) K
  have rank : Module.finrank (ZMod p) K=3 := by
    have total := Module.card_eq_pow_finrank (K:=ZMod p) (V:=K)
    exact Nat.pow_right_injective (Fintype.one_lt_card (α:=ZMod p)) (total.symm.trans card)
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp twoPts
  obtain ⟨U,hU⟩ := S.surj u
  obtain ⟨V,hV⟩ := S.surj v
  let θ := (V:K)/(U:K)
  have vu : θ*(U:K)=(V:K) := div_mul_cancel₀ _ U.ne_zero
  have ns : θ∉Set.range φ := by
    rintro ⟨k,e⟩
    have same := (S.same V U).mpr ⟨k,by rw [Algebra.smul_def];change (V:K)=φ k*U;rw [e,vu]⟩
    exact uv (hU.symm.trans (same.symm.trans hV))
  have ud := (S.mem U).mp (hU ▸ hu)
  have vd := (S.mem V).mp (hV ▸ hv)
  let line (x : ZMod p) : Kˣ := Units.mk0 ((U:K)*(θ-φ x))
    (mul_ne_zero U.ne_zero (sub_ne_zero.mpr (fun e => ns ⟨x,e.symm⟩)))
  have embed : Function.Injective (fun x : ZMod p => S.tag (line x)) := by
    intro x y eq
    obtain ⟨k,ke⟩ := (S.same (line x) (line y)).mp eq
    rw [Algebra.smul_def] at ke
    change (U:K)*(θ-φ x)=φ k*((U:K)*(θ-φ y)) at ke
    have rel : θ-φ x=φ k*(θ-φ y) := mul_left_cancel₀ U.ne_zero (by linear_combination ke)
    by_cases unit : k=1
    · apply φ.injective
      rw [unit,map_one,one_mul] at rel
      exact sub_right_inj.mp rel
    · have nk : (1:K)-φ k≠0 := sub_ne_zero.mpr (fun e => unit (φ.injective ((map_one φ).trans e).symm))
      apply False.elim
      apply ns
      refine ⟨(x-k*y)/(1-k),?_⟩
      rw [map_div₀,map_sub,map_mul,map_sub,map_one]
      apply (div_eq_iff nk).mpr
      linear_combination -rel
  let e : ZMod p ↪ G := ⟨_,embed⟩
  have inside (x) : e x∈D := by
    apply (S.mem (line x)).mpr
    change S.form ((U:K)*(θ-φ x))=0
    rw [show (U:K)*(θ-φ x)=(V:K)-x • (U:K) by rw [Algebra.smul_def,←vu];ring,
      map_sub,map_smul,ud,vd,smul_zero,sub_zero]
  obtain ⟨W,wc⟩ := S.surj center
  have degree := degree_three rank ns
  obtain ⟨a,b,c,coeff⟩ := span_quadratics θ card degree ((W:K)/(U:K)^3)
  obtain ⟨i,j,k,s,t,st,one,two,three,irr,root⟩ := cubic_poles θ degree
  let P : Pencil (ZMod p) := ⟨i,j,k,a,b,c⟩
  have value : (P.map φ).quad θ=(W:K)/(U:K)^3 := coeff
  have nz : (P.map φ).quad θ≠0 := value.trans_ne (div_ne_zero W.ne_zero (pow_ne_zero 3 U.ne_zero))
  have count := many_pairs (by rw [rank];decide) P θ s t one two three st nz big
  have label (x y) (hy : y∈fiber P x) : center-e x-e y∈D := by
    have prod := product_identity φ P hy θ root
    let z := P.mate x y
    have group : S.tag (line x*line y*line z)=S.tag W := by
      apply (S.same _ _).mpr
      refine ⟨-(P.cubic x)/(P.quad x),?_⟩
      rw [Algebra.smul_def]
      change ((U:K)*(θ-φ x))*((U:K)*(θ-φ y))*((U:K)*(θ-φ z))=φ _*(W:K)
      have rep : (P.map φ).quad θ*(U:K)^3=(W:K) := (eq_div_iff (pow_ne_zero 3 U.ne_zero)).mp value
      calc _ = ((θ-φ x)*(θ-φ y)*(θ-φ z))*(U:K)^3 := by ring
           _ = _ := by rw [prod,mul_assoc,rep]
    rw [S.mul,S.mul,wc] at group
    have eq : center-e x-e y=e z := by change e x+e y+e z=center at group;rw [←group];abel
    exact eq ▸ inside z
  have lower := paths_three D center e inside (fiber P) label
  have realCount : (p:ℝ)≤(∑ x : ZMod p,((fiber P x).card:ℝ))+80*((p.sqrt:ℝ)+1)+8 := by exact_mod_cast count
  linarith

#print axioms triple_lower

open Green33SingerAllCharacteristics Green33PrimeSingerBasisGap Green33SingerBlockingLayers
open Green33SingerKloosterman (hyperplane cubic_parameters)
open Green33PerfectDifferenceCenters (doubled_count)

/-- Every point of the cyclic cubic Singer group has many ordered representations
as a sum of three hyperplane labels, including non-distinct summands. -/
theorem label_triples {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] (h : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 400≤p)
    (c : ZMod (order (ZMod p))) :
    (p:ℝ)≤paths (labels h L) 3 c+80*((p.sqrt:ℝ)+1)+8 := by
  classical
  have size : (labels h L).card=p+1 := by
    rw [labels,card_map,(cubic_parameters L onto h).1,ZMod.card]
  obtain ⟨geom⟩ := singer_map h L onto
  exact triple_lower (labels h L) geom (by omega) h big c

/-- The reflected cyclic double misses at least a proportion tending to one
eighth, uniformly in its reflection axis. -/
theorem reflected_defect {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] (h : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 400≤p)
    (t : ZMod (order (ZMod p))) :
    p*(p+1)≤4*(reflected h L t+reflected h L t)ᶜ.card+(p+1)*(80*(p.sqrt+1)+16) := by
  classical
  let D := labels h L
  let R := reflected h L t
  let c := 1+t+t
  have size : D.card=p+1 := by rw [show D.card=(hyperplane L).card by simp [D,labels],
    (cubic_parameters L onto h).1,ZMod.card]
  let error : ℝ := 80*((p.sqrt:ℝ)+1)+8
  have each (x : ZMod (order (ZMod p))) : (p:ℝ)-error≤paths D 3 (c-x) := by
    have good := label_triples h L onto big (c-x)
    change (p:ℝ)≤paths D 3 (c-x)+80*((p.sqrt:ℝ)+1)+8 at good
    dsimp [error];linarith
  have four := sum_le_sum (s:=D) (fun x _ => each x)
  rw [sum_const,nsmul_eq_mul,size] at four
  change ((p+1:ℕ):ℝ)*((p:ℝ)-error)≤paths D 4 c at four
  have hd := perfect_labels h L onto
  have inter := (Green33ReflectedLayers.two_walk_overlap hd.sidon c).1
  change paths D 4 c≤4*(overlap D c:ℝ) at inter
  have ne : D.Nonempty := card_pos.mp (by omega)
  have count := doubled_count (m:=positiveOrder (ZMod p)) hd ne t
  change (R+R).card+overlap D c+1=2*(positiveOrder (ZMod p)).val+2*D.card at count
  have total := card_add_card_compl (R+R)
  rw [ZMod.card] at total
  rw [size] at count
  have mass : (R+R)ᶜ.card+2*(p+1)=overlap D c+1 := by omega
  have realMass := congrArg (Nat.cast (R:=ℝ)) mass
  push_cast at realMass four
  dsimp only [error] at four
  change p*(p+1)≤4*(R+R)ᶜ.card+(p+1)*(80*(p.sqrt+1)+16)
  exact_mod_cast (show (p:ℝ)*(p+1)≤4*((R+R)ᶜ.card:ℝ)+(p+1)*(80*((p.sqrt:ℝ)+1)+16)
    by nlinarith only [realMass,inter,four])

/-- Every balanced opposite layer leaves quadratically many holes over large
prime fields. -/
theorem unconditional_holes {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] (h : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 1000000≤p)
    (B : Finset (ZMod (order (ZMod p)))) (sizeB : B.card=p+1) :
    let S := split (v:=positiveOrder (ZMod p)) (labels h L) B
    p^2≤20*(S+S)ᶜ.card := by
  apply holes_of_reflection h L onto (by omega) _ B sizeB
  intro t
  have finite := reflected_defect h L onto (by omega) t
  have large : 1000≤p.sqrt := Nat.le_sqrt.mpr big
  have cost : 8*(80*(p.sqrt+1)+16)≤p := by
    nlinarith only [Nat.sqrt_le p,Nat.mul_le_mul_right p.sqrt large,large]
  nlinarith only [finite,Nat.mul_le_mul_left (p+1) cost,Nat.zero_le p]

/-- No full cyclic basis retaining the even prime Singer line attains Green's
size coefficient, independently of the rest of the basis. -/
theorem unconditional_gap {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] (h : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 1000000≤p)
    (T : Finset (ZMod (2*(positiveOrder (ZMod p)).val)))
    (anchor : (labels h L).image (doubleHom (positiveOrder (ZMod p)))⊆T)
    (full : T+T=univ) :
    40001*p≤20000*T.card ∧ Real.sqrt 2+1/100000≤
      (T.card:ℝ)/Real.sqrt ((2*(positiveOrder (ZMod p)).val:ℕ):ℝ) :=
  gap_of_holes h L onto (by omega) (unconditional_holes h L onto big) T anchor full

#print axioms label_triples
#print axioms reflected_defect
#print axioms unconditional_holes
#print axioms unconditional_gap

/-- Removing any subset of the even line charges its cardinality to the
normalized size of an arbitrary full basis. -/
theorem omitted_points {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] [Algebra (ZMod p) K] (h : Fintype.card K=(Fintype.card (ZMod p))^3)
    (L : K→ₗ[ZMod p] ZMod p) (onto : Function.Surjective L) (big : 1000000≤p)
    (T : Finset (ZMod (2*(positiveOrder (ZMod p)).val))) (full : T+T=univ) :
    let E := (labels h L).image (doubleHom (positiveOrder (ZMod p)))
    40001*p≤20000*((E\T).card+T.card) ∧
      Real.sqrt 2+1/100000≤(((E\T).card+T.card:ℕ):ℝ)/Real.sqrt ((2*(positiveOrder (ZMod p)).val:ℕ):ℝ) := by
  intro E
  have cover : (E∪T)+(E∪T)=univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp (show x∈T+T from full ▸ mem_univ _)
    exact add_mem_add (mem_union_right E ha) (mem_union_right E hb)
  rw [card_sdiff_add_card E T]
  exact unconditional_gap h L onto big (E∪T) subset_union_left cover

#print axioms omitted_points

end Green33PrimeSingerTriples
