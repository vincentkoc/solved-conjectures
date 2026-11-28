import Green53ParityThresholds

/-! # Folded cube eigenvalues and the inertia bound for independent sets -/
open Finset Green53Threshold Green53ParityThreshold
open scoped Classical
namespace Green53FoldedCube

/-- The Walsh character associated to a set of coordinates. -/
def character {J : Type*} (S : Finset J) (x : J → F) : ℝ := ∏ j∈S,spin (x j)
private theorem char_add {J : Type*} (S : Finset J) (x y : J → F) :
    character S (x+y)=character S x*character S y := by
  have add (u v : F) : spin (u+v)=spin u*spin v := by
    rw [spin_add]; by_cases h : v=0 <;> simp [spin,h]
  simp only [character,Pi.add_apply,add,prod_mul_distrib]

private theorem char_unit {J : Type*} [DecidableEq J] (S : Finset J) (i : J) :
    character S (Pi.single i 1)=if i∈S then -1 else 1 := by
  classical
  have term (j : J) : spin ((Pi.single i (1:F) : J → F) j)=if j=i then -1 else 1 := by
    by_cases h : j=i
    · subst j; norm_num [spin]
    · simp [spin,h]
  simp only [character,term]
  exact Finset.prod_ite_eq' S i (fun _ => (-1:ℝ))

theorem folded_character {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) (x : J → F) :
    (∑ i,character S (x+Pi.single i 1)) + character S (x+fun _ => 1) =
      ((Fintype.card J:ℝ)-2*S.card+(-1:ℝ)^S.card)*character S x := by
  classical
  have point (i : J) : character S (Pi.single i 1)=(1:ℝ)-(if i∈S then 2 else 0) := by
    rw [char_unit]; by_cases hi : i∈S <;> norm_num [hi]
  have ones : character S (fun _ => 1) = (-1:ℝ)^S.card := by norm_num [character,spin]
  simp only [char_add,←mul_sum,point,sum_sub_distrib,sum_ite_mem,univ_inter,ones]
  simp; ring
private theorem diagonal_sum {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I]
    (w : I → X → ℝ) (n : ℝ)
    (orth : ∀ i j, (∑ x,w i x*w j x)=if i=j then n else 0)
    (a b : I → ℝ) :
    (∑ x,(∑ i,a i*w i x)*(∑ j,b j*w j x))=n*∑ i,a i*b i := by
  classical
  calc
    _ = ∑ x,∑ i,∑ j,(a i*b j)*(w i x*w j x) := by
      apply sum_congr rfl; intro x _
      rw [sum_mul]
      apply sum_congr rfl; intro i _; rw [mul_sum]
      apply sum_congr rfl; intro j _; ring
    _ = ∑ i,∑ j,(a i*b j)*(∑ x,w i x*w j x) := by
      rw [sum_comm]
      apply sum_congr rfl; intro i _
      rw [sum_comm]; simp only [mul_sum]
    _ = _ := by simp [orth,mul_ite,mul_comm n,sum_mul]

/-- Independent support misses at least as many coordinates as a positive
orthogonal eigenspace has modes. Scaling the operator gives the negative case. -/
theorem inertia_bound {I X : Type*} [Fintype I] [Fintype X] [DecidableEq I] [DecidableEq X]
    (A : Finset X) (T : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (w : I → X → ℝ)
    (n : ℝ) (hn : 0<n) (eigval : I → ℝ) (pos : ∀ i,0<eigval i)
    (orth : ∀ i j,(∑ x,w i x*w j x)=if i=j then n else 0)
    (eig : ∀ i,T (w i)=eigval i • w i)
    (vanish : ∀ f : X → ℝ,(∀ x∉A,f x=0) → (∑ x,f x*T f x)=0) :
    Fintype.card I≤Aᶜ.card := by
  classical
  let eval : (I → ℝ) →ₗ[ℝ] (↥(Aᶜ : Finset X) → ℝ) := {
    toFun := fun c x => ∑ i,c i*w i x.val
    map_add' := by intro c d; ext x; simp [add_mul,sum_add_distrib]
    map_smul' := by intro r c; ext x; simp [mul_assoc,mul_sum] }
  have inj : Function.Injective eval := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro c hz
    let f := ∑ i,c i • w i
    have fe (x : X) : f x=∑ i,c i*w i x := by simp [f,Finset.sum_apply]
    have vz := vanish f (fun x hx => by
      have h := congrFun hz (⟨x,mem_compl.mpr hx⟩ : ↥(Aᶜ : Finset X))
      simpa only [fe,eval,LinearMap.coe_mk,AddHom.coe_mk,Pi.zero_apply] using h)
    have te (x : X) : T f x=∑ i,(c i*eigval i)*w i x := by
      simp [f,map_sum,map_smul,eig,Finset.sum_apply,mul_assoc]
    simp only [fe,te] at vz
    rw [diagonal_sum w n orth c (fun i => c i*eigval i)] at vz
    have vs := (mul_eq_zero.mp vz).resolve_left hn.ne'
    have nn (i : I) : 0≤c i*(c i*eigval i) := by rw [←mul_assoc]; exact mul_nonneg (mul_self_nonneg _) (pos i).le
    have point := (sum_eq_zero_iff_of_nonneg (fun i _ => nn i)).mp vs
    funext i
    have prod := point i (mem_univ _)
    rcases mul_eq_zero.mp prod with h|h
    · exact h
    · exact (mul_eq_zero.mp h).resolve_right (pos i).ne'))
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using LinearMap.finrank_le_finrank_of_injective (f:=eval) inj

private theorem char_sq {J : Type*} (S : Finset J) (x : J → F) : character S x*character S x=1 := by
  have point (a : F) : spin a*spin a=1 := by by_cases h : a=0 <;> norm_num [spin,h]
  simp [character,←prod_mul_distrib,point]

private theorem orthogonal {J : Type*} [Fintype J] [DecidableEq J] (S T : Finset J) :
    (∑ x : J → F,character S x*character T x)=if S=T then (Fintype.card (J → F):ℝ) else 0 := by
  classical
  by_cases eq : S=T
  · subst T; simp [char_sq]
  · obtain ⟨j,ne⟩ : ∃ j,¬(j∈S ↔ j∈T) := by
      by_contra! h; exact eq (Finset.ext h)
    let g : J → F := Pi.single j 1
    have anti : character S g*character T g= -1 := by
      by_cases a : j∈S <;> by_cases b : j∈T <;> simp_all [g,char_unit]
    let f (x : J → F) := character S x*character T x
    have neg (x : J → F) : f (g+x)= -f x := by
      simp only [f,char_add]; rw [mul_mul_mul_comm,anti,neg_one_mul]
    have e := Equiv.sum_comp (Equiv.addLeft g) f
    change (∑ x,f (g+x))=∑ x,f x at e
    simp_rw [neg,sum_neg_distrib] at e
    rw [if_neg eq]; change (∑ x,f x)=0; linarith

/-- The adjacency eigenvalue of the Walsh character in the folded cube. -/
def foldedValue {J : Type*} [Fintype J] (S : Finset J) : ℝ :=
  (Fintype.card J:ℝ)-2*S.card+(-1:ℝ)^S.card

private noncomputable def adjacency {J : Type*} [Fintype J] [DecidableEq J] (sign : ℝ) :
    ((J → F) → ℝ) →ₗ[ℝ] ((J → F) → ℝ) where
  toFun f x := sign*((∑ i,f (x+Pi.single i 1))+f (x+fun _ => 1))
  map_add' f g := by funext x; simp only [Pi.add_apply,sum_add_distrib]; ring
  map_smul' t f := by funext x; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,←mul_sum]; ring

/-- The size of an independent family in the folded cube is bounded by the
number of eigenvalues outside either open half-line, counted with multiplicity. -/
theorem folded_inertia {J : Type*} [Fintype J] [DecidableEq J] (A : Finset (J → F))
    (edges : ∀ x∈A, (∀ i,x+Pi.single i 1∉A) ∧ x+(fun _ => 1)∉A) (sign : ℝ) :
    ((univ : Finset (Finset J)).filter (fun S => 0<sign*foldedValue S)).card ≤ Aᶜ.card := by
  classical
  let I := (univ : Finset (Finset J)).filter (fun S => 0<sign*foldedValue S)
  have hyp := inertia_bound (I:=I) A (adjacency sign) (fun s => character s.val)
    (Fintype.card (J → F)) (by positivity) (fun s => sign*foldedValue s.val)
    (fun s => (mem_filter.mp s.property).2) (fun s t => by
      simpa only [Subtype.coe_inj] using orthogonal s.val t.val)
    (fun s => by
      funext x
      change sign*((∑ i,character s.val (x+Pi.single i 1))+character s.val (x+fun _ => 1))=_
      rw [folded_character]; change sign*(_*character s.val x)=(_*_)*character s.val x
      rw [mul_assoc]; rfl)
    (fun f outside => sum_eq_zero (fun x _ => by
      by_cases hx : x∈A
      · change f x*(sign*((∑ i,f (x+Pi.single i 1))+f (x+fun _ => 1)))=0
        simp [fun i => outside _ ((edges x hx).1 i),outside _ (edges x hx).2]
      · rw [outside _ hx,zero_mul]))
  simpa only [Fintype.card_coe] using hyp

private theorem spectral_level (k t : ℕ) :
    (0 < (2*(k:ℝ)-2*t+(-1:ℝ)^t)) ↔ t<k ∨ (t=k ∧ Even k) := by
  rcases lt_trichotomy t k with h|rfl|h
  · have diff : (t:ℝ)+1≤k := by exact_mod_cast h
    rcases neg_one_pow_eq_or ℝ t with p|p <;> simp only [p] <;> constructor
    all_goals first | exact fun _ => Or.inl h | intro _; linarith
  · rcases Nat.even_or_odd t with h|h
    · simp [h,h.neg_one_pow]
    · norm_num [h.neg_one_pow,Nat.not_even_iff_odd.mpr h]
  · have diff : (k:ℝ)+1≤t := by exact_mod_cast h
    have neq := ne_of_gt h
    rcases neg_one_pow_eq_or ℝ t with p|p <;> simp [p,not_lt.mpr h.le,neq] <;> linarith

private theorem level_partition {J : Type*} [Fintype J] [DecidableEq J] (k : ℕ)
    (dim : Fintype.card J = 2*k) :
    let low := (univ : Finset (Finset J)).filter (fun S => S.card<k)
    let high := (univ : Finset (Finset J)).filter (fun S => k<S.card)
    low.card = high.card ∧ 2*low.card+(2*k).choose k=2^(2*k) := by
  classical
  let low := (univ : Finset (Finset J)).filter (fun S => S.card<k)
  let high := (univ : Finset (Finset J)).filter (fun S => k<S.card)
  change low.card=high.card ∧ _
  have swap : low.card=high.card := by
    let e : ↥low ≃ ↥high := {
      toFun S := ⟨S.valᶜ, by have h := (mem_filter.mp S.property).2
                             simp only [high,mem_filter,mem_univ,true_and,card_compl,dim]; omega⟩
      invFun S := ⟨S.valᶜ, by have h := (mem_filter.mp S.property).2
                              have top := S.val.card_le_univ
                              rw [dim] at top
                              simp only [low,mem_filter,mem_univ,true_and,card_compl,dim]; omega⟩
      left_inv S := by simp
      right_inv S := by simp }
    simpa only [Fintype.card_coe] using Fintype.card_congr e
  refine ⟨swap, ?_⟩
  let mid := (univ : Finset J).powersetCard k
  have eq : low ∪ mid ∪ high = univ := by
    ext S
    simp [low,mid,high]; omega
  have dis : Disjoint low mid := by
    rw [disjoint_left]; simp [low,mid]; omega
  have dis' : Disjoint (low ∪ mid) high := by
    rw [disjoint_left]; simp [low,mid,high]; omega
  have count := congrArg Finset.card eq
  rw [card_union_of_disjoint dis',card_union_of_disjoint dis] at count
  simp only [mid,card_powersetCard,card_univ,Fintype.card_finset,dim] at count
  change 2*low.card+_=_
  omega

/-- Counting the levels below the middle and their complements leaves exactly
the central binomial level. -/
theorem strict_layers_card {J : Type*} [Fintype J] [DecidableEq J] (k : ℕ)
    (dim : Fintype.card J=2*k) :
    2*((univ : Finset (Finset J)).filter (fun S => S.card<k)).card +
      (2*k).choose k = 2^(2*k) := (level_partition k dim).2

/-- The two collections of levels strictly below and above the middle have equal
size. Either one bounds the size of an independent set in an even-dimensional cube with all antipodes joined. -/
theorem folded_independent_bound {J : Type*} [Fintype J] [DecidableEq J] (k : ℕ)
    (dim : Fintype.card J = 2*k) (A : Finset (J → F))
    (edges : ∀ x∈A, (∀ i,x+Pi.single i 1∉A) ∧ x+(fun _ => 1)∉A) :
    2*A.card + (2*k).choose k ≤ 2^(2*k) := by
  classical
  let low := (univ : Finset (Finset J)).filter (fun S => S.card<k)
  let high := (univ : Finset (Finset J)).filter (fun S => k<S.card)
  have part := level_partition k dim
  change low.card=high.card ∧ 2*low.card+(2*k).choose k=2^(2*k) at part
  have common : Fintype.card (Finset J)=Fintype.card (J → F) := by simp [F,ZMod.card]
  have val (S : Finset J) : foldedValue S=2*(k:ℝ)-2*S.card+(-1:ℝ)^S.card := by
    simp [foldedValue,dim]
  have bound (B : Finset (Finset J)) (sgn : ℝ) (hb : ∀ S∉B,0<sgn*foldedValue S) :
      A.card≤B.card := by
    have sub : Bᶜ ⊆ (univ : Finset (Finset J)).filter (fun S => 0<sgn*foldedValue S) :=
      fun S hs => mem_filter.mpr ⟨mem_univ _,hb S (mem_compl.mp hs)⟩
    have cnt := (card_le_card sub).trans (folded_inertia A edges sgn)
    rw [card_compl,card_compl,common] at cnt
    have ha := A.card_le_univ
    have hb' := B.card_le_univ
    omega
  by_cases even : Even k
  · have b := bound high 1 (by
      intro S hs
      have h : S.card≤k := by simpa [high] using hs
      rw [one_mul,val,spectral_level]; rcases lt_or_eq_of_le h with h|h
      · exact Or.inl h
      · exact Or.inr ⟨h,even⟩)
    omega
  · have b := bound low (-1) (by
      intro S hs
      have h : k≤S.card := by simpa [low] using hs
      rw [val]; rcases eq_or_lt_of_le h with he|hlt
      · rw [←he,(Nat.not_even_iff_odd.mp even).neg_one_pow]; linarith
      · have d : (k:ℝ)+1≤S.card := by exact_mod_cast hlt
        rcases neg_one_pow_eq_or ℝ S.card with hp|hp <;> rw [hp] <;> linarith)
    omega

end Green53FoldedCube
#print axioms Green53FoldedCube.folded_character
#print axioms Green53FoldedCube.inertia_bound
#print axioms Green53FoldedCube.folded_inertia
#print axioms Green53FoldedCube.folded_independent_bound
#print axioms Green53FoldedCube.strict_layers_card
