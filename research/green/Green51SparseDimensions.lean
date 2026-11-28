import Green50Sharp
/-! # Three-dimensional linear subspaces in binary doubles -/
open Finset
open scoped Classical Pointwise
namespace Green51SparseDimensions
local notation "F" => ZMod 2
variable {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]

private theorem triple_space (S : Finset G) (x y z : G)
    (inside : ∀ t∈({0,x,y,z,x+y,x+z,y+z,x+y+z}:Finset G),t∈S)
    (distinct : x≠0 ∧ y≠0 ∧ z≠0 ∧ x+y≠0 ∧ x+z≠0 ∧ y+z≠0 ∧ x+y+z≠0) :
    ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈S := by
  classical
  let L : (Fin 3 → F) →ₗ[F] G := Fintype.linearCombination F ![x,y,z]
  have eval (v : Fin 3 → F) : L v=v 0 • x+v 1 • y+v 2 • z := by
    simp [L,Fintype.linearCombination_apply,Fin.sum_univ_three]
  have bit (c : F) : c=0 ∨ c=1 := by fin_cases c <;> first | exact Or.inl rfl | exact Or.inr rfl
  obtain ⟨x0,y0,z0,xy0,xz0,yz0,xyz0⟩ := distinct
  have inj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro v hv
    rcases bit (v 0) with h0|h0 <;> rcases bit (v 1) with h1|h1 <;>
      rcases bit (v 2) with h2|h2 <;> simp [eval,h0,h1,h2,x0,y0,z0,xy0,xz0,yz0,xyz0] at hv
    funext j; fin_cases j <;> assumption
  refine ⟨L.range,by rw [L.finrank_range_of_inj inj]; simp,?_⟩
  rintro _ ⟨v,rfl⟩
  apply inside
  rcases bit (v 0) with h0|h0 <;> rcases bit (v 1) with h1|h1 <;> rcases bit (v 2) with h2|h2 <;>
    simp [eval,h0,h1,h2]

/-- Four points whose nonzero sum is also in the double generate a
three-dimensional linear subspace there. -/
theorem quadruple_space (A : Finset G) (a b c d : G)
    (ha : a∈A) (hb : b∈A) (hc : c∈A) (hd : d∈A)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (nz : a+b+c+d≠0) (hs : a+b+c+d∈A+A) :
    ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  have pair (u v : G) : (a+u)+(a+v)=u+v := by rw [add_add_add_comm,ZModModule.add_self,zero_add]
  have triple : (a+b)+(a+c)+(a+d)=a+b+c+d := by rw [pair]; abel
  have nonzero (u v : G) (ne : u≠v) : u+v≠0 := fun h =>
    ne (add_right_cancel (h.trans (ZModModule.add_self v).symm))
  apply triple_space (A+A) (a+b) (a+c) (a+d)
  · intro w hw
    simp only [mem_insert,mem_singleton,pair] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (ZModModule.add_self a) ▸ add_mem_add ha ha
    · exact add_mem_add ha hb
    · exact add_mem_add ha hc
    · exact add_mem_add ha hd
    · exact add_mem_add hb hc
    · exact add_mem_add hb hd
    · exact add_mem_add hc hd
    · simpa only [pair] using (triple ▸ hs : (a+b)+(a+c)+(a+d)∈A+A)
  · rw [triple,pair,pair,pair]
    exact ⟨nonzero _ _ ab,nonzero _ _ ac,nonzero _ _ ad,nonzero _ _ bc,nonzero _ _ bd,nonzero _ _ cd,nz⟩

/-- A zero sum on four distinct labels gives a plane, and a fifth label
completes a three-dimensional linear subspace in the double. -/
private theorem from_four (A T : Finset G) (large : 5≤A.card) (sub : T⊆A)
    (four : T.card=4) (sum : (∑ t∈T,t)=0) :
    ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  classical
  obtain ⟨x,hxA,hxT⟩ : ∃ x∈A,x∉T := by
    by_contra! h
    have le := card_le_card h
    omega
  obtain ⟨a,b,c,d,ab,ac,ad,bc,bd,cd,rfl⟩ := card_eq_four.mp four
  have sites : a∈A ∧ b∈A ∧ c∈A ∧ d∈A := by simpa only [insert_subset_iff,singleton_subset_iff] using sub
  simp only [mem_insert,mem_singleton,not_or] at hxT
  have relation : a+b+c=d := by
    have h : a+b+c+d=0 := by simpa [ab,ac,ad,bc,bd,cd,add_assoc] using sum
    exact add_right_cancel (h.trans (ZModModule.add_self d).symm)
  apply quadruple_space A a b c x sites.1 sites.2.1 sites.2.2.1 hxA ab ac (Ne.symm hxT.1)
    bc (Ne.symm hxT.2.1) (Ne.symm hxT.2.2.1)
  · rw [relation]; intro eq
    exact hxT.2.2.2 (add_right_cancel (b:=d) (by rwa [add_comm x d,ZModModule.add_self]))
  · rw [relation]; exact add_mem_add sites.2.2.2 hxA

private theorem from_six (A T : Finset G) (sub : T⊆A)
    (six : T.card=6) (sum : (∑ t∈T,t)=0) :
    ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  classical
  obtain ⟨U,ut,uc⟩ := exists_subset_card_eq (show 4≤T.card by omega)
  have two : (T\U).card=2 := by rw [card_sdiff_of_subset ut];omega
  obtain ⟨e,f,ef,rest⟩ := card_eq_two.mp two
  have efA : ({e,f}:Finset G)⊆A := by rw [←rest]; exact fun _ h => sub (mem_sdiff.mp h).1
  have pair := sum_sdiff ut (f:=id)
  change (∑ t∈T\U,t)+(∑ t∈U,t)=∑ t∈T,t at pair
  rw [rest,sum_pair ef,sum] at pair
  have take : ∑ t∈U,t=e+f := add_left_cancel (pair.trans (ZModModule.add_self (e+f)).symm)
  obtain ⟨a,b,c,d,ab,ac,ad,bc,bd,cd,rfl⟩ := card_eq_four.mp uc
  have sites : a∈A ∧ b∈A ∧ c∈A ∧ d∈A := by
    simpa only [insert_subset_iff,singleton_subset_iff] using ut.trans sub
  have split : a+b+c+d=e+f := by simpa [ab,ac,ad,bc,bd,cd,add_assoc] using take
  apply quadruple_space A a b c d sites.1 sites.2.1 sites.2.2.1 sites.2.2.2 ab ac ad bc bd cd
  · rw [split]; intro eq; exact ef (add_right_cancel (eq.trans (ZModModule.add_self f).symm))
  · rw [split]; exact add_mem_add (efA (mem_insert_self _ _)) (efA (mem_insert_of_mem (mem_singleton_self _)))

private theorem small_collision (A U V : Finset G) (large : 5≤A.card)
    (ua : U⊆A) (va : V⊆A) (us : U.card=1 ∨ U.card=3) (vs : V.card=1 ∨ V.card=3)
    (different : U≠V) (equal : (∑ u∈U,u)=∑ v∈V,v) :
    ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  classical
  let I := U∩V
  have iu : I⊆U := inter_subset_left
  have iv : I⊆V := inter_subset_right
  let T := (U\I)∪(V\I)
  have dis : Disjoint (U\I) (V\I) := by
    rw [disjoint_left]
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_inter.mpr ⟨(mem_sdiff.mp hx).1,(mem_sdiff.mp hy).1⟩)
  have sub : T⊆A := union_subset (fun _ h => ua (mem_sdiff.mp h).1) (fun _ h => va (mem_sdiff.mp h).1)
  have eq : (∑ x∈U\I,x)=(∑ x∈V\I,x) :=
    add_right_cancel ((sum_sdiff iu (f:=id)).trans (equal.trans (sum_sdiff iv (f:=id)).symm))
  have zero : (∑ x∈T,x)=0 := by dsimp only [T]; rw [sum_union dis,eq,ZModModule.add_self]
  have ct : T.card=(U.card-I.card)+(V.card-I.card) := by
    dsimp only [T]; rw [card_union_of_disjoint dis,card_sdiff_of_subset iu,card_sdiff_of_subset iv]
  have leu := card_le_card iu
  have lev := card_le_card iv
  by_cases four : T.card=4
  · exact from_four A T large sub four zero
  by_cases six : T.card=6
  · exact from_six A T sub six zero
  exfalso
  by_cases two : T.card=2
  · obtain ⟨e,f,ne,h⟩ := card_eq_two.mp two
    rw [h,sum_pair ne] at zero
    exact ne (add_right_cancel (zero.trans (ZModModule.add_self f).symm))
  exact different ((eq_of_subset_of_card_le iu (by omega)).symm.trans (eq_of_subset_of_card_le iv (by omega)))

/-- The four- and six-label obstructions give the binary triple-packing
bound for every double which excludes a three-dimensional linear space. -/
theorem triple_packing [Fintype G] (A : Finset G) (large : 5≤A.card)
    (no : ¬∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A) :
    A.card+A.card.choose 3≤Fintype.card G := by
  classical
  let T := A.powersetCard 1 ∪ A.powersetCard 3
  have member {U : Finset G} (h : U∈T) : U⊆A ∧ (U.card=1 ∨ U.card=3) := by
    rcases mem_union.mp h with b|b
    · exact ⟨(mem_powersetCard.mp b).1,Or.inl (mem_powersetCard.mp b).2⟩
    · exact ⟨(mem_powersetCard.mp b).1,Or.inr (mem_powersetCard.mp b).2⟩
  let f (U : Finset G) := ∑ a∈U,a
  have inj : Set.InjOn f (↑T) := by
    intro U hu V hv eq
    by_contra ne
    exact no (small_collision A U V large (member hu).1 (member hv).1 (member hu).2 (member hv).2 ne eq)
  have card := (T.image f).card_le_univ
  rw [card_image_iff.mpr inj] at card
  have dis : Disjoint (A.powersetCard 1) (A.powersetCard 3) := by
    rw [disjoint_left]; intro U b c
    have h := (mem_powersetCard.mp b).2.symm.trans (mem_powersetCard.mp c).2
    omega
  dsimp only [T] at card
  simpa only [card_union_of_disjoint dis,card_powersetCard,Nat.choose_one_right] using card

open Green50Sharp Green50Downsets

/-- A linear subspace in the image of a ball lifts when every nontrivial
kernel vector has weight greater than three times the radius. -/
theorem sparse_linear_flat {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
    {N r : ℕ} (P : Cube N →ₗ[F] G)
    (hk : ∀ z, (supp z).card≤3*r → P z=0 → z=0)
    (W : Submodule F G) (inside : ∀ w∈W,w∈(ball N r).image P) :
    Module.finrank F W≤r := by
  classical
  have ex (w : W) : ∃ z∈ball N r,P z=w.val := mem_image.mp (inside w w.property)
  choose f hf fp using ex
  have hzero : f 0=0 := hk _ ((mem_filter.mp (hf 0)).2.trans (by omega)) (fp 0)
  have add (a b : W) : f (a+b)=f a+f b := by
    let z := f (a+b)+(f a+f b)
    have small : z∈(3:ℕ) • ball N r := by
      rw [show (3:ℕ)=1+2 by decide,add_nsmul,one_nsmul,two_nsmul]
      exact add_mem_add (hf _) (add_mem_add (hf _) (hf _))
    have ker : P z=0 := by
      simp only [z,map_add,fp,Submodule.coe_add,ZModModule.add_self]
    have eq := hk z (weight_of_mem_sum small) ker
    apply add_right_cancel (b:=f a+f b)
    exact eq.trans (ZModModule.add_self (f a+f b)).symm
  let L : W →ₗ[F] Cube N :=
    { toFun := f
      map_add' := add
      map_smul' := by
        intro c w
        rcases (show ∀ c:F,c=0 ∨ c=1 from by decide) c with h|h <;> simp [h,hzero] }
  have inj : Function.Injective L := fun x y eq => Subtype.ext (by
    simpa only [show ∀ x : W,P (L x)=x.val from fp] using congrArg P eq)
  obtain ⟨y,hy,rank⟩ := max_weight L.range 0
  have mem : y∈L.range := by simpa using hy
  obtain ⟨w,rfl⟩ := mem
  exact (L.finrank_range_of_inj inj).symm.trans_le (rank.trans (mem_filter.mp (hf w)).2)

/-- With all four- and six-point relations excluded, the augmented label
columns give a binary check map of distance at least seven. Every nonzero
pair sum has a two-coordinate representative. -/
theorem even_pair_columns (A : Finset G)
    (free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0) :
    ∃ P : Cube A.card →ₗ[F] F×G,
      (∀ z, P z=∑ i∈supp z, ((1:F),(A.equivFin.symm i).val)) ∧
      (∀ z, P z=0 → 2∣(supp z).card) ∧
      (∀ z, (supp z).card≤6 → P z=0 → z=0) ∧
      ∀ w∈A+A, ∃ z, P z=(0,w) ∧ (supp z).card≤2 ∧ (w≠0 → (supp z).card=2) := by
  classical
  let index : Fin A.card ↪ G :=
    ⟨fun i => (A.equivFin.symm i).val,Subtype.val_injective.comp A.equivFin.symm.injective⟩
  let col (i : Fin A.card) : F×G := (1,index i)
  let P := Fintype.linearCombination F col
  have eval (z : Cube A.card) : P z=∑ i∈supp z,col i := by
    simp only [P,Fintype.linearCombination_apply,supp,sum_filter]
    apply sum_congr rfl
    intro i _
    rcases (show ∀ u:F,u=0 ∨ u=1 from by decide) (z i) with h|h <;> simp [h]
  have parity (z : Cube A.card) (hz : P z=0) : 2∣(supp z).card := by
    rw [eval] at hz
    simpa only [Prod.fst_sum,Prod.fst_zero,col,sum_const,nsmul_eq_mul,mul_one,ZMod.natCast_eq_zero_iff]
      using congrArg Prod.fst hz
  have kernel (z : Cube A.card) (small : (supp z).card≤3*2) (zero : P z=0) : z=0 := by
    have even := parity z zero
    rw [eval] at zero
    let T := (supp z).map index
    have size : T.card=(supp z).card := card_map _
    have ta : T⊆A := by
      intro a ha
      obtain ⟨i,_,rfl⟩ := mem_map.mp ha
      exact (A.equivFin.symm i).property
    have total : ∑ a∈T,a=0 := by
      rw [sum_map]
      simpa only [Prod.snd_sum,col,Prod.snd_zero] using congrArg Prod.snd zero
    by_cases empty : (supp z).card=0
    · funext i
      by_contra! ne
      have mem : i∈supp z := mem_filter.mpr ⟨mem_univ _,ne⟩
      rw [card_eq_zero.mp empty] at mem
      exact notMem_empty i mem
    by_cases two : T.card=2
    · obtain ⟨a,b,ne,h⟩ := card_eq_two.mp two
      rw [h,sum_pair ne] at total
      exact (ne (add_right_cancel (total.trans (ZModModule.add_self b).symm))).elim
    exact (free T ta (by omega) total).elim
  have single (i : Fin A.card) : P (Pi.single i 1)=col i := by
    rw [eval]
    have eq : supp (Pi.single i (1:F))={i} := by
      ext j
      by_cases h : j=i
      · simp [h,supp]
      · simp [h,supp]
    rw [eq,sum_singleton]
  refine ⟨P,eval,parity,kernel,?_⟩
  rintro w hw
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hw
  let i := A.equivFin ⟨a,ha⟩
  let j := A.equivFin ⟨b,hb⟩
  refine ⟨Pi.single i 1+Pi.single j 1,?_,?_⟩
  · rw [map_add,single,single]
    apply Prod.ext
    · rfl
    · simp [col,index,i,j]
  · by_cases eq : i=j
    · have ab : a=b := congrArg Subtype.val (A.equivFin.injective eq)
      simp [eq,ab,ZModModule.add_self,supp]
    · have support : supp (Pi.single i (1:F)+Pi.single j 1)={i,j} := by
        ext l
        by_cases li : l=i <;> by_cases lj : l=j <;> simp [supp,Pi.single_apply,li,lj,eq,Ne.symm eq]
      simp [support,eq]

/-- Forget the column labels while retaining the even distance and pair lifts. -/
theorem even_pair_check (A : Finset G)
    (free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0) :
    ∃ P : Cube A.card →ₗ[F] F×G,
      (∀ z, P z=0 → 2∣(supp z).card) ∧
      (∀ z, (supp z).card≤6 → P z=0 → z=0) ∧
      ∀ w∈A+A, ∃ z, P z=(0,w) ∧ (supp z).card≤2 ∧ (w≠0 → (supp z).card=2) := by
  obtain ⟨P,_,parity,kernel,lifts⟩ := even_pair_columns A free
  exact ⟨P,parity,kernel,lifts⟩

/-- The even check map also gives two-coordinate lifts of every nonzero pair sum. -/
theorem pair_check (A : Finset G)
    (free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0) :
    ∃ P : Cube A.card →ₗ[F] F×G,
      (∀ z, (supp z).card≤6 → P z=0 → z=0) ∧
      ∀ w∈A+A, ∃ z, P z=(0,w) ∧ (supp z).card≤2 ∧ (w≠0 → (supp z).card=2) := by
  obtain ⟨P,_,kernel,lifts⟩ := even_pair_check A free
  exact ⟨P,kernel,lifts⟩

/-- Every linear flat in this double has rank at most two. -/
theorem rank_without_relation (A : Finset G)
    (free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ t∈T,t)≠0)
    (W : Submodule F G) (inside : ∀ x∈W,x∈A+A) : Module.finrank F W≤2 := by
  classical
  obtain ⟨P,kernel,lift⟩ := pair_check A free
  let J := LinearMap.inr F F G
  have inj : Function.Injective J := LinearMap.inr_injective
  have bound := sparse_linear_flat P kernel (W.map J) (by
    rintro _ ⟨w,hw,rfl⟩
    obtain ⟨z,eq,small,_⟩ := lift w (inside w hw)
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,small⟩,eq⟩)
  exact (W.equivMapOfInjective J inj).finrank_eq.trans_le bound

/-- For at least five labels, the double contains a three-dimensional
linear space exactly when four or six distinct labels sum to zero. -/
theorem linear_three_iff (A : Finset G) (large : 5≤A.card) :
    (∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A) ↔
      ∃ T⊆A,(T.card=4 ∨ T.card=6) ∧ (∑ t∈T,t)=0 := by
  constructor
  · rintro ⟨W,dim,inside⟩
    by_contra! free
    have low := rank_without_relation A free W inside
    omega
  · rintro ⟨T,sub,h|h,sum⟩
    · exact from_four A T large sub h sum
    · exact from_six A T sub h sum

end Green51SparseDimensions
#print axioms Green51SparseDimensions.quadruple_space
#print axioms Green51SparseDimensions.triple_packing
#print axioms Green51SparseDimensions.sparse_linear_flat
#print axioms Green51SparseDimensions.even_pair_columns
#print axioms Green51SparseDimensions.even_pair_check
#print axioms Green51SparseDimensions.pair_check
#print axioms Green51SparseDimensions.rank_without_relation
#print axioms Green51SparseDimensions.linear_three_iff
