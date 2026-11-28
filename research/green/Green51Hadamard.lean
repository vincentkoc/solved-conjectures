import Green51SmallDimensions

/-! # Binary codes at the Plotkin bound and saturated affine labels -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51Hadamard
local notation "F" => ZMod 2

private def sign (x : F) : ℤ := if x=0 then 1 else -1
private theorem sign_add (x y : F) : sign (x+y)=sign x*sign y := by decide +revert

private theorem character_sum {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (f : V →ₗ[F] F) : (∑ x:V,sign (f x))=if f=0 then (Fintype.card V:ℤ) else 0 := by
  classical
  by_cases h : f=0
  · simp [h,sign]
  rw [if_neg h]
  obtain ⟨a,ha⟩ : ∃ a,f a≠0 := by
    by_contra! hn
    exact h (LinearMap.ext hn)
  have c : sign (f a) = -1 := if_neg ha
  have shift := Equiv.sum_comp (Equiv.addLeft a) (fun x => sign (f x))
  change (∑ x:V,sign (f (a+x)))=∑ x:V,sign (f x) at shift
  simp only [map_add,sign_add,c,neg_one_mul,sum_neg_distrib] at shift
  omega

private def imbalance {n : ℕ} (x : Cube n) : ℤ := ∑ i,sign (x i)

private theorem imbalance_weight {n : ℕ} (x : Cube n) :
    imbalance x = (n:ℤ)-2*(supp x).card := by
  have term (i : Fin n) : sign (x i) = 1 - (if x i ≠ 0 then (2:ℤ) else 0) := by
    by_cases h : x i=0 <;> simp [sign,h]
  simp_rw [imbalance,term]
  simp [sum_sub_distrib,sum_ite,supp,mul_comm]

private def column {n : ℕ} (C : Submodule F (Cube n)) (i : Fin n) : C →ₗ[F] F :=
  (LinearMap.proj i).comp C.subtype

private theorem moments {n : ℕ} (C : Submodule F (Cube n)) :
    0≤∑ x:C,imbalance x.val ∧
    (n:ℤ)*Fintype.card C≤∑ x:C,(imbalance x.val)^2 := by
  classical
  have pt (i j : Fin n) : (∑ x:C,sign (x.val i)*sign (x.val j))=
      if column C i+column C j=0 then (Fintype.card C:ℤ) else 0 := by
    simpa only [LinearMap.add_apply,sign_add,column,LinearMap.comp_apply,LinearMap.proj_apply,
      Submodule.subtype_apply] using character_sum (column C i+column C j)
  constructor
  · change 0≤∑ x:C,∑ i,sign (x.val i)
    rw [sum_comm]
    apply sum_nonneg
    intro i _
    change 0≤∑ x:C,sign (column C i x)
    rw [character_sum];split <;> positivity
  · have expand (x : C) : (imbalance x.val)^2=∑ i:Fin n,∑ j:Fin n,sign (x.val i)*sign (x.val j) := by
      simp only [imbalance,sq,sum_mul,mul_sum]
      rw [sum_comm]
    simp_rw [expand]
    rw [sum_comm]
    calc
      _ = ∑ i:Fin n,(Fintype.card C:ℤ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro i _
        rw [sum_comm]
        have h := single_le_sum (s:=univ) (f:=fun j:Fin n => ∑ x:C,sign (x.val i)*sign (x.val j))
          (fun j _ => by rw [pt];split <;> positivity) (mem_univ i)
        rw [pt,ZModModule.add_self,if_pos rfl] at h
        exact h

/-- Equality in the binary Plotkin bound at relative distance one half.
Every code of size at least twice its positive length contains the all-one
word. Its remaining nonzero words have exactly half their entries set. -/
theorem equality_words {n : ℕ} (pos : 0<n) (C : Submodule F (Cube n))
    (large : 2*n≤Fintype.card C) (distance : ∀ x:C,x≠0 → n≤2*(supp x.val).card) :
    Fintype.card C=2*n ∧ (fun _ => (1:F))∈C ∧
      ∀ x:C,x≠0 → x.val≠(fun _ => 1) → n=2*(supp x.val).card := by
  classical
  let I (x:C) := imbalance x.val
  let R := (univ : Finset C).erase 0
  have zero : I 0=n := by simp [I,imbalance,sign]
  have bounds (x : C) (non : x≠0) : -(n:ℤ)≤I x ∧ I x≤0 := by
    have d := distance x non
    have u : (supp x.val).card≤n := (supp x.val).card_le_univ.trans_eq (by simp)
    dsimp only [I];rw [imbalance_weight];omega
  have nonneg (x : C) (hx : x∈R) : 0≤ -I x*((n:ℤ)+I x) := by
    have pair := bounds x (mem_erase.mp hx).1
    exact mul_nonneg (by omega) (by omega)
  have m := moments C
  change 0≤∑ x:C,I x ∧ (n:ℤ)*Fintype.card C≤∑ x:C,(I x)^2 at m
  have full (f : C → ℤ) : ∑ x∈R,f x + f 0 = ∑ x:C,f x := sum_erase_add _ _ (mem_univ _)
  have ms := full I
  have msq := full (fun x => (I x)^2)
  rw [zero] at ms msq
  have eq : ∑ x∈R,-I x*((n:ℤ)+I x) = -(n:ℤ)*(∑ x∈R,I x) - ∑ x∈R,(I x)^2 := by
    rw [mul_sum,←sum_sub_distrib];apply sum_congr rfl;intro x _;ring
  have z := sum_nonneg nonneg
  have big : 2*(n:ℤ)≤Fintype.card C := by exact_mod_cast large
  have npos : (0:ℤ)<n := by exact_mod_cast pos
  have upper : (n:ℤ)*(Fintype.card C)≤2*(n:ℤ)^2 := by
    nlinarith [m.1,m.2,mul_nonneg (le_of_lt npos) m.1]
  have size : Fintype.card C=2*n := by
    have up : (Fintype.card C:ℤ)≤2*n := by nlinarith
    exact Nat.le_antisymm (by exact_mod_cast up) large
  have total : ∑ x∈R,-I x*((n:ℤ)+I x)=0 := by
    rw [size] at m
    push_cast at m
    nlinarith [m.1,m.2,mul_nonneg (le_of_lt npos) m.1]
  have alternatives (x : C) (non : x≠0) : I x=0 ∨ I x= -(n:ℤ) := by
    have t := (sum_eq_zero_iff_of_nonneg nonneg).mp total x (mem_erase.mpr ⟨non,mem_univ _⟩)
    rcases mul_eq_zero.mp t with l|r
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have all_of_min (x : C) (h : I x= -(n:ℤ)) : x.val=(fun _ => 1) := by
    change imbalance x.val=_ at h
    rw [imbalance_weight] at h
    have card : (supp x.val).card=n := by omega
    have fullSupp := eq_univ_of_card (s:=supp x.val) (card.trans (Fintype.card_fin n).symm)
    funext i
    have hit : i∈supp x.val := fullSupp ▸ mem_univ _
    exact (show ∀ b:F,b≠0 → b=1 from by decide) _ (mem_filter.mp hit).2
  refine ⟨size,?_,?_⟩
  · by_contra absent
    have vanish (x : C) (hx : x∈R) : I x=0 :=
      (alternatives x (mem_erase.mp hx).1).resolve_right fun h => absent (all_of_min x h ▸ x.property)
    have sums : ∑ x∈R,(I x)^2=0 := sum_eq_zero fun x hx => by rw [vanish x hx];norm_num
    rw [size] at m
    push_cast at m
    nlinarith [m.2]
  · intro x non different
    have h := (alternatives x non).resolve_right fun h => different (all_of_min x h)
    change imbalance x.val=0 at h
    rw [imbalance_weight] at h
    omega

private def dot (a b : Cube 3) : F := ∑ j,a j*b j

def bitAt (u v : Cube 3) : F := if v=u then 1 else 0

private theorem table (p s : Cube 3) :
    (∑ b:Cube 3, sign (dot b p)*sign (dot b s))=if s=p then 8 else 0 := by
  decide +revert +kernel

private theorem planes (u v : Cube 3) :
    ∃ b : Cube 3, ∃ c:F, ∀ s:Cube 3,
      bitAt u s+bitAt v s+bitAt (u+v) s+bitAt 0 s=c+dot b s := by
  decide +revert +kernel

/-- Three independent nonconstant balanced rows give a partition into pairs. -/
private theorem partition_from_rows (C:Submodule F (Cube 16)) (i₀ i₁:Fin 16)
    (L:Cube 3 →ₗ[F] C) (injective:Function.Injective L)
    (vanish₀:∀b,(L b).val i₀=0) (vanish₁:∀b,(L b).val i₁=0)
    (allOnes:(fun _=>1)∈C)
    (balanced:∀x:C,x≠0 → x.val≠(fun _=>1) → 16=2*(supp x.val).card) :
    ∃p:Fin 16→Cube 3,p i₀=0 ∧ p i₁=0 ∧ (∀s,(univ.filter fun i=>p i=s).card=2) ∧
      ∀u v:Cube 3,(fun i=>bitAt u (p i)+bitAt v (p i)+bitAt (u+v) (p i)+bitAt 0 (p i))∈C := by
  let T := C.subtype.comp L
  let p (i:Fin 16) (j:Fin 3) := T (Pi.single j 1) i
  have coord (b:Cube 3) (i:Fin 16) : T b i=dot b (p i) := by
    have expand : ∑ j:Fin 3,b j • Pi.single j (1:F)=b := by
      funext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
      simp [mul_ite]
    conv_lhs => rw [←expand]
    simp [map_sum,Finset.sum_apply,p,dot]
  have rows (b:Cube 3) : (∑ i,sign (dot b (p i)))=if b=0 then 16 else 0 := by
    simp_rw [←coord]
    by_cases zero : b=0
    · simp [zero,sign]
    · have non : L b ≠ 0 := fun h=>zero (injective (h.trans L.map_zero.symm))
      have different : (L b).val≠(fun _=>1) := by
        intro bad
        have h:=vanish₀ b
        simp [bad] at h
      have eq:=balanced _ non different
      rw [if_neg zero]
      change imbalance (L b).val=0
      rw [imbalance_weight];omega
  refine ⟨p,?_,?_,?_,?_⟩
  · funext j;exact vanish₀ (Pi.single j 1)
  · funext j;exact vanish₁ (Pi.single j 1)
  · intro s
    have joint : (∑ i:Fin 16,∑ b:Cube 3,sign (dot b (p i))*sign (dot b s))=16 := by
      rw [sum_comm]
      simp_rw [←sum_mul,rows]
      simp [ite_mul,sign,dot]
    simp_rw [table] at joint
    have h : (∑ i:Fin 16,if s=p i then (8:ℤ) else 0)=
        8*((univ.filter fun i => p i=s).card:ℤ) := by simp [sum_ite,eq_comm,mul_comm]
    omega
  · intro u v
    obtain ⟨b,c,h⟩ := planes u v
    have eq : (fun i => bitAt u (p i)+bitAt v (p i)+bitAt (u+v) (p i)+bitAt 0 (p i))=
        c • (fun _:Fin 16 => (1:F))+T b := by
      funext i
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_one,coord] using h (p i)
    rw [eq]
    exact C.add_mem (C.smul_mem c allOnes) (L b).property

/-- Three independent balanced rows partition the sixteen positions into
eight pairs, with both prescribed positions in the zero fiber. The union of the four pairs in any plane through zero is a
codeword. Repeated points in a degenerate plane cancel in characteristic two. -/
theorem pair_partition {n : ℕ} (length : n=16) (C : Submodule F (Cube n)) (i₀ i₁ : Fin n)
    (large : 32≤Fintype.card C) (distance : ∀ x:C,x≠0 → 8≤(supp x.val).card) :
    ∃ p : Fin n → Cube 3, p i₀=0 ∧ p i₁=0 ∧ (∀ s,(univ.filter fun i => p i=s).card=2) ∧
      ∀ u v : Cube 3, (fun i => bitAt u (p i)+bitAt v (p i)+bitAt (u+v) (p i)+bitAt 0 (p i))∈C := by
  subst n
  obtain ⟨size,allOnes,balanced⟩ := equality_words (by decide : 0<16) C large (fun x hx => by
    have h := distance x hx;omega)
  let l := (column C i₀).prod (column C i₁)
  have rank := l.finrank_range_add_finrank_ker
  have bound := Submodule.finrank_le l.range
  have dim : Module.finrank F C=5 := by
    have count := Module.card_eq_pow_finrank (K:=F) (V:=C)
    rw [ZMod.card,size] at count
    exact (Nat.pow_right_injective (by decide : 2≤2) (show 2^Module.finrank F C=2^5 from count.symm))
  have fits : Module.finrank F (Cube 3)≤Module.finrank F l.ker := by
    have target : Module.finrank F (F×F)=2 := by simp [Module.finrank_prod]
    rw [target] at bound
    rw [dim] at rank
    have low : Module.finrank F (Cube 3)=3 := by simp [Cube]
    rw [low]; omega
  obtain ⟨L,injective⟩ := finrank_le_iff_exists_linearMap.mp fits
  exact partition_from_rows C i₀ i₁ (l.ker.subtype.comp L) (Subtype.val_injective.comp injective)
    (fun b=>congrArg Prod.fst (show l (L b).val=0 from (L b).property))
    (fun b=>congrArg Prod.snd (show l (L b).val=0 from (L b).property)) allOnes balanced

/-- If every common linear shift leaves eight ones in the two rows together,
the rows take opposite values at every paired position. -/
theorem opposite_on_pairs (u v : Cube 3 → F)
    (balanced : ∀ f:Cube 3 →ₗ[F] F,
      (univ.filter (fun z => u z+f z≠0)).card+(univ.filter (fun z => v z+f z≠0)).card=8) :
    ∀ z,u z≠v z := by
  let row (b : Cube 3) : Cube 3 →ₗ[F] F := {
    toFun := dot b
    map_add' := by intro x y;simp [dot,mul_add,sum_add_distrib]
    map_smul' := by intro c x;rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) c with h|h <;> simp [h,dot] }
  have count (u : Cube 3 → F) : (∑ z,sign (u z))=8-2*((univ.filter fun z => u z≠0).card:ℤ) := by
    have pt (z:Cube 3) : sign (u z)=1-(if u z≠0 then (2:ℤ) else 0) := by by_cases h : u z=0 <;> simp [sign,h]
    simp_rw [pt]
    simp [sum_sub_distrib,sum_ite,Cube,mul_comm]
  let t (z:Cube 3) := sign (u z)+sign (v z)
  have coeff (b : Cube 3) : (∑ z,t z * sign (dot b z))=0 := by
    have q := balanced (row b)
    change (univ.filter (fun z => u z+dot b z≠0)).card+(univ.filter (fun z => v z+dot b z≠0)).card=8 at q
    simp only [t,add_mul,←sign_add,sum_add_distrib,count]
    omega
  intro a same
  have invert : (∑ b:Cube 3, (∑ z,t z * sign (dot b z)) * sign (dot b a))=8*t a := by
    simp_rw [sum_mul,mul_assoc]
    rw [sum_comm]
    simp_rw [←mul_sum,table]
    simp [mul_ite,mul_comm]
  simp_rw [coeff,zero_mul,sum_const_zero] at invert
  have cases := (show ∀ x:F,sign x=1 ∨ sign x= -1 from by decide) (v a)
  dsimp only [t] at invert
  rw [same] at invert
  omega


/-- Four independent codewords suffice when the length-sixteen all-one word is available. -/
theorem partition_of_ones {n:ℕ} (length:n=16) (C:Submodule F (Cube n))
    (rank:4≤Module.finrank F C) (ones:(fun _=>1)∈C)
    (distance:∀x:C,x≠0 → 8≤(supp x.val).card) :
    ∃p:Fin n→Cube 3,(∀s,(univ.filter fun i=>p i=s).card=2) ∧
      ∀u v:Cube 3,(fun i=>bitAt u (p i)+bitAt v (p i)+bitAt (u+v) (p i)+bitAt 0 (p i))∈C := by
  subst n
  let l:=column C (0:Fin 16)
  have sum:=l.finrank_range_add_finrank_ker
  have bound:=Submodule.finrank_le l.range
  rw [show Module.finrank F F=1 by simp] at bound
  have fits:Module.finrank F (Cube 3)≤Module.finrank F l.ker := by
    rw [show Module.finrank F (Cube 3)=3 by simp [Cube]]
    omega
  obtain ⟨L,inj⟩:=finrank_le_iff_exists_linearMap.mp fits
  have balanced (x:C) (non:x≠0) (diff:x.val≠(fun _=>1)) : 16=2*(supp x.val).card := by
    let O:C:=⟨_,ones⟩
    have nz:x+O≠0 := by
      intro h
      have e:=add_right_cancel (h.trans (ZModModule.add_self O).symm)
      exact diff (congrArg Subtype.val e)
    have comp:supp (x+O).val=(supp x.val)ᶜ := by
      ext i
      change i∈supp (x.val+(fun _:Fin 16=>(1:F))) ↔ _
      rcases (show ∀a:F,a=0 ∨ a=1 from by decide) (x.val i) with e|e <;>
        simp [supp,e,show (1:F)+1=0 by decide]
    have low:=distance x non
    have high:=distance (x+O) nz
    rw [comp,card_compl,Fintype.card_fin] at high
    have atMost:=(supp x.val).card_le_univ
    rw [Fintype.card_fin] at atMost
    omega
  have vanish (b:Cube 3):(L b).val.val 0=0:=(L b).property
  obtain ⟨p,_,_,h,k⟩:=partition_from_rows C 0 0 (l.ker.subtype.comp L)
    (Subtype.val_injective.comp inj) vanish vanish ones balanced
  exact ⟨p,h,k⟩

/-- The second binary character moment, expressed in support sizes. -/
theorem weight_second_moment {n:ℕ} (C:Submodule F (Cube n)) :
    (n:ℤ)*Fintype.card C≤∑x:C,((n:ℤ)-2*(supp x.val).card)^2 := by
  simpa only [←imbalance_weight] using (moments C).2

end Green51Hadamard
#print axioms Green51Hadamard.partition_of_ones

#print axioms Green51Hadamard.equality_words
#print axioms Green51Hadamard.pair_partition

#print axioms Green51Hadamard.opposite_on_pairs

#print axioms Green51Hadamard.weight_second_moment
