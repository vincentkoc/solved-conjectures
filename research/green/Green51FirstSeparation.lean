import Green51Hadamard
import Green51SmallWitnesses

/-! # The distinct affine and linear three-space thresholds in dimension ten -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51FirstSeparation
local notation "F" => ZMod 2

variable {G : Type*} [AddCommGroup G] [Module F G]

private theorem affine_of_four (q : Cube 3 → G) (inj : Function.Injective q)
    (plane : ∀ u v,q u+q v+q (u+v)+q 0=0) (S : Finset G) (inside : ∀ s,q s∈S) :
    ∃ W : Submodule F G, Module.finrank F W=3 ∧ ∀ w∈W,q 0+w∈S := by
  let L : Cube 3 →ₗ[F] G := {
    toFun := fun x => q x+q 0
    map_add' := by
      intro u v
      have h : q (u+v)+q 0=q u+q v := by
        apply add_left_cancel (a:=q u+q v)
        rw [←add_assoc,plane,ZModModule.add_self]
      rw [h,add_add_add_comm,ZModModule.add_self,add_zero]
    map_smul' := by
      intro c x
      rcases (show ∀ b:F,b=0 ∨ b=1 from by decide) c with h|h <;>
        simp [h,ZModModule.add_self] }
  have hi : Function.Injective L := fun _ _ eq => inj (add_right_cancel eq)
  refine ⟨L.range,?_,?_⟩
  · simpa [Cube] using L.finrank_range_of_inj hi
  · rintro _ ⟨x,rfl⟩
    simpa [L,add_left_comm,ZModModule.add_self] using inside x

private theorem checked_sixteen (A : Finset (Cube 10)) (size : A.card=16)
    (avoid : ¬∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A) :
    ∃ P : Cube A.card →ₗ[F] F×Cube 10,
      (∀ z, P z=∑ i∈supp z, ((1:F),(A.equivFin.symm i).val)) ∧
      32≤Fintype.card P.ker ∧ ∀ x:P.ker,x≠0 → 8≤(supp x.val).card := by
  have free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ a∈T,a)≠0 :=
    fun T sub sz zero => avoid ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,sz,zero⟩)
  obtain ⟨P,eval,parity,kernel,_⟩ := Green51SparseDimensions.even_pair_columns A free
  refine ⟨P,eval,?_,?_⟩
  · rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
    apply Nat.pow_le_pow_right (by decide : 0<2) (show 5≤_ from ?_)
    have eq := P.finrank_range_add_finrank_ker
    have up := Submodule.finrank_le P.range
    have source : Module.finrank F (Cube A.card)=16 := by simp [Cube,size]
    have target : Module.finrank F (F×Cube 10)=11 := by simp [Module.finrank_prod,Cube]
    rw [source] at eq;rw [target] at up;omega
  · intro x non
    have even := parity x.val x.property
    by_contra! low
    exact non (Subtype.ext (kernel x.val (by omega) x.property))

/-- Every sixteen-point set in ten dimensions that avoids a linear three-space
in its double has zero total sum. -/
theorem sixteen_sum (A : Finset (Cube 10)) (size : A.card=16)
    (avoid : ¬∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A) :
    ∑ a∈A,a=0 := by
  obtain ⟨P,eval,large,distance⟩ := checked_sixteen A size avoid
  obtain ⟨_,allOnes,_⟩ := Green51Hadamard.equality_words (show 0<A.card by omega) P.ker
    (by simpa only [size] using large) (fun x hx => by have h := distance x hx;omega)
  have h := (eval (fun _ => 1)).symm.trans (show P (fun _ => 1)=0 from allOnes)
  have total := congrArg Prod.snd h
  simp only [Prod.snd_sum,Prod.snd_zero] at total
  have support : supp (fun _:Fin A.card => (1:F))=univ := by ext i; simp [supp]
  rw [support] at total
  calc
    _ = ∑ a:A,a.val := (sum_attach A id).symm
    _ = ∑ i:Fin A.card,(A.equivFin.symm i).val := (A.equivFin.symm.sum_comp Subtype.val).symm
    _ = 0 := total

/-- Seventeen labels suffice for a linear three-space. The proof uses the
zero totals of all sixteen-point deletions. -/
theorem seventeen_linear (A : Finset (Cube 10)) (size : 17≤A.card) :
    ∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  by_contra avoid
  obtain ⟨B,sub,card⟩ := exists_subset_card_eq size
  have total (x : Cube 10) (hx : x∈B) : (∑ b∈B,b)=x := by
    have avoid' : ¬∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈B.erase x+B.erase x := by
      rintro ⟨W,d,inside⟩
      have sb := (erase_subset x B).trans sub
      exact avoid ⟨W,d,fun w hw => add_subset_add sb sb (inside w hw)⟩
    have sum := sixteen_sum (B.erase x) (by rw [card_erase_of_mem hx,card]) avoid'
    have eq := sum_erase_add B (fun b => b) hx
    rw [sum,zero_add] at eq
    exact eq.symm
  have small := card_le_one.mpr (fun x hx y hy => (total x hx).symm.trans (total y hy))
  omega

/-- For an extremal set with no linear three-space, every sum of distinct
labels belongs to an affine three-space in its double. -/
theorem affine_through_pair (A : Finset (Cube 10)) (size : A.card=16)
    (linear : ¬∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A)
    {a b : Cube 10} (ha : a∈A) (hb : b∈A) (ne : a≠b) :
    ∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,(a+b)+w∈A+A := by
  classical
  obtain ⟨P,eval,large,distance⟩ := checked_sixteen A size linear
  let i₀ := A.equivFin ⟨a,ha⟩
  let i₁ := A.equivFin ⟨b,hb⟩
  have distinct : i₀≠i₁ := fun eq => ne (congrArg Subtype.val (A.equivFin.injective eq))
  obtain ⟨p,h₀,h₁,count,planes⟩ := Green51Hadamard.pair_partition size P.ker i₀ i₁ large distance
  let block (s : Cube 3) : Cube A.card := fun i => Green51Hadamard.bitAt s (p i)
  have support (s : Cube 3) : supp (block s)=univ.filter fun i => p i=s := by
    ext i;simp [supp,block,Green51Hadamard.bitAt]
  let q (s : Cube 3) := (P (block s)).2
  have image (s : Cube 3) : P (block s)=(0,q s) ∧ q s∈A+A := by
    have two : (supp (block s)).card=2 := (congrArg card (support s)).trans (count s)
    obtain ⟨i,j,ne,eq⟩ := card_eq_two.mp two
    have h := eval (block s)
    rw [eq,sum_pair ne] at h
    have second := congrArg Prod.snd h
    change q s=(A.equivFin.symm i).val+(A.equivFin.symm j).val at second
    refine ⟨Prod.ext ((congrArg Prod.fst h).trans (by rfl)) rfl,?_⟩
    rw [second]
    exact add_mem_add (A.equivFin.symm i).property (A.equivFin.symm j).property
  have injective : Function.Injective q := by
    intro s t eq
    have ker : block s+block t∈P.ker := by
      change P (block s+block t)=0
      rw [map_add,(image s).1,(image t).1,eq,ZModModule.add_self]
    have sub : supp (block s+block t)⊆supp (block s)∪supp (block t) := by
      intro i h
      by_contra! away
      have off := notMem_union.mp away
      have a : block s i=0 := by simpa [supp] using off.1
      have b : block t i=0 := by simpa [supp] using off.2
      simp [supp,a,b] at h
    have low := (card_le_card sub).trans (card_union_le _ _)
    rw [support,support,count,count] at low
    have zero : block s+block t=0 := by
      by_contra ne
      have non : (⟨block s+block t,ker⟩:P.ker)≠0 := fun h => ne (congrArg Subtype.val h)
      have high := distance _ non
      change 8≤(supp (block s+block t)).card at high
      omega
    have same : block s=block t := add_right_cancel (zero.trans (ZModModule.add_self _).symm)
    obtain ⟨i,hi⟩ := card_pos.mp (show 0<(univ.filter fun i => p i=s).card by rw [count];decide)
    have is := (mem_filter.mp hi).2
    have atI := congrFun same i
    by_contra different
    simp [block,Green51Hadamard.bitAt,is,different] at atI
  have target : q 0=a+b := by
    have eq : supp (block 0)={i₀,i₁} := by
      symm
      apply eq_of_subset_of_card_le
      · rw [support,insert_subset_iff,singleton_subset_iff]
        exact ⟨mem_filter.mpr ⟨mem_univ _,h₀⟩,mem_filter.mpr ⟨mem_univ _,h₁⟩⟩
      · rw [support,count,card_pair distinct]
    have h := eval (block 0)
    rw [eq,sum_pair distinct] at h
    simpa only [q,Prod.snd_add,i₀,i₁,Equiv.symm_apply_apply] using congrArg Prod.snd h
  rw [←target]
  apply affine_of_four q injective _ _ (fun s => (image s).2)
  intro u v
  have h : P (block u+block v+block (u+v)+block 0)=0 := planes u v
  exact (show _ from by simpa only [map_add,Prod.snd_add,Prod.snd_zero,q] using congrArg Prod.snd h)

/-- Sixteen labels always force an affine three-space in ten dimensions. -/
theorem sixteen_affine (A : Finset (Cube 10)) (size : A.card=16) :
    ∃ (W : Submodule F (Cube 10)) (a : Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,a+w∈A+A := by
  by_cases linear : ∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A
  · obtain ⟨W,d,hw⟩ := linear
    exact ⟨W,0,d,fun w h => by simpa using hw w h⟩
  have many : 1<A.card := by omega
  obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp many
  obtain ⟨W,d,inside⟩ := affine_through_pair A size linear ha hb ne
  exact ⟨W,a+b,d,inside⟩

private theorem density (A : Finset (Cube 10)) : (A.dens:ℝ)=(A.card:ℝ)/1024 := by
  rw [nnratCast_dens];norm_num [Cube]

private theorem guarantee_lower {α : ℝ} (one : α≤1) (lo : 15/1024<α) :
    3≤Green51.guaranteedMaxCosetDim 10 α := by
  classical
  unfold Green51.guaranteedMaxCosetDim
  apply le_csInf
  · refine ⟨_,univ,?_,rfl⟩;simpa using one
  · rintro _ ⟨A,ha,rfl⟩
    have lt := lo.trans_le ha
    rw [density,div_lt_div_iff_of_pos_right (by norm_num)] at lt
    have enough : 16≤A.card := by exact_mod_cast (show (15:ℝ)<A.card from lt)
    obtain ⟨B,sub,size⟩ := exists_subset_card_eq enough
    obtain ⟨W,a,dim,inside⟩ := sixteen_affine B size
    apply le_csSup
    · refine ⟨Module.finrank F (Cube 10),?_⟩
      rintro _ ⟨S,_,rfl⟩;exact Submodule.finrank_le _
    · refine ⟨AffineSubspace.mk' a W,?_,by rwa [AffineSubspace.direction_mk']⟩
      intro z hz
      have t := inside _ (AffineSubspace.mem_mk'.mp hz)
      apply add_subset_add sub sub
      simpa [vsub_eq_sub] using t

private theorem sparse_witnesses :
    (∃ A : Finset (Cube 10), A.card=15 ∧ maxCosetDim F (Cube 10) ↑(A+A)≤2) ∧
    (∃ A : Finset (Cube 10), A.card=16 ∧ maxCosetDim F (Cube 10) ↑(A+A)≤3) := by
  obtain ⟨A,size,avoid,_⟩ := Green51TenDimensions.sixteen_in_ten
  obtain ⟨B,sub,count⟩ := exists_subset_card_eq (show 15≤A.card by omega)
  have avoidB : ¬∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈B+B := by
    rintro ⟨W,d,hw⟩
    exact avoid ⟨W,d,fun w h => add_subset_add sub sub (hw w h)⟩
  constructor
  · exact ⟨B,count,Green51SmallWitnesses.max_dim_of_avoiding B le_rfl avoidB (by rw [count];decide)⟩
  · exact ⟨A,size,Green51SmallWitnesses.max_dim_of_avoiding A (by decide) avoid (by rw [size];decide)⟩

private theorem guarantee_upper {k d : ℕ} {α : ℝ}
    (ex : ∃ A : Finset (Cube 10), A.card=k ∧ maxCosetDim F (Cube 10) ↑(A+A)≤d)
    (small : α≤k/1024) : Green51.guaranteedMaxCosetDim 10 α≤d := by
  obtain ⟨A,sz,bound⟩ := ex
  have admissible : α≤(A.dens:ℝ) := by rwa [density,sz]
  have le : Green51.guaranteedMaxCosetDim 10 α ≤ maxCosetDim F (Cube 10) ↑(A+A) :=
    csInf_le (OrderBot.bddBelow _) ⟨A,admissible,rfl⟩
  exact le.trans bound

/-- The affine threshold of the original guarantee is sixteen points. -/
theorem three_iff {α : ℝ} (one : α≤1) :
    3≤Green51.guaranteedMaxCosetDim 10 α ↔ 15/1024<α := by
  refine ⟨?_,guarantee_lower one⟩
  intro h
  by_contra! small
  have upper := guarantee_upper sparse_witnesses.1 (by exact_mod_cast small : α≤(15:ℕ)/ (1024:ℝ))
  omega

/-- Between fifteen and sixteen points inclusive of the upper boundary, the
affine guarantee equals three, although a linear three-space can be absent. -/
theorem affine_plateau {α : ℝ} (lo : 15/1024<α) (hi : α≤16/1024) :
    Green51.guaranteedMaxCosetDim 10 α=3 ∧
      ∃ A : Finset (Cube 10), α≤(A.dens:ℝ) ∧
        ¬∃ W : Submodule F (Cube 10), Module.finrank F W=3 ∧ ∀ w∈W,w∈A+A := by
  obtain ⟨A,sz,avoid,_⟩ := Green51TenDimensions.sixteen_in_ten
  refine ⟨le_antisymm (guarantee_upper sparse_witnesses.2 (by simpa using hi))
      (guarantee_lower (by linarith) lo),A,?_,avoid⟩
  simpa [density,sz] using hi

/-- The preceding plateau, when at least three and at most fifteen labels
are required, has guaranteed dimension two. -/
theorem two_plateau {α : ℝ} (lo : 2/1024<α) (hi : α≤15/1024) :
    Green51.guaranteedMaxCosetDim 10 α=2 := by
  apply le_antisymm (guarantee_upper sparse_witnesses.1 (by simpa using hi))
  apply Green51SparseBounds.two_above_two_points (by linarith)
  convert lo using 1; norm_num

end Green51FirstSeparation

#print axioms Green51FirstSeparation.sixteen_sum
#print axioms Green51FirstSeparation.seventeen_linear
#print axioms Green51FirstSeparation.affine_through_pair
#print axioms Green51FirstSeparation.sixteen_affine
#print axioms Green51FirstSeparation.three_iff
#print axioms Green51FirstSeparation.affine_plateau
#print axioms Green51FirstSeparation.two_plateau
