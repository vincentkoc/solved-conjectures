import Green51ElevenColumns
import Green51NineteenMoments

/-! # Nineteen labels force an affine three-space in eleven dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51ElevenDimensions
open scoped Classical Pointwise
namespace Green51NineteenLabels
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem spans_off (A : Finset V) (size : A.card=19) (avoid : ¬∃p,FlatAt A p)
    (T : Finset (Fin A.card)) (few : T.card≤3) (S : Submodule F (F×V))
    (hit : ∀i∉T,((1:F),(A.equivFin.symm i).val)∈S) : S=⊤ := by
  let idx (i:Fin A.card) := (A.equivFin.symm i).val
  have inj : Function.Injective idx := Subtype.val_injective.comp A.equivFin.symm.injective
  let B := Tᶜ.image idx
  have sub : B⊆A := by
    intro x hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx; exact (A.equivFin.symm i).property
  have large : 16≤B.card := by
    rw [show B=Tᶜ.image idx from rfl,card_image_of_injective _ inj,card_compl,Fintype.card_fin]
    omega
  have full := Green51ElevenColumns.columns_span B large
    (fun ⟨p,h⟩ => avoid ⟨p,Green51ElevenColumns.flat_mono sub h⟩)
  apply top_unique
  rw [←full,Submodule.span_le]
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  exact hit i (mem_compl.mp hi)

private theorem count_projection {n:ℕ} (P : Cube n →ₗ[F] F×V) (dim : Module.finrank F P.ker=7)
    (T : Finset (Fin n))
    (full : ∀S:Submodule F (F×V), (∀ i∉T,P (Pi.single i 1)∈S) → S=⊤) :
    (univ.filter fun c:P.ker => T⊆supp c.val).card=2^(7-T.card) := by
  classical
  let R : Cube n →ₗ[F] (T→F) := LinearMap.pi fun i:T => LinearMap.proj i.val
  let U := R.domRestrict P.ker
  have complete : Function.Surjective (P.domRestrict R.ker) := by
    apply LinearMap.range_eq_top.mp
    apply full
    intro i hi
    refine ⟨⟨Pi.single i 1,?_⟩,rfl⟩
    apply funext; intro j
    change (Pi.single i (1:F) : Cube n) j.val=0
    apply Pi.single_eq_of_ne
    intro e; exact hi (e ▸ j.property)
  have onto : Function.Surjective U := by
    intro y
    let x : Cube n := fun i => if h:i∈T then y ⟨i,h⟩ else 0
    obtain ⟨z,hz⟩ := complete (P x)
    have eq : P z.val=P x := hz
    have hR : R z.val=0 := z.property
    refine ⟨⟨x-z.val,by change P (x-z.val)=0; rw [map_sub,eq,sub_self]⟩,?_⟩
    change R (x-z.val)=y
    rw [map_sub,hR,sub_zero]
    funext j; change (if h:j.val∈T then y ⟨_,h⟩ else 0)=_
    simp [j.property]
  let v : T→F := fun _ => 1
  have support (c:P.ker) : T⊆supp c.val ↔ U c=v := by
    constructor
    · intro h
      funext i
      exact (show ∀x:F,x≠0 → x=1 from by decide) _ ((mem_filter.mp (h i.property)).2)
    · intro h i hi
      exact mem_filter.mpr ⟨mem_univ _,fun ne =>
        zero_ne_one (ne.symm.trans (congrFun h (⟨i,hi⟩:T)))⟩
  have kerDim := U.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,dim] at kerDim
  have outDim : Module.finrank F (T→F)=T.card := by simp
  rw [outDim] at kerDim
  have cardKernel : Fintype.card U.ker=2^(7-T.card) := by
    rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,show Module.finrank F U.ker=7-T.card by omega]
  let e : {c:P.ker // U c=v} ≃ U.ker := AddMonoidHom.fiberEquivKerOfSurjective
    (f:=U.toAddMonoidHom) onto v
  have count := Fintype.card_congr e
  rw [Fintype.card_subtype] at count
  calc
    _ = (univ.filter fun c:P.ker => U c=v).card := congrArg card (filter_congr fun c _ => support c)
    _ = _ := count.trans cardKernel

private theorem obstruction {n:ℕ} (size:n=19) (C : Submodule F (Cube n))
    (dim : Module.finrank F C=7) (allowed:∀c:C,weight c.val∈allowedWeights)
    (strength:∀T:Finset (Fin n), T.card≤3 →
      (univ.filter fun c:C=>T⊆supp c.val).card=2^(7-T.card)) : False := by
  subst n
  apply code_obstruction C (by rw [Module.card_eq_pow_finrank (K:=F),dim,ZMod.card];decide) allowed
  intro k hk T hT
  have eq := (mem_powersetCard.mp hT).2
  rw [←eq]
  apply strength
  simp only [mem_insert,mem_singleton] at hk
  omega

/-- Every nineteen-element set in eleven binary dimensions has an affine
three-space in its double. -/
theorem nineteen_affine (A : Finset V) (size : A.card=19) : ∃p,FlatAt A p := by
  classical
  by_contra avoid
  have free : ∀ T⊆A, T.card=4 ∨ T.card=6 → (∑ a∈T,a)≠0 :=
    fun T sub sz zero => avoid ⟨0,(flat_zero A).mpr
      ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,sz,zero⟩)⟩
  obtain ⟨P,eval,parity,kernel,_⟩ := Green51SparseDimensions.even_pair_columns A free
  let idx (i:Fin A.card) := (A.equivFin.symm i).val
  have inj : Function.Injective idx := Subtype.val_injective.comp A.equivFin.symm.injective
  have unit (i:Fin A.card) : P (Pi.single i 1)=(1,idx i) := by
    have eq : supp (Pi.single i (1:F))={i} := by
      ext t
      by_cases h:t=i <;> simp [supp,Pi.single_apply,h]
    rw [eval,eq,sum_singleton]
  have full : P.range=⊤ := spans_off A size avoid ∅ (by simp) P.range
    (fun i _ => unit i ▸ LinearMap.mem_range_self P _)
  have dim := P.finrank_range_add_finrank_ker
  rw [full,finrank_top,show Module.finrank F (F×V)=12 by simp [Cube,Module.finrank_prod],
    show Module.finrank F (Cube A.card)=19 by simp [Cube,size]] at dim
  have codeRank : Module.finrank F P.ker=7 := by omega
  apply obstruction size P.ker codeRank
  · intro c
    have even := parity c.val c.property
    have upper := (supp c.val).card_le_univ
    rw [Fintype.card_fin] at upper
    have low : (supp c.val).card=0 ∨ 8≤(supp c.val).card := by
      by_contra! small
      have zero := kernel c.val (by omega) c.property
      simp [zero,supp] at small
    have different : (supp c.val).card≠16 := by
      intro eq
      let B := (supp c.val).image idx
      have sub : B⊆A := by
        intro x hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx; exact (A.equivFin.symm i).property
      have count : B.card=16 := (card_image_of_injective _ inj).trans eq
      have total := congrArg Prod.snd ((eval c.val).symm.trans c.property)
      simp only [Prod.snd_sum,Prod.snd_zero] at total
      have sum : (∑ b∈B,b)=0 := (sum_image inj.injOn).trans total
      obtain ⟨p,flat⟩ := Green51ElevenRelations.affine_of_sixteen_sum B count sum
      exact avoid ⟨p,Green51ElevenColumns.flat_mono sub flat⟩
    simp only [weight,allowedWeights,mem_insert,mem_singleton]
    omega
  · intro T small
    apply count_projection P codeRank T
    intro S hS
    exact spans_off A size avoid T small S (fun i hi => unit i ▸ hS i hi)

end Green51NineteenLabels
#print axioms Green51NineteenLabels.nineteen_affine
