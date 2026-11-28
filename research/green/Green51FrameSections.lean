import Green51GreatestExtension
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Affine hyperplanes and dense subsets of circuit cosets -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- A functional constant on a majority of a periodic set annihilates its periods. -/
theorem kills_periods_of_majority (P : Submodule F G) (C D : Finset G)
    (sub : D ⊆ (P : Set G).toFinset + C)
    (dense : ((P : Set G).toFinset + C).card < 2*D.card)
    (f : G →ₗ[F] F) (b : F) (val : ∀ x ∈ D, f x = b) : ∀ t ∈ P, f t = 0 := by
  classical
  intro t ht
  by_contra ne
  let E := D.map (Equiv.addRight t).toEmbedding
  have dis : Disjoint D E := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨y,hyD,eq⟩ : ∃ y ∈ D, (Equiv.addRight t).toEmbedding y = x := mem_map.mp hy
    subst x
    have contra := val _ hx
    change f (y+t) = b at contra
    rw [map_add,val y hyD] at contra
    exact ne (add_left_cancel (show b+f t=b+0 by simpa using contra))
  have subE : E ⊆ (P : Set G).toFinset + C := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hz
    obtain ⟨p,hp,c,hc,rfl⟩ := mem_add.mp (sub hx)
    exact mem_add.mpr ⟨p+t,Set.mem_toFinset.mpr (P.add_mem (Set.mem_toFinset.mp hp) ht),c,hc,by change p+t+c=p+c+t; abel⟩
  have ct := card_le_card (Finset.union_subset sub subE)
  rw [card_union_of_disjoint dis] at ct
  change D.card+(D.map _).card ≤ _ at ct
  rw [card_map] at ct
  omega

/-- Above half of a circuit construction, nonaffinity means that all circuit cosets are met. -/
theorem majority_nonaffine_iff {C E : Finset G} (m : ShortestOddCircuit E C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (D : Finset G) (sub : D ⊆ (P : Set G).toFinset + C)
    (dense : ((P : Set G).toFinset + C).card < 2*D.card) :
    (¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1) ↔ ∀ c ∈ C, ∃ t ∈ P, t+c ∈ D := by
  classical
  constructor
  · intro nonaff c hc
    by_contra notHit
    obtain ⟨f,ones⟩ := Module.exists_dual_forall_apply_eq_one (independent_erase m hc)
    change ∀ i ∈ C.erase c, f i = 1 at ones
    let V := Submodule.span F (C : Set G)
    let proj := V.subtype.comp (V.projectionOnto P comp.symm)
    apply nonaff
    refine ⟨f.comp proj, ?_⟩
    intro x hx
    obtain ⟨t,ht,i,hi,rfl⟩ := mem_add.mp (sub hx)
    have tP := Set.mem_toFinset.mp ht
    have iV : i ∈ V := Submodule.subset_span hi
    have distinct : i ≠ c := fun eq => notHit ⟨t,tP,eq ▸ hx⟩
    have t0 : proj t = 0 := by
      change ((V.projectionOnto P comp.symm t : V) : G) = 0
      rw [Submodule.projectionOnto_apply_of_mem_right comp.symm tP]; rfl
    have ii : proj i = i := by
      change ((V.projectionOnto P comp.symm i : V) : G) = i
      rw [Submodule.projectionOnto_apply_of_mem_left comp.symm iV]
    change f (proj (t+i)) = 1
    rw [map_add,t0,ii,zero_add,ones i (mem_erase.mpr ⟨distinct,hi⟩)]
  · intro hit ⟨f,val⟩
    have zero := kills_periods_of_majority P C D sub dense f 1 val
    have ones (c : G) (hc : c ∈ C) : f c = 1 := by
      obtain ⟨t,ht,h⟩ := hit c hc
      simpa only [map_add,zero t ht,zero_add] using val _ h
    have eq := congrArg f m.2.2.1
    rw [map_sum,map_zero,sum_eq_card_nsmul (fun c hc => ones c hc),nsmul_eq_mul,mul_one] at eq
    have even := (ZMod.natCast_eq_zero_iff C.card 2).mp eq
    have par := m.2.1
    rw [Nat.odd_iff] at par
    omega

end Green51GirthFrame
#print axioms Green51GirthFrame.kills_periods_of_majority
#print axioms Green51GirthFrame.majority_nonaffine_iff

namespace Green51GirthFrame
open Finset
open scoped Classical
variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

private theorem mem_meet {β : Type*} [Fintype β] [DecidableEq β]
    (T : Finset ι) (f : ι → Finset β) (x : β) :
    x ∈ T.inf f ↔ ∀ i ∈ T, x ∈ f i := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T _ ih => simp [ih]

theorem count_all_parts (U : Finset α) (C : Finset ι) (F : ι → Finset α) (k : ℕ) :
    (((U.powersetCard k).filter fun D => ∀ i ∈ C, ¬Disjoint D (F i)).card : ℤ) =
      ∑ T ∈ C.powerset, (-1 : ℤ)^T.card * ((U \ T.biUnion F).card.choose k : ℕ) := by
  classical
  let Ω := ↥(U.powersetCard k)
  let bad (i : ι) : Finset Ω := univ.filter fun D => Disjoint (D : Finset α) (F i)
  have miss (T : Finset ι) (D : Ω) : D ∈ T.inf bad ↔ (D : Finset α) ⊆ U \ T.biUnion F := by
    rw [mem_meet]
    have inU := (mem_powersetCard.mp D.property).1
    constructor
    · intro h x hx
      refine mem_sdiff.mpr ⟨inU hx,?_⟩
      intro many
      obtain ⟨i,hi,hF⟩ := mem_biUnion.mp many
      exact Finset.disjoint_left.mp (mem_filter.mp (h i hi)).2 hx hF
    · intro h i hi
      apply mem_filter.mpr
      refine ⟨mem_univ _,Finset.disjoint_left.mpr ?_⟩
      intro x hx hF
      exact (mem_sdiff.mp (h hx)).2 (mem_biUnion.mpr ⟨i,hi,hF⟩)
  have hits (D : Ω) : D ∈ C.inf (fun i => (bad i)ᶜ) ↔ ∀ i ∈ C, ¬Disjoint (D : Finset α) (F i) := by
    rw [mem_meet]; simp [bad]
  have left : (C.inf fun i => (bad i)ᶜ).card = ((U.powersetCard k).filter fun D => ∀ i ∈ C, ¬Disjoint D (F i)).card := by
    apply card_bij (fun D _ => D.val)
    · exact fun D h => mem_filter.mpr ⟨D.property,(hits D).mp h⟩
    · exact fun _ _ _ _ eq => Subtype.ext eq
    · intro D h
      obtain ⟨ok,hit⟩ := mem_filter.mp h
      exact ⟨⟨D,ok⟩,(hits ⟨D,ok⟩).mpr hit,rfl⟩
  have each (T : Finset ι) : (T.inf bad).card = ((U \ T.biUnion F).card).choose k := by
    rw [←card_powersetCard]
    apply card_bij (fun D _ => D.val)
    · intro D h
      exact mem_powersetCard.mpr ⟨(miss T D).mp h,(mem_powersetCard.mp D.property).2⟩
    · exact fun _ _ _ _ eq => Subtype.ext eq
    · intro D h
      obtain ⟨inside,sz⟩ := mem_powersetCard.mp h
      have original := mem_powersetCard.mpr ⟨inside.trans sdiff_subset,sz⟩
      exact ⟨⟨D,original⟩,(miss T ⟨D,original⟩).mpr inside,rfl⟩
  rw [←left,inclusion_exclusion_card_inf_compl]
  simp only [each]

end Green51GirthFrame
#print axioms Green51GirthFrame.count_all_parts

namespace Green51GirthFrame
open Finset Green53ParityThreshold
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

theorem count_nonaffine_in_frame {C E : Finset G} (m : ShortestOddCircuit E C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G)))
    (k : ℕ) (dense : ((P : Set G).toFinset+C).card < 2*k) :
    ((((P : Set G).toFinset+C).powersetCard k).filter
      (fun D => ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1)).card =
        ∑ j ∈ range (C.card+1), ((C.card.choose j : ℕ) : ℤ) *
          ((-1 : ℤ)^j * (((C.card-j)*(P : Set G).toFinset.card).choose k : ℕ)) := by
  classical
  let K := (P : Set G).toFinset
  let U := K+C
  let part (i : G) := K.map (Equiv.addRight i).toEmbedding
  have member (x i : G) : x ∈ part i ↔ ∃ t ∈ P, t+i=x := by
    simp only [part,K,Finset.mem_map,Set.mem_toFinset]
    rfl
  have allParts : C.biUnion part = U := by
    ext x
    simp only [mem_biUnion,member,Finset.mem_add,U,K,Set.mem_toFinset]
    constructor
    · rintro ⟨i,hi,t,ht,eq⟩; exact ⟨t,ht,i,hi,eq⟩
    · rintro ⟨t,ht,i,hi,eq⟩; exact ⟨i,hi,t,ht,eq⟩
  have dis : (C : Set G).PairwiseDisjoint part := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro x h1 h2
    obtain ⟨t,ht,e1⟩ := (member _ _).mp h1
    obtain ⟨s,hs,e2⟩ := (member _ _).mp h2
    let V := Submodule.span F (C : Set G)
    let proj := V.subtype.comp (V.projectionOnto P comp.symm)
    have right (z : G) (hz : z ∈ P) : proj z = 0 := by
      change ((V.projectionOnto P comp.symm z : V) : G) = 0
      rw [Submodule.projectionOnto_apply_of_mem_right comp.symm hz]; rfl
    have left (z : G) (hz : z ∈ C) : proj z = z := by
      change ((V.projectionOnto P comp.symm z : V) : G) = z
      rw [Submodule.projectionOnto_apply_of_mem_left comp.symm (show z ∈ V from Submodule.subset_span hz)]
    have same := congrArg proj (e1.trans e2.symm)
    change proj (t+i) = proj (s+j) at same
    rw [map_add,map_add,right t ht,right s hs,left i hi,left j hj,zero_add,zero_add] at same
    exact ne same
  have sizes (T : Finset G) (h : T ⊆ C) : (T.biUnion part).card = T.card*K.card := by
    have small : (T : Set G).PairwiseDisjoint part := by
      intro i hi j hj ne
      exact dis (h hi) (h hj) ne
    rw [card_biUnion small]
    simp [part]
  have outside (T : Finset G) (h : T ⊆ C) : (U \ T.biUnion part).card = (C.card-T.card)*K.card := by
    have incl : T.biUnion part ⊆ U := by
      rw [←allParts]
      intro x hx
      obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hx
      exact mem_biUnion.mpr ⟨i,h hi,hx⟩
    rw [card_sdiff_of_subset incl,sizes _ h,←allParts,sizes _ Subset.rfl,Nat.sub_mul]
  have filtered : ((U.powersetCard k).filter (fun D => ¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x = 1)) =
      (U.powersetCard k).filter (fun D => ∀ i ∈ C, ¬Disjoint D (part i)) := by
    apply Finset.filter_congr
    intro D h
    obtain ⟨sub,card⟩ := mem_powersetCard.mp h
    rw [majority_nonaffine_iff m P comp D sub (by simpa [card] using dense)]
    simp only [Finset.not_disjoint_iff,member]
    constructor
    · intro hit i hi; obtain ⟨t,ht,hD⟩ := hit i hi; exact ⟨t+i,hD,t,ht,rfl⟩
    · intro hit i hi; obtain ⟨x,hD,t,ht,rfl⟩ := hit i hi; exact ⟨t,ht,hD⟩
  change (((U.powersetCard k).filter _).card : ℤ) = _
  rw [filtered]
  trans ∑ T ∈ C.powerset, (-1 : ℤ)^T.card * ((U \ T.biUnion part).card.choose k : ℕ)
  · convert (count_all_parts U C part k) using 1
    congr 2
    ext D
    simp
  trans ∑ T ∈ C.powerset, (-1 : ℤ)^T.card * (((C.card-T.card)*K.card).choose k : ℕ)
  · apply sum_congr rfl
    intro T hT
    rw [outside T (mem_powerset.mp hT)]
  · rw [sum_powerset]
    apply sum_congr rfl
    intro j _
    simpa [K,nsmul_eq_mul] using sum_powersetCard j C (fun x => (-1 : ℤ)^x * (((C.card-x)*K.card).choose k : ℕ))

end Green51GirthFrame
#print axioms Green51GirthFrame.count_nonaffine_in_frame
