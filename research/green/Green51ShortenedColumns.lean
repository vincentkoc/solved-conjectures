import Green51ShortenedProfiles
import Green51AffineMatchings
import Green51ResidualPacking

/-! # Augmented binary columns for label completion -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open scoped Classical Pointwise
namespace Green51ShortenedColumns
local notation "F" => ZMod 2
local notation "V" => Cube 11

private noncomputable def index (A:Finset V) : Fin A.card ↪ V :=
  ⟨fun i => (A.equivFin.symm i).val,Subtype.val_injective.comp A.equivFin.symm.injective⟩

/-- The set of labels selected by a column vector. -/
noncomputable def selected (A:Finset V) (z:Cube A.card) : Finset V := (supp z).map (index A)

theorem selected_card (A:Finset V) (z:Cube A.card) : (selected A z).card=(supp z).card := card_map _

theorem selected_sub (A:Finset V) (z:Cube A.card) : selected A z⊆A := by
  intro x h;obtain ⟨i,_,rfl⟩:=mem_map.mp h;exact (A.equivFin.symm i).property

theorem selected_injective (A:Finset V) : Function.Injective (selected A) := by
  intro x y eq
  have s:supp x=supp y:=Finset.map_injective _ eq
  funext i
  have h:=Finset.ext_iff.mp s i
  simp only [supp,mem_filter,mem_univ,true_and] at h
  rcases (show ∀ a:F,a=0 ∨ a=1 by decide) (x i) with a|a <;>
    rcases (show ∀ a:F,a=0 ∨ a=1 by decide) (y i) with b|b <;> simp_all

theorem selected_onto (A:Finset V) {S:Finset V} (sub:S⊆A) : ∃z,selected A z=S := by
  classical
  let z:Cube A.card:= fun i=>if index A i∈S then 1 else 0
  refine ⟨z,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩:=mem_map.mp hx
    simpa [supp,z] using hi
  · intro hx
    let i:=A.equivFin ⟨x,sub hx⟩
    have eq:index A i=x := congrArg Subtype.val (A.equivFin.symm_apply_apply _)
    exact mem_map.mpr ⟨i,by simp [supp,z,eq,hx],eq⟩

/-- Each syndrome records the parity and the sum of the selected labels. -/
structure Presentation (A:Finset V) where
  P : Cube A.card →ₗ[F] F×V
  eval : ∀z,P z=(((supp z).card:F),syndrome (selected A z))
  allowed : ∀c:P.ker,(supp c.val).card∈({0,8,12,16}:Finset ℕ)
  rank : Module.finrank F P.ker=A.card-12
  onto : Function.Surjective P

/-- A set with only doubly even label relations has a full presentation
already at seventeen labels. -/
theorem presentation_of_four {A:Finset V} (lo:17≤A.card) (hi:A.card≤23) (avoid:¬FlatAt A 0)
    (fourSum:∀ T⊆A,2∣T.card → syndrome T=0 → 4∣T.card) :
    Nonempty (Presentation A) := by
  classical
  have free : ∀T⊆A,T.card=4 ∨ T.card=6 → syndrome T≠0 := fun T sub sz zero=>
    avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,sz,zero⟩))
  obtain ⟨P,eval,parity,kernel,_⟩:=Green51SparseDimensions.even_pair_columns A free
  have ev (z) : P z=(((supp z).card:F),syndrome (selected A z)) := by
    rw [eval]
    apply Prod.ext
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum,selected,syndrome,index]
  have dist (c:P.ker) (nz:c≠0) : 8≤(supp c.val).card := by
    have e:=parity c.val c.property
    by_contra! small
    exact nz (Subtype.ext (kernel c.val (by omega) c.property))
  have four (c:P.ker) : 4∣(supp c.val).card := by
    have e:=parity c.val c.property
    have sum : syndrome (selected A c.val)=0 := congrArg Prod.snd ((ev c.val).symm.trans c.property)
    rw [←selected_card] at e ⊢
    exact fourSum _ (selected_sub ..) e sum
  have allowed (c:P.ker) : (supp c.val).card∈({0,8,12,16}:Finset ℕ) := by
    have f:=four c
    have upper: (supp c.val).card≤A.card := (supp c.val).card_le_univ.trans_eq (by simp)
    have no20 : (supp c.val).card≠20 := by
      intro w
      apply Green51MissingLabel.forbidden (T:=selected A c.val) (by rw [selected_card,w];decide)
        (fun T sub=>free T (sub.trans (selected_sub ..)))
      exact congrArg Prod.snd ((ev c.val).symm.trans c.property)
    by_cases nz:c=0
    · simp [nz,supp]
    · have d:=dist c nz
      simp only [mem_insert,mem_singleton];omega
  have add:=P.finrank_range_add_finrank_ker
  have up:=Submodule.finrank_le P.range
  have target:Module.finrank F (F×V)=12:=by simp [Cube,Module.finrank_prod]
  rw [target] at up
  rw [show Module.finrank F (Cube A.card)=A.card by simp [Cube]] at add
  have rank:=(Green51ResidualPacking.projection (by omega) P.ker (by omega) dist four).1
  exact ⟨⟨P,ev,allowed,rank,LinearMap.range_eq_top.mp
    (Submodule.eq_top_of_finrank_eq (by rw [target];omega))⟩⟩

/-- All avoiding sets in the shortened range have a surjective check map and
the exact relation dimension. -/
theorem presentation {A:Finset V} (lo:18≤A.card) (hi:A.card≤23) (avoid:¬FlatAt A 0) :
    Nonempty (Presentation A) := by
  exact presentation_of_four (by omega) hi avoid fun _ sub even zero =>
    Green51ResidualPacking.four_divisibility lo avoid sub even zero

/-- Orthogonality is precisely invariance of weight modulo four under
translation by a word of weight divisible by four. -/
theorem weight_mod_four {n:ℕ} (z c:Cube n) (four:4∣(supp c).card) :
    (supp (z+c)).card%4=(supp z).card%4 ↔ dotProduct z c=0 := by
  have add:=Green51AffineMatchings.weight_sum z c
  have bit (i:Fin n) : z i*c i = if i∈supp z∩supp c then (1:F) else 0 := by
    rcases (show ∀a:F,a=0 ∨ a=1 by decide) (z i) with a|a <;>
      rcases (show ∀a:F,a=0 ∨ a=1 by decide) (c i) with b|b <;> simp [supp,a,b]
  have dot : dotProduct z c=((supp z∩supp c).card:F) := by
    simp only [dotProduct,bit,sum_boole]
    rw [filter_mem_eq_inter,univ_inter]
  rw [dot,ZMod.natCast_eq_zero_iff]
  omega

end Green51ShortenedColumns
#print axioms Green51ShortenedColumns.presentation
#print axioms Green51ShortenedColumns.weight_mod_four

#print axioms Green51ShortenedColumns.selected_card
#print axioms Green51ShortenedColumns.selected_sub
#print axioms Green51ShortenedColumns.selected_injective
#print axioms Green51ShortenedColumns.selected_onto

#print axioms Green51ShortenedColumns.presentation_of_four
