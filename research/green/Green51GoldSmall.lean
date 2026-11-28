import Green51BCHScalarProfile
/-! # Maximum scalar BCH dimension outside the field of 64 elements -/
open Green50Downsets Green51BCH Green51BCHCompression Green51GoldForms Green51LocalFlats Finset
open scoped Pointwise
namespace Green51GoldSmall
local notation "F" => ZMod 2
variable {K : Type*} [Field K] [CharP K 2] [Algebra F K] [Fintype K]
omit [CharP K 2] in
theorem plane_in_double (l : K →ₗ[F] F) (room : 2≤Module.finrank F K) :
    2 ≤ maxCosetDim F (Space K × F) (Set.range (lifted l)+Set.range (lifted l)) := by
  classical
  let A := univ.image (lifted l)
  have ca : A.card=Fintype.card K := (card_image_of_injective _ (fun x y eq =>
    congrArg (fun z : Space K × F => z.1.1) eq)).trans card_univ
  have large : 3≤A.card := by
    rw [ca,Module.card_eq_pow_finrank (K:=F),ZMod.card]
    exact (by decide : 3≤2^2).trans (Nat.pow_le_pow_right (by decide) room)
  obtain ⟨W,dim,inside⟩ := Green51SparseBounds.plane_of_three A large
  apply (le_iff_coset (by decide : 0<2) _).mpr
  refine ⟨W,0,dim,?_⟩
  rw [zero_vadd]
  intro w hw
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp (inside w hw)
  obtain ⟨u,_,rfl⟩ := mem_image.mp ha
  obtain ⟨v,_,rfl⟩ := mem_image.mp hb
  exact ⟨_,⟨u,rfl⟩,_,⟨v,rfl⟩,rfl⟩

theorem small (l : K →ₗ[F] F) (nl : l≠0) (lower : 2≤Module.finrank F K)
    (upper : Module.finrank F K≤3) :
    maxCosetDim F (Space K × F) (Set.range (lifted l)+Set.range (lifted l))=2 := by
  refine le_antisymm ?_ (plane_in_double l lower)
  by_contra! high
  obtain ⟨W,p,dim,sub⟩ := (le_iff_coset (by decide : 0<3) _).mp high
  have impossible := half_bound l nl p W sub dim.ge
  omega
omit [CharP K 2] in
theorem degree_one (l : K →ₗ[F] F) (dim : Module.finrank F K=1) :
    maxCosetDim F (Space K × F) (Set.range (lifted l)+Set.range (lifted l))=1 := by
  let v := lifted l 1
  let D := Submodule.span F {v}
  have nv : v≠0 := fun h => one_ne_zero (congrArg (fun z:Space K × F => z.1.1) h)
  have rank : Module.finrank F D=1 := finrank_span_singleton nv
  have two (z:K) : z=0 ∨ z=1 := by
    have eq := FiniteField.pow_card z
    rw [Module.card_eq_pow_finrank (K:=F),ZMod.card,dim,pow_one] at eq
    have prod : z*(z-1)=0 := by linear_combination eq
    exact (mul_eq_zero.mp prod).imp_right sub_eq_zero.mp
  have zero : lifted l 0=0 := by simp [lifted,Green51BCH.curve]
  have vs : v∈D := Submodule.subset_span (Set.mem_singleton _)
  have ran : Set.range (lifted l)=(D:Set _) := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      rcases two z with rfl|rfl
      · rw [zero];exact D.zero_mem
      · exact vs
    · intro hx
      obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (show x∈Submodule.span F {v} from hx)
      rcases (show ∀ a:F,a=0 ∨ a=1 from by decide) a with rfl|rfl
      · exact ⟨0,zero.trans (by simpa using ha)⟩
      · exact ⟨1,by simpa using ha⟩
  have dbl : (D:Set (Space K × F))+(D:Set _)=(D:Set _) := by
    ext x
    constructor
    · rintro ⟨a,ha,b,hb,rfl⟩; exact D.add_mem ha hb
    · intro hx;exact ⟨x,hx,0,D.zero_mem,add_zero _⟩
  rw [ran,dbl]
  apply le_antisymm
  · by_contra! high
    obtain ⟨W,p,d,sub⟩ := (le_iff_coset (by decide : 0<2) _).mp high
    have hp : p∈D := sub ⟨0,W.zero_mem,by simp⟩
    have le : W≤D := by
      intro x hx
      have hpx : p+x∈D := sub ⟨x,hx,rfl⟩
      simpa using D.sub_mem hpx hp
    have h := Submodule.finrank_mono le
    omega
  · exact (le_iff_coset (by decide : 0<1) _).mpr ⟨D,0,rank,by simp⟩

theorem maximum_outside_six (l : K →ₗ[F] F) (nl : l≠0) (six : Module.finrank F K≠6) :
    maxCosetDim F (Space K × F) (Set.range (lifted l)+Set.range (lifted l))=Module.finrank F K/2+1 := by
  have pos : 0<Module.finrank F K := Module.finrank_pos
  by_cases one : Module.finrank F K=1
  · rw [degree_one l one,one]
  by_cases hi : 4≤Module.finrank F K
  · obtain ⟨⟨p,W,rank,sub⟩,bound⟩ := scalar_profile l nl hi six
    apply le_antisymm
    · by_contra! above
      obtain ⟨V,q,qr,fits⟩ := (le_iff_coset (by omega : 0<Module.finrank F K/2+1+1) _).mp above
      have h := bound q V fits
      omega
    · exact (le_iff_coset (by omega) _).mpr ⟨W,p,rank,sub⟩
  · rw [small l nl (by omega) (by omega)]
    omega

end Green51GoldSmall
#print axioms Green51GoldSmall.maximum_outside_six
#print axioms Green51GoldSmall.small
