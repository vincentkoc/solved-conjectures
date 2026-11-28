import Green51FourSpaceProjection
import Green51LocalFlats

/-! # The even relation code forced by an affine flat -/

open Finset Green50Downsets
open scoped Classical Pointwise
namespace Green51FourSpace
local notation "F" => ZMod 2

/-- The kernel records even selections of sites whose sum of left endpoints
lies in the span of the distinguished pair sums. -/
def projectedCheck {d:ℕ} {G:Type*} [AddCommGroup G] [Module F G]
    (a:Cube d→G) (e:(F × Cube d) →ₗ[F] G) :
    (Cube d → F) →ₗ[F] (F × (G ⧸ e.range)) :=
  (Fintype.linearCombination F fun _ : Cube d => (1:F)).prod
    (e.range.mkQ.comp (Fintype.linearCombination F a))

theorem projected_rank {d:ℕ} {G:Type*} [AddCommGroup G] [Module F G] [Module.Finite F G]
    (a:Cube d→G) (e:(F × Cube d) →ₗ[F] G) (inj:Function.Injective e) :
    2^d+d ≤ Module.finrank F (projectedCheck a e).ker+Module.finrank F G := by
  have dim := (projectedCheck a e).finrank_range_add_finrank_ker
  have upper := Submodule.finrank_le (projectedCheck a e).range
  have quotient := e.range.finrank_quotient_add_finrank
  rw [e.finrank_range_of_inj inj,Module.finrank_prod] at quotient
  rw [Module.finrank_prod] at upper
  have src : Module.finrank F (Cube d → F)=2^d := by simp [Cube]
  have scal : Module.finrank F F=1 := by simp
  have idx : Module.finrank F (Cube d)=d := by simp [Cube]
  rw [src] at dim
  rw [scal] at upper
  rw [scal,idx] at quotient
  omega

def wordSupport {d:ℕ} (w:Cube d → F) : Finset (Cube d) := univ.filter (fun i=>w i≠0)

private theorem lincomb_bits {I G:Type*} [Fintype I] [DecidableEq I] [AddCommGroup G] [Module F G]
    (a:I→G) (w:I→F) :
    Fintype.linearCombination F a w = ∑ i ∈ univ.filter (fun i=>w i≠0),a i := by
  rw [Fintype.linearCombination_apply,sum_filter]
  apply sum_congr rfl
  intro i _
  rcases (show ∀ b:F,b=0 ∨ b=1 from by decide) (w i) with h|h <;> simp [h]

theorem member_support {d:ℕ} {G:Type*} [AddCommGroup G] [Module F G]
    (a:Cube d→G) (e:(F × Cube d) →ₗ[F] G) (w:Cube d → F) :
    w∈(projectedCheck a e).ker ↔ 2∣(wordSupport w).card ∧ (∑ i∈wordSupport w,a i)∈e.range := by
  change (_,_) = (0:F×(G⧸e.range)) ↔ _
  change (Fintype.linearCombination F (fun _ : Cube d => (1:F)) w,e.range.mkQ (Fintype.linearCombination F a w))=(0,0) ↔ _
  rw [Prod.mk.injEq,lincomb_bits,lincomb_bits]
  change ((∑ _ ∈ wordSupport w, (1:F))=0 ∧ Submodule.Quotient.mk (∑ i∈wordSupport w, a i)=0) ↔ _
  rw [Submodule.Quotient.mk_eq_zero, sum_const,nsmul_eq_mul,mul_one,ZMod.natCast_eq_zero_iff]
variable {G:Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

/-- An affine flat of dimension at least three gives an even relation code
whose six-site supports lie in proper affine subspaces of the flat. -/
theorem obstruction_code {d:ℕ} (large:3≤d) (A:Finset G)
    (avoid:¬∃ V:Submodule F G, Module.finrank F V=3 ∧ ∀ v∈V,v∈A+A)
    (p:G) (W:Submodule F G) (dim:Module.finrank F W=d)
    (inside:p +ᵥ (W:Set G) ⊆ ↑(A+A)) :
    ∃ K:Submodule F (Cube d → F), 2^d+d ≤ Module.finrank F K+Module.finrank F G ∧
      ∀ w∈K, 2∣(wordSupport w).card ∧ (wordSupport w).card≠2 ∧ (wordSupport w).card≠4 ∧
        ((wordSupport w).card=6 → Submodule.span F ((fun z:Cube d => ((1:F),z)) ''
          (wordSupport w:Set (Cube d)))≠⊤) := by
  classical
  obtain ⟨f,j,sub,values⟩ := Green51LocalFlats.model_image A W dim p inside
  let L := W.subtype.comp j.toLinearMap
  have linj : Function.Injective L := Subtype.val_injective.comp j.injective
  let e := f.comp (LinearMap.inr F (Cube d→F) (F × Cube d))
  have ev (z:Cube d) : e (1,z)=p+L z := values z
  let a (z:Cube d) := f (Green51LocalFlats.leftPoint z)
  let δ (z:Cube d) := e (1,z)
  have right (z:Cube d) : a z+δ z=f (Green51LocalFlats.rightPoint z) := by
    change f _ + f (0,1,z)=_
    rw [←map_add]
    congr 1
    simp [Green51LocalFlats.leftPoint,Green51LocalFlats.rightPoint]
  have inA (i:Cube d×F) : endpoint a δ i∈A := by
    obtain ⟨z,b⟩ := i
    rcases (show ∀ b:F,b=0 ∨ b=1 from by decide) b with rfl|rfl
    · simp only [endpoint,zero_smul,add_zero]
      exact sub (mem_image_of_mem _ (mem_union_left _ (mem_image_of_mem _ (mem_univ z))))
    · simp only [endpoint,one_smul,right]
      exact sub (mem_image_of_mem _ (mem_union_right _ (mem_image_of_mem _ (mem_univ z))))
  have pairs (z:Cube d) : endpoint a δ (z,0)+endpoint a δ (z,1)=p+L z := by
    simp only [endpoint,zero_smul,one_smul,add_zero,←add_assoc,ZModModule.add_self,zero_add]
    exact ev _
  have distinct := Green51QuadraticFlats.disjoint_representatives large A avoid (endpoint a δ) inA p L linj pairs
  have big := Green51AffineMatchings.affine_flat_cost A avoid W p inside (dim ▸ large)
  rw [dim] at big
  have emin : 2^4 ≤ 2^(d+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have ej : Function.Injective e := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    rintro ⟨b,z⟩ h
    have zero : e (b,z)=0 := h
    rcases (show ∀ b:F,b=0 ∨ b=1 from by decide) b with rfl|rfl
    · have r := congrArg (fun x => e x) (show (((1:F),z)+(1,0))=(0,z) by simp [Prod.mk_add_mk,ZModModule.add_self])
      simp only [map_add,ev,map_zero,add_zero,zero] at r
      have h0 : L z=0 := by
        calc L z = p+(p+L z) := by rw [←add_assoc,ZModModule.add_self,zero_add]
             _ = 0 := by rwa [add_comm]
      exact (Submodule.mem_bot F).mpr (by simp [linj (h0.trans L.map_zero.symm)])
    · have he := pairs z
      rw [←ev,zero] at he
      have s := distinct (add_right_cancel (he.trans (ZModModule.add_self (endpoint a δ (z,1))).symm))
      exact False.elim ((by decide : (0:F)≠1) (congrArg Prod.snd s))
  let K := (projectedCheck a e).ker
  refine ⟨K,projected_rank a e ej,?_⟩
  intro w hw
  obtain ⟨even,rel⟩ := (member_support a e w).mp hw
  refine ⟨even,projected_support a e ?_ (wordSupport w) rel⟩
  intro B size zero
  let T := B.image (endpoint a δ)
  have sizeT : T.card=B.card := card_image_of_injective _ distinct
  have inT : T⊆A := by intro x hx; obtain ⟨i,_,rfl⟩ := mem_image.mp hx;exact inA i
  have zeroT : ∑ x∈T,x=0 := by simpa [T,sum_image distinct.injOn] using zero
  rcases size with two|other
  · obtain ⟨x,y,ne,eq⟩ := card_eq_two.mp (sizeT.trans two)
    rw [eq,sum_pair ne] at zeroT
    exact ne (add_right_cancel (zeroT.trans (ZModModule.add_self _).symm))
  · exact avoid ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,inT,by rwa [sizeT],zeroT⟩)

end Green51FourSpace
#print axioms Green51FourSpace.obstruction_code
