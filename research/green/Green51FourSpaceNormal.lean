import Green51FourSpaceMoves
/-! # Relabeling a code with a weight-six word -/
open Finset Green50Downsets Green50Sharp
open Green51FourSpace.Moves
namespace Green51FourSpace
local notation "F" => ZMod 2

private noncomputable def changePositions (k:Fin 12) : Cube 16 ≃ₗ[F] Cube 16 :=
  LinearEquiv.piCongrLeft' F (fun _:Fin 16=>F) (perm k)

private theorem support_change (k:Fin 12) (w:Cube 16) :
    supp (changePositions k w)=(supp w).image (step k) := by
  ext i
  change (i∈univ.filter (fun a=>w ((perm k).symm a)≠0)) ↔ _
  simp only [mem_filter,mem_univ,true_and,mem_image]
  constructor
  · exact fun h=>⟨(perm k).symm i,by simpa [supp] using h,(perm k).apply_symm_apply _⟩
  · rintro ⟨j,hj,h⟩
    change perm k j=i at h
    subst i
    simpa [supp] using hj

private theorem valid_change (C:Submodule F (Cube 16)) (hc:validCode C) (k:Fin 12) :
    validCode (C.map (changePositions k).toLinearMap) := by
  rintro w ⟨v,hv,rfl⟩
  change 2∣(supp (changePositions k v)).card ∧ _
  have ds := congrArg card (support_change k v)
  rw [card_image_of_injective _ (bijections k).1] at ds
  obtain ⟨a,b,c,d⟩:=hc v hv
  refine ⟨ds ▸ a,ds ▸ b,ds ▸ c,fun h=>?_⟩
  obtain ⟨p,hp,sub⟩:=d (ds ▸ h)
  obtain ⟨q,hq,e⟩:=preserved k p hp
  refine ⟨q,hq,?_⟩
  change supp (changePositions k v)⊆positions q
  rw [support_change,←e]
  exact image_mono _ sub

private theorem move_minimum (n:Nat) (C:Submodule F (Cube 16)) (hc:validCode C)
    (dim:6≤Module.finrank F C) (w:Cube 16) (hw:w∈C) (six:(supp w).card=6)
    (size:tag (supp w)=n) : ∃ K:Submodule F (Cube 16),6≤Module.finrank F K ∧ validCode K ∧
      ∃ w∈K,supp w=positions 63 := by
  induction n using Nat.strong_induction_on generalizing C w with
  | h n ih =>
    obtain ⟨p,hp,pw⟩:=(hc w hw).2.2.2 six
    rcases descent_table p hp _ (mem_powersetCard.mpr ⟨pw,six⟩) with done|⟨k,lt⟩
    · exact ⟨C,dim,hc,w,hw,done⟩
    · let e:=changePositions k
      let C' := C.map e.toLinearMap
      have rank : Module.finrank F C'=Module.finrank F C := e.finrank_map_eq C
      have hw' : e w∈C' := ⟨w,hw,rfl⟩
      have weight : (supp (e w)).card=6 := by rw [support_change,card_image_of_injective _ (bijections k).1,six]
      have lower : tag (supp (e w)) < n := by rw [support_change,←size];exact lt
      exact ih _ lower C' (valid_change C hc k) (by omega) (e w) hw' weight rfl

/-- Relabeling the affine cube places one minimum word at the mask 63, without
changing the dimension or the restrictions on the other supports. -/
theorem normalized_code (C:Submodule F (Cube 16)) (hc:validCode C) (dim:6≤Module.finrank F C) :
    ∃ K:Submodule F (Cube 16),6≤Module.finrank F K ∧ validCode K ∧
      ∃ w∈K,supp w=positions 63 := by
  classical
  obtain ⟨w,hw,ne,small⟩:=below_eight C dim
  have tests:=hc w hw
  have pos : (supp w).Nonempty := by
    by_contra! h
    apply ne
    funext i
    by_contra! nonzero
    have hi : i∈supp w := by simpa [supp] using nonzero
    simp [h] at hi
  have six : (supp w).card=6 := by have := pos.card_pos;omega
  exact move_minimum _ C hc dim w hw six rfl
end Green51FourSpace
#print axioms Green51FourSpace.normalized_code
