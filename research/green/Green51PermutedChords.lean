import Green51PermutedPairs

/-! # The four vertical choices over a nonzero chord -/

open Finset Green50Downsets Green51QuadraticFlats
open scoped Classical Pointwise symmDiff
namespace Green51PermutedPairs
local notation "F" => ZMod 2
variable {n:ℕ}

theorem mem_labels (f:Cube n→Cube n) (b:Cube n→V n) (P:E n) :
    P∈labels f b ↔ ∃ (x:Cube n) (s:F), P=(quad x,b x+s • delta f x) := by
  constructor
  · intro h
    rcases mem_union.mp h with l|r
    · obtain ⟨x,_,rfl⟩:=mem_image.mp l
      exact ⟨x,0,by simp [lower]⟩
    · obtain ⟨x,_,rfl⟩:=mem_image.mp r
      exact ⟨x,1,by simp [upper]⟩
  · rintro ⟨x,s,rfl⟩
    rcases (show ∀ v:F,v=0 ∨ v=1 from by decide) s with rfl|rfl
    · simp only [zero_smul,add_zero]
      exact mem_union_left _ (mem_image_of_mem (lower b) (mem_univ x))
    · simp only [one_smul]
      exact mem_union_right _ (mem_image_of_mem (upper f b) (mem_univ x))

theorem chord_slice (f:Cube n→Cube n) (b:Cube n→V n) {x y:Cube n}
    (ne:x≠y) (v:V n) :
    (quad x+quad y,v)∈labels f b+labels f b ↔
      ∃ s t:F,v=(b x+s • delta f x)+(b y+t • delta f y) := by
  constructor
  · rintro h
    obtain ⟨P,hP,Q,hQ,e⟩:=mem_add.mp h
    obtain ⟨z,s,rfl⟩:=(mem_labels _ _ _).mp hP
    obtain ⟨w,t,rfl⟩:=(mem_labels _ _ _).mp hQ
    have h:=congrArg Prod.fst e
    have vval:=congrArg Prod.snd e
    rcases chord_unique ne h.symm with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨s,t,vval.symm⟩
    · exact ⟨t,s,vval.symm.trans (add_comm _ _)⟩
  · rintro ⟨s,t,rfl⟩
    exact add_mem_add ((mem_labels _ _ _).mpr ⟨x,s,rfl⟩) ((mem_labels _ _ _).mpr ⟨y,t,rfl⟩)

def pairPlane (f:Cube n→Cube n) (x y:Cube n) : Submodule F (V n) :=
  (F ∙ delta f x) ⊔ (F ∙ delta f y)

theorem mem_pairPlane (f:Cube n→Cube n) (x y:Cube n) (v:V n) :
    v∈pairPlane f x y ↔ ∃ s t:F,v=s • delta f x+t • delta f y := by
  rw [pairPlane,Submodule.mem_sup]
  constructor
  · rintro ⟨a,ha,b,hb,rfl⟩
    obtain ⟨s,rfl⟩:=Submodule.mem_span_singleton.mp ha
    obtain ⟨t,rfl⟩:=Submodule.mem_span_singleton.mp hb
    exact ⟨s,t,rfl⟩
  · rintro ⟨s,t,rfl⟩
    exact ⟨_,Submodule.mem_span_singleton.mpr ⟨s,rfl⟩,_,Submodule.mem_span_singleton.mpr ⟨t,rfl⟩,rfl⟩

theorem chord_difference (f:Cube n→Cube n) (b:Cube n→V n) {x y:Cube n} (ne:x≠y)
    {v w:V n} (hv:(quad x+quad y,v)∈labels f b+labels f b)
    (hw:(quad x+quad y,w)∈labels f b+labels f b) : v+w∈pairPlane f x y := by
  obtain ⟨s,t,rfl⟩:=(chord_slice f b ne _).mp hv
  obtain ⟨u,k,rfl⟩:=(chord_slice f b ne _).mp hw
  apply (mem_pairPlane _ _ _ _).mpr
  refine ⟨s+u,t+k,?_⟩
  rw [add_smul,add_smul]
  calc
    _ = (b x+b x)+(b y+b y)+((s • delta f x+u • delta f x)+(t • delta f y+k • delta f y)) := by abel
    _ = _ := by rw [ZModModule.add_self,ZModModule.add_self,zero_add,zero_add]

theorem delta_mem (f:Cube n→Cube n) (inj:Function.Injective f) (x y z:Cube n) :
    delta f z∈pairPlane f x y ↔ z=x ∨ z=y := by
  rw [mem_pairPlane]
  constructor
  · rintro ⟨s,t,e⟩
    rcases (show ∀ v:F,v=0 ∨ v=1 from by decide) s with rfl|rfl <;>
      rcases (show ∀ v:F,v=0 ∨ v=1 from by decide) t with rfl|rfl <;>
      simp only [zero_smul,one_smul,zero_add,add_zero] at e
    · exact False.elim (one_ne_zero (congrArg Prod.fst e))
    · exact Or.inr (inj (congrArg Prod.snd e))
    · exact Or.inl (inj (congrArg Prod.snd e))
    · have h:=congrArg Prod.fst e
      exact False.elim ((by decide : (1:F)≠1+1) h)
  · rintro (rfl|rfl)
    · exact ⟨1,0,by simp⟩
    · exact ⟨0,1,by simp⟩

theorem plane_determines_chord (f:Cube n→Cube n) (inj:Function.Injective f) {x y z w:Cube n}
    (ne:x≠y) (same:pairPlane f x y=pairPlane f z w) : quad x+quad y=quad z+quad w := by
  have hx : x=z ∨ x=w := (delta_mem f inj z w x).mp (same ▸ (delta_mem f inj x y x).mpr (Or.inl rfl))
  have hy : y=z ∨ y=w := (delta_mem f inj z w y).mp (same ▸ (delta_mem f inj x y y).mpr (Or.inr rfl))
  rcases hx with rfl|rfl <;> rcases hy with h|h <;> first | exact False.elim (ne h.symm) | simp [h,add_comm]

theorem pairPlane_rank (f:Cube n→Cube n) (x y:Cube n) : Module.finrank F (pairPlane f x y)≤2 := by
  have h:=Submodule.finrank_sup_add_finrank_inf_eq (F ∙ delta f x) (F ∙ delta f y)
  rw [finrank_span_singleton (show delta f x≠0 from fun e=>one_ne_zero (congrArg Prod.fst e)),
    finrank_span_singleton (show delta f y≠0 from fun e=>one_ne_zero (congrArg Prod.fst e))] at h
  unfold pairPlane
  omega

end Green51PermutedPairs

#print axioms Green51PermutedPairs.chord_slice
#print axioms Green51PermutedPairs.delta_mem
#print axioms Green51PermutedPairs.plane_determines_chord
#print axioms Green51PermutedPairs.pairPlane_rank
