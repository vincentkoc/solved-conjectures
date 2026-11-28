import Green51DualSections
import Green51SeventeenProfiles
import Green51ElevenColumns

/-! # Seventeen labels in eleven binary dimensions determine a fifteen-point section -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open Green51ShortenedColumns Green51ShortenedProfiles Green51SeventeenProfiles Green51WeightTransform
open scoped Classical Pointwise
namespace Green51SeventeenSection
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem profile_two {n:ℕ} (size:n=17) (C:Submodule F (Cube n))
    (rank:5≤Module.finrank F C) (even:∀x:C,2∣(supp x.val).card)
    (dist:∀x:C,x≠0 → 8≤(supp x.val).card) (heavy:Green51ShortenedProfiles.multiplicity C 16=0) :
    Module.finrank F C=5 ∧ ∃ z∈dualWords C,(supp z).card=2 := by
  classical
  subst n
  obtain ⟨rk,profile⟩ := Green51SeventeenProfiles.profiles C rank even dist
  have one : dualCount C {2}=1 := by
    simp only [heavy,mem_insert,mem_singleton,Prod.mk.injEq] at profile
    omega
  have pos : 0<dualCount C {2} := by omega
  obtain ⟨z,hz⟩ := card_pos.mp pos
  exact ⟨rk,z,(mem_filter.mp hz).1,mem_singleton.mp (mem_filter.mp hz).2⟩

theorem hyperplane (A:Finset V) (size:A.card=17) (avoid:¬∃p,FlatAt A p) :
    ∃ (L:V→ₗ[F] F) (c:F), L≠0 ∧ (A.filter (fun x => L x=c)).card=15 := by
  classical
  have free : ∀T⊆A,T.card=4 ∨ T.card=6 → (∑t∈T,t)≠0 := fun T sub sz z =>
    avoid ⟨0,(flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,sz,z⟩)⟩
  obtain ⟨P,ev,even,kernel,_⟩ := Green51SparseDimensions.even_pair_columns A free
  have unit (i:Fin A.card) : P (Pi.single i 1)=(1,(A.equivFin.symm i).val) := by
    have hs : supp (Pi.single i (1:F))={i} := by
      ext t; by_cases eq:t=i <;> simp [supp,Pi.single_apply,eq]
    rw [ev,hs,sum_singleton]
  have dist (c:P.ker) (nz:c≠0) : 8≤(supp c.val).card := by
    have parity := even c.val c.property
    by_contra! small
    exact nz (Subtype.ext (kernel c.val (by omega) c.property))
  have heavy : Green51ShortenedProfiles.multiplicity P.ker 16=0 := by
    rw [Green51ShortenedProfiles.multiplicity,card_eq_zero,eq_empty_iff_forall_notMem]
    intro c hc
    have zero : syndrome (selected A c.val)=0 := by
      have eq := congrArg Prod.snd ((ev c.val).symm.trans c.property)
      simp only [selected,syndrome,sum_map]
      change (∑ i∈supp c.val,(A.equivFin.symm i).val)=0
      simpa only [Prod.snd_sum,Prod.snd_zero] using eq
    obtain ⟨p,hp⟩ := Green51ElevenRelations.affine_of_sixteen_sum (selected A c.val)
      ((selected_card A c.val).trans (mem_filter.mp hc).2) zero
    exact avoid ⟨p,Green51FlatSections.flat_mono (selected_sub A c.val) hp⟩
  have dims := P.finrank_range_add_finrank_ker
  have upper := Submodule.finrank_le P.range
  have target : Module.finrank F (F×V)=12 := by simp [Module.finrank_prod,Cube]
  rw [show Module.finrank F (Cube A.card)=17 by simp [Cube,size]] at dims
  rw [target] at upper
  obtain ⟨rank,z,dual,weight⟩ := profile_two size P.ker (by omega) (fun x => even x.val x.property) dist heavy
  have onto := LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq
    (show Module.finrank F P.range=Module.finrank F (F×V) by omega))
  obtain ⟨L,c,non,cut⟩ := Green51DualSections.level P onto unit dual (by omega) (by omega)
  exact ⟨L,c,non,by omega⟩

end Green51SeventeenSection
#print axioms Green51SeventeenSection.hyperplane
