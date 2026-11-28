import Erdos478LowJointSurjection
import Erdos478EvenGapReflection
import Erdos478LowerDegreeActions

/-! # Numbering factorial-gap roots and pairing the four quartic roots -/

namespace Erdos478.LowGapAction
open Equiv Finset Polynomial MulAction BinaryGap FirstCollision FrobeniusCounts
noncomputable section
variable (K : Type*) [Field K] [Algebra ℚ K]

def rootLabels {k : ℕ} (pos : 0<k) (sp : ((rationalGap k).map (algebraMap ℚ K)).Splits) :
    GapRoots K k ≃ Fin k := Fintype.equivFinOfCardEq (gap_card_of_pos K pos sp)

def numberedAction {k : ℕ} (e : GapRoots K k ≃ Fin k) : Aut K →* Perm (Fin k) :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (Aut K) (GapRoots K k))

theorem numbered_apply {k : ℕ} (e : GapRoots K k ≃ Fin k) (g : Aut K) (x : Fin k) :
    numberedAction K e g x=e (g • e.symm x) := rfl

theorem numbered_fixed {k : ℕ} (e : GapRoots K k ≃ Fin k) (g : Aut K) :
    pointCount (numberedAction K e g)=fixedGap K k g := by
  classical
  let T := univ.filter fun x => numberedAction K e g x=x
  let f (x : T) : fixedBy (GapRoots K k) g :=
    ⟨e.symm x.val, by
      have h := (mem_filter.mp x.prop).2
      change e (g • e.symm x.val)=x.val at h
      exact e.eq_symm_apply.mpr h⟩
  have bij : Function.Bijective f := by
    constructor
    · exact fun a b h => Subtype.ext (e.symm.injective (congrArg Subtype.val h))
    · intro x
      refine ⟨⟨e x.val,mem_filter.mpr ⟨mem_univ _,?_⟩⟩,?_⟩
      · rw [numbered_apply,e.symm_apply_apply]
        exact congrArg e x.prop
      · exact Subtype.ext (e.symm_apply_apply x.val)
  exact (Nat.card_eq_finsetCard T).symm.trans (Nat.card_congr (Equiv.ofBijective f bij))

theorem numbered_transitive [Normal ℚ K] {k : ℕ} (pos : 0<k) (e : GapRoots K k ≃ Fin k)
    (x y : Fin k) : ∃ g, numberedAction K e g x=y := by
  let a := e.symm x
  let b := e.symm y
  have irr := GapFamilies.irreducible_gap_rat pos
  have ha := minpoly.eq_of_irreducible irr (mem_rootSet.mp a.prop).2
  have hb := minpoly.eq_of_irreducible irr (mem_rootSet.mp b.prop).2
  obtain ⟨g,hg⟩ := (Normal.minpoly_eq_iff_mem_orbit K).mp (hb.symm.trans ha)
  exact ⟨g,(congrArg e (show g • a=b by exact Subtype.ext hg)).trans (e.apply_symm_apply y)⟩

private theorem reflected (x : GapRoots K 4) : (3:K)-x.val≠x.val ∧
    (3:K)-x.val∈(rationalGap 4).rootSet K := by
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let F := rationalGap 4
  have mapF : F.map (algebraMap ℚ K)=descPochhammer K 4-1 := by simp [F,rationalGap]
  have mon : F.Monic := by
    have h := (SplittingDensity.gap_degree (by decide : 0<4)).monic.map (Int.castRingHom ℚ)
    simpa [F,SplittingDensity.gapPoly,rationalGap] using h
  have mem (z : K) : z∈F.rootSet K ↔ (descPochhammer K 4-1).IsRoot z := by
    rw [← mapF,IsRoot.def,eval_map_algebraMap]; exact mon.mem_rootSet
  have sep : (descPochhammer K 4-1).Separable := mapF ▸ (GapFamilies.irreducible_gap_rat (by decide : 0<4)).separable.map
  have h := EffectiveResolvent.two_even_roots (K:=K) (by norm_num) 2 sep ((mem x.val).mp x.prop)
  constructor
  · convert (Ne.symm h.1) using 2
    norm_num
  · apply (mem _).mpr
    convert h.2 using 2
    norm_num

def rootReflection : Perm (GapRoots K 4) :=
  let f (x : GapRoots K 4) : GapRoots K 4 := ⟨3-x.val,(reflected K x).2⟩
  let hi (x : GapRoots K 4) : f (f x)=x := Subtype.ext (by dsimp [f]; ring)
  ⟨f,f,hi,hi⟩

def pairedReflection (e : GapRoots K 4 ≃ Fin 4) := e.permCongrHom (rootReflection K)

theorem reflection_data (e : GapRoots K 4 ≃ Fin 4) :
    let r := pairedReflection K e
    r*r=1 ∧ pointCount r=0 ∧ ∀ g, numberedAction K e g*r=r*numberedAction K e g := by
  let R := rootReflection K
  have inv : R*R=1 := Equiv.ext fun x => R.left_inv x
  refine ⟨(map_mul e.permCongrHom R R).symm.trans (inv ▸ map_one _),?_,?_⟩
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := (mem_filter.mp hx).2
    change e (R (e.symm x))=x at h
    exact (reflected K _).1 (congrArg Subtype.val (e.eq_symm_apply.mpr h))
  · intro g
    let A := MulAction.toPermHom (Aut K) (GapRoots K 4)
    have c : A g*R=R*A g := by
      ext x
      change g (3-x.val)=3-g x.val
      rw [map_sub,show g (3:K)=3 from map_ofNat g 3]
    exact (map_mul e.permCongrHom _ _).symm.trans ((congrArg e.permCongrHom c).trans (map_mul _ _ _))

#print axioms rootLabels
#print axioms numberedAction
#print axioms numbered_apply
#print axioms numbered_fixed
#print axioms numbered_transitive
#print axioms rootReflection
#print axioms pairedReflection
#print axioms reflection_data
end
end Erdos478.LowGapAction
