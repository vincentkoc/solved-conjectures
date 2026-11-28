import Green51TranslationClasses
import Green51RealizableShifts
import Green51DenseSumsetEnumeration

/-! # Distinct dense sumsets up to translation -/

namespace Green51OriginRecovery
open Finset Green53ParityThreshold Green51GirthFrame Green51Hyperplane Green51MissingMasks
open scoped Classical Pointwise

private theorem dimension_criterion {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    (S : Finset (𝔽₂ (2*(s+1)+r))) (sz : Sᶜ.card=k)
    (valid : ∃ A : Finset (𝔽₂ (2*(s+1)+r)), A+A=S ∧ threshold (2*s)<(A.dens : ℝ)) :
    maxCosetDim F (𝔽₂ (2*(s+1)+r)) ↑S=2*(s+1)+r-2 ↔
      ¬∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ Sᶜ, f x=1 := by
  obtain ⟨A,rfl,ha⟩ := valid
  have no := girth_of_density A s ha
  have h := near_girth_dimension (n := 2*(s+1)+r) (g := 2*s+3) (by omega) (A+A)ᶜ
    (by omega) ⟨s+1,by omega⟩ (by simpa only [show 2*(s+1)+1=2*s+3 by omega] using no)
    (by simpa only [show 2*(s+1)+r+1-(2*s+3)=r by omega,sz] using near)
  simpa only [compl_compl] using h

/-- For a counted sumset, the shifts preserving dense realizability form an explicitly detected
subspace of order `2^r`. The largest affine dimension is preserved throughout these shifts. -/
theorem counted_translations {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {S : Finset (𝔽₂ (2*(s+1)+r))} (hS : S∈countedDoubles (2*(s+1)+r) k (threshold (2*s))) :
    ∃ P : Submodule F (𝔽₂ (2*(s+1)+r)), (P : Set (𝔽₂ (2*(s+1)+r))).toFinset.card=2^r ∧
      ∀ b, (b∈P ↔ 2*2^r < lag Sᶜ b) ∧
        (translate S b∈countedDoubles (2*(s+1)+r) k (threshold (2*s)) ↔ b∈P) ∧
        ((∃ A : Finset (𝔽₂ (2*(s+1)+r)), A+A=translate S b ∧ threshold (2*s)<(A.dens : ℝ)) ↔ b∈P) := by
  classical
  obtain ⟨sz,dim,valid⟩ := (mem_filter.mp hS).2
  have no := (dimension_criterion hs near S sz valid).mp dim
  obtain ⟨A,eA,hA⟩ := valid
  have realD : ∃ B : Finset (𝔽₂ (2*(s+1)+r)), (B+B)ᶜ=Sᶜ ∧ threshold (2*s)<(B.dens : ℝ) :=
    ⟨A,congrArg (fun X : Finset (𝔽₂ (2*(s+1)+r)) => Xᶜ) eA,hA⟩
  have band : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*Sᶜ.card := sz ▸ near
  obtain ⟨P,cardP,iffP⟩ := realizable_shifts hs no band realD
  refine ⟨P,cardP,fun b => ⟨(iffP b).1,?_⟩⟩
  have eqv : (∃ B : Finset (𝔽₂ (2*(s+1)+r)), B+B=translate S b ∧ threshold (2*s)<(B.dens : ℝ)) ↔ b∈P := by
    rw [←(iffP b).2]
    change _ ↔ ∃ B : Finset (𝔽₂ (2*(s+1)+r)), (B+B)ᶜ=translate Sᶜ b ∧ _
    rw [←translate_compl]
    simp only [compl_inj_iff]
  refine ⟨⟨fun mem => eqv.mp (mem_filter.mp mem).2.2.2,fun hb => ?_⟩,eqv⟩
  have valid := eqv.mpr hb
  have size : (translate S b)ᶜ.card=k := by rw [translate_compl,translate_card,sz]
  apply mem_filter.mpr
  refine ⟨mem_univ _,size,(dimension_criterion hs near _ size valid).mpr ?_,valid⟩
  rw [translate_compl]
  exact nonaffine_after_shift hs no band realD b

/-- At odd missing cardinality, every translation class meets the counted family in exactly
`2^r` distinct sumsets. -/
theorem odd_class_fiber {s r k : ℕ} (hs : 5 ≤ s) (odd : Odd k)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    {S : Finset (𝔽₂ (2*(s+1)+r))} (hS : S∈countedDoubles (2*(s+1)+r) k (threshold (2*s))) :
    ((countedDoubles (2*(s+1)+r) k (threshold (2*s))).filter
      (fun T => translationClass T=translationClass S)).card=2^r := by
  classical
  obtain ⟨P,cardP,h⟩ := counted_translations hs near hS
  have size := (mem_filter.mp hS).2.1
  have inj : Function.Injective (translate S) := by
    intro a b eq
    apply odd_translation_injective Sᶜ (size ▸ odd)
    simpa only [←translate_compl] using congrArg (fun V : Finset (𝔽₂ (2*(s+1)+r)) => Vᶜ) eq
  rw [←cardP]
  apply (card_bij (fun b _ => translate S b) ?_ ?_ ?_).symm
  · intro b hb
    exact mem_filter.mpr ⟨(h b).2.1.mpr (Set.mem_toFinset.mp hb),(same_class_iff _ _).mpr ⟨b,rfl⟩⟩
  · exact fun _ _ _ _ eq => inj eq
  · intro T hT
    obtain ⟨belongs,same⟩ := mem_filter.mp hT
    obtain ⟨b,rfl⟩ := (same_class_iff _ _).mp same
    exact ⟨b,Set.mem_toFinset.mpr ((h b).2.1.mp belongs),rfl⟩

theorem odd_class_count {s r k : ℕ} (hs : 5 ≤ s) (odd : Odd k)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) :
    let family := countedDoubles (2*(s+1)+r) k (threshold (2*s))
    (family.image translationClass).card * 2^r=family.card :=
  uniform_class_count _ _ (fun _ h => odd_class_fiber hs odd near h)

theorem classes_at_forty_one :
    ((countedDoubles 16 41 (threshold 12)).image translationClass).card =
      7173767398331178268151749942350710292430047640794411461865652617216000 := by
  let c := ((countedDoubles 16 41 (threshold 12)).image translationClass).card
  have h : c*4=(countedDoubles 16 41 (threshold 12)).card :=
    odd_class_count (s := 6) (r := 2) (by decide) (by decide : Odd 41) (by decide)
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0<4) (h.trans count_at_forty_one)

end Green51OriginRecovery
#print axioms Green51OriginRecovery.counted_translations
#print axioms Green51OriginRecovery.odd_class_fiber
#print axioms Green51OriginRecovery.odd_class_count
#print axioms Green51OriginRecovery.classes_at_forty_one
