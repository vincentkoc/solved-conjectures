import Green51AffineOrbitCount
import Green51CompleteSumsetCount
import Green51PeriodClassCount

/-! # Complete translation-class count for near-extremal dense binary sumsets -/

namespace Green51AffineTranslation
open Finset Green53ParityThreshold Green51AffineEnumeration Green51OriginRecovery Green51MissingMasks Green51Hyperplane
open scoped Classical Pointwise

/-- For a missing set of proper affine span, exactly the shifts outside the span have
a dense generator. -/
theorem dense_origins {s r : ℕ} (hs : 5 ≤ s) {D : Finset (𝔽₂ (2*(s+1)+r))}
    (proper : admitsOrigin D) (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*D.card)
    (cap : D.card≤(2*s+3)*2^r) (b : 𝔽₂ (2*(s+1)+r)) :
    (∃ A, (A+A)ᶜ=Green51OriginRecovery.translate D b ∧ threshold (2*s)<(A.dens : ℝ)) ↔
      b∉affineSpan F (D : Set (𝔽₂ (2*(s+1)+r))) := by
  have live := card_pos.mp (show 0<D.card by omega)
  rw [←separating_origin_iff live]
  have band : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*(Green51OriginRecovery.translate D b).card := by
    simpa only [translate_card] using near
  constructor
  · intro realized
    by_contra no
    obtain ⟨c,level⟩ := (admits_translate D b).mpr proper
    exact nonaffine_after_shift hs no band realized c level
  · intro level
    exact separated_realizable hs _ level band (by simpa only [translate_card] using cap)

/-- The admissible origins of a nonspanning mask of affine dimension `d` number
`2^n−2^d`. Periods can identify the outputs of different origins. -/
theorem dense_origin_count {s r : ℕ} (hs : 5 ≤ s) {D : Finset (𝔽₂ (2*(s+1)+r))}
    (proper : admitsOrigin D) (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*D.card)
    (cap : D.card≤(2*s+3)*2^r) :
    (univ.filter (fun b => ∃ A, (A+A)ᶜ=Green51OriginRecovery.translate D b ∧ threshold (2*s)<(A.dens : ℝ))).card =
      2^(2*(s+1)+r)-2^affineRank D := by
  classical
  have live := card_pos.mp (show 0<D.card by omega)
  have eq : (univ.filter (fun b => ∃ A, (A+A)ᶜ=Green51OriginRecovery.translate D b ∧ threshold (2*s)<(A.dens : ℝ))) =
      (((affineSpan F (D : Set (𝔽₂ (2*(s+1)+r)))) : Set _).toFinset)ᶜ := by
    ext b
    simp only [mem_filter,mem_univ,true_and,mem_compl,Set.mem_toFinset]
    exact dense_origins hs proper near cap b
  rw [eq,card_compl,affine_span_card live]
  simp [𝔽₂,𝔽]

/-- The two branches of the labelled classification give disjoint ambient translation
classes. The separated branch meets every class of masks with proper affine span. -/
theorem dense_class_partition {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) (cap : k≤(2*s+3)*2^r) :
    let n := 2*(s+1)+r
    let α := threshold (2*s)
    ((allDenseDoubles n k α).image translationClass).card =
      ((properOutputs (𝔽₂ n) k).image translationClass).card +
      ((countedDoubles n k α).image translationClass).card := by
  classical
  let n := 2*(s+1)+r
  let G := 𝔽₂ n
  let α := threshold (2*s)
  let A := allDenseDoubles n k α
  let P := properOutputs G k
  let C := countedDoubles n k α
  have strat : A.filter (fun S => ¬separated Sᶜ)=C := nonseparated_doubles hs k near
  have union : A.image translationClass=P.image translationClass ∪ C.image translationClass := by
    ext V
    constructor
    · rintro hx
      obtain ⟨S,hS,rfl⟩ := mem_image.mp hx
      by_cases good : separated Sᶜ
      · apply mem_union_left
        exact mem_image.mpr ⟨S,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hS).2.1,0,
          by simpa only [Green51OriginRecovery.translate_zero] using good⟩,rfl⟩
      · exact mem_union_right _ (mem_image.mpr ⟨S,strat ▸ mem_filter.mpr ⟨hS,good⟩,rfl⟩)
    · rintro hx
      rcases mem_union.mp hx with hp | hc
      · obtain ⟨S,hS,rfl⟩ := mem_image.mp hp
        obtain ⟨sz,b,sep⟩ := (mem_filter.mp hS).2
        let U := Green51OriginRecovery.translate S b
        have eq : Uᶜ=Green51OriginRecovery.translate Sᶜ b := translate_compl S b
        have num : Uᶜ.card=k := by rw [eq,translate_card,sz]
        obtain ⟨X,hX,den⟩ := separated_realizable hs Uᶜ (eq ▸ sep)
          (by simpa only [num] using near) (by simpa only [num] using cap)
        exact mem_image.mpr ⟨U,mem_filter.mpr ⟨mem_univ _,num,X,compl_inj_iff.mp hX,den⟩,
          (same_class_iff S U).mpr ⟨b,rfl⟩⟩
      · obtain ⟨S,hS,rfl⟩ := mem_image.mp hc
        rw [←strat] at hS
        exact mem_image.mpr ⟨S,(mem_filter.mp hS).1,rfl⟩
  have dis : Disjoint (P.image translationClass) (C.image translationClass) := by
    apply disjoint_left.mpr
    intro V hP hC
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hC
    obtain ⟨U,hU,same⟩ := mem_image.mp hP
    obtain ⟨b,rfl⟩ := (same_class_iff S U).mp same
    have h := (proper_translate S b k).mp hU
    obtain ⟨sz,t,sep⟩ := (mem_filter.mp h).2
    rw [←strat] at hS
    obtain ⟨valid,no⟩ := mem_filter.mp hS
    obtain ⟨_,X,sum,den⟩ := (mem_filter.mp valid).2
    exact nonaffine_after_shift hs no (by simpa only [sz] using near)
      ⟨X,congrArg (fun T : Finset G => Tᶜ) sum,den⟩ t sep
  change (A.image translationClass).card=_; rw [union,card_union_of_disjoint dis]

/-- Arithmetic contribution from the affine branch in dimension `n`. -/
def affineOrbitNumber (n k : ℕ) :=
  (properNumber n k+(2^n-1)*(if 2∣k then properNumber (n-1) (k/2) else 0))/2^n

theorem affine_orbit_number {n : ℕ} (pos : 0<n) (k : ℕ) :
    ((properOutputs (𝔽₂ n) k).image translationClass).card=affineOrbitNumber n k := by
  cases n with
  | zero => omega
  | succ n =>
    unfold affineOrbitNumber
    rw [Nat.succ_sub_one,←proper_orbit_count,Nat.mul_div_cancel _ (by positivity)]

/-- Every dense translation class, for odd or even missing cardinality. The correction for
periodic representatives appears in both branches. -/
theorem all_dense_class_count {s r k : ℕ} (hs : 5 ≤ s)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) (cap : k≤(2*s+3)*2^r) :
    let n := 2*(s+1)+r
    let α := threshold (2*s)
    ((allDenseDoubles n k α).image translationClass).card =
      affineOrbitNumber n k +
        ((countedDoubles n k α).card+
          (2^n-1)*(if 2∣k then (countedDoubles (n-1) (k/2) α).card else 0))/2^r := by
  dsimp only
  rw [dense_class_partition hs near cap,affine_orbit_number (by omega),
    ←Green51PeriodQuotients.all_class_counts hs near,Nat.mul_div_cancel _ (by positivity)]

end Green51AffineTranslation
#print axioms Green51AffineTranslation.dense_origins
#print axioms Green51AffineTranslation.dense_origin_count
#print axioms Green51AffineTranslation.dense_class_partition
#print axioms Green51AffineTranslation.affine_orbit_number
#print axioms Green51AffineTranslation.all_dense_class_count
