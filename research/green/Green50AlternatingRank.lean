import Green50QuadraticDiameter

/-! # Minimum rank in affine spaces of alternating forms over finite fields

The quotient by the direction of an affine space turns rank minimization into a
shortest representation by values of the exterior product.
-/

open Finset
namespace Green50AlternatingRank

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
local notation "Form" => LinearMap.BilinForm K V
local notation "Dual" => Module.Dual K V

/-- The space of scalar alternating forms on V. -/
def alternatingForms (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Submodule K (LinearMap.BilinForm K V) where
  carrier := {F | F.IsAlt}
  zero_mem' := fun _ => rfl
  add_mem' hx hy := hx.add hy
  smul_mem' c A hA := by intro x; simp [hA x]

instance instAddCommGroup : AddCommGroup (alternatingForms K V) := Module.addCommMonoidToAddCommGroup K

private def exteriorPair (a b : Dual) : alternatingForms K V :=
  ⟨a.smulRight b - b.smulRight a, fun x => by change a x * b x - b x * a x = 0; ring⟩

private theorem pair_apply (a b : Dual) (x y : V) :
    (exteriorPair a b).val x y = a x * b y - b x * a y := rfl

private def wedgeMap : Dual →ₗ[K] Dual →ₗ[K] alternatingForms K V :=
  LinearMap.mk₂ K exteriorPair
    (by intros; apply Subtype.ext; ext x y; simp [pair_apply]; ring)
    (by intros; apply Subtype.ext; ext x y; simp [pair_apply]; ring)
    (by intros; apply Subtype.ext; ext x y; simp [pair_apply]; ring)
    (by intros; apply Subtype.ext; ext x y; simp [pair_apply]; ring)

/-- Exterior product of two functionals, projected to the chosen quotient. -/
def quotientPair (T : Submodule K (alternatingForms K V)) :
    Dual →ₗ[K] Dual →ₗ[K] (alternatingForms K V ⧸ T) :=
  (LinearMap.llcomp K Dual (alternatingForms K V) (alternatingForms K V ⧸ T) T.mkQ).comp wedgeMap

private theorem quotientPair_apply (T : Submodule K (alternatingForms K V)) (a b : Dual) :
    quotientPair T a b = T.mkQ (exteriorPair a b) := rfl

private theorem sum_representative {k : ℕ} (a b : Fin k → Dual) (F : alternatingForms K V)
    (h : ∀ x y, F.val x y = ∑ i, (a i x * b i y - b i x * a i y)) :
    F = ∑ i, exteriorPair (a i) (b i) := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simpa only [Submodule.coe_sum, LinearMap.sum_apply, pair_apply] using h x y

private theorem pair_sum_rank [FiniteDimensional K V] {k : ℕ} (a b : Fin k → Dual) :
    Module.finrank K ((∑ i, exteriorPair (a i) (b i)).val.range) ≤ 2 * k := by
  let Φ := (LinearMap.pi a).prod (LinearMap.pi b)
  let F := (∑ i, exteriorPair (a i) (b i)).val
  have hk : Φ.ker ≤ F.ker := by
    intro x hx
    have hp : ((fun i => a i x), fun i => b i x) = 0 := hx
    have ha := congrArg Prod.fst hp
    have hb := congrArg Prod.snd hp
    apply LinearMap.ext
    intro y
    simp only [F, Submodule.coe_sum, LinearMap.sum_apply, pair_apply]
    simp [show ∀ i, a i x = 0 from fun i => congrFun ha i,
      show ∀ i, b i x = 0 from fun i => congrFun hb i]
  have hΦ := Φ.finrank_range_add_finrank_ker
  have hF := F.finrank_range_add_finrank_ker
  have hker := Submodule.finrank_mono hk
  have hcod := Φ.range.finrank_le
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at hcod
  change Module.finrank K F.range ≤ 2 * k
  omega


/-- The alternating product modulo T generates the full quotient. -/
theorem quotient_span [FiniteDimensional K V] (T : Submodule K (alternatingForms K V)) :
    Green50QuadraticDiameter.valueSpan (quotientPair T) = ⊤ := by
  refine top_unique fun w _ => ?_
  obtain ⟨J, rfl⟩ := T.mkQ_surjective w
  obtain ⟨m, _, _, a, b, h⟩ := Green50SymplecticSpaces.alternating_decomposition K
    (Module.finrank K V) J.val J.property rfl
  rw [sum_representative a b J h, map_sum]
  exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨(a i, b i), rfl⟩)

/-- An m-term representation supplies a form of rank at most 2m in its class. -/
theorem class_rank_of_rep [FiniteDimensional K V] (T : Submodule K (alternatingForms K V))
    (J : alternatingForms K V) {m : ℕ} (h : Green50QuadraticDiameter.Represented
      (quotientPair T) m (T.mkQ J)) :
    ∃ F : alternatingForms K V, F - J ∈ T ∧ Module.finrank K F.val.range ≤ 2 * m := by
  obtain ⟨a, b, h⟩ := h
  let F := ∑ i, exteriorPair (a i) (b i)
  have he : T.mkQ F = T.mkQ J := by dsimp only [F]; rw [map_sum]; exact h
  exact ⟨F, (Submodule.Quotient.eq T).mp he, pair_sum_rank a b⟩

theorem quotient_alt (T : Submodule K (alternatingForms K V)) (a : Dual) :
    quotientPair T a a = 0 := by
  change T.mkQ (exteriorPair a a) = 0
  have ha : exteriorPair a a = 0 := by apply Subtype.ext; ext x y; simp [pair_apply]
  rw [ha, map_zero]

/-- An affine space of alternating forms of codimension d contains a form of rank
at most 2⌊√d⌋ over any finite field. -/
theorem exists_rank_le [Fintype K] [FiniteDimensional K V] (T : Submodule K (alternatingForms K V))
    (J : alternatingForms K V) : ∃ F : alternatingForms K V, F - J ∈ T ∧
      Module.finrank K F.val.range ≤ 2 * (Module.finrank K (alternatingForms K V ⧸ T)).sqrt := by
  classical
  let B := quotientPair T
  have hB (x : Dual) : B x x = 0 := by
    change T.mkQ (exteriorPair x x) = 0
    have hxx : exteriorPair x x = 0 := by
      apply Subtype.ext
      ext a b
      simp [pair_apply]
    rw [hxx, map_zero]
  obtain ⟨m, _, _, a, b, h⟩ := Green50SymplecticSpaces.alternating_decomposition K
    (Module.finrank K V) J.val J.property rfl
  have hmem : T.mkQ J ∈ Green50QuadraticDiameter.valueSpan B := by
    rw [sum_representative a b J h, map_sum]
    exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨(a i, b i), rfl⟩)
  obtain ⟨c, d, hrep⟩ := (Green50QuadraticDiameter.span_iff_represented B hB _).mp hmem
  let F := ∑ i, exteriorPair (c i) (d i)
  have he : T.mkQ F = T.mkQ J := by
    dsimp only [F]
    rw [map_sum]
    exact hrep
  refine ⟨F, (Submodule.Quotient.eq T).mp he, (pair_sum_rank c d).trans ?_⟩
  exact Nat.mul_le_mul_left 2 (Nat.sqrt_le_sqrt (Green50QuadraticDiameter.valueSpan B).finrank_le)

/-- If every form in a translate has rank at least 2r, its codimension in the
alternating forms is at least r². -/
theorem codimension_of_lower_rank [Fintype K] [FiniteDimensional K V]
    (T : Submodule K (alternatingForms K V)) (J : alternatingForms K V) (r : ℕ)
    (h : ∀ F : alternatingForms K V, F - J ∈ T → 2 * r ≤ Module.finrank K F.val.range) :
    r * r ≤ Module.finrank K (alternatingForms K V ⧸ T) := by
  obtain ⟨F, hF, hr⟩ := exists_rank_le T J
  exact Nat.le_sqrt.mp (by have := h F hF; omega)


variable [FiniteDimensional K V]

/-- Any matrix of sampled values of a bilinear form factors through its image. -/
private theorem sample_rank {I : Type*} [Fintype I] [DecidableEq I] (F : LinearMap.BilinForm K V)
    (x y : I → V) : (Matrix.of fun i j => F (x i) (y j)).rank ≤ Module.finrank K F.range := by
  classical
  let _ : AddCommGroup F.range := Module.addCommMonoidToAddCommGroup K
  let b := Module.finBasis K F.range
  let z (i : I) : F.range := ⟨F (x i), ⟨x i, rfl⟩⟩
  let X := Matrix.of fun i t => b.repr (z i) t
  let Y := Matrix.of fun t j => (b t).val (y j)
  have fact : X * Y = Matrix.of (fun i j => F (x i) (y j)) := by
    ext i j
    change ∑ t, b.repr (z i) t * (b t).val (y j) = F (x i) (y j)
    have he := congrArg (fun v : F.range => v.val (y j)) (b.sum_repr (z i))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, z] using he
  rw [← fact]
  exact ((Matrix.rank_mul_le_left X Y).trans (Matrix.rank_le_card_width X)).trans_eq (Fintype.card_fin _)

/-- The off-diagonal block is unitriangular and the first family is totally isotropic. -/
private theorem triangular_rank {k : ℕ} (F : alternatingForms K V) (a b : Fin k → V)
    (haa : ∀ i j, F.val (a i) (a j) = 0)
    (hab : ∀ i j, i ≤ j → F.val (a i) (b j) = if i = j then 1 else 0) :
    2 * k ≤ Module.finrank K F.val.range := by
  classical
  let C := Matrix.of fun i j => F.val (a i) (b j)
  let D := Matrix.of fun i j => F.val (b i) (b j)
  let X := Matrix.of fun i j => F.val (Sum.elim b a i) (Sum.elim a b j)
  have blocks : X = Matrix.fromBlocks (-C.transpose) D 0 C := by
    ext i j
    cases i <;> cases j <;> simp [X, C, D, haa, F.property.neg_eq]
  have tri : C.IsLowerTriangular := by
    intro i j h
    change i < j at h
    exact (hab i j h.le).trans (if_neg h.ne)
  have diag i : C i i = 1 := by simpa [C] using hab i i le_rfl
  have hdet : C.det = 1 := by rw [Matrix.det_of_isLowerTriangular C tri]; simp [diag]
  have unit : IsUnit X := by
    rw [Matrix.isUnit_iff_isUnit_det, blocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg,
      Matrix.det_transpose, hdet]
    simp
  have h := sample_rank F.val (Sum.elim b a) (Sum.elim a b)
  change X.rank ≤ _ at h
  rw [Matrix.rank_of_isUnit _ unit, Fintype.card_sum, Fintype.card_fin] at h
  omega

/-- A coordinate model in dimension 2r + s. -/
abbrev Model (K : Type*) (r s : ℕ) := (Fin r → K) × (Fin r → K) × (Fin s → K)

private def leftVector (K : Type*) [Field K] {r s : ℕ} (i : Fin r) : Model K r s :=
  (Pi.single i 1, 0, 0)
private def rightVector (K : Type*) [Field K] {r s : ℕ} (i : Fin r) : Model K r s :=
  (0, Pi.single i 1, 0)

private def leftCoord {r s : ℕ} (i : Fin r) : Module.Dual K (Model K r s) :=
  (LinearMap.proj i).comp (LinearMap.fst K _ _)
private def rightCoord {r s : ℕ} (i : Fin r) : Module.Dual K (Model K r s) :=
  (LinearMap.proj i).comp ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _))

private def standard (r s : ℕ) : alternatingForms K (Model K r s) :=
  ∑ i : Fin r, exteriorPair (leftCoord i) (rightCoord i)

private theorem standard_left {r s : ℕ} (i j : Fin r) :
    (standard (K := K) r s).val (leftVector K i) (leftVector K j) = 0 := by
  simp [standard, LinearMap.sum_apply, pair_apply, leftCoord, rightCoord, leftVector]

private theorem standard_mixed {r s : ℕ} (i j : Fin r) :
    (standard (K := K) r s).val (leftVector K i) (rightVector K j) = if i = j then 1 else 0 := by
  simp [standard, LinearMap.sum_apply, pair_apply, leftCoord, rightCoord,
    leftVector, rightVector, Pi.single_apply, eq_comm]

private def entries (r s : ℕ) : alternatingForms K (Model K r s) →ₗ[K] Matrix (Fin r) (Fin r) K where
  toFun F := Matrix.of fun i j => if i < j then F.val (leftVector K i) (leftVector K j)
    else F.val (leftVector K j) (rightVector K i)
  map_add' F G := by ext i j; dsimp; split <;> rfl
  map_smul' c F := by ext i j; dsimp; split <;> rfl

private theorem same_entries {r s : ℕ} (F : alternatingForms K (Model K r s))
    (h : entries r s F = entries r s (standard r s)) :
    2 * r ≤ Module.finrank K F.val.range := by
  have upper (i j : Fin r) (lt : i < j) : F.val (leftVector K i) (leftVector K j) = 0 := by
    have he := congrArg (fun A : Matrix (Fin r) (Fin r) K => A i j) h
    simpa [entries, lt, standard_left] using he
  apply triangular_rank F (leftVector K) (rightVector K)
  · intro i j
    rcases lt_trichotomy i j with lt | rfl | gt
    · exact upper i j lt
    · exact F.property _
    · rw [← F.property.neg_eq (leftVector K j) (leftVector K i), upper j i gt, neg_zero]
  · intro i j le
    have he := congrArg (fun A : Matrix (Fin r) (Fin r) K => A j i) h
    simpa [entries, not_lt.mpr le, standard_mixed] using he

/-- In each dimension 2r + s a family of codimension r² attains minimum rank 2r. -/
theorem sharp_family (K : Type*) [Field K] [Fintype K] (r s : ℕ) :
    ∃ (T : Submodule K (alternatingForms K (Model K r s))) (J : alternatingForms K (Model K r s)),
      Module.finrank K (alternatingForms K (Model K r s) ⧸ T) = r * r ∧
      (∀ F : alternatingForms K (Model K r s), F-J ∈ T → 2 * r ≤ Module.finrank K F.val.range) ∧
      ∃ F : alternatingForms K (Model K r s), F-J ∈ T ∧ Module.finrank K F.val.range = 2 * r := by
  classical
  let L := entries (K := K) r s
  let J := standard (K := K) r s
  have allF (F : alternatingForms K (Model K r s)) (h : F-J ∈ L.ker) :
      2 * r ≤ Module.finrank K F.val.range := by
    apply same_entries
    exact sub_eq_zero.mp (by simpa only [← map_sub] using (LinearMap.mem_ker.mp h))
  have lb := codimension_of_lower_rank L.ker J r allF
  have ub := L.range.finrank_le
  rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin, mul_one] at ub
  have eq : Module.finrank K (alternatingForms K (Model K r s) ⧸ L.ker) = r * r := by
    rw [L.quotKerEquivRange.finrank_eq] at lb ⊢
    omega
  obtain ⟨F, hF, small⟩ := exists_rank_le L.ker J
  rw [eq, Nat.sqrt_eq] at small
  exact ⟨L.ker, J, eq, allF, F, hF, le_antisymm small (allF F hF)⟩


private abbrev Upper (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private noncomputable def upperEntries {n : ℕ} (b : Module.Basis (Fin n) K V) :
    alternatingForms K V →ₗ[K] (Upper n → K) where
  toFun F p := F.val (b p.val.1) (b p.val.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K V] in
private theorem upper_bijective {n : ℕ} (b : Module.Basis (Fin n) K V) :
    Function.Bijective (upperEntries b) := by
  classical
  constructor
  · intro F G h
    apply Subtype.ext
    apply b.ext
    intro i
    apply b.ext
    intro j
    rcases lt_trichotomy i j with lt | rfl | gt
    · exact congrFun h ⟨(i, j), lt⟩
    · exact (F.property _).trans (G.property _).symm
    · rw [← F.property.neg_eq (b j) (b i), ← G.property.neg_eq (b j) (b i)]
      exact congrArg Neg.neg (congrFun h ⟨(j, i), gt⟩)
  · intro c
    refine ⟨∑ p : Upper n, c p • exteriorPair (b.coord p.val.1) (b.coord p.val.2), ?_⟩
    funext p
    simp only [upperEntries, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum,
      Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, pair_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    rw [sum_eq_single p]
    · simp [p.property.ne, p.property.ne']
    · rintro ⟨⟨i, j⟩, gt⟩ _ h
      have h₁ : ¬(i = p.val.1 ∧ j = p.val.2) := by rintro ⟨rfl, rfl⟩; exact h rfl
      have h₂ : ¬(j = p.val.1 ∧ i = p.val.2) := by rintro ⟨rfl, rfl⟩; exact gt.asymm p.property
      dsimp only
      split_ifs <;> simp_all
    · simp

/-- Feasible codimensions range from zero to n choose two in dimension n. -/
theorem dimension (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Module.finrank K (alternatingForms K V) = (Module.finrank K V).choose 2 := by
  classical
  let b := Module.finBasis K V
  rw [(LinearEquiv.ofBijective (upperEntries b) (upper_bijective b)).finrank_eq, Module.finrank_pi,
    Fintype.card_subtype]
  simpa only [univ_product_univ, card_univ, Fintype.card_fin] using
    (card_product_filter_lt (s := (univ : Finset (Fin (Module.finrank K V)))))

/-- Slice an extremal family through a minimum-rank form to prescribe the codimension.
Every codimension from r² to the dimension of the whole alternating space occurs. -/
theorem minimum_rank_at_codimension (K : Type*) [Field K] [Fintype K] (r s d : ℕ)
    (hd : d ≤ (2 * r + s).choose 2) :
    (∃ (T : Submodule K (alternatingForms K (Model K r s))) (J : alternatingForms K (Model K r s)),
      Module.finrank K (alternatingForms K (Model K r s) ⧸ T) = d ∧
      Module.finrank K J.val.range = 2 * r ∧
      ∀ F : alternatingForms K (Model K r s), F - J ∈ T → 2 * r ≤ Module.finrank K F.val.range) ↔
      r * r ≤ d := by
  classical
  have ambient : Module.finrank K (Model K r s) = 2 * r + s := by
    simp [Model, Module.finrank_prod]; omega
  have bound : d ≤ Module.finrank K (alternatingForms K (Model K r s)) := by
    rwa [dimension, ambient]
  constructor
  · rintro ⟨T, J, hT, _, hF⟩
    exact (codimension_of_lower_rank T J r hF).trans_eq hT
  · intro hr
    obtain ⟨T, J, hT, lower, F, hF, eqF⟩ := sharp_family K r s
    let n := Module.finrank K (alternatingForms K (Model K r s))
    have ht := T.finrank_quotient_add_finrank
    rw [hT] at ht
    have hk : n - d ≤ Module.finrank K T := by dsimp [n]; omega
    obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := T) hk
    let U := Submodule.span K (Set.range g)
    let S := U.map T.subtype
    have hu : Module.finrank K U = n - d := by
      simpa [U] using finrank_span_eq_card hg
    have hs : Module.finrank K S = n - d := by
      rw [← hu]
      exact (U.equivMapOfInjective T.subtype Subtype.val_injective).finrank_eq.symm
    have hsub : S ≤ T := by rintro _ ⟨u, _, rfl⟩; exact u.property
    refine ⟨S, F, ?_, eqF, ?_⟩
    · have h := S.finrank_quotient_add_finrank
      rw [hs] at h
      change _ + (n - d) = n at h
      change d ≤ n at bound
      omega
    · intro A hA
      exact lower A (by simpa only [sub_add_sub_cancel] using T.add_mem (hsub hA) hF)

end Green50AlternatingRank

#print axioms Green50AlternatingRank.dimension
#print axioms Green50AlternatingRank.exists_rank_le
#print axioms Green50AlternatingRank.codimension_of_lower_rank
#print axioms Green50AlternatingRank.sharp_family
#print axioms Green50AlternatingRank.minimum_rank_at_codimension
#print axioms Green50AlternatingRank.quotient_span
#print axioms Green50AlternatingRank.class_rank_of_rep
#print axioms Green50AlternatingRank.quotient_alt
