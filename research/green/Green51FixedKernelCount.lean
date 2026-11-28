import Green51QuotientFlatDimension

/-! # Counting dense sumsets invariant under the kernel of a quotient -/

namespace Green51PeriodQuotients
open Finset Green53ParityThreshold Green51MissingMasks Green51OriginRecovery
open scoped Classical Pointwise
variable {G H : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]
  [AddCommGroup H] [Module F H] [Fintype H] [DecidableEq H]

omit [DecidableEq G] [Fintype H] in
/-- A full inverse image is invariant under its kernel. -/
theorem pull_fixed (f : G →ₗ[F] H) (T : Finset H) (t : G) (ht : t∈f.ker) :
    translate (pull f T) t=pull f T := by
  classical
  ext x
  obtain ⟨y,rfl⟩ := (Equiv.addRight t).surjective x
  simp only [Green51OriginRecovery.translate,Finset.mem_map_equiv,Equiv.symm_apply_apply,mem_pull]
  change f y∈T ↔ f (y+t)∈T
  rw [map_add,LinearMap.mem_ker.mp ht,add_zero]

omit [DecidableEq G] [Fintype H] in
/-- Every set invariant under the kernel is recovered losslessly from its quotient image. -/
theorem saturated (f : G →ₗ[F] H) (S : Finset G) (fixed : ∀ t∈f.ker, translate S t=S) :
    pull f (S.image f)=S := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y,hy,eq⟩ := mem_image.mp ((mem_pull _ _ _).mp hx)
    have good : x-y∈f.ker := LinearMap.mem_ker.mpr (by rw [map_sub,eq,sub_self])
    rw [←fixed _ good]
    exact mem_map.mpr ⟨y,hy,by change y+(x-y)=x;abel⟩
  · exact fun hx => (mem_pull _ _ _).mpr (mem_image_of_mem _ hx)

omit [DecidableEq G] [Fintype H] [DecidableEq H] in
private theorem kernel_card (f : G →ₗ[F] H) :
    (f.ker : Set G).toFinset.card=2^(Module.finrank F f.ker) := by
  rw [Set.toFinset_card]
  change Fintype.card f.ker=_
  rw [Module.card_eq_pow_finrank (K := F),ZMod.card]

/-- Removing a full period subspace preserves dense realizability and affine codimension. -/
theorem counted_pull_iff {n h k : ℕ} (dim : 3 ≤ n)
    (f : (𝔽₂ (n+h)) →ₗ[F] (𝔽₂ n)) (onto : Function.Surjective f)
    (rank : Module.finrank F f.ker=h) (T : Finset (𝔽₂ n)) (α : ℝ) :
    pull f T∈countedDoubles (n+h) (2^h*k) α ↔ T∈countedDoubles n k α := by
  classical
  simp only [countedDoubles,mem_filter,mem_univ,true_and, pull_compl,card_pull f onto,kernel_card,rank,
    dense_double_pull_iff f onto]
  have pos : 0<2^h := by positivity
  by_cases live : T.Nonempty
  · rw [max_dimension_pull f onto T live,rank]
    have same : h+maxCosetDim F (𝔽₂ n) ↑T=n+h-2 ↔ maxCosetDim F (𝔽₂ n) ↑T=n-2 := by omega
    rw [same,Nat.mul_right_inj (Nat.ne_of_gt pos)]
  · have emp := not_nonempty_iff_eq_empty.mp live
    subst T
    have empty : pull f (∅ : Finset (𝔽₂ n))=∅ := by ext x;simp
    simp only [empty,coe_empty,maxCosetDim_empty]
    have hn : n-2≠0 := by omega
    have hh : n+h-2≠0 := by omega
    simp [Ne.symm hn,Ne.symm hh]

/-- Exact number of counted doubles with a prescribed period subspace. Distinct preimages
correspond to distinct quotient outputs even when the quotient has more periods. -/
theorem fixed_kernel_count {n h k : ℕ} (dim : 3 ≤ n)
    (f : (𝔽₂ (n+h)) →ₗ[F] (𝔽₂ n)) (onto : Function.Surjective f)
    (rank : Module.finrank F f.ker=h) (α : ℝ) :
    ((countedDoubles (n+h) (2^h*k) α).filter
      (fun S => ∀ t∈f.ker, translate S t=S)).card=(countedDoubles n k α).card := by
  classical
  symm
  apply card_bij (fun T _ => pull f T)
  · intro T hT
    exact mem_filter.mpr ⟨(counted_pull_iff dim f onto rank T α).mpr hT,pull_fixed f T⟩
  · intro T _ U _ eq
    simpa only [image_pull f onto] using congrArg (fun S : Finset (𝔽₂ (n+h)) => S.image f) eq
  · intro S hS
    obtain ⟨h,stable⟩ := mem_filter.mp hS
    have eq := saturated f S stable
    exact ⟨_,(counted_pull_iff dim f onto rank (S.image f) α).mp (eq.symm ▸ h),eq⟩

/-- An invariant output can omit only a multiple of the kernel order. -/
theorem period_divides_missing (f : G →ₗ[F] H) (onto : Function.Surjective f)
    (S : Finset G) (stable : ∀ t∈f.ker, translate S t=S) :
    2^Module.finrank F f.ker ∣ Sᶜ.card := by
  have sz := card_pull f onto (S.image f)ᶜ
  rw [←pull_compl,saturated f S stable,kernel_card] at sz
  exact ⟨_,sz⟩

theorem projection_with_kernel {n h : ℕ} (P : Submodule F (𝔽₂ (n+h)))
    (rank : Module.finrank F P=h) :
    ∃ f : 𝔽₂ (n+h) →ₗ[F] 𝔽₂ n, Function.Surjective f ∧ f.ker=P := by
  classical
  have dims := P.finrank_quotient_add_finrank
  have amb : Module.finrank F (𝔽₂ (n+h))=n+h := by simp [𝔽₂,𝔽]
  have tgt : Module.finrank F (𝔽₂ n)=n := by simp [𝔽₂,𝔽]
  let e : ((𝔽₂ (n+h)) ⧸ P) ≃ₗ[F] (𝔽₂ n) := LinearEquiv.ofFinrankEq _ _ (by omega)
  exact ⟨e.toLinearMap.comp P.mkQ,e.surjective.comp P.mkQ_surjective,
    (LinearMap.ker_comp_of_ker_eq_bot P.mkQ e.ker).trans P.ker_mkQ⟩

theorem fixed_line_iff {n : ℕ} (t : 𝔽₂ n) (S : Finset (𝔽₂ n)) :
    (∀ b∈(F ∙ t), translate S b=S) ↔ translate S t=S := by
  constructor
  · exact fun stable => stable t (Submodule.mem_span_singleton_self _)
  · rintro stable b hb
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hb
    have binary : ∀ i : F, i=0 ∨ i=1 := by decide
    rcases binary a with rfl | rfl
    · simpa only [zero_smul] using translate_zero S
    · simpa only [one_smul] using stable

end Green51PeriodQuotients
#print axioms Green51PeriodQuotients.pull_fixed
#print axioms Green51PeriodQuotients.saturated
#print axioms Green51PeriodQuotients.counted_pull_iff
#print axioms Green51PeriodQuotients.fixed_kernel_count
#print axioms Green51PeriodQuotients.period_divides_missing
#print axioms Green51PeriodQuotients.projection_with_kernel
#print axioms Green51PeriodQuotients.fixed_line_iff
