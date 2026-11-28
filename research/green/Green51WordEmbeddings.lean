import Green51RowDifferenceKernels

/-! # Injectivity on unlabelled row types under an enlargement of the fibre space -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical
variable {I J H K : Type*} [AddCommGroup H] [Module F H] [DecidableEq H]
    [AddCommGroup K] [Module F K] [DecidableEq K]

/-- Rows may be permuted. Their independent translations share one linear part. -/
def WordMatch (A : I → Finset H) (B : J → Finset H) : Prop :=
  ∃ (σ : I ≃ J) (u : H ≃ₗ[F] H) (t : I → H), ∀ i,
    (A i).map ((u.toEquiv.trans (Equiv.addRight (t i))).toEmbedding)=B (σ i)

omit [AddCommGroup K] [Module F K] [DecidableEq K] in
private theorem maps_eq_iff {V W : Type*} (A : Finset V) (B : Finset W) (p : V ↪ K) (q : W ↪ K) :
    A.map p=B.map q ↔ ∃ τ : ↥A ≃ ↥B, ∀ x : A,p x=q (τ x) := by
  constructor
  · intro eq
    let E := Equiv.setCongr (congrArg (fun C : Finset K => (C : Set K)) eq)
    let τ := ((A.equivMap p).trans E).trans (B.equivMap q).symm
    refine ⟨τ,fun x => ?_⟩
    exact (congrArg Subtype.val ((B.equivMap q).apply_symm_apply (E (A.equivMap p x)))).symm
  · rintro ⟨τ,h⟩
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      exact mem_map.mpr ⟨_,(τ ⟨v,hv⟩).property,(h ⟨v,hv⟩).symm⟩
    · intro hx
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hx
      let v := τ.symm ⟨w,hw⟩
      exact mem_map.mpr ⟨_,v.property,(h v).trans (congrArg (fun k : B => q k.val) (τ.apply_symm_apply ⟨w,hw⟩))⟩

omit [AddCommGroup H] [Module F H] [DecidableEq H] [DecidableEq K] in
private theorem embedded_labels (A : I → Finset H) (B : J → Finset H) (f : H ↪ K) :
    WordMatch (fun i => (A i).map f) (fun j => (B j).map f) ↔
      ∃ (σ : I ≃ J) (τ : ∀ i, ↥(A i) ≃ ↥(B (σ i))) (u : K ≃ₗ[F] K) (t : I → K),
        ∀ i (x : A i),u (f x.val)+t i=f (τ i x).val := by
  classical
  constructor
  · rintro ⟨σ,u,t,hm⟩
    let e (i : I) := (u.toEquiv.trans (Equiv.addRight (t i))).toEmbedding
    have hh (i : I) := (maps_eq_iff (A i) (B (σ i)) (f.trans (e i)) f).mp
      ((map_map f (e i) (A i)).symm.trans (hm i))
    choose τ act using hh
    exact ⟨σ,τ,u,t,act⟩
  · rintro ⟨σ,τ,u,t,h⟩
    refine ⟨σ,u,t,fun i => ?_⟩
    rw [map_map]
    exact (maps_eq_iff _ _ _ _).mpr ⟨τ i,h i⟩

omit [DecidableEq H] [DecidableEq K] in
/-- Arbitrary row permutations and relabellings create precisely the same equivalences
after the whole configuration is embedded into a larger binary vector space. -/
theorem word_embedding_iff [FiniteDimensional F H] [FiniteDimensional F K]
    (A : I → Finset H) (B : J → Finset H) (f : H →ₗ[F] K) (inj : Function.Injective f) :
    WordMatch (fun i => (A i).map ⟨f,inj⟩) (fun j => (B j).map ⟨f,inj⟩) ↔ WordMatch A B := by
  rw [embedded_labels]
  have base := embedded_labels A B (Function.Embedding.refl H)
  simp only [map_refl,Function.Embedding.refl_apply] at base
  rw [base]
  apply exists_congr
  intro σ
  apply exists_congr
  intro τ
  exact row_embedding_iff f inj (fun i (x : A i) => x.val) (fun i x => (τ i x).val)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.word_embedding_iff
