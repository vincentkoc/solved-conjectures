import Green51OmissionSpan
import Green51WordEmbeddings

/-! # Stabilization of finite configurations under an enlargement of the common fibre -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold
open scoped Classical
variable {I H K : Type*} [Fintype I] [AddCommGroup H] [Module F H] [Fintype H]
    [AddCommGroup K] [Module F K] [Fintype K] [DecidableEq K]

omit [Fintype I] in
private theorem sum_pred_le (a : I → ℕ) (B : Finset I) :
    ∑ i∈B,(a i-1) ≤ (∑ i∈B,a i)-1 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | @insert j S hj ih => rw [sum_insert hj,sum_insert hj];omega

omit [DecidableEq K] in
private theorem move_span (P : Submodule F K) (f : H →ₗ[F] K) (inj : Function.Injective f)
    (rank : Module.finrank F P≤Module.finrank F H) :
    ∃ u : K ≃ₗ[F] K,∀ x∈P,u x∈LinearMap.range f := by
  obtain ⟨a,ha⟩ := finrank_le_iff_exists_linearMap.mp rank
  let j := f.comp a
  let v := LinearEquiv.ofInjective j (inj.comp ha)
  obtain ⟨u,hu⟩ := Submodule.exists_linearEquiv_restrict_eq v
  exact ⟨u,fun x hx => ⟨a ⟨x,hx⟩,hu ⟨x,hx⟩⟩⟩

/-- For fixed total number of sites, every larger-space word comes from a smaller space
as soon as its dimension covers the sum of the row sizes minus one in each nonempty row. -/
theorem compress_word (f : H →ₗ[F] K) (inj : Function.Injective f) (w : I → Finset K)
    (enough : (∑ i,((w i).card-1))≤Module.finrank F H) :
    ∃ a : I → Finset H, (∀ i,(a i).card=(w i).card) ∧
      WordMatch w (fun i => (a i).map ⟨f,inj⟩) := by
  classical
  obtain ⟨P,c,r,inside⟩ := common_omission_span univ w
  obtain ⟨u,hu⟩ := move_span P f inj (r.trans enough)
  let e (i : I) := (u.toEquiv.trans (Equiv.addRight (-u (c i)))).toEmbedding
  let m (i : I) := (w i).map (e i)
  have covered (i : I) (x : K) (hx : x∈m i) : x∈LinearMap.range f := by
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hx
    change u z + -u (c i)∈LinearMap.range f
    rw [←sub_eq_add_neg,←map_sub]
    exact hu (z-c i) (inside i (mem_univ _) z hz)
  let a (i : I) := univ.filter fun z => f z∈m i
  have fill (i : I) : (a i).map ⟨f,inj⟩=m i := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
      exact (mem_filter.mp hy).2
    · intro hx
      obtain ⟨y,rfl⟩ := covered i x hx
      exact mem_map.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,hx⟩,rfl⟩
  refine ⟨a,fun i => ?_,Equiv.refl _,u,fun i => -u (c i),fun i => (fill i).symm⟩
  simpa only [m,card_map] using congrArg card (fill i)

theorem compress_of_total (f : H →ₗ[F] K) (inj : Function.Injective f) (w : I → Finset K)
    (enough : (∑ i,(w i).card)-1≤Module.finrank F H) :
    ∃ a : I → Finset H, (∀ i,(a i).card=(w i).card) ∧
      WordMatch w (fun i => (a i).map ⟨f,inj⟩) :=
  compress_word f inj w ((sum_pred_le (fun i => (w i).card) univ).trans enough)

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.compress_word
#print axioms Green51FrameIsomorphisms.compress_of_total
