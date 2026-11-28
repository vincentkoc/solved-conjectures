import Green51RootedAffineSets

/-! # Counting subsets in level-one affine hyperplanes by dimension -/

namespace Green51AffineEnumeration
open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical

theorem affine_count_succ (n k : ℕ) (pos : 0<k) :
    affineCount (𝔽₂ (n+1)) k =
      (2^(n+1)-1)*((2^n).choose k - affineCount (𝔽₂ n) k) := by
  classical
  let G := 𝔽₂ (n+1)
  let H := 𝔽₂ n
  let : Finite (Module.Dual F G) := Finite.of_injective (fun f : Module.Dual F G => (f : G → F)) DFunLike.coe_injective
  let : Fintype (Module.Dual F G) := Fintype.ofFinite _
  let K := rootedSets G k
  let fs := (univ : Finset (Module.Dual F G)).erase 0
  let V (E : Finset G) := ((Submodule.span F (E : Set G)) : Set G).toFinset.card
  let killedBy (f : Module.Dual F G) (E : Finset G) : Prop := ∀ x ∈ E, f x=0
  have ambient : Module.finrank F G=n+1 := by simp [G,𝔽₂,𝔽]
  have hdim : Module.finrank F H=n := by simp [H,𝔽₂,𝔽]
  have hc : Fintype.card H=2^n := by simp [H,𝔽₂,𝔽]
  have fc : fs.card=2^(n+1)-1 := by
    rw [card_erase_of_mem (mem_univ _),card_univ,Module.card_eq_pow_finrank (K := F),Subspace.dual_finrank_eq,ambient]
    rfl
  have incidence (E : Finset G) : (∑ f ∈ fs, if killedBy f E then V E else 0) = Fintype.card G-V E := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    have eq : fs.filter (fun f => killedBy f E) = univ.filter (fun f : Module.Dual F G => f≠0 ∧ ∀ x ∈ E, f x=0) := by
      ext f; simp [fs,killedBy]
    rw [eq]
    exact annihilator_weight E
  have each (f : Module.Dual F G) (hf : f ∈ fs) :
      (∑ E ∈ K, if killedBy f E then V E else 0) = k*((2^n).choose k-affineCount H k) := by
    have nonzero := (mem_erase.mp hf).1
    have rank := Module.Dual.finrank_ker_add_one_of_ne_zero nonzero
    let l : H ≃ₗ[F] f.ker := LinearEquiv.ofFinrankEq H f.ker (by omega)
    let j : H →ₗ[F] G := f.ker.subtype.comp l.toLinearMap
    have range_j : j.range=f.ker := by
      ext x; constructor
      · rintro ⟨v,rfl⟩; exact (l v).property
      · intro hx
        exact ⟨l.symm ⟨x,hx⟩,congrArg Subtype.val (l.apply_symm_apply ⟨x,hx⟩)⟩
    have transfer := rooted_image_sum j (Subtype.val_injective.comp l.injective) k
    rw [range_j] at transfer
    have cond : K.filter (killedBy f) = (rootedSets G k).filter (fun E => ∀ x ∈ E, x ∈ f.ker) := by
      ext E; simp only [mem_filter,LinearMap.mem_ker,K,killedBy]
    have sumH := (affine_rooted_sums H k).2
    rw [hc] at sumH
    rw [←sum_filter,cond]
    exact transfer.trans sumH.symm
  have result : k*affineCount G k = k*((2^(n+1)-1)*((2^n).choose k-affineCount H k)) := by
    calc
      _ = ∑ E ∈ K, (Fintype.card G-V E) := (affine_rooted_sums G k).1
      _ = ∑ E ∈ K, ∑ f ∈ fs, if killedBy f E then V E else 0 := sum_congr rfl fun E _ => (incidence E).symm
      _ = ∑ f ∈ fs, ∑ E ∈ K, if killedBy f E then V E else 0 := sum_comm
      _ = _ := by
        rw [sum_congr rfl each,sum_const,nsmul_eq_mul,fc]
        exact Nat.mul_left_comm _ _ _
  exact Nat.eq_of_mul_eq_mul_left pos result
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.affine_count_succ


namespace Green51AffineEnumeration
open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical

/-- Number of nonempty fixed-cardinality subsets in some level-one hyperplane. -/
def affineNumber (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => (2^(n+1)-1)*((2^n).descFactorial k / k.factorial - affineNumber k n)

theorem affineCount_eq_number (n k : ℕ) (pos : 0<k) : affineCount (𝔽₂ n) k = affineNumber k n := by
  induction n with
  | zero =>
    classical
    unfold affineCount
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro D hD
    obtain ⟨num,f,ones⟩ := mem_filter.mp hD
    have hsize := (mem_powersetCard.mp num).2
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<D.card by omega)
    have x0 : x=0 := Subsingleton.elim _ _
    exact zero_ne_one ((map_zero f).symm.trans (x0 ▸ ones x hx))
  | succ n ih =>
    rw [affine_count_succ n k pos,ih,affineNumber,Nat.choose_eq_descFactorial_div_factorial]
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.affineCount_eq_number
