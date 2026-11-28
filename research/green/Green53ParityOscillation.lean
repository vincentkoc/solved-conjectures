import Green53ParityThresholds

/-! # Oscillation of weighted sign sums on affine parity slices -/
open Finset Green53ParityThreshold Green53Threshold
open scoped Classical Pointwise
namespace Green53ParityOscillation

/-- A set of at most twice the check rank, chosen independently of the weights
and the coset, suffices to bound the full possible oscillation from below. -/
theorem slice_oscillation {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (S : Finset J) :
    ∃ T⊆S, T.card≤2*Module.finrank F V ∧ ∀ (anchor : J → F) (a : J → ℝ),
      ∃ x y : J → F, Q x=Q anchor ∧ Q y=Q anchor ∧
        (∀ j,j∉S → x j=anchor j ∧ y j=anchor j) ∧
        2*(∑ j∈S\T, |a j|) ≤ (∑ j∈S,a j*spin (x j))-(∑ j∈S,a j*spin (y j)) := by
  classical
  obtain ⟨P,ps,pc,repP⟩ := sparse_correction Q S
  obtain ⟨R,rs,rc,repR⟩ := sparse_correction Q (S\P)
  let T := P∪R
  let U := S\T
  have us : U⊆S := sdiff_subset
  have up : U⊆S\P := by
    intro j hj
    exact mem_sdiff.mpr ⟨us hj,fun hp => (mem_sdiff.mp hj).2 (mem_union_left _ hp)⟩
  refine ⟨T,union_subset ps (rs.trans sdiff_subset),(card_union_le (s:=P) (t:=R)).trans (by omega),?_⟩
  intro anchor a
  let bits (j : J) : F := if j∈U then 1 else 0
  obtain ⟨v,vs,ve⟩ := repR bits (by intro j hj; exact if_neg (fun h => hj (up h)))
  let d := bits-v
  have dz : Q d=0 := by simp [d,ve]
  have ds (j : J) (hj : j∉S\P) : d j=0 := by
    have nu : j∉U := fun h => hj (up h)
    have nr : j∉R := fun h => hj (rs h)
    simp [d,bits,nu,vs j nr]
  have du (j : J) (hj : j∈U) : d j=1 := by
    have nr : j∉R := fun h => (mem_sdiff.mp hj).2 (mem_union_right _ h)
    simp [d,bits,hj,vs j nr]
  let orient (j : J) : F := if 0≤a j then 0 else 1
  let z (j : J) := if j∈S\P then orient j else anchor j
  obtain ⟨u,uf,uq⟩ := repP (z-anchor) (by
    intro j hj; have no : j∉S\P := fun h => hj (mem_sdiff.mp h).1
    simp only [Pi.sub_apply,z,if_neg no,sub_self])
  let x := z-u
  have xq : Q x=Q anchor := by change Q (z-u)=Q anchor; rw [map_sub,uq,map_sub]; abel
  have fixed (j : J) (hj : j∉S) : x j=anchor j := by
    have nsp : j∉S\P := fun h => hj (mem_sdiff.mp h).1
    simp only [x,Pi.sub_apply,z,if_neg nsp,uf j (fun h => hj (ps h)),sub_zero]
  have row (j : J) : a j*spin (x j)-a j*spin ((x+d) j) =
      if d j=0 then 0 else 2*|a j| := by
    by_cases h : d j=0
    · simp [h]
    · have hsp : j∈S\P := by by_contra nh; exact h (ds _ nh)
      have xo : x j=orient j := by simp only [x,Pi.sub_apply,z,if_pos hsp,uf _ (mem_sdiff.mp hsp).2,sub_zero]
      rw [Pi.add_apply,spin_add,if_pos h,if_neg h,xo]
      by_cases pos : 0≤a j
      · simp [orient,pos,spin,abs_of_nonneg pos]; ring
      · simp [orient,pos,spin,abs_of_neg (lt_of_not_ge pos)]; ring
  refine ⟨x,x+d,xq,by rw [map_add,xq,dz,add_zero],?_,?_⟩
  · intro j hj; have h := ds j (fun m => hj (mem_sdiff.mp m).1)
    simp [fixed j hj,h]
  · rw [←sum_sub_distrib]
    calc
      _ = ∑ j∈U, (if d j=0 then 0 else 2*|a j|) := by
        rw [mul_sum]
        exact sum_congr rfl (fun j hj => by simp [du j hj])
      _ ≤ ∑ j∈S, (if d j=0 then 0 else 2*|a j|) := sum_le_sum_of_subset_of_nonneg us
        (fun j _ _ => by split <;> positivity)
      _ = _ := sum_congr rfl (fun j _ => (row j).symm)
end Green53ParityOscillation
#print axioms Green53ParityOscillation.slice_oscillation
