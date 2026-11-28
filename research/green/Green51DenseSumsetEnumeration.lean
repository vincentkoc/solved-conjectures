import Green51MissingMaskClassification
import Green51CircuitFrameCount
import Green51SectionDimension

/-! # Exact enumeration of dense doubles with largest affine dimension two below ambient -/

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51GirthFrame
open scoped Classical Pointwise

theorem dense_sumset_section_count {s r : ℕ} (hs : 5 ≤ s) (k : ℕ)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) :
    let G := 𝔽₂ (2*(s+1)+r)
    let g := 2*s+3
    ((((univ : Finset G).powersetCard k).filter (fun D =>
      (¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x=1) ∧
      ∃ A : Finset G, (A+A)ᶜ=D ∧ threshold (2*s) < (A.dens : ℝ))).card : ℤ) =
      (circuitFrames G g).card * ∑ j ∈ range (g+1), ((g.choose j : ℕ) : ℤ) *
        ((-1 : ℤ)^j * (((g-j)*2^r).choose k : ℕ)) := by
  classical
  let G := 𝔽₂ (2*(s+1)+r)
  let g := 2*s+3
  have rank : Module.finrank F G = 2*(s+1)+r := by simp [G,𝔽₂,𝔽]
  have free : Module.finrank F G + 1-g = r := by dsimp only [g]; omega
  have order := count_global_sections (G := G) g k (by dsimp [g]; omega) ⟨s+1,by dsimp [g]; omega⟩
    (by simpa only [free,g] using near)
  rw [free] at order
  refine Eq.trans ?_ order
  congr 2
  apply filter_congr
  intro D mem
  have sz := (mem_powersetCard.mp mem).2
  constructor <;> rintro ⟨no,h⟩
  · exact ⟨no,(realizable_iff_odd_girth hs D no (by simpa only [sz] using near)).mp h⟩
  · exact ⟨no,(realizable_iff_odd_girth hs D no (by simpa only [sz] using near)).mpr h⟩
end Green51MissingMasks
#print axioms Green51MissingMasks.dense_sumset_section_count

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51GirthFrame
open scoped Classical Pointwise

/-- Distinct sumsets at the specified density whose largest affine subspace has codimension two. -/
noncomputable def countedDoubles (n k : ℕ) (α : ℝ) : Finset (Finset (𝔽₂ n)) :=
  univ.filter fun S => Sᶜ.card=k ∧ maxCosetDim F (𝔽₂ n) ↑S=n-2 ∧
    ∃ A : Finset (𝔽₂ n), A+A=S ∧ α < (A.dens : ℝ)

/-- A closed formula for the number of distinct sumsets in the prescribed missing-count band. -/
theorem count_dense_doubles {s r : ℕ} (hs : 5 ≤ s) (k : ℕ)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) :
    let n := 2*(s+1)+r
    let g := 2*s+3
    ((countedDoubles n k (threshold (2*s))).card : ℤ)*g.factorial =
      ((∏ i : Fin (2*(s+1)), (2^n-2^i.val : ℕ)) : ℕ) *
        ∑ j ∈ range (g+1), ((g.choose j : ℕ) : ℤ) *
          ((-1 : ℤ)^j * (((g-j)*2^r).choose k : ℕ)) := by
  classical
  let n := 2*(s+1)+r
  let G := 𝔽₂ n
  let g := 2*s+3
  let ds := ((univ : Finset G).powersetCard k).filter (fun D =>
    (¬∃ f : G →ₗ[F] F, ∀ x ∈ D, f x=1) ∧ ∃ A : Finset G, (A+A)ᶜ=D ∧ threshold (2*s) < (A.dens : ℝ))
  have rank : Module.finrank F G = n := by simp [G,𝔽₂,𝔽]
  have remsz : n+1-g=r := by dsimp [n,g]; omega
  have criterion (A : Finset G) (ha : threshold (2*s) < (A.dens : ℝ)) (size : (A+A)ᶜ.card = k) :
      maxCosetDim F G ↑(A+A)=n-2 ↔ ¬∃ f : G →ₗ[F] F, ∀ x ∈ (A+A)ᶜ, f x=1 := by
    have short := girth_of_density A s ha
    have h := near_girth_dimension (n := n) (g := g) (by dsimp [n]; omega) (A+A)ᶜ
      (by dsimp [g]; omega) ⟨s+1,by dsimp [g]; omega⟩
      (by simpa only [g,show 2*(s+1)+1=2*s+3 by omega] using short)
      (by simpa only [size,remsz,g] using near)
    simpa only [compl_compl] using h
  have same : (countedDoubles n k (threshold (2*s))).card=ds.card := by
    apply card_bij (fun S _ => Sᶜ)
    · intro S hS
      obtain ⟨sz,dim,A,rfl,ha⟩ := (mem_filter.mp hS).2
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,sz⟩,(criterion A ha sz).mp dim,A,rfl,ha⟩
    · intro S _ T _ eq
      simpa only [compl_compl] using congrArg (fun V : Finset G => Vᶜ) eq
    · intro D hD
      obtain ⟨bound,no,A,rfl,ha⟩ := mem_filter.mp hD
      have size := (mem_powersetCard.mp bound).2
      exact ⟨A+A,mem_filter.mpr ⟨mem_univ _,size,(criterion A ha size).mpr no,A,rfl,ha⟩,rfl⟩
  have sectionCount := dense_sumset_section_count hs k near
  change (ds.card : ℤ) = _ at sectionCount
  have frames := count_circuit_frames G s (by omega) (by rw [rank]; dsimp [n]; omega)
  rw [rank] at frames
  dsimp only
  rw [show 2*(s+1)+r=n from rfl,same,sectionCount]
  push_cast [←frames]
  ring
end Green51MissingMasks
#print axioms Green51MissingMasks.count_dense_doubles

namespace Green51MissingMasks
open Finset Green51Hyperplane
open scoped Classical

private theorem count_at_forty_one_arithmetic :
    (((∏ i : Fin 14, (2^16-2^i.val : ℕ)) : ℕ) : ℤ) *
      (∑ j ∈ range 16, ((Nat.choose 15 j : ℕ) : ℤ) * ((-1 : ℤ)^j * (((15-j)*2^2).choose 41 : ℕ))) =
      (28695069593324713072606999769402841169720190563177645847462610468864000 : ℤ)*(Nat.factorial 15 : ℕ) := by
  simp_rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

/-- Distinct doubles in dimension 16 with 41 missing directions and largest affine dimension 14. -/
theorem count_at_forty_one :
    (countedDoubles 16 41 (threshold 12)).card = 28695069593324713072606999769402841169720190563177645847462610468864000 := by
  have h := count_dense_doubles (s := 6) (r := 2) (by decide) 41 (by decide)
  have spec : (((countedDoubles 16 41 (threshold 12)).card : ℤ) * (Nat.factorial 15 : ℕ)) =
      (28695069593324713072606999769402841169720190563177645847462610468864000 : ℤ)*(Nat.factorial 15 : ℕ) :=
    h.trans count_at_forty_one_arithmetic
  apply (Nat.cast_injective (R := ℤ))
  exact mul_right_cancel₀ (by positivity : ((Nat.factorial 15 : ℕ) : ℤ) ≠ 0) spec
end Green51MissingMasks
#print axioms Green51MissingMasks.count_at_forty_one
