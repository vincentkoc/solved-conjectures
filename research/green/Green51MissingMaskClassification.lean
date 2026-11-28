import Green51HammingMasks
import Green51CircuitEquivalence
import Green51MissingStability

/-! # Odd-girth recognition for the missing set of a dense binary double -/

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51GirthFrame
open scoped Classical Pointwise
private theorem transport_double {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
    (l : G ≃ₗ[F] G) (A : Finset G) (z : G) :
    l z ∈ A.map l.toEquiv.toEmbedding + A.map l.toEquiv.toEmbedding ↔ z ∈ A+A := by
  constructor
  · intro hz
    obtain ⟨a,ha,b,hb,eq⟩ := mem_add.mp hz
    obtain ⟨x,hx,rfl⟩ := mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hb
    exact mem_add.mpr ⟨x,hx,y,hy,l.injective ((l.map_add x y).trans eq)⟩
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := mem_add.mp hz
    exact mem_add.mpr ⟨_,mem_map_of_mem _ hx,_,mem_map_of_mem _ hy,(l.map_add x y).symm⟩

theorem realize_in_container {s r : ℕ} (hs : 5 ≤ s) {C D : Finset (𝔽₂ (2*(s+1)+r))}
    (m : ShortestOddCircuit D C) (len : C.card = 2*s+3)
    (P : Submodule F (𝔽₂ (2*(s+1)+r))) (comp : IsCompl P (Submodule.span F (C : Set _)))
    (J : Finset (𝔽₂ (2*(s+1)+r))) (sub : J ⊆ (P : Set _).toFinset + C) :
    ∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ = J ∧ threshold (2*s) < (A.dens : ℝ) := by
  classical
  let G := 𝔽₂ (2*(s+1)+r)
  let H := ball (s+1) r
  have large := density_after_edit (r := r) hs H (by dsimp [H]; omega)
  obtain ⟨_,size,avoid⟩ := hamming_ball_data (s+1) r
  have hit : (2*s+3)*2^r ≤ (H+H)ᶜ.card := by change _ ≤ (ball (s+1) r+ball (s+1) r)ᶜ.card; rw [size]; ring_nf; omega
  obtain ⟨C0,m0,len0,P0,r0,comp0,full0⟩ := missing_circuit (by omega : 0<s) H large avoid hit
  have rC := circuit_rank m
  have rP := Submodule.finrank_add_eq_of_isCompl comp
  have amb : Module.finrank F G = 2*(s+1)+r := by simp [G,𝔽₂,𝔽]
  change _ + _ = Module.finrank F G at rP
  obtain ⟨l, matchC⟩ := container_equiv m0 m (len0.trans len.symm) P0 P (by omega) comp0 comp
  have full : (H+H)ᶜ = (P0 : Set G).toFinset + C0 := by
    ext z
    rw [full0, mem_add]
    constructor
    · rintro ⟨x,hx,i,hi,eq⟩
      exact ⟨x,Set.mem_toFinset.mpr hx,i,hi,eq.symm⟩
    · rintro ⟨x,hx,i,hi,eq⟩
      exact ⟨x,Set.mem_toFinset.mp hx,i,hi,eq.symm⟩
  let J0 := J.map l.symm.toEquiv.toEmbedding
  have sub0 : J0 ⊆ (H+H)ᶜ := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hz
    have inU := sub hy
    rw [←matchC] at inU
    obtain ⟨x,hx,eq⟩ := mem_map.mp inU
    rw [full]
    change l.symm y ∈ _
    rw [show l.symm y = x from l.symm_apply_eq.mpr eq.symm]
    exact hx
  obtain ⟨A,actual,dens,_,_⟩ := realize_cylinder_mask hs J0 sub0
  refine ⟨A.map l.toEquiv.toEmbedding, ?_, ?_⟩
  · ext y; obtain ⟨x,rfl⟩ := l.surjective y
    rw [mem_compl, transport_double, ←mem_compl,actual]
    change x ∈ J.map l.symm.toEquiv.toEmbedding ↔ l x ∈ J
    simp [Finset.mem_map_equiv]
  · simpa [Finset.dens] using dens

theorem realizable_iff_odd_girth {s r : ℕ} (hs : 5 ≤ s) (D : Finset (𝔽₂ (2*(s+1)+r)))
    (no : ¬∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ D, f x = 1)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20) * 2^r < 8*D.card) :
    (∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ = D ∧ threshold (2*s) < (A.dens : ℝ)) ↔
      ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → 2*s+3 ≤ R.card := by
  classical
  constructor
  · rintro ⟨A,rfl,large⟩
    simpa [show 2*(s+1)+1 = 2*s+3 by omega] using girth_of_density A s large
  · intro short
    have amb : Module.finrank F (𝔽₂ (2*(s+1)+r)) = 2*(s+1)+r := by simp [𝔽₂,𝔽]
    obtain ⟨C,m,len,P,comp,great,_⟩ := greatest_girth_extension D (2*s+3) (by omega) (by exact ⟨s+1, by omega⟩) short no
      (by rwa [amb, show 2*(s+1)+r+1-(2*s+3)=r by omega])
    exact realize_in_container hs m len P comp D great.1.1

end Green51MissingMasks
#print axioms Green51MissingMasks.realize_in_container
#print axioms Green51MissingMasks.realizable_iff_odd_girth

namespace Green51MissingMasks
open Finset Green53ParityThreshold Green51Hyperplane Green51GirthFrame
open scoped Classical Pointwise

private theorem small_frame {s : ℕ} (hs : 5 ≤ s) : 4*(2*s+3) < 2^(2*(s+1)) := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s _ ih =>
    rw [show 2*(s+1+1) = 2*(s+1)+2 by omega,pow_add]
    norm_num
    omega

/-- Within the extremal count band the odd zero sums characterize all possible missing sets. -/
theorem realizable_iff_in_band {s r : ℕ} (hs : 5 ≤ s) (D : Finset (𝔽₂ (2*(s+1)+r)))
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20) * 2^r < 8*D.card)
    (cap : D.card ≤ (2*s+3)*2^r) :
    (∃ A : Finset (𝔽₂ (2*(s+1)+r)), (A+A)ᶜ = D ∧ threshold (2*s) < (A.dens : ℝ)) ↔
      ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x) = 0 → 2*s+3 ≤ R.card := by
  classical
  by_cases aff : ∃ f : (𝔽₂ (2*(s+1)+r)) →ₗ[F] F, ∀ x ∈ D, f x = 1
  · obtain ⟨f,level⟩ := aff
    obtain ⟨t,ht⟩ := card_pos.mp (show 0 < D.card by omega)
    have ambient : Fintype.card (𝔽₂ (2*(s+1)+r)) = 2^(2*(s+1)+r) := by simp [𝔽₂,𝔽]
    have thin : 4*D.card < Fintype.card (𝔽₂ (2*(s+1)+r)) := by
      rw [ambient,pow_add]
      calc
        _ ≤ 4*((2*s+3)*2^r) := Nat.mul_le_mul_left _ cap
        _ = (4*(2*s+3))*2^r := by ring
        _ < _ := Nat.mul_lt_mul_of_pos_right (small_frame hs) (by positivity)
    obtain ⟨A,full,sz⟩ := realize_affine D f t (level t ht) level thin
    constructor
    · rintro ⟨B,rfl,large⟩
      simpa [show 2*(s+1)+1 = 2*s+3 by omega] using girth_of_density B s large
    · intro _
      refine ⟨A,full,density_after_edit hs A ?_⟩
      obtain ⟨h,_,_⟩ := hamming_ball_data (s+1) r
      rw [ambient] at sz
      have hcap : D.card ≤ 3*(2*s+3)*2^r := by
        calc
          _ ≤ (2*s+3)*2^r := cap
          _ ≤ 3*((2*s+3)*2^r) := by omega
          _ = _ := by ring
      omega
  · exact realizable_iff_odd_girth hs D aff near

end Green51MissingMasks
#print axioms Green51MissingMasks.realizable_iff_in_band
