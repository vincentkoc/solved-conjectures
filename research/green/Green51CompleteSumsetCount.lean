import Green51AffineCount
import Green51DenseSumsetEnumeration

/-! # All dense sumsets with prescribed near-extremal missing cardinality -/

namespace Green51AffineEnumeration
open Finset Green53ParityThreshold Green51Hyperplane Green51NearThreshold Green51GirthFrame Green51MissingMasks
open scoped Classical Pointwise

/-- Distinct doubles of a dense input with a prescribed number of missing points. -/
noncomputable def allDenseDoubles (n k : ℕ) (α : ℝ) : Finset (Finset (𝔽₂ n)) :=
  univ.filter fun S => Sᶜ.card=k ∧ ∃ A : Finset (𝔽₂ n), A+A=S ∧ α < (A.dens : ℝ)

private theorem affine_girth {G : Type*} [AddCommGroup G] [Module F G] [DecidableEq G]
    (D : Finset G) (aff : separated D) (R : Finset G) (sub : R ⊆ D) (par : Odd R.card) :
    ∑ x ∈ R, x ≠ 0 := by
  obtain ⟨f,level⟩ := aff
  intro zero
  have z : ∑ x ∈ R, f x=0 := by rw [←map_sum,zero,map_zero]
  rw [sum_congr rfl (g := fun _ => 1) (fun x hx => level _ (sub hx)),sum_const,nsmul_eq_mul,mul_one] at z
  have dv := (ZMod.natCast_eq_zero_iff _ _).mp z
  rw [Nat.odd_iff] at par
  omega

theorem count_all_dense_doubles {s r : ℕ} (hs : 5 ≤ s) (k : ℕ)
    (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k) (cap : k ≤ (2*s+3)*2^r) :
    let n := 2*(s+1)+r
    (allDenseDoubles n k (threshold (2*s))).card =
      affineNumber k n + (countedDoubles n k (threshold (2*s))).card := by
  classical
  let n := 2*(s+1)+r
  let G := 𝔽₂ n
  let g := 2*s+3
  let T := allDenseDoubles n k (threshold (2*s))
  have position : 0<k := by omega
  have diff : n+1-g=r := by dsimp [n,g]; omega
  have nearD (D : Finset G) (size : D.card=k) :
      min (5*g+12) (4*g+20)*2^(n+1-g) < 8*D.card := by simpa only [g,size,diff] using near
  have affine : (T.filter (fun S => separated Sᶜ)).card = affineCount G k := by
    apply card_bij (fun S _ => Sᶜ)
    · intro S hS
      obtain ⟨inT,level⟩ := mem_filter.mp hS
      obtain ⟨size,_⟩ := (mem_filter.mp inT).2
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,size⟩,level⟩
    · intro S _ V _ eq
      simpa only [compl_compl] using congrArg (fun E : Finset G => Eᶜ) eq
    · intro D hD
      obtain ⟨num,level⟩ := mem_filter.mp hD
      have size := (mem_powersetCard.mp num).2
      obtain ⟨A,eq,ha⟩ := (realizable_iff_in_band hs D (by simpa only [size] using near)
        (by simpa only [size] using cap)).mpr (fun R sub odd zero => (affine_girth D level R sub odd zero).elim)
      refine ⟨A+A,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,by rw [eq,size],A,rfl,ha⟩,?_⟩,eq⟩
      rw [eq]; exact level
  have other : T.filter (fun S => ¬separated Sᶜ) = countedDoubles n k (threshold (2*s)) := by
    ext S
    simp only [T,allDenseDoubles,countedDoubles,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨⟨num,A,rfl,ha⟩,no⟩
      have girth := girth_of_density A s ha
      have eq := (near_girth_dimension (n := n) (g := g) (by dsimp [n]; omega) (A+A)ᶜ (by dsimp [g]; omega)
        ⟨s+1,by dsimp [g]; omega⟩ (by simpa only [g,show 2*(s+1)+1=2*s+3 by omega] using girth)
        (nearD _ num)).mpr no
      exact ⟨num,by simpa only [compl_compl] using eq,A,rfl,ha⟩
    · rintro ⟨num,dim,A,rfl,ha⟩
      have girth := girth_of_density A s ha
      have no := (near_girth_dimension (n := n) (g := g) (by dsimp [n]; omega) (A+A)ᶜ (by dsimp [g]; omega)
        ⟨s+1,by dsimp [g]; omega⟩ (by simpa only [g,show 2*(s+1)+1=2*s+3 by omega] using girth)
        (nearD _ num)).mp (by simpa only [compl_compl] using dim)
      exact ⟨⟨num,A,rfl,ha⟩,no⟩
  have eq := card_filter_add_card_filter_not (s := T) (fun S => separated Sᶜ)
  rw [affine,other,affineCount_eq_number n k position] at eq
  exact eq.symm
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.count_all_dense_doubles

namespace Green51AffineEnumeration
open Green51Hyperplane Green51MissingMasks

private theorem affine_number_at_forty_one : affineNumber 41 16 = 259788104246795549280143177514902925015369624323705604423368778268772923229789555693885214593135706130828857829612275414717382255841256477120 := by
  decide +kernel

private theorem count_at_dimension {n d s r : ℕ} (dim : 2*(s+1)+r=n) (cut : 2*s=d)
    (hs : 5 ≤ s) (k : ℕ) (near : min (5*(2*s+3)+12) (4*(2*s+3)+20)*2^r < 8*k)
    (cap : k ≤ (2*s+3)*2^r) :
    (allDenseDoubles n k (threshold d)).card = affineNumber k n + (countedDoubles n k (threshold d)).card := by
  subst n; subst d; exact count_all_dense_doubles hs k near cap

/-- The complete dimension-sixteen count with no restriction on the largest affine subspace. -/
theorem all_at_forty_one :
    (allDenseDoubles 16 41 (threshold 12)).card = 259788104246795549280143177514902925015369624323705604423368778268772951924859149018598287200135475533670027549802838592363229718451725341120 := by
  have h := count_at_dimension (n := 16) (d := 12) (s := 6) (r := 2) rfl rfl (by decide) 41 (by decide) (by decide)
  exact h.trans (congrArg₂ (fun x y : ℕ => x+y) affine_number_at_forty_one count_at_forty_one)
end Green51AffineEnumeration
#print axioms Green51AffineEnumeration.all_at_forty_one
