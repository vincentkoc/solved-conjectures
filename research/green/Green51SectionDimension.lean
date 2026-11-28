import Green51FrameSections
import Green51MissingStability

/-! # Affine dimension of majority sections of binary circuit frames -/

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical Pointwise
variable {G : Type*} [AddCommGroup G] [Module F G] [Fintype G] [DecidableEq G]

theorem constant_on_majority {C E : Finset G} (m : ShortestOddCircuit E C)
    (P : Submodule F G) (comp : IsCompl P (Submodule.span F (C : Set G))) (D : Finset G)
    (sub : D ⊆ (P : Set G).toFinset+C) (dense : ((P : Set G).toFinset+C).card < 2*D.card)
    (hit : ∀ c ∈ C, ∃ t ∈ P, t+c ∈ D)
    (f : G →ₗ[F] F) (b : F) (val : ∀ x ∈ D, f x = b) : f = 0 := by
  classical
  have vanish := kills_periods_of_majority P C D sub dense f b val
  have nonaff := (majority_nonaffine_iff m P comp D sub dense).mpr hit
  have b0 : b = 0 := by
    rcases (show b=0 ∨ b=1 by fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl) with h|h
    · exact h
    · exact (nonaff ⟨f,fun x hx => (val x hx).trans h⟩).elim
  have ker : P ⊔ Submodule.span F (C : Set G) ≤ f.ker := by
    apply sup_le (fun t ht => LinearMap.mem_ker.mpr (vanish t ht))
    apply Submodule.span_le.mpr
    intro c hc
    obtain ⟨t,ht,mem⟩ := hit c hc
    exact LinearMap.mem_ker.mpr (by simpa only [map_add,vanish t ht,zero_add,b0] using val _ mem)
  rw [comp.sup_eq_top] at ker
  exact LinearMap.ker_eq_top.mp (top_unique ker)

/-- An affine subspace missing a set of full affine span has codimension at least two. -/
theorem flat_upper_of_constants {n : ℕ} (D : Finset (𝔽₂ n)) (hd : D.Nonempty)
    (const : ∀ (f : (𝔽₂ n) →ₗ[F] F) (b : F), (∀ x ∈ D, f x=b) → f=0) :
    ∀ S : AffineSubspace F (𝔽₂ n), (∃ a, a ∈ S) → (∀ x ∈ S, x ∉ D) →
      Module.finrank F S.direction + 1 < n := by
  classical
  rintro S ⟨a,ha⟩ away
  by_contra! dim
  obtain ⟨y,hy⟩ := hd
  have dir (z : 𝔽₂ n) : z-a∈S.direction ↔ z∈S := AffineSubspace.vsub_right_mem_direction_iff_mem ha z
  have out : y-a ∉ S.direction := fun h => away y ((dir y).mp h) hy
  obtain ⟨f,nz,ann⟩ := Submodule.exists_dual_map_eq_bot_of_notMem out inferInstance
  have le : S.direction ≤ f.ker := by
    intro x hx
    have h : f x ∈ S.direction.map f := ⟨x,hx,rfl⟩
    rwa [ann] at h
  have low : Module.finrank F f.ker < n := by
    have ne : f.ker ≠ ⊤ := fun eq => nz ((LinearMap.ker_eq_top.mp eq) ▸ (rfl : (0 : (𝔽₂ n) →ₗ[F] F) (y-a)=0))
    simpa [𝔽₂,𝔽] using Submodule.finrank_lt (s:=f.ker) ne
  have reverse : Module.finrank F f.ker ≤ Module.finrank F S.direction := by omega
  have eq := Submodule.eq_of_le_of_finrank_le le reverse
  have same (z : 𝔽₂ n) (hz : z ∈ D) : f z = 1 + f a := by
    have diff : f (z-a) ≠ 0 := by
      intro zero
      have inz := LinearMap.mem_ker.mpr zero
      rw [←eq] at inz
      exact away z ((dir z).mp inz) hz
    have one : f (z-a) = 1 := (show ∀ v : F, v=0 ∨ v=1 from by decide) _ |>.resolve_left diff
    rw [map_sub] at one
    exact sub_eq_iff_eq_add.mp one
  exact nz ((const f _ same) ▸ (rfl : (0 : (𝔽₂ n) →ₗ[F] F) (y-a)=0))

end Green51GirthFrame
#print axioms Green51GirthFrame.constant_on_majority
#print axioms Green51GirthFrame.flat_upper_of_constants

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51Hyperplane Green51NearThreshold
open scoped Classical Pointwise

private theorem upper_dim {n k : ℕ} (B : Finset (𝔽₂ n))
    (bound : ∀ S : AffineSubspace F (𝔽₂ n), (∃ a, a ∈ S) → (∀ x ∈ S, x ∈ B) →
      Module.finrank F S.direction ≤ k) : maxCosetDim F (𝔽₂ n) ↑B ≤ k := by
  apply csSup_le
  · exact ⟨0,⊥,by simp,by simp⟩
  · rintro _ ⟨S,sub,rfl⟩
    by_cases h : ∃ a, a ∈ S
    · exact bound S h (fun _ hx => sub hx)
    · have bot : S = ⊥ := by
        ext x; simp only [AffineSubspace.notMem_bot,iff_false]; exact fun hx => h ⟨x,hx⟩
      rw [bot,AffineSubspace.direction_bot]; simp

private theorem ker_le_dim {n : ℕ} {W : Type*} [AddCommGroup W] [Module F W]
    (B : Finset (𝔽₂ n)) (f : (𝔽₂ n) →ₗ[F] W) (sub : ∀ x ∈ f.ker, x ∈ B) :
    Module.finrank F f.ker ≤ maxCosetDim F (𝔽₂ n) ↑B := by
  apply le_csSup
  · refine ⟨n, ?_⟩
    rintro _ ⟨S,_,rfl⟩
    simpa [𝔽₂,𝔽] using Submodule.finrank_le S.direction
  · exact ⟨f.ker.toAffineSubspace, fun x hx => sub x hx, by rw [Submodule.toAffineSubspace_direction]⟩

theorem majority_flat_dimension {n : ℕ} (dim : 2 ≤ n) {C E : Finset (𝔽₂ n)}
    (m : ShortestOddCircuit E C) (g : 5 ≤ C.card) (P : Submodule F (𝔽₂ n))
    (comp : IsCompl P (Submodule.span F (C : Set _))) (D : Finset (𝔽₂ n))
    (sub : D ⊆ (P : Set _).toFinset+C) (dense : ((P : Set _).toFinset+C).card < 2*D.card) :
    maxCosetDim F (𝔽₂ n) ↑(Dᶜ) =
      if ∀ c ∈ C, ∃ t ∈ P, t+c ∈ D then n-2 else n-1 := by
  classical
  have pos : D.Nonempty := card_pos.mp (by omega)
  have amb : Module.finrank F (𝔽₂ n) = n := by simp [𝔽₂,𝔽]
  split_ifs with hits
  · have hi := upper_dim (k := n-2) Dᶜ (by
      intro S live inc
      have h := flat_upper_of_constants D pos (constant_on_majority m P comp D sub dense hits)
        S live (fun x hx => mem_compl.mp (inc x hx))
      omega)
    obtain ⟨mU,_⟩ := container_size_girth m P comp
    obtain ⟨f,miss⟩ := container_coordinates mU g comp (by
      intro x hx
      obtain ⟨t,ht,i,hi,eq⟩ := mem_add.mp hx
      exact ⟨t,Set.mem_toFinset.mp ht,i,hi,eq.symm⟩)
    have lo := ker_le_dim Dᶜ f (by intro x hx; exact mem_compl.mpr fun hd => miss x (sub hd) (LinearMap.mem_ker.mp hx))
    have sum := f.finrank_range_add_finrank_ker
    have range := Submodule.finrank_le f.range
    simp only [Module.finrank_prod,Module.finrank_self] at range
    rw [amb] at sum
    omega
  · have aff : ∃ f : (𝔽₂ n) →ₗ[F] F, ∀ x ∈ D, f x = 1 :=
      Classical.not_not.mp (fun no => hits ((majority_nonaffine_iff m P comp D sub dense).mp no))
    obtain ⟨f,val⟩ := aff
    have lo := ker_le_dim Dᶜ f (by
      intro x hx
      exact mem_compl.mpr fun h => one_ne_zero ((val _ h).symm.trans (LinearMap.mem_ker.mp hx)))
    have sum := f.finrank_range_add_finrank_ker
    have range := Submodule.finrank_le f.range
    rw [Module.finrank_self] at range
    rw [amb] at sum
    have hi := upper_dim (k := n-1) Dᶜ (by
      rintro S ⟨a,ha⟩ inc
      obtain ⟨z,hz⟩ := pos
      have ne : S.direction ≠ ⊤ := by
        intro eq
        have all : z-a ∈ S.direction := eq ▸ Submodule.mem_top
        exact mem_compl.mp (inc z ((AffineSubspace.vsub_right_mem_direction_iff_mem ha z).mp all)) hz
      have h := (Submodule.finrank_lt (s := S.direction) ne).trans_eq amb
      omega)
    omega
end Green51GirthFrame
#print axioms Green51GirthFrame.majority_flat_dimension

namespace Green51GirthFrame
open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical Pointwise

/-- For a missing set in the near-extremal band, the nonaffine branch is precisely codimension two. -/
theorem near_girth_dimension {n g : ℕ} (dim : 2 ≤ n) (D : Finset (𝔽₂ n))
    (large : 5 ≤ g) (odd : Odd g)
    (girth : ∀ R ⊆ D, Odd R.card → (∑ x ∈ R, x)=0 → g ≤ R.card)
    (near : min (5*g+12) (4*g+20)*2^(n+1-g)<8*D.card) :
    maxCosetDim F (𝔽₂ n) ↑(Dᶜ)=n-2 ↔
      ¬∃ f : 𝔽₂ n →ₗ[F] F, ∀ x ∈ D, f x=1 := by
  classical
  have amb : Module.finrank F (𝔽₂ n) = n := by simp [𝔽₂,𝔽]
  constructor
  · rintro eq ⟨f,ones⟩
    have low := ker_le_dim Dᶜ f (by
      intro x hx
      exact mem_compl.mpr fun hd => one_ne_zero ((ones x hd).symm.trans (LinearMap.mem_ker.mp hx)))
    have sum := f.finrank_range_add_finrank_ker
    have ran := Submodule.finrank_le f.range
    rw [Module.finrank_self] at ran
    rw [amb] at sum
    omega
  · intro no
    obtain ⟨C,m,len,P,comp,gr,num⟩ := greatest_girth_extension D g large odd girth no (by rwa [amb])
    have dense : ((P : Set _).toFinset+C).card < 2*D.card := by
      have h := Nat.mul_le_mul_right (2^(n+1-g)) (show 4*g ≤ min (5*g+12) (4*g+20) by omega)
      rw [Nat.mul_assoc] at h
      rw [num,amb]
      omega
    have hits := (majority_nonaffine_iff m P comp D gr.1.1 dense).mp no
    simpa only [if_pos hits] using majority_flat_dimension dim m (by omega) P comp D gr.1.1 dense
end Green51GirthFrame
#print axioms Green51GirthFrame.near_girth_dimension
