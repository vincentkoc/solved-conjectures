import Green51MissingDirections
import Green51CosetThreshold

/-! # The next density interval for the guaranteed coset dimension -/

open Finset Green53ParityThreshold Green51Hyperplane
open scoped Classical Pointwise
namespace Green51NearThreshold

/-- A linear map can take arbitrary prescribed values on independent directions. -/
theorem extend_values {G W : Type*} [AddCommGroup G] [Module F G]
    [AddCommGroup W] [Module F W] {B : Set G} (ind : LinearIndepOn F id B) (w : G → W) :
    ∃ f : G →ₗ[F] W, ∀ x∈B,f x=w x := by
  classical
  let b : Module.Basis _ F G := .mk (ind.linearIndepOn_extend (Set.subset_univ _)) <| by
    simpa using ind.span_extend_eq_span (Set.subset_univ _)
  let f := b.constr F (fun i => w i.val)
  refine ⟨f,fun x hx => ?_⟩
  let i : ind.extend (Set.subset_univ _) := ⟨x,ind.subset_extend _ hx⟩
  have bi : b i=x := by simp [b,i]
  calc
    f x = f (b i) := congrArg f bi.symm
    _ = w x := by simp [f,i]

/-- Two output coordinates suffice to avoid zero on a nonempty independent set and its sum. -/
theorem frame_projection {G : Type*} [AddCommGroup G] [Module F G]
    (B : Finset G) (inh : B.Nonempty) (ind : LinearIndepOn F id (B:Set G)) :
    ∃ f : G →ₗ[F] F×F, (∀ b∈B,f b≠0) ∧ f (∑ b∈B,b)≠0 := by
  classical
  obtain ⟨j,hj⟩ := inh
  let w (x : G) : F×F := (1, if x=j then 1 else 0)
  obtain ⟨f,ext⟩ := extend_values ind w
  have fe (x) (hx : x∈B) : (f x).2=if x=j then 1 else 0 := congrArg Prod.snd (ext x hx)
  refine ⟨f,fun x hx hz => one_ne_zero (show (1:F)=0 from congrArg Prod.fst ((ext x hx).symm.trans hz)),?_⟩
  intro zero
  have z := congrArg Prod.snd zero
  rw [map_sum,Prod.snd_sum] at z
  have calcSum := sum_congr rfl fe
  rw [calcSum] at z
  simp [hj] at z

/-- A density above the hyperplane threshold for two fewer coordinates gives
a linear subspace of codimension at most two in the full even-dimensional sumset. -/
theorem even_codimension_two (s : ℕ) (A : Finset (Fin (2*(s+1)) → F))
    (large : 2^(2*(s+1)) < 2*A.card + 4*(2*s).choose s) :
    ∃ f : (Fin (2*(s+1)) → F) →ₗ[F] F×F, ∀ x∈f.ker,x∈A+A := by
  rcases even_missing_directions s A large with ⟨l,h⟩|⟨B,card,ind,missing⟩
  · refine ⟨l.prod 0,fun x hx => h x ?_⟩
    exact congrArg Prod.fst (LinearMap.mem_ker.mp hx)
  · obtain ⟨f,onB,atSum⟩ := frame_projection B (card_pos.mp (by omega)) ind
    refine ⟨f,fun x hx => ?_⟩
    by_contra out
    have absent : x∈(((A+A : Finset _) : Set (Fin (2*(s+1)) → F))ᶜ) := out
    rw [missing] at absent
    rcases absent with h|h
    · exact onB x h (LinearMap.mem_ker.mp hx)
    · exact atSum (h ▸ LinearMap.mem_ker.mp hx)

/-- The width of the interval immediately below the even hyperplane threshold. -/
theorem layer_step (s : ℕ) :
    threshold (2*(s+1))-threshold (2*s)=halfLayer s/(2*(s+1)) := by
  simp only [threshold,Nat.mul_div_cancel_left _ (by decide : 0<2)]
  have recurrence : ((s:ℝ)+1)*((2*(s+1)).choose (s+1):ℝ)=
      2*(2*s+1)*((2*s).choose s : ℝ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ s
  unfold halfLayer
  have step : (2:ℝ)^(2*(s+1))=4*2^(2*s) := by rw [Nat.mul_add,pow_add]; ring
  rw [step]
  field_simp
  nlinarith only [recurrence]

private theorem dense_iff {s : ℕ} (A : Finset (𝔽₂ (2*(s+1)))) :
    threshold (2*s)<(A.dens : ℝ) ↔ 2^(2*(s+1)) < 2*A.card + 4*(2*s).choose s := by
  rw [threshold,Nat.mul_div_cancel_left _ (by decide : 0<2),nnratCast_dens]
  unfold halfLayer
  simp only [𝔽₂,𝔽,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  have size : (2:ℝ)^(2*(s+1))=4*2^(2*s) := by rw [Nat.mul_add,pow_add]; ring
  have natSize : (2:ℕ)^(2*(s+1))=4*2^(2*s) := by rw [Nat.mul_add,pow_add]; ring
  rw [size,natSize]
  have eq : (4:ℝ)*2^(2*s)<2*A.card+4*((2*s).choose s:ℝ) ↔
      4*(2:ℕ)^(2*s)<2*A.card+4*(2*s).choose s := by norm_cast
  rw [←eq]
  field_simp
  constructor <;> intro h <;> linarith

/-- Linear kernels of maps to two coordinates give a lower bound for the
host's guaranteed affine coset dimension. -/
theorem guaranteed_lower_of_two_coordinates {n : ℕ} {α : ℝ} (hα : α≤1)
    (all : ∀ A : Finset (𝔽₂ n), α≤(A.dens:ℝ) →
      ∃ f : (𝔽₂ n) →ₗ[F] F×F, ∀ x∈f.ker,x∈A+A) :
    n-2≤Green51.guaranteedMaxCosetDim n α := by
  classical
  unfold Green51.guaranteedMaxCosetDim
  apply le_csInf
  · exact ⟨_,univ,by simpa using hα,rfl⟩
  · rintro _ ⟨A,ha,rfl⟩
    obtain ⟨f,sub⟩ := all A ha
    have dim := f.finrank_range_add_finrank_ker
    have r := Submodule.finrank_le f.range
    simp only [Module.finrank_prod,Module.finrank_self] at r
    have ambient : Module.finrank F (𝔽₂ n)=n := by simp [𝔽₂,𝔽]
    rw [ambient] at dim
    have gain : n-2≤Module.finrank F f.ker := by omega
    apply gain.trans
    apply le_csSup
    · refine ⟨n,?_⟩
      rintro _ ⟨S,_,rfl⟩; exact (Submodule.finrank_le S.direction).trans_eq ambient
    · exact ⟨f.ker.toAffineSubspace,fun _ hx => sub _ hx,by rw [Submodule.toAffineSubspace_direction]⟩

/-- Green's guaranteed dimension has the exact value `n−2` in the first
interval immediately below the hyperplane cutoff in even dimension `n=2s+2`. -/
theorem guaranteed_even_next_interval (s : ℕ) {α : ℝ}
    (large : threshold (2*s)<α) (boundary : α≤threshold (2*(s+1))) :
    Green51.guaranteedMaxCosetDim (2*(s+1)) α=2*s := by
  classical
  let n := 2*(s+1)
  have hn : 2≤n := by dsimp [n]; omega
  have one : α≤1 := by
    apply boundary.trans
    unfold threshold halfLayer
    have nn : 0 ≤ ((2*(n/2)).choose (n/2):ℝ)/(2*2^(2*(n/2))) := by positivity
    change 1/2-((2*(n/2)).choose (n/2):ℝ)/(2*2^(2*(n/2)))≤1
    linarith
  have no := mt (guaranteed_hyperplane_iff hn one).mp (not_lt_of_ge boundary)
  apply le_antisymm
  · change ¬2*(s+1)≤Green51.guaranteedMaxCosetDim (2*(s+1)) α+1 at no
    omega
  have lo := guaranteed_lower_of_two_coordinates (n:=2*(s+1)) one (fun A ha =>
    even_codimension_two s A ((dense_iff A).mp (large.trans_le ha)))
  omega

end Green51NearThreshold
#print axioms Green51NearThreshold.layer_step
#print axioms Green51NearThreshold.even_codimension_two
#print axioms Green51NearThreshold.guaranteed_even_next_interval

#print axioms Green51NearThreshold.extend_values
#print axioms Green51NearThreshold.frame_projection
#print axioms Green51NearThreshold.guaranteed_lower_of_two_coordinates
