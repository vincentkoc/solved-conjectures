import Green52AffineDerivatives

/-! # Binary quadratic character sums -/
open Finset
namespace Green52CubicBias
local notation "𝔽" => ZMod 2
def parity (a : 𝔽) : ℤ := if a=0 then 1 else -1
theorem parity_add (a b : 𝔽) : parity (a+b) = parity a * parity b := by decide +revert
variable {U : Type*} [AddCommGroup U] [Module 𝔽 U] [Fintype U]

/-- A nontrivial binary linear functional has zero character sum. -/
theorem linear_sum (l : Module.Dual 𝔽 U) (hl : l ≠ 0) : ∑ x, parity (l x) = 0 := by
  obtain ⟨u,hu⟩ : ∃ u, l u ≠ 0 := by
    by_contra! hall
    exact hl (LinearMap.ext fun x => hall x)
  have neg : parity (l u) = -1 := if_neg hu
  have h := Equiv.sum_comp (Equiv.addLeft u) (fun x => parity (l x))
  change (∑ x, parity (l (u+x))) = ∑ x, parity (l x) at h
  simp only [map_add,parity_add,neg,neg_one_mul,sum_neg_distrib] at h
  omega

/-- The square of a quadratic Walsh sum is bounded by the cardinality of the
space times the cardinality of the radical of its polar form. -/
theorem quadratic_sum_sq (f : U → 𝔽) (B : U →ₗ[𝔽] Module.Dual 𝔽 U)
    (hf : ∀ a x, f x+f (a+x) = B a x + (f 0+f a)) :
    (∑ x, parity (f x))^2 ≤ (Fintype.card U : ℤ) * Nat.card B.ker := by
  classical
  let b (a : U) := ∑ x, parity (f x+f (a+x))
  have expand : (∑ x, parity (f x))^2 = ∑ a, b a := by
    change _ = ∑ a, ∑ x, parity (f x+f (a+x))
    rw [sum_comm,sq,sum_mul]
    apply sum_congr rfl
    intro x _
    simp only [parity_add,←mul_sum]
    exact congrArg (fun z => parity (f x)*z) (Equiv.sum_comp (Equiv.addRight x) (fun y => parity (f y))).symm
  have per (a : U) : b a ≤ if a ∈ B.ker then (Fintype.card U:ℤ) else 0 := by
    by_cases h : B a=0
    · simp only [LinearMap.mem_ker,h,if_true]
      dsimp [b]
      simp only [hf,h,LinearMap.zero_apply,zero_add,sum_const,card_univ,nsmul_eq_mul]
      have z : parity (f 0+f a) ≤ 1 := by unfold parity; split <;> decide
      simpa using mul_le_mul_of_nonneg_left z (show (0:ℤ)≤Fintype.card U by positivity)
    · simp only [LinearMap.mem_ker,h,if_false]
      dsimp [b]
      simp only [hf,parity_add (B a _) _,←sum_mul,linear_sum (B a) h,zero_mul,le_refl]
  rw [expand]
  refine (sum_le_sum (fun a _ => per a)).trans_eq ?_
  rw [sum_ite,Finset.sum_const_zero,add_zero,sum_const,nsmul_eq_mul,mul_comm]
  congr 1
  exact_mod_cast (show (univ.filter (· ∈ B.ker)).card = Nat.card B.ker by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype])

/-- At polar rank at least 2s, the absolute character sum is at most the
size of the space divided by 2ˢ. The integer formulation includes rank zero. -/
theorem quadratic_sum_rank (f : U → 𝔽) (B : U →ₗ[𝔽] Module.Dual 𝔽 U)
    (hf : ∀ a x, f x+f (a+x) = B a x + (f 0+f a)) (s : ℕ)
    (rank : 2*s ≤ Module.finrank 𝔽 B.range) :
    (2:ℤ)^s * |∑ x, parity (f x)| ≤ Fintype.card U := by
  classical
  have dim := LinearMap.finrank_range_add_finrank_ker (K:=𝔽) (V:=U) (V₂:=Module.Dual 𝔽 U) B
  have product : 2^(2*s)*Nat.card B.ker ≤ Fintype.card U := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=𝔽) (V:=B.ker),Module.card_eq_pow_finrank (K:=𝔽) (V:=U)]
    simp only [ZMod.card,←pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have squared := quadratic_sum_sq f B hf
  let z := |∑ x, parity (f x)|
  have zz : z^2=(∑ x, parity (f x))^2 := sq_abs _
  have fac : ((2:ℤ)^s)^2=(2:ℤ)^(2*s) := by rw [←pow_mul,Nat.mul_comm]
  have prod' : (2:ℤ)^(2*s)*(Nat.card B.ker:ℤ) ≤ Fintype.card U := by exact_mod_cast product
  have hq := mul_le_mul_of_nonneg_left squared (show (0:ℤ)≤2^(2*s) by positivity)
  have hs := mul_le_mul_of_nonneg_left prod' (show (0:ℤ)≤Fintype.card U by positivity)
  change (2:ℤ)^s*z ≤ Fintype.card U
  have hsq : ((2:ℤ)^s*z)^2 ≤ (Fintype.card U:ℤ)^2 := by
    rw [mul_pow,fac,zz]; nlinarith only [hq,hs]
  nlinarith [sq_nonneg ((2:ℤ)^s*z-Fintype.card U),show (0:ℤ)≤Fintype.card U by positivity]

end Green52CubicBias
#print axioms Green52CubicBias.quadratic_sum_sq
#print axioms Green52CubicBias.quadratic_sum_rank

/-! # Detecting a zero derivative with binary characters -/
open Finset
open Green52CubicBias
namespace Green52CubicFibres
local notation "𝔽" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module 𝔽 U] [Fintype U]
  [AddCommGroup V] [Module 𝔽 V] [Fintype V]

/-- On this horizontal subspace, every scalar projection of every derivative
has a zero. The points witnessing the zeros may depend on the functional. -/
theorem horizontal_projections (f : U → V) : ∃ H : Submodule 𝔽 U,
    Module.finrank 𝔽 U ≤ Module.finrank 𝔽 H + (Fintype.card V-1) ∧
    ∀ a : H, ∀ l : Module.Dual 𝔽 V, ∃ x, l (f x+f (x+a.val))=0 := by
  classical
  obtain ⟨T,dim,proj⟩ := Green52AffineDerivatives.projection_flat f
  let Q := T.mkQ.comp (LinearMap.inl 𝔽 U V)
  refine ⟨Q.ker,?_,?_⟩
  · have hn := Q.finrank_range_add_finrank_ker
    have le := Submodule.finrank_le Q.range
    have sum := T.finrank_quotient_add_finrank
    omega
  · intro a l
    have h : (a.val,(0:V))∈T := (Submodule.Quotient.mk_eq_zero T).mp (show Q a.val=0 from a.property)
    simpa using proj (a.val,0) h l

/-- An affine binary function that takes the value zero has nonnegative bias. -/
theorem affine_nonneg (f : U → 𝔽) (l : Module.Dual 𝔽 U) (b : 𝔽)
    (repr : ∀ x, f x=l x+b) (hz : ∃ x, f x=0) : 0 ≤ ∑ x, parity (f x) := by
  by_cases h : l=0
  · obtain ⟨x,hx⟩ := hz
    have hb : b=0 := by simpa [repr,h] using hx
    simp [repr,h,hb,parity]
  · simp only [repr,parity_add,←sum_mul,linear_sum l h,zero_mul,le_refl]

private theorem orthogonal [Fintype (Module.Dual 𝔽 V)] {v : V} (hv : v≠0) :
    ∑ l : Module.Dual 𝔽 V, parity (l v) = 0 := by
  obtain ⟨u,hu⟩ := Module.Projective.exists_dual_eq_one 𝔽 hv
  have e := Equiv.sum_comp (Equiv.addLeft u) (fun l : Module.Dual 𝔽 V => parity (l v))
  change (∑ l : Module.Dual 𝔽 V, parity ((u+l) v)) = ∑ l : Module.Dual 𝔽 V, parity (l v) at e
  simp only [LinearMap.add_apply,hu,parity_add,show parity 1=(-1:ℤ) by decide,neg_one_mul,sum_neg_distrib] at e
  omega

omit [Module 𝔽 U] in
/-- If all scalar character sums are nonnegative or have absolute value
less than |U|/|V|, the vector-valued map must have a zero. -/
theorem exists_zero (f : U → V) (hf : ∀ l : Module.Dual 𝔽 V,
    0≤∑ x, parity (l (f x)) ∨ (Fintype.card V:ℤ)*|∑ x, parity (l (f x))| < Fintype.card U) :
    ∃ x, f x=0 := by
  classical
  let _ : Fintype (Module.Dual 𝔽 V) := Fintype.ofInjective (fun l : Module.Dual 𝔽 V => (l : V → 𝔽)) DFunLike.coe_injective
  let b (l : Module.Dual 𝔽 V) := ∑ x, parity (l (f x))
  have cardD : Fintype.card (Module.Dual 𝔽 V)=Fintype.card V := by
    calc
      _ = Fintype.card 𝔽 ^ Module.finrank 𝔽 (Module.Dual 𝔽 V) := Module.card_eq_pow_finrank
      _ = _ := by rw [Subspace.dual_finrank_eq]; exact Module.card_eq_pow_finrank.symm
  have per (l : Module.Dual 𝔽 V) : -(Fintype.card U:ℤ) < (Fintype.card V:ℤ)*b l := by
    rcases hf l with h|h
    · exact lt_of_lt_of_le (by exact_mod_cast neg_lt_zero.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α:=U)) : (0:ℤ)<Fintype.card U)) (mul_nonneg (by positivity) h)
    · change (Fintype.card V:ℤ)*|b l| < _ at h
      have lo := mul_le_mul_of_nonneg_left (neg_le_abs (b l)) (show (0:ℤ)≤Fintype.card V by positivity)
      linarith
  by_contra! gone
  have vanish : ∑ l, b l = 0 := by
    dsimp only [b]
    rw [sum_comm]
    simp [fun x => orthogonal (gone x)]
  let rest := (univ : Finset (Module.Dual 𝔽 V)).erase 0
  have sumRest := Finset.sum_le_sum (s:=rest) (fun l _ => (per l).le)
  simp only [sum_const,nsmul_eq_mul,←mul_sum] at sumRest
  have count : rest.card+1=Fintype.card V := by simpa [rest,cardD] using
    (card_erase_add_one (s:=(univ : Finset (Module.Dual 𝔽 V))) (mem_univ 0))
  have sum := sum_erase_add (s:=(univ : Finset (Module.Dual 𝔽 V))) b (mem_univ 0)
  have b0 : b 0 = Fintype.card U := by simp [b,parity]
  change ∑ l∈rest, b l + _ = _ at sum
  rw [b0,vanish] at sum
  have count' : (rest.card:ℤ)+1=Fintype.card V := by exact_mod_cast count
  nlinarith [show (0:ℤ)<Fintype.card U by positivity]
end Green52CubicFibres
#print axioms Green52CubicFibres.horizontal_projections
#print axioms Green52CubicFibres.exists_zero
