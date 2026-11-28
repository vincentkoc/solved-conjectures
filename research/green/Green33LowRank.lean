import Green33ShiftVariation
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Low-rank approximation of the table of translates of a cyclic representation function. -/

open Finset Filter LinearMap
open scoped InnerProductSpace Topology Pointwise Matrix

namespace Green33LowRank

section Trace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem sum_images {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (S : E →ₗ[ℝ] E) : ∑ i, ‖S (b i)‖^2 = trace ℝ E ((adjoint S).comp S) := by
  rw [trace_eq_sum_inner _ b]
  simp only [comp_apply, adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Operators with the same image norms have a trace obstruction to fitting
one of them with a map of small rank. -/
theorem trace_rank_bound {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ E)
    (R D K : E →ₗ[ℝ] E) (same : ∀ x, ‖R x‖=‖D x‖) (L : ℝ)
    (cap : ∀ x, ‖x‖=1 → ‖D x‖ ≤ L) :
    trace ℝ E D ≤ Real.sqrt (Module.finrank ℝ E) * Real.sqrt (∑ i, ‖(R-K) (basis i)‖^2) +
      (Module.finrank ℝ (LinearMap.range K):ℝ)*L := by
  classical
  let V := LinearMap.ker K
  let v := stdOrthonormalBasis ℝ V
  let w := stdOrthonormalBasis ℝ Vᗮ
  let b := (v.prod w).map (V.orthogonalDecomposition.symm)
  have left (i) : b (.inl i) = (v i : E) := by simp [b,OrthonormalBasis.prod_apply]
  have norm1 (j) : ‖b j‖=1 := b.orthonormal.norm_eq_one j
  have null (i) : K (b (.inl i)) = 0 := left i ▸ (v i).property
  have bound (j) : ⟪b j,D (b j)⟫_ℝ ≤ ‖(R-K) (b j)‖ + Sum.elim (fun _ => 0) (fun _ => L) j := by
    have le := real_inner_le_norm (b j) (D (b j))
    rw [norm1,one_mul] at le
    cases j with
    | inl i => simpa [← same, LinearMap.sub_apply, null] using le
    | inr i => exact (le.trans (cap _ (norm1 _))).trans (le_add_of_nonneg_left (norm_nonneg _))
  have tot := sum_le_sum (s:=univ) (fun j _ => bound j)
  rw [← trace_eq_sum_inner D b, sum_add_distrib, Fintype.sum_sum_type (f:=Sum.elim (fun _ => (0:ℝ)) (fun _ => L))] at tot
  have dim := V.finrank_add_finrank_orthogonal
  have rk := K.finrank_range_add_finrank_ker
  change Module.finrank ℝ (range K)+Module.finrank ℝ V = _ at rk
  have eq : Module.finrank ℝ Vᗮ = Module.finrank ℝ (range K) := by omega
  simp only [Sum.elim_inl, Sum.elim_inr,sum_const_zero,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,zero_add,eq] at tot
  have cs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ => (1:ℝ)) (fun j => ‖(R-K) (b j)‖)
  simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,Fintype.card_sum,Fintype.card_fin,dim] at cs
  rw [sum_images b, ← sum_images basis] at cs
  exact tot.trans (add_le_add_left cs _)
end Trace

section Cyclic
open Green33Multiplicity Green33TailEnergy Green33ShiftVariation
variable {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

/-- Table containing every translate of a finite real profile. -/
def table (f : G → ℝ) : Matrix G G ℝ := fun i j => f (i-j)

private def translate (h : G) (u : EuclideanSpace ℝ G) : EuclideanSpace ℝ G :=
  WithLp.toLp 2 (fun i => u (i-h))

omit [DecidableEq G] in
private lemma translate_norm (h : G) (u : EuclideanSpace ℝ G) : ‖translate h u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_equiv (Equiv.subRight h) _ _ fun _ => rfl

/-- The sum of the absolute profile values bounds the operator norm of its circulant. -/
theorem table_cap (f : G → ℝ) (u : EuclideanSpace ℝ G) :
    ‖(table f).toEuclideanLin u‖ ≤ (∑ i, |f i|) * ‖u‖ := by
  have conv : (table f).toEuclideanLin u = ∑ h, f h • translate h u := by
    ext i
    change _ = WithLp.ofLp (∑ h, f h • translate h u) i
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
    change ∑ j, f (i-j) * u j = ∑ h, f h * u (i-h)
    apply Fintype.sum_equiv (Equiv.subLeft i)
    intro j
    simp
  rw [conv]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_smul,Real.norm_eq_abs,translate_norm,sum_mul])

private lemma correlation (A : Finset G) (h : G) :
    ∑ z, ((reps A z:ℝ)-2)*(reps A (z+h)-2) =
      ∑ z, ((diffReps A z:ℝ)-2)*(diffReps A (z+h)-2) := by
  have total (f : G × G → G) :
      ∑ z, (((A ×ˢ A).filter fun x => f x = z).card : ℝ) = (A.card:ℝ)^2 := by
    exact_mod_cast (by simpa [sq] using sum_card_fiberwise_eq_card_filter (A ×ˢ A) univ f :
      ∑ z, ((A ×ˢ A).filter fun x => f x = z).card = A.card^2)
  have sr := total (fun x => x.1+x.2)
  have sd := total (fun x => x.1-x.2)
  change ∑ z, (reps A z:ℝ) = _ at sr
  change ∑ z, (diffReps A z:ℝ) = _ at sd
  have raw : ∑ z, (reps A z:ℝ)*reps A (z+h) = ∑ z, (diffReps A z:ℝ)*diffReps A (z+h) := by
    exact_mod_cast shifted_correlation A h
  have shift (f : G → ℝ) : ∑ z, f (z+h) = ∑ z, f z :=
    Fintype.sum_equiv (Equiv.addRight h) _ _ fun _ => rfl
  have expand (x y:ℝ) : (x-2)*(y-2) = x*y-2*x-2*y+4 := by ring
  simp only [expand,sum_add_distrib,sum_sub_distrib,← mul_sum,shift (fun z => (reps A z:ℝ)),shift (fun z => (diffReps A z:ℝ)),sr,sd,raw]

private lemma gram (A : Finset G) :
    let R := table (fun z => (reps A z:ℝ)-2)
    let D := table (fun z => (diffReps A z:ℝ)-2)
    R.transpose * R = D.transpose * D := by
  dsimp only
  ext a b
  have recenter (f : G → ℝ) : ∑ z, f (z-a)*f (z-b) = ∑ z, f z * f (z+(a-b)) := by
    apply Fintype.sum_equiv (Equiv.subRight a)
    intro z
    simp only [Equiv.subRight_apply]
    rw [show z-a+(a-b)=z-b by abel]
  change ∑ z, _*_ = ∑ z, _*_
  exact (recenter _).trans ((correlation A (a-b)).trans (recenter _).symm)

omit [AddCommGroup G] in
/-- Equal Gram matrices give equal image norms for each vector. -/
theorem gram_norm {R D : Matrix G G ℝ} (same : R.transpose * R = D.transpose * D)
    (u : EuclideanSpace ℝ G) : ‖R.toEuclideanLin u‖ = ‖D.toEuclideanLin u‖ := by
  have quadratic (B : Matrix G G ℝ) :
      ‖B.toEuclideanLin u‖^2 =
        (WithLp.ofLp u) ⬝ᵥ ((B.transpose * B) *ᵥ (WithLp.ofLp u)) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change ∑ i, ((B *ᵥ WithLp.ofLp u) i)^2 = _
    simp only [sq]
    rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by rw [quadratic,quadratic,same])

omit [AddCommGroup G] in
private lemma matrix_rank (B : Matrix G G ℝ) :
    Module.finrank ℝ (range B.toEuclideanLin) = B.rank :=
  (B.rank_eq_finrank_range_toLin (EuclideanSpace.basisFun G ℝ).toBasis
    (EuclideanSpace.basisFun G ℝ).toBasis).symm

omit [AddCommGroup G] in
private lemma rank_shift (B : Matrix G G ℝ) :
    (B + Matrix.vecMulVec (fun _ : G => (-2:ℝ)) (fun _ : G => (1:ℝ))).rank ≤ B.rank+1 := by
  let J := Matrix.vecMulVec (fun _ : G => (-2:ℝ)) (fun _ : G => (1:ℝ))
  change (B+J).rank ≤ _
  rw [← matrix_rank,map_add]
  calc
    _ ≤ Module.finrank ℝ (range B.toEuclideanLin + range J.toEuclideanLin) :=
      Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (by
      rw [matrix_rank,matrix_rank]
      exact Nat.add_le_add_left (Matrix.rank_vecMulVec_le _ _) _)

omit [AddCommGroup G] in
private lemma images_entries (B : Matrix G G ℝ) :
    ∑ j, ‖B.toEuclideanLin (EuclideanSpace.basisFun G ℝ j)‖^2 = ∑ j, ∑ i, (B i j)^2 := by
  apply sum_congr rfl
  intro j _
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.basisFun_apply]
  change ∑ i, ((B *ᵥ Pi.single j 1) i)^2 = _
  rw [Matrix.mulVec_single_one]
  rfl

/-- Squared entrywise error in a real matrix approximation to the full
ordered representation table. Each column is a translate of the profile. -/
def errorSq (A : Finset G) (B : Matrix G G ℝ) : ℝ :=
  ∑ j, ∑ i, ((reps A (i-j):ℝ)-B i j)^2

/-- The trace of the difference-count table forces residual error after any
real low-rank approximation of the ordered sum-count table. -/
theorem finite_rank_bound (A : Finset G) (B : Matrix G G ℝ) :
    (Fintype.card G:ℝ)*(A.card-2) ≤
      Real.sqrt (Fintype.card G)*Real.sqrt (errorSq A B) + (B.rank+1)*deviation A := by
  let R := table (fun z => (reps A z:ℝ)-2)
  let D := table (fun z => (diffReps A z:ℝ)-2)
  let J := Matrix.vecMulVec (fun _ : G => (-2:ℝ)) (fun _ : G => (1:ℝ))
  let K := B+J
  let b := EuclideanSpace.basisFun G ℝ
  have same (u) : ‖R.toEuclideanLin u‖=‖D.toEuclideanLin u‖ := gram_norm (gram A) u
  have cap (u) (hu : ‖u‖=1) : ‖D.toEuclideanLin u‖ ≤ deviation A := by
    rw [← same]
    simpa only [hu,mul_one,R,deviation] using table_cap (fun z => (reps A z:ℝ)-2) u
  have ineq := trace_rank_bound b R.toEuclideanLin D.toEuclideanLin K.toEuclideanLin same _ cap
  have d0 : diffReps A 0 = A.card := by simp only [diffReps,sub_eq_zero,← diag_eq_filter,diag_card]
  have diag : trace ℝ _ D.toEuclideanLin = (Fintype.card G:ℝ)*(A.card-2) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.trace_toLin_eq]
    simp [Matrix.trace,Matrix.diag,D,table,d0,mul_sub]
  have residual : ∑ i, ‖(R.toEuclideanLin-K.toEuclideanLin) (b i)‖^2 = errorSq A B := by
    rw [← map_sub,images_entries]
    apply sum_congr rfl; intro j _
    apply sum_congr rfl; intro i _
    simp [R,K,J,table,Matrix.vecMulVec,sub_eq_add_neg]
  rw [diag,residual,finrank_euclideanSpace,matrix_rank] at ineq
  have rk : (K.rank:ℝ) ≤ B.rank+1 := by
    have rkn : K.rank ≤ B.rank+1 := rank_shift B
    exact_mod_cast rkn
  exact ineq.trans (add_le_add_right (mul_le_mul_of_nonneg_right rk
    (sum_nonneg fun _ _ => abs_nonneg _)) _)

end Cyclic

section Limits

open Green33ShiftVariation Green33TailEnergy

variable {ι : Type*} {l : Filter ι} (M : ι → ℕ+) (A : (i : ι) → Finset (ZMod (M i)))
    (big : Tendsto (fun i => (M i).val) l atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))
    (cover : Tendsto (fun i => (((A i)+(A i)).card:ℝ)/(M i:ℝ)) l (𝓝 1))

include big size cover in
/-- Every real matrix of rank at most a fixed multiple of the square root of
the order leaves mean squared entry error with lower limit at least two. -/
theorem low_rank_residual (C : ℝ) {L : ℝ} (hL : L < 2) :
    ∀ᶠ i in l, ∀ B : Matrix (ZMod (M i)) (ZMod (M i)) ℝ,
      (B.rank:ℝ) ≤ C*Real.sqrt (M i) → L < errorSq (A i) B/(M i:ℝ)^2 := by
  obtain ⟨small, square⟩ := card_limits M (fun i => (A i).card) big size
  have deviationSmall : Tendsto (fun i => deviation (A i)/(M i:ℝ)) l (𝓝 0) := by
    have h := (((square.add (tendsto_const_nhds (x:=(2:ℝ)))).sub
      (cover.const_mul 4)).add (small.const_mul 2))
    norm_num at h
    apply squeeze_zero (fun i => div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)) _ h
    intro i
    have hm : (0:ℝ) < M i := by exact_mod_cast (M i).pos
    have up := div_le_div_of_nonneg_right (deviation_upper (A i)) hm.le
    rw [ZMod.card] at up
    apply up.trans_eq
    field_simp
  have twoSmall : Tendsto (fun i => 2/Real.sqrt (M i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big))
  have approx := (size.sub twoSmall).sub (deviationSmall.const_mul (C+1))
  simp only [mul_zero,sub_zero] at approx
  have threshold : Real.sqrt (max L 0) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by positivity)
    (max_lt hL (by norm_num))
  filter_upwards [approx.eventually_const_lt threshold] with i hi
  intro B hrank
  let m : ℝ := M i
  have hm : 0 < m := by dsimp [m]; exact_mod_cast (M i).pos
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hone : 1 ≤ Real.sqrt m  := Real.one_le_sqrt.mpr (by
    dsimp [m]
    exact_mod_cast (show 1 ≤ (M i).val from (M i).pos))
  have hd : 0 ≤ deviation (A i) := sum_nonneg fun _ _ => abs_nonneg _
  have bound := finite_rank_bound (A i) B
  rw [ZMod.card] at bound
  have hr : (B.rank:ℝ)+1 ≤ (C+1)*Real.sqrt m := by
    change _ ≤ C*Real.sqrt m at hrank
    linarith
  have bnd := bound.trans (add_le_add_right (mul_le_mul_of_nonneg_right hr hd) _)
  have divided := div_le_div_of_nonneg_right bnd (mul_pos hm hs).le
  change m*((A i).card-2)/(m*Real.sqrt m) ≤
    (Real.sqrt m*Real.sqrt (errorSq (A i) B)+(C+1)*Real.sqrt m*deviation (A i))/(m*Real.sqrt m) at divided
  have lhs : m*((A i).card-2)/(m*Real.sqrt m) =
      (A i).card/Real.sqrt m - 2/Real.sqrt m := by field_simp
  have rhs : (Real.sqrt m*Real.sqrt (errorSq (A i) B)+(C+1)*Real.sqrt m*deviation (A i))/(m*Real.sqrt m) =
      Real.sqrt (errorSq (A i) B)/m + (C+1)*(deviation (A i)/m) := by field_simp
  rw [lhs,rhs] at divided
  change Real.sqrt (max L 0) < (A i).card/Real.sqrt m - 2/Real.sqrt m - (C+1)*(deviation (A i)/m) at hi
  have ht : Real.sqrt (max L 0) < Real.sqrt (errorSq (A i) B)/m := by linarith
  have hsquared := (sq_lt_sq₀ (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hm.le)).mpr ht
  have he : 0 ≤ errorSq (A i) B := sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.sq_sqrt (le_max_right L 0),div_pow,Real.sq_sqrt he] at hsquared
  exact lt_of_le_of_lt (le_max_left _ _) hsquared

include big size in
/-- Full coverage as in the canonical Green 33 hypothesis. -/
theorem green_low_rank_residual (full : ∀ i, (A i)+(A i)=univ)
    (C : ℝ) {L : ℝ} (hL : L < 2) :
    ∀ᶠ i in l, ∀ B : Matrix (ZMod (M i)) (ZMod (M i)) ℝ,
      (B.rank:ℝ) ≤ C*Real.sqrt (M i) → L < errorSq (A i) B/(M i:ℝ)^2 := by
  apply low_rank_residual M A big size _ C hL
  refine tendsto_const_nhds.congr fun i => ?_
  rw [full,card_univ,ZMod.card,div_self (by exact_mod_cast (M i).ne_zero)]

end Limits

#print axioms gram_norm
#print axioms table_cap
#print axioms trace_rank_bound
#print axioms finite_rank_bound
#print axioms low_rank_residual
#print axioms green_low_rank_residual
end Green33LowRank
