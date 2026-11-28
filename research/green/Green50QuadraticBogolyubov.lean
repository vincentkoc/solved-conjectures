import Green50QuadraticRankDescent

/-! # Five sums of a binary quadratic graph

Averaging a weighted sum of scalar polar ranks over direction tuples bounds the cost of
making the graph affine modulo the attainable outputs. Two directions always suffice
for an affine flat of at least the input dimension.
-/

open Finset
open scoped Pointwise
namespace Green50QuadraticBogolyubov
open Green50QuadraticGraphs Green50QuadraticFibres Green50QuadraticFlats Green50QuadraticRankDescent
local notation "F₂" => ZMod 2
variable {U V : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] [DecidableEq U]
  [AddCommGroup V] [Module F₂ V] [Fintype V] [DecidableEq V]

noncomputable section
open scoped Classical
local instance : Fintype (Module.Dual F₂ V) := Fintype.ofInjective
  (fun l : Module.Dual F₂ V => (l : V → F₂)) DFunLike.coe_injective

private def evaluation (B : U →ₗ[F₂] U →ₗ[F₂] V) {k : ℕ} (a : Fin k → U) :
    (Fin k → U) →ₗ[F₂] V := ∑ j, (B (a j)).comp (LinearMap.proj j)

omit [Fintype U] [DecidableEq U] [DecidableEq V] in
private theorem annihilator_iff (B : U →ₗ[F₂] U →ₗ[F₂] V) {k : ℕ} (a : Fin k → U)
    (l : Module.Dual F₂ V) :
    l ∈ (evaluation B a).range.dualAnnihilator ↔ ∀ j, component B l (a j) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h j
    apply LinearMap.ext
    intro x
    apply h
    refine ⟨Pi.single j x,?_⟩
    simp [evaluation,LinearMap.sum_apply,Pi.single_apply,apply_ite]
  · rintro h _ ⟨x,rfl⟩
    simp only [evaluation,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,map_sum]
    exact sum_eq_zero (fun j _ => LinearMap.congr_fun (h j) (x j))

omit [DecidableEq U] in
private theorem weighted_directions (B : U →ₗ[F₂] U →ₗ[F₂] V) (k : ℕ) :
    ∃ a : Fin k → U,
      ∑ l : (evaluation B a).range.dualAnnihilator,
        (2:ℕ)^(k*Module.finrank F₂ (component B l.val).range) ≤ 2^Module.finrank F₂ V := by
  classical
  let rank (l : Module.Dual F₂ V) := Module.finrank F₂ (component B l).range
  let wt (l : Module.Dual F₂ V) := 2^(k*rank l)
  let good (a : Fin k → U) (l : Module.Dual F₂ V) := ∀ j, component B l (a j) = 0
  have cell (l : Module.Dual F₂ V) :
      (univ.filter fun a => good a l).card * wt l = Fintype.card (Fin k → U) := by
    let R := (component B l).ker
    let e : {a : Fin k → U // good a l} ≃ (Fin k → R) :=
      { toFun := fun p j => ⟨p.val j,p.property j⟩
        invFun := fun x => ⟨fun j => (x j).val,fun j => (x j).property⟩
        left_inv := by intro; rfl
        right_inv := by intro; rfl }
    have hcard : (univ.filter fun a => good a l).card = Fintype.card R ^ k := by
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun,Fintype.card_fin]
    rw [hcard,Fintype.card_fun,Fintype.card_fin,Module.card_eq_pow_finrank (K := F₂) (V := R),
      Module.card_eq_pow_finrank (K := F₂) (V := U)]
    change (2^Module.finrank F₂ R)^k * 2^(k*rank l) = (2^Module.finrank F₂ U)^k
    have he := congrArg (fun n : ℕ => n*k) (component B l).finrank_range_add_finrank_ker
    simp only [Nat.add_mul] at he
    rw [← pow_mul, ← pow_add, ← pow_mul]
    congr 1
    rw [Nat.mul_comm k]
    change rank l * k + Module.finrank F₂ R * k = _ at he
    omega
  have total : ∑ a : Fin k → U, ∑ l : Module.Dual F₂ V, (if good a l then wt l else 0) =
      ∑ _a : Fin k → U, 2^Module.finrank F₂ V := by
    rw [sum_comm]
    calc
      _ = ∑ l : Module.Dual F₂ V, Fintype.card (Fin k → U) := by
        apply sum_congr rfl
        intro l _
        rw [← sum_filter]
        simpa using cell l
      _ = _ := by
        simp only [sum_const,card_univ,nsmul_eq_mul]
        rw [Module.card_eq_pow_finrank (K := F₂) (V := Module.Dual F₂ V),Subspace.dual_finrank_eq]
        exact Nat.mul_comm _ _
  obtain ⟨a,_,ha⟩ := exists_le_of_sum_le (s := univ) univ_nonempty total.le
  refine ⟨a,?_⟩
  have eq := sum_subtype (F := (inferInstance : Fintype (evaluation B a).range.dualAnnihilator)) (univ.filter fun l => good a l)
    (p := fun l => l ∈ (evaluation B a).range.dualAnnihilator)
    (fun l => by simp only [mem_filter,mem_univ,true_and]; exact (annihilator_iff B a l).symm) wt
  rw [sum_filter] at eq
  change ∑ l : (evaluation B a).range.dualAnnihilator, wt l.val ≤ _
  rw [← eq]
  exact ha

/-- An affine lower bound on the exponential at integer exponents. -/
private theorem exp_support (m t : ℕ) : (m+2)*2^t ≤ t*2^t + 2*2^m := by
  by_cases h : m+2 ≤ t
  · exact (Nat.mul_le_mul_right _ h).trans (Nat.le_add_right _ _)
  · by_cases h' : m < t
    · have ht : t = m+1 := by omega
      rw [ht,pow_succ]
      exact le_of_eq (by ring)
    · obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h')
      have small : z+2 ≤ 2*2^z := by
        induction z with
        | zero => decide
        | succ z ih => rw [pow_succ]; omega
      rw [pow_add]
      nlinarith [Nat.mul_le_mul_right (2^t) small]

/-- A bound on the exponential mean bounds the ordinary mean of the exponents. -/
private theorem mean_exponent {E : Type*} [Fintype E] (f : E → ℕ) (t : ℕ)
    (h : (∑ z, 2^(f z)) ≤ Fintype.card E * 2^t) :
    (∑ z, f z) ≤ Fintype.card E * t := by
  classical
  let p := 2^t
  have hsum : ((∑ z, f z) + 2*Fintype.card E)*p ≤ (Fintype.card E*t+2*Fintype.card E)*p := by
    calc
      _ = ∑ z : E, (f z+2)*p := by rw [← sum_mul,sum_add_distrib]; simp [Nat.mul_comm]
      _ ≤ ∑ z : E, (t*p+2*2^(f z)) := sum_le_sum fun z _ => exp_support (f z) t
      _ = Fintype.card E*(t*p) + 2*(∑ z : E, 2^(f z)) := by
        simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id,mul_sum]
      _ ≤ Fintype.card E*(t*p) + 2*(Fintype.card E*p) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 h) _
      _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right hsum (show 0 < p by dsimp [p]; positivity)
  omega

private def sliceForm (B : U →ₗ[F₂] U →ₗ[F₂] V) (W : Submodule F₂ V) :
    W.dualAnnihilator →ₗ[F₂] LinearMap.BilinForm F₂ U :=
  { toFun := fun l => component B l.val
    map_add' := by intros; ext; rfl
    map_smul' := by intros; ext; rfl }

/-- Select input and output subspaces so that the polar form vanishes in the quotient
and every selected output is a sum of `k` polar values. -/
theorem polar_compression (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (k : ℕ) :
    ∃ (H : Submodule F₂ U) (W : Submodule F₂ V),
      (∀ x y : H, B x.val y.val ∈ W) ∧
      (∀ w : W, ((0:U),w.val) ∈ k • vertical B) ∧
      k*(Module.finrank F₂ U - Module.finrank F₂ H) ≤ 2*Module.finrank F₂ W := by
  classical
  obtain ⟨a,ha⟩ := weighted_directions B k
  let W := (evaluation B a).range
  let L := W.dualAnnihilator
  let m := Module.finrank F₂ W
  let R (l : L) := Module.finrank F₂ (sliceForm B W l).range
  have card : Fintype.card L * 2^m = 2^Module.finrank F₂ V := by
    rw [Module.card_eq_pow_finrank (K := F₂) (V := L)]
    change 2^Module.finrank F₂ W.dualAnnihilator * 2^Module.finrank F₂ W = _
    rw [←pow_add,Nat.add_comm,Subspace.finrank_add_finrank_dualAnnihilator_eq]
  have cost : k*(∑ z : L, R z) ≤ Fintype.card L*m := by
    rw [mul_sum]
    exact mean_exponent (fun z : L => k*R z) m (ha.trans_eq card.symm)
  have diag (x : U) : B x x = 0 := by
    have xx : x+x = 0 := by
      rw [← two_smul F₂ x,show (2:F₂)=0 by decide,zero_smul]
    have h := hf x x
    rw [xx,add_comm (f 0)] at h
    exact (add_right_cancel ((zero_add _).trans h)).symm
  obtain ⟨H,hiso,hc⟩ := common_isotropic_mean (sliceForm B W)
    (fun l x => by change l.val (B x x) = 0; rw [diag,map_zero])
  let loss := Module.finrank F₂ U - Module.finrank F₂ H
  change loss * Fintype.card L ≤ 2*(∑ z : L, R z) at hc
  have paid : k*loss ≤ 2*m := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < Fintype.card L from Fintype.card_pos)
    calc
      _ = k*(loss*Fintype.card L) := by ring
      _ ≤ k*(2*∑ z : L, R z) := Nat.mul_le_mul_left k hc
      _ = 2*(k*∑ z : L, R z) := by ring
      _ ≤ 2*(Fintype.card L*m) := Nat.mul_le_mul_left 2 cost
      _ = _ := by ring
  have his (x y : H) : B x.val y.val ∈ W :=
    (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp
      (fun l hl => hiso ⟨l,hl⟩ x x.property y y.property)
  have free (w : W) : ((0:U),w.val) ∈ k • vertical B := by
    obtain ⟨z,hz⟩ := w.property
    exact (mem_vertical_sum B k _).mpr ⟨a,z,by simpa [evaluation,LinearMap.sum_apply] using hz⟩
  exact ⟨H,W,his,free,paid⟩

/-- There are m attainable vertical dimensions. The cost of the horizontal restriction
is at most 2m/k for k independent polar products. -/
theorem weighted_graph_flat (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) (k : ℕ) :
    ∃ (S : Submodule F₂ (U × V)) (t : U × V) (m : ℕ), m ≤ Module.finrank F₂ V ∧
      (∀ p ∈ S, t+p ∈ (2*k+1) • graph f) ∧
      k*Module.finrank F₂ U + k*m ≤ k*Module.finrank F₂ S + 2*m := by
  classical
  obtain ⟨H,W,his,free,paid⟩ := polar_compression f B hf k
  let m := Module.finrank F₂ W
  let loss := Module.finrank F₂ U - Module.finrank F₂ H
  change k*loss ≤ 2*m at paid
  obtain ⟨S,t,hS,he⟩ := flat_of_compression f B hf H W his k free
  refine ⟨S,t,m,W.finrank_le,hS,?_⟩
  have decomp : Module.finrank F₂ U = Module.finrank F₂ H + loss :=
    (Nat.add_sub_of_le H.finrank_le).symm
  change Module.finrank F₂ S = Module.finrank F₂ H + m at he
  rw [decomp,he,Nat.mul_add,Nat.mul_add]
  omega

/-- Five sums of every binary quadratic graph contain an affine flat of dimension
at least its input dimension. The zero map attains equality. -/
theorem fivefold_quadratic_flat (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) :
    ∃ (S : Submodule F₂ (U × V)) (t : U × V),
      (∀ p ∈ S, t+p ∈ (5:ℕ) • graph f) ∧ Module.finrank F₂ U ≤ Module.finrank F₂ S := by
  obtain ⟨S,t,m,_,hS,hd⟩ := weighted_graph_flat f B hf 2
  exact ⟨S,t,hS,by omega⟩

/-- Three sums suffice for a flat of codimension at most twice the output dimension. -/
theorem threefold_quadratic_flat (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) :
    ∃ (S : Submodule F₂ (U × V)) (t : U × V),
      (∀ p ∈ S, t+p ∈ (3:ℕ) • graph f) ∧
      Module.finrank F₂ U ≤ Module.finrank F₂ S + Module.finrank F₂ V := by
  obtain ⟨S,t,m,hm,hS,hd⟩ := weighted_graph_flat f B hf 1
  exact ⟨S,t,hS,by omega⟩

/-- Ten sums give a linear codimension bound whenever A+A contains the indicated quadratic
graph over complementary subspaces. -/
theorem tenfold_quadratic_linear {G : Type*} [AddCommGroup G] [Module F₂ G] [Fintype G]
    [DecidableEq G] (A : Finset G) (U V : Submodule F₂ G) (hc : IsCompl U V)
    (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hg : Green50Graphs.graph U V f ⊆ A+A)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a)) :
    ∃ (W : Submodule F₂ G) (t : G), t +ᵥ (W : Set G) ⊆ (↑((10:ℕ) • A) : Set G) ∧
      Module.finrank F₂ G ≤ Module.finrank F₂ W + Module.finrank F₂ V := by
  classical
  obtain ⟨S,t,hS,hd⟩ := fivefold_quadratic_flat f B hf
  let e := U.prodEquivOfIsCompl V hc
  have hg' : (graph f).image e = Green50Graphs.graph U V f := by
    rw [graph,Green50Graphs.graph,image_image]
    rfl
  have hembed : ((5:ℕ) • graph f).image e ⊆ (10:ℕ) • A := by
    rw [image_nsmul,hg']
    simpa only [← two_nsmul, ← mul_smul, show (5:ℕ)*2=10 by decide] using
      (nsmul_subset_nsmul_left (n := 5) hg)
  refine ⟨S.map e.toLinearMap,e t,?_,?_⟩
  · rintro _ ⟨_,⟨w,hw,rfl⟩,rfl⟩
    apply hembed
    change e t + e w ∈ _
    rw [← map_add]
    exact mem_image_of_mem _ (hS w hw)
  · rw [← e.finrank_eq,Module.finrank_prod,← (S.equivMapOfInjective e.toLinearMap e.injective).finrank_eq]
    omega

/-- Green's tenfold conclusion with coefficient one for a quadratic graph model satisfying
the output-dimension bound from the twofold quotient construction. -/
theorem quadratic_model_green50 {n : ℕ} (A : Finset (Fin n → F₂))
    (U V : Submodule F₂ (Fin n → F₂)) (hc : IsCompl U V)
    (f : U → V) (B : U →ₗ[F₂] U →ₗ[F₂] V)
    (hg : Green50Graphs.graph U V f ⊆ A+A)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0+f a))
    (hd : (Module.finrank F₂ V : ℝ) ≤ Real.logb 2 (1/(A.dens:ℝ))) :
    ∃ (W : Submodule F₂ (Fin n → F₂)) (v : Fin n → F₂),
      v +ᵥ (W : Set (Fin n → F₂)) ⊆ ↑((10:ℕ) • A) ∧
        (n:ℝ) - Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W := by
  obtain ⟨W,t,hw,h⟩ := tenfold_quadratic_linear A U V hc f B hg hf
  refine ⟨W,t,hw,?_⟩
  rw [Module.finrank_pi,Fintype.card_fin] at h
  have h'' : (n:ℝ) ≤ (Module.finrank F₂ W:ℝ) + (Module.finrank F₂ V:ℝ) := by exact_mod_cast h
  linarith

end
end Green50QuadraticBogolyubov
#print axioms Green50QuadraticBogolyubov.polar_compression
#print axioms Green50QuadraticBogolyubov.weighted_graph_flat
#print axioms Green50QuadraticBogolyubov.fivefold_quadratic_flat
#print axioms Green50QuadraticBogolyubov.threefold_quadratic_flat
#print axioms Green50QuadraticBogolyubov.tenfold_quadratic_linear
#print axioms Green50QuadraticBogolyubov.quadratic_model_green50
