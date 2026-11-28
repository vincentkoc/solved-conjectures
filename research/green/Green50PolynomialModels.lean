import Mathlib.FieldTheory.ChevalleyWarning
import Green50HammingDensity
import Green50Graphs
import Green50HalfDensity

/-!
# Polynomial equations and binary quadratic graphs

Chevalley–Warning on a coordinate face through an extremal zero bounds how many coordinates
can vanish at every solution. The second part represents a quadratic graph by equations in
the original ambient coordinates, including when both summands are arbitrary subspaces.
-/
open MvPolynomial Finset
open scoped Pointwise

namespace Green50PolynomialModels
private theorem degree_subst {K σ τ : Type*} [CommSemiring K]
    (p : MvPolynomial σ K) (g : σ → MvPolynomial τ K)
    (hg : ∀ i, (g i).totalDegree ≤ 1) : (aeval g p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  change (C (coeff s p) : MvPolynomial τ K).totalDegree + _ ≤ _
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd s.support _).trans ((Finset.sum_le_sum ?_).trans (le_totalDegree hs))
  intro i hi
  exact (totalDegree_pow _ _).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (s i) (hg i))

/-- Over a finite field, every nonempty polynomial zero set has a point with at most the sum
of the defining degrees many zero coordinates. -/
theorem few_zero_coordinates {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype σ] [DecidableEq σ] [Fintype ι] (p : ℕ) [CharP K p] (hp : p.Prime)
    (f : ι → MvPolynomial σ K) (hne : ∃ x, ∀ i, eval x (f i) = 0) :
    ∃ x : σ → K, (∀ i, eval x (f i) = 0) ∧
      (univ.filter fun j => x j = 0).card ≤ ∑ i, (f i).totalDegree := by
  classical
  let zeros (x : σ → K) := univ.filter fun j => x j = 0
  let sol := univ.filter fun x : σ → K => ∀ i, eval x (f i) = 0
  obtain ⟨x₀,h₀⟩ := hne
  obtain ⟨x,hx,hmin⟩ := sol.exists_min_image (fun x => (zeros x).card)
    ⟨x₀, by simpa [sol] using h₀⟩
  have hx' : ∀ i, eval x (f i) = 0 := by simpa [sol] using hx
  refine ⟨x,hx',?_⟩
  change (zeros x).card ≤ _
  by_contra! h
  let s := zeros x
  let g (j : σ) : MvPolynomial s K := if hj : j ∈ s then X ⟨j,hj⟩ else C (x j)
  let lift (z : s → K) (j : σ) := if hj : j ∈ s then z ⟨j,hj⟩ else x j
  have heval (z : s → K) (i : ι) :
      eval z (aeval g (f i)) = eval (lift z) (f i) := by
    change (aeval z) (aeval g (f i)) = aeval (lift z) (f i)
    rw [comp_aeval_apply]
    congr 2
    funext j
    by_cases hj : j ∈ s <;> simp [g,lift,hj]
  have hdeg : (∑ i, (aeval g (f i)).totalDegree) < Fintype.card s := by
    rw [Fintype.card_coe]
    exact (sum_le_sum fun i _ => degree_subst (f i) g (fun j => by
      by_cases hj : j ∈ s <;> simp [g,hj])).trans_lt h
  have hd := char_dvd_card_solutions_of_fintype_sum_lt p hdeg
  have h0 : lift 0 = x := by
    funext j
    by_cases hj : j ∈ s
    · have h' : x j = 0 := (mem_filter.mp hj).2
      simp [lift,hj,h']
    · simp [lift,hj]
  have hu : Fintype.card {z : s → K // ∀ i, eval z (aeval g (f i)) = 0} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨0,fun i => by rw [heval,h0,hx']⟩,?_⟩
    rintro ⟨z,hz⟩
    have hl : lift z ∈ sol := by
      apply mem_filter.mpr
      exact ⟨mem_univ _,fun i => (heval z i).symm.trans (hz i)⟩
    have hs : zeros (lift z) ⊆ s := by
      intro j hj
      by_contra hnot
      have h' : lift z j = 0 := (mem_filter.mp hj).2
      have hxj : x j = 0 := by simpa [lift,hnot] using h'
      exact hnot (mem_filter.mpr ⟨mem_univ _,hxj⟩)
    have hsame := eq_of_subset_of_card_le hs (hmin _ hl)
    apply Subtype.ext
    funext j
    have hmem : j.val ∈ zeros (lift z) := hsame.symm ▸ j.property
    have h' : lift z j.val = 0 := (mem_filter.mp hmem).2
    simpa [lift,j.property] using h'
  rw [hu] at hd
  exact hp.not_dvd_one hd

local notation "K" => ZMod 2
private theorem polynomial_of_quadratic {n : ℕ} (f : (Fin n → K) → K)
    (hf : ∀ a, ∃ l : (Fin n → K) →ₗ[K] K,
       ∀ x, f x + f (x+a) = l x + (f 0 + f a)) :
    ∃ P : MvPolynomial (Fin n) K, P.totalDegree ≤ 2 ∧ ∀ x, eval x P = f x := by
  classical
  let e (j : Fin n) : Fin n → K := Pi.single j (1:K)
  let mask (s : Finset (Fin n)) (x : Fin n → K) := ∑ j ∈ s, x j • e j
  have lin (l : (Fin n → K) →ₗ[K] K) (s : Finset (Fin n)) :
      ∃ Q : MvPolynomial (Fin n) K, Q.totalDegree ≤ 1 ∧ ∀ x, eval x Q = l (mask s x) := by
    refine ⟨∑ i ∈ s, C (l (e i)) * X i,totalDegree_finsetSum_le (fun i _ =>
      (totalDegree_mul _ _).trans (by simp)),?_⟩
    intro x
    simp [mask,smul_eq_mul,mul_comm]
  have partialEval (s : Finset (Fin n)) :
      ∃ P : MvPolynomial (Fin n) K, P.totalDegree ≤ 2 ∧ ∀ x, eval x P = f (mask s x) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨C (f 0), by simp, by simp [mask]⟩
    | @insert j s hj ih =>
      obtain ⟨P,hP,hp⟩ := ih
      obtain ⟨l,hl⟩ := hf (e j)
      obtain ⟨Q,hQ,hq⟩ := lin l s
      refine ⟨P + X j * (Q + C (f 0 + f (e j))),
        (totalDegree_add ..).trans (max_le hP ((totalDegree_mul ..).trans ?_)),?_⟩
      · have := totalDegree_add Q (C (f 0 + f (e j)))
        simp only [totalDegree_C, _root_.max_zero] at this
        rw [totalDegree_X]; omega
      · intro x
        have hx : mask (insert j s) x = x j • e j + mask s x := by simp [mask,hj]
        simp only [map_add,map_mul,eval_X,eval_C,hq,hp,hx]
        have hb : ∀ b : K, b = 0 ∨ b = 1 := by decide
        rcases hb (x j) with h | h
        · simp [h]
        · simp only [h,one_smul,one_mul]
          have key := hl (mask s x)
          rw [add_comm (e j) (mask s x)]
          linear_combination -key + (by decide : (2:K) = 0) * f (mask s x)
  obtain ⟨P,hP,hp⟩ := partialEval univ
  refine ⟨P,hP,fun x => (hp x).trans (congrArg f ?_)⟩
  funext i
  simp [mask,e,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]

/-- In the original ambient coordinates a full quadratic graph over complementary subspaces
is the common zero set of one quadratic equation per output dimension. -/
theorem quadratic_graph_equations {n : ℕ} (U V : Submodule K (Fin n → K))
    (hc : IsCompl U V) (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0 + f a)) :
    ∃ P : Fin (Module.finrank K V) → MvPolynomial (Fin n) K,
      (∀ i, (P i).totalDegree ≤ 2) ∧
      ∀ x, x ∈ Green50Graphs.graph U V f ↔ ∀ i, eval x (P i) = 0 := by
  classical
  let e := U.prodEquivOfIsCompl V hc
  let u : (Fin n → K) →ₗ[K] U := (LinearMap.fst K U V).comp e.symm.toLinearMap
  let v : (Fin n → K) →ₗ[K] V := (LinearMap.snd K U V).comp e.symm.toLinearMap
  let b := Module.finBasis K V
  let g (i : Fin (Module.finrank K V)) (x : Fin n → K) := b.coord i (f (u x)) + b.coord i (v x)
  have h (i : Fin (Module.finrank K V)) :
      ∃ P : MvPolynomial (Fin n) K, P.totalDegree ≤ 2 ∧ ∀ x, eval x P = g i x := by
    apply polynomial_of_quadratic
    intro a
    let c := b.coord i
    refine ⟨(c.comp (B (u a))).comp u,?_⟩
    intro x
    have he := congrArg c (hf (u a) (u x))
    simp only [map_add] at he
    change c (f (u x)) + c (v x) + (c (f (u (x+a))) + c (v (x+a))) =
      c (B (u a) (u x)) + (c (f (u 0)) + c (v 0) + (c (f (u a)) + c (v a)))
    simp only [map_zero,map_add,add_zero]
    linear_combination he + (by decide : (2:K)=0) * c (v x)
  choose P hdeg hval using h
  refine ⟨P,hdeg,?_⟩
  intro x
  have char : x ∈ Green50Graphs.graph U V f ↔ v x = f (u x) := by
    constructor
    · intro hx
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hx
      change e (a, f a) = x at ha
      subst x
      change (e.symm (e (a,f a))).2 = f ((e.symm (e (a,f a))).1)
      simp
    · intro hx
      apply Finset.mem_image.mpr
      refine ⟨u x, mem_univ _,?_⟩
      change e (u x,f (u x)) = x
      rw [←hx]
      exact e.apply_symm_apply x
  rw [char]
  simp_rw [hval]
  constructor
  · intro h i
    change b.coord i (f (u x)) + b.coord i (v x) = 0
    rw [h]
    exact (by decide : ∀ t : K, t+t=0) _
  · intro h
    apply b.repr.injective
    ext i
    have hi := h i
    change b.coord i (f (u x)) + b.coord i (v x) = 0 at hi
    change b.coord i (v x) = b.coord i (f (u x))
    exact (by decide : ∀ a c : K, a+c=0 → c=a) _ _ hi


/-- If a nonempty polynomial zero set lies in an iterated binary Hamming ball, its total
defining degree is at least the gap between the ambient dimension and the weight bound. -/
theorem degree_in_ball_sum {n k r : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → MvPolynomial (Fin n) K) (hne : ∃ x, ∀ i, eval x (P i) = 0)
    (hc : ∀ x, (∀ i, eval x (P i) = 0) → x ∈ r • Green50Sharp.ball n k) :
    n ≤ r*k + ∑ i, (P i).totalDegree := by
  obtain ⟨x,hx,hd⟩ := few_zero_coordinates 2 Nat.prime_two P hne
  have hw := Green50Sharp.weight_of_mem_sum (hc x hx)
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun i => x i = 0)
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  change (univ.filter fun i => x i ≠ 0).card ≤ r*k at hw
  calc
    n = (univ.filter fun i => x i ≠ 0).card + (univ.filter fun i => x i = 0).card := by
      rw [add_comm]; exact hcard.symm
    _ ≤ _ := Nat.add_le_add hw hd

/-- A quadratic graph inside a twofold Hamming ball must pay at least half the weight gap
in output dimension, independently of the chosen complement. -/
theorem quadratic_codimension {n k : ℕ} (U V : Submodule K (Fin n → K))
    (hc : IsCompl U V) (f : U → V) (B : U →ₗ[K] U →ₗ[K] V)
    (hf : ∀ a x, f x + f (x+a) = B a x + (f 0 + f a))
    (hg : Green50Graphs.graph U V f ⊆ Green50Sharp.ball n k + Green50Sharp.ball n k) :
    n ≤ 2*k + 2*Module.finrank K V := by
  classical
  obtain ⟨P,hP,heq⟩ := quadratic_graph_equations U V hc f B hf
  have hne : ∃ x, ∀ i, eval x (P i) = 0 :=
    ⟨_,(heq _).mp (Finset.mem_image.mpr ⟨(0:U),mem_univ _,rfl⟩)⟩
  have h := degree_in_ball_sum (r:=2) P hne (fun x hx => by
    simpa only [two_nsmul] using hg ((heq x).mpr hx))
  have hle : (∑ i, (P i).totalDegree) ≤ ∑ _i : Fin (Module.finrank K V), 2 :=
    sum_le_sum fun i _ => hP i
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at hle
  omega


private theorem linear_polynomial {n : ℕ} (l : (Fin n → K) →ₗ[K] K) :
    ∃ Q : MvPolynomial (Fin n) K, Q.totalDegree ≤ 1 ∧ ∀ x, eval x Q = l x := by
  classical
  let e (i : Fin n) : Fin n → K := Pi.single i 1
  refine ⟨∑ i, C (l (e i)) * X i,totalDegree_finsetSum_le (fun i _ =>
    (totalDegree_mul _ _).trans (by simp)),?_⟩
  intro x
  have hx : (∑ i, x i • e i) = x := by
    funext j; simp [e,Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  conv_rhs => rw [←hx, map_sum]
  simp [smul_eq_mul,mul_comm]

/-- Any polynomial graph inside a Hamming-ball sum has a degree budget at least as large
as the missing weight. Both coordinate bases and the ambient complementary subspaces are
arbitrary. Each coordinate of degree zero still costs one linear equation. -/
theorem polynomial_graph_degree {n k r : ℕ} {I J : Type*} [Fintype J]
    (U V : Submodule K (Fin n → K)) (hc : IsCompl U V)
    (bu : Module.Basis I K U) (bv : Module.Basis J K V) (f : U → V)
    (P : J → MvPolynomial I K)
    (hf : ∀ a j, bv.coord j (f a) = eval (fun i => bu.coord i a) (P j))
    (hg : Green50Graphs.graph U V f ⊆ r • Green50Sharp.ball n k) :
    n ≤ r*k + ∑ j, max 1 (P j).totalDegree := by
  classical
  let e := U.prodEquivOfIsCompl V hc
  let u : (Fin n → K) →ₗ[K] U := (LinearMap.fst K U V).comp e.symm.toLinearMap
  let v : (Fin n → K) →ₗ[K] V := (LinearMap.snd K U V).comp e.symm.toLinearMap
  choose L hdeg heval using fun i => linear_polynomial ((bu.coord i).comp u)
  choose M hM hm using fun j => linear_polynomial ((bv.coord j).comp v)
  let Q (j : J) := M j + aeval L (P j)
  have qdeg (j : J) : (Q j).totalDegree ≤ max 1 (P j).totalDegree :=
    (totalDegree_add ..).trans (max_le_max (hM j) (degree_subst _ _ hdeg))
  have qeval (x : Fin n → K) (j : J) : eval x (Q j) = bv.coord j (v x) + bv.coord j (f (u x)) := by
    dsimp only [Q]
    rw [map_add,hm,hf]
    congr 1
    change aeval x (aeval L (P j)) = aeval (fun i => bu.coord i (u x)) (P j)
    rw [comp_aeval_apply]
    congr 2
    funext i
    exact heval i x
  have char (x : Fin n → K) : (∀ j, eval x (Q j) = 0) ↔ v x = f (u x) := by
    constructor
    · intro h
      apply bv.repr.injective
      ext j
      apply (by decide : ∀ a c : K, a+c=0 → a=c)
      exact (qeval x j).symm.trans (h j)
    · intro h j
      rw [qeval,h]
      exact (by decide : ∀ a : K, a+a=0) _
  have hz : v (e (0,f 0)) = f (u (e (0,f 0))) := by
    change (e.symm (e (0,f 0))).2 = f ((e.symm (e (0,f 0))).1)
    simp
  have h := degree_in_ball_sum Q ⟨_,(char _).mpr hz⟩ (fun x hx => hg (by
    apply Finset.mem_image.mpr
    refine ⟨u x, mem_univ _,?_⟩
    change e (u x,f (u x)) = x
    rw [←(char _).mp hx]
    exact e.apply_symm_apply x))
  exact h.trans (Nat.add_le_add_left (sum_le_sum fun j _ => qdeg j) _)

/-- At any fixed density below one half there are arbitrarily large binary balls whose
twofold sum contains no nonempty zero set of bounded total defining degree. -/
theorem near_half_degree (ρ : ℝ) (hρ : ρ < 1/2) (D N : ℕ) :
    ∃ n ≥ N, ∃ k, ρ < ((Green50Sharp.ball n k).dens : ℝ) ∧
      ∀ (j : ℕ) (P : Fin j → MvPolynomial (Fin n) K),
        (∃ x, ∀ i, eval x (P i) = 0) →
        (∀ x, (∀ i, eval x (P i) = 0) → x ∈ Green50Sharp.ball n k + Green50Sharp.ball n k) →
        D < ∑ i, (P i).totalDegree := by
  obtain ⟨n,hn,k,hα,hgap⟩ := Green50HammingDensity.near_half_gap ρ hρ D N
  refine ⟨n,hn,k,hα,?_⟩
  intro j P hne hzero
  have h := degree_in_ball_sum (r:=2) P hne (fun x hx => by simpa only [two_nsmul] using hzero x hx)
  omega

/-- Below density one half no constant multiple of the density logarithm guarantees
a full quadratic graph in the twofold sum, even after allowing arbitrary complements. -/
theorem positive_density_obstruction (ρ C : ℝ) (hρ : ρ < 1/2) (hC : 0 ≤ C) (N : ℕ) :
    ∃ n ≥ N, ∃ k, ρ < ((Green50Sharp.ball n k).dens : ℝ) ∧
      ∀ (U V : Submodule K (Fin n → K)), IsCompl U V →
        ∀ (f : U → V) (B : U →ₗ[K] U →ₗ[K] V),
          (∀ a x, f x + f (x+a) = B a x + (f 0 + f a)) →
          Green50Graphs.graph U V f ⊆ Green50Sharp.ball n k + Green50Sharp.ball n k →
          C * Real.logb 2 (1 / ((Green50Sharp.ball n k).dens : ℝ)) < Module.finrank K V := by
  obtain ⟨n,hn,k,hα,hgap⟩ := Green50HammingDensity.near_half_gap (max ρ (1/4)) (max_lt hρ (by norm_num))
    (2*⌈2*C⌉₊) N
  refine ⟨n,hn,k,(le_max_left ..).trans_lt hα,?_⟩
  intro U V hc f B hf hg
  have hdim := quadratic_codimension U V hc f B hf hg
  have hsV : ⌈2*C⌉₊ < Module.finrank K V := by omega
  have hquarter := (le_max_right ..).trans_lt hα
  have hpos : 0 < ((Green50Sharp.ball n k).dens : ℝ) := by linarith
  have hlog : Real.logb 2 (1 / ((Green50Sharp.ball n k).dens : ℝ)) ≤ 2 := by
    apply (Real.logb_le_iff_le_rpow (by norm_num) (by positivity)).mpr
    rw [div_le_iff₀ hpos]
    norm_num
    linarith
  calc
    _ ≤ C*2 := mul_le_mul_of_nonneg_left hlog hC
    _ ≤ (⌈2*C⌉₊:ℝ) := by simpa only [mul_comm C 2] using Nat.le_ceil (2*C)
    _ < _ := by exact_mod_cast hsV

/-- All binary sets of density at least `ρ` admit a nonempty polynomial zero set of bounded
total defining degree in their twofold sum. The bound is uniform in the ambient dimension. -/
def BoundedDegreeModels (ρ : ℝ) : Prop :=
  ∃ D : ℕ, ∀ (n : ℕ) (A : Finset (Fin n → K)), ρ ≤ (A.dens:ℝ) →
    ∃ (j : ℕ) (P : Fin j → MvPolynomial (Fin n) K),
      (∃ x, ∀ i, eval x (P i) = 0) ∧
      (∀ x, (∀ i, eval x (P i) = 0) → x ∈ A+A) ∧
      ∑ i, (P i).totalDegree ≤ D

/-- One half is exactly the density threshold for a uniform polynomial-system bound.
At and above the endpoint a single linear equation suffices. -/
theorem bounded_degree_iff (ρ : ℝ) : BoundedDegreeModels ρ ↔ 1/2 ≤ ρ := by
  constructor
  · rintro ⟨D,hD⟩
    by_contra! hρ
    obtain ⟨n,_,k,ha,h⟩ := near_half_degree ρ hρ D 0
    obtain ⟨j,P,hne,hzero,hdeg⟩ := hD n _ ha.le
    exact (Nat.not_lt_of_ge hdeg) (h j P hne hzero)
  · intro hρ
    refine ⟨1,?_⟩
    intro n A ha
    obtain ⟨l,hl⟩ := Green50HalfDensity.half_density_kernel A (hρ.trans ha)
    obtain ⟨Q,hQ,hq⟩ := linear_polynomial l
    refine ⟨1,fun _ => Q,⟨0,fun _ => by rw [hq,map_zero]⟩,?_,?_⟩
    · intro x hx
      exact hl x ((hq x).symm.trans (hx 0))
    · simpa using hQ

#print axioms Green50PolynomialModels.bounded_degree_iff

#print axioms Green50PolynomialModels.near_half_degree
#print axioms Green50PolynomialModels.polynomial_graph_degree
#print axioms Green50PolynomialModels.positive_density_obstruction

#print axioms Green50PolynomialModels.few_zero_coordinates
#print axioms Green50PolynomialModels.quadratic_graph_equations
#print axioms Green50PolynomialModels.degree_in_ball_sum
#print axioms Green50PolynomialModels.quadratic_codimension

end Green50PolynomialModels
