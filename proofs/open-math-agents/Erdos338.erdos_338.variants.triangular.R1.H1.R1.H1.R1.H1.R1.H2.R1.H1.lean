import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H2_R1

namespace OMA.GaussPsi

open Finset Polynomial

noncomputable section

/-- Odd factors `∏_{k<j} (1 - X^(2k+1))`. -/
def O (j : ℕ) : ℤ[X] := ∏ k ∈ range j, (1 - X ^ (2 * k + 1))

/-- Even factors `∏_{a<k≤b} (1 - X^(2k))`. -/
def Ev (a b : ℕ) : ℤ[X] := ∏ k ∈ Ico (a + 1) (b + 1), (1 - X ^ (2 * k))

/-- Shanks' sum, cleared of denominators. -/
def L (n : ℕ) : ℤ[X] := ∑ s ∈ range n, X ^ (s * (2 * n + 1)) * Ev s n * O s

/-- Triangular numbers. -/
def Tr (x : ℕ) : ℕ := ∑ j ∈ range x, (j + 1)

/-- Partial theta sum `∑_{x<2n} X^(T x)`. -/
def S (n : ℕ) : ℤ[X] := ∑ x ∈ range (2 * n), X ^ (Tr x)

/-- Telescoping term. -/
def beta (n j : ℕ) : ℤ[X] :=
  X ^ (j * (2 * n + 1)) * (∏ k ∈ Ico j (n + 1), (1 - X ^ (2 * k))) * O j

lemma Tr_succ (x : ℕ) : Tr (x + 1) = Tr x + (x + 1) := by
  simp [Tr, sum_range_succ]

lemma le_Tr (x : ℕ) : x ≤ Tr x := by
  induction x with
  | zero => simp [Tr]
  | succ x ih => rw [Tr_succ]; omega

lemma Tr_two (n : ℕ) :
    Tr (2 * n) = n * (2 * n + 1) ∧ Tr (2 * n + 1) = (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp [Tr]
  | succ n ih =>
    have h1 : Tr (2 * (n + 1)) = (n + 1) * (2 * (n + 1) + 1) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Tr_succ, ih.2]; ring
    refine ⟨h1, ?_⟩
    rw [Tr_succ, h1]; ring

lemma beta_zero (n : ℕ) : beta n 0 = 0 := by
  unfold beta
  rw [prod_eq_zero (i := 0) (by simp) (by simp)]
  simp

lemma Ev_succ_right (j n : ℕ) (h : j ≤ n) :
    Ev j (n + 1) = Ev j n * (1 - X ^ (2 * (n + 1))) := by
  unfold Ev
  rw [prod_Ico_succ_top (by omega)]

lemma prod_Ico_bot (j n : ℕ) (h : j < n + 1) :
    (∏ k ∈ Ico j (n + 1), (1 - X ^ (2 * k) : ℤ[X])) = (1 - X ^ (2 * j)) * Ev j n := by
  unfold Ev
  rw [prod_eq_prod_Ico_succ_bot h]

lemma O_succ (j : ℕ) : O (j + 1) = O j * (1 - X ^ (2 * j + 1)) := by
  simp [O, prod_range_succ]

lemma tele (n j : ℕ) (hj : j ≤ n) :
    ∑ s ∈ range j, (X ^ (s * (2 * n + 3)) * Ev s (n + 1) * O s -
      (1 - X ^ (2 * n + 1)) * (X ^ (s * (2 * n + 1)) * Ev s n * O s)) = beta n j := by
  induction j with
  | zero => simp [beta_zero]
  | succ j ih =>
    rw [sum_range_succ, ih (by omega), Ev_succ_right j n (by omega)]
    unfold beta
    rw [prod_Ico_bot j n (by omega), O_succ]
    have e : (∏ k ∈ Ico (j + 1) (n + 1), (1 - X ^ (2 * k) : ℤ[X])) = Ev j n := rfl
    rw [e]
    ring

lemma shanks (n : ℕ) : L n = O n * S n := by
  induction n with
  | zero => simp [L, S]
  | succ n ih =>
    have hL : L (n + 1) = beta n n + (1 - X ^ (2 * n + 1)) * L n +
        X ^ (n * (2 * n + 3)) * (1 - X ^ (2 * (n + 1))) * O n := by
      have hE : Ev n (n + 1) = 1 - X ^ (2 * (n + 1)) := by
        simp [Ev]
      have hc : ∀ s ∈ range n, X ^ (s * (2 * (n + 1) + 1)) * Ev s (n + 1) * O s =
          (X ^ (s * (2 * n + 3)) * Ev s (n + 1) * O s -
            (1 - X ^ (2 * n + 1)) * (X ^ (s * (2 * n + 1)) * Ev s n * O s)) +
          (1 - X ^ (2 * n + 1)) * (X ^ (s * (2 * n + 1)) * Ev s n * O s) := by
        intro s _
        rw [show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
        ring
      unfold L
      rw [sum_range_succ, sum_congr rfl hc, sum_add_distrib, tele n n le_rfl, ← mul_sum, hE,
        show 2 * (n + 1) + 1 = 2 * n + 3 by ring]
    have hb : beta n n = X ^ (n * (2 * n + 1)) * (1 - X ^ (2 * n)) * O n := by
      simp [beta]
    have hS : S (n + 1) = S n + X ^ (n * (2 * n + 1)) + X ^ ((n + 1) * (2 * n + 1)) := by
      unfold S
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ,
        (Tr_two n).1, (Tr_two n).2]
    rw [hL, hb, ih, hS, O_succ]
    ring

lemma dvd_mul_cong {M : ℕ} {a b c d : ℤ[X]} (h1 : X ^ M ∣ a - b) (h2 : X ^ M ∣ c - d) :
    X ^ M ∣ a * c - b * d := by
  have : a * c - b * d = (a - b) * c + b * (c - d) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

lemma prod_cong_one {M : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℤ[X])
    (h : ∀ i ∈ s, X ^ M ∣ f i - 1) : X ^ M ∣ (∏ i ∈ s, f i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have := dvd_mul_cong (h a (mem_insert_self a s))
      (ih (fun i hi => h i (mem_insert_of_mem hi)))
    simpa using this

lemma pow_cong_one {M k : ℕ} (hk : M ≤ k) : X ^ M ∣ (1 - X ^ k : ℤ[X]) - 1 := by
  have : (1 - X ^ k : ℤ[X]) - 1 = -(X ^ k) := by ring
  rw [this, dvd_neg]
  exact pow_dvd_pow _ hk

lemma pow_cong_one' {M k : ℕ} (hk : M ≤ k) : X ^ M ∣ (1 + X ^ k : ℤ[X]) - 1 := by
  have : (1 + X ^ k : ℤ[X]) - 1 = X ^ k := by ring
  rw [this]
  exact pow_dvd_pow _ hk

lemma one_sub_ne_zero {k : ℕ} (hk : k ≠ 0) : (1 - X ^ k : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  simp [zero_pow hk] at this

/-- Euler, finite form: `∏_{i<2N}(1+X^(i+1)) · O N = ∏_{N≤i<2N} (1 - X^(2(i+1)))`. -/
lemma euler (N : ℕ) :
    (∏ i ∈ range (2 * N), (1 + X ^ (i + 1) : ℤ[X])) * O N =
      ∏ i ∈ Ico N (2 * N), (1 - X ^ (2 * (i + 1)) : ℤ[X]) := by
  have ha : (∏ i ∈ range (2 * N), (1 + X ^ (i + 1) : ℤ[X])) *
      ∏ i ∈ range (2 * N), (1 - X ^ (i + 1) : ℤ[X]) =
      ∏ i ∈ range (2 * N), (1 - X ^ (2 * (i + 1)) : ℤ[X]) := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    rw [pow_mul']
    ring
  have hb : ∀ N : ℕ, (∏ i ∈ range (2 * N), (1 - X ^ (i + 1) : ℤ[X])) =
      O N * ∏ i ∈ range N, (1 - X ^ (2 * (i + 1)) : ℤ[X]) := by
    intro N
    induction N with
    | zero => simp [O]
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
        O_succ, prod_range_succ]
      rw [show 2 * N + 1 + 1 = 2 * (N + 1) by ring, show 2 * N + 1 = 2 * N + 1 by rfl]
      ring
  have hc : (∏ i ∈ range (2 * N), (1 - X ^ (2 * (i + 1)) : ℤ[X])) =
      (∏ i ∈ range N, (1 - X ^ (2 * (i + 1)) : ℤ[X])) *
        ∏ i ∈ Ico N (2 * N), (1 - X ^ (2 * (i + 1)) : ℤ[X]) :=
    (prod_range_mul_prod_Ico _ (by omega)).symm
  have hQ : (∏ i ∈ range N, (1 - X ^ (2 * (i + 1)) : ℤ[X])) ≠ 0 :=
    prod_ne_zero_iff.mpr (fun i _ => one_sub_ne_zero (by omega))
  rw [hb, hc] at ha
  apply mul_left_cancel₀ hQ
  rw [← ha]
  ring

/-- Gauss: `∏_{i=1}^m (1+X^i)(1-X^(2i)) ≡ ∑_{x≤m} X^(T x) (mod X^(m+1))`. -/
lemma gauss_cong (m : ℕ) :
    X ^ (m + 1) ∣ (∏ i ∈ Icc 1 m, ((1 + X ^ i) * (1 - X ^ (2 * i)) : ℤ[X])) -
      ∑ x ∈ range (m + 1), X ^ (Tr x) := by
  -- F ≡ Fbig
  have hF : X ^ (m + 1) ∣ (∏ i ∈ Icc 1 m, (1 + X ^ i : ℤ[X])) -
      ∏ i ∈ range (2 * (m + 1)), (1 + X ^ (i + 1) : ℤ[X]) := by
    rw [← prod_range_mul_prod_Ico _ (show m ≤ 2 * (m + 1) by omega)]
    have e : (∏ i ∈ Icc 1 m, (1 + X ^ i : ℤ[X])) =
        ∏ i ∈ range m, (1 + X ^ (i + 1) : ℤ[X]) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
      refine prod_congr (by simp) (fun i _ => by rw [add_comm 1 i])
    rw [e]
    have := dvd_mul_left (X ^ (m + 1)) (∏ i ∈ range m, (1 + X ^ (i + 1) : ℤ[X]))
    have h1 := prod_cong_one (M := (m + 1)) (Ico m (2 * (m + 1)))
      (fun i => (1 + X ^ (i + 1) : ℤ[X]))
      (fun i hi => pow_cong_one' (by simp at hi; omega))
    have : (∏ i ∈ range m, (1 + X ^ (i + 1) : ℤ[X])) -
        (∏ i ∈ range m, (1 + X ^ (i + 1) : ℤ[X])) *
          ∏ i ∈ Ico m (2 * (m + 1)), (1 + X ^ (i + 1)) =
        -((∏ i ∈ range m, (1 + X ^ (i + 1) : ℤ[X])) *
          ((∏ i ∈ Ico m (2 * (m + 1)), (1 + X ^ (i + 1) : ℤ[X])) - 1)) := by ring
    rw [this, dvd_neg]
    exact dvd_mul_of_dvd_right h1 _
  -- Gm ≡ Ev 0 (m + 1)
  have hG : X ^ (m + 1) ∣ (∏ i ∈ Icc 1 m, (1 - X ^ (2 * i) : ℤ[X])) - Ev 0 (m + 1) := by
    have e : Ev 0 (m + 1) =
        (∏ i ∈ Icc 1 m, (1 - X ^ (2 * i) : ℤ[X])) * (1 - X ^ (2 * (m + 1))) := by
      unfold Ev
      rw [prod_Ico_succ_top (by omega), Finset.Ico_add_one_right_eq_Icc]
    rw [e]
    have : (∏ i ∈ Icc 1 m, (1 - X ^ (2 * i) : ℤ[X])) -
        (∏ i ∈ Icc 1 m, (1 - X ^ (2 * i) : ℤ[X])) * (1 - X ^ (2 * (m + 1))) =
        -((∏ i ∈ Icc 1 m, (1 - X ^ (2 * i) : ℤ[X])) * ((1 - X ^ (2 * (m + 1))) - 1)) := by
      ring
    rw [this, dvd_neg]
    exact dvd_mul_of_dvd_right (pow_cong_one (by omega)) _
  -- Ev 0 (m + 1) ≡ L (m + 1)
  have hL : X ^ (m + 1) ∣ Ev 0 (m + 1) - L (m + 1) := by
    unfold L
    rw [sum_range_succ']
    have : Ev 0 (m + 1) - (∑ s ∈ range m,
        X ^ ((s + 1) * (2 * (m + 1) + 1)) * Ev (s + 1) (m + 1) * O (s + 1) +
        X ^ (0 * (2 * (m + 1) + 1)) * Ev 0 (m + 1) * O 0) =
        -(∑ s ∈ range m,
          X ^ ((s + 1) * (2 * (m + 1) + 1)) * Ev (s + 1) (m + 1) * O (s + 1)) := by
      simp [O]
    rw [this, dvd_neg]
    refine dvd_sum (fun s _ => ?_)
    rw [mul_assoc]
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by nlinarith)) _
  -- S (m + 1) ≡ Ψ
  have hS : X ^ (m + 1) ∣ S (m + 1) - ∑ x ∈ range (m + 1), X ^ (Tr x) := by
    unfold S
    rw [← sum_range_add_sum_Ico _ (show m + 1 ≤ 2 * (m + 1) by omega), add_sub_cancel_left]
    exact dvd_sum (fun x hx => pow_dvd_pow _ (by simp at hx; have := le_Tr x; omega))
  -- R ≡ 1
  have hR : X ^ (m + 1) ∣
      (∏ i ∈ Ico (m + 1) (2 * (m + 1)), (1 - X ^ (2 * (i + 1)) : ℤ[X])) - 1 :=
    prod_cong_one _ _ (fun i hi => pow_cong_one (by simp at hi; omega))
  -- assemble
  rw [prod_mul_distrib]
  have h2 : X ^ (m + 1) ∣ (∏ i ∈ Icc 1 m, (1 - X ^ (2 * i) : ℤ[X])) - L (m + 1) := by
    have := dvd_add hG hL
    rwa [sub_add_sub_cancel] at this
  have step1 := dvd_mul_cong hF h2
  -- Fbig * L (m + 1) = R * S (m + 1)
  have hFL : (∏ i ∈ range (2 * (m + 1)), (1 + X ^ (i + 1) : ℤ[X])) * L (m + 1) =
      (∏ i ∈ Ico (m + 1) (2 * (m + 1)), (1 - X ^ (2 * (i + 1)) : ℤ[X])) * S (m + 1) := by
    rw [shanks, ← mul_assoc, euler]
  have step2 : X ^ (m + 1) ∣
      (∏ i ∈ Ico (m + 1) (2 * (m + 1)), (1 - X ^ (2 * (i + 1)) : ℤ[X])) * S (m + 1) -
        S (m + 1) := by
    have : (∏ i ∈ Ico (m + 1) (2 * (m + 1)), (1 - X ^ (2 * (i + 1)) : ℤ[X])) * S (m + 1) -
        S (m + 1) =
        ((∏ i ∈ Ico (m + 1) (2 * (m + 1)), (1 - X ^ (2 * (i + 1)) : ℤ[X])) - 1) * S (m + 1) := by
      ring
    rw [this]
    exact dvd_mul_of_dvd_left hR _
  have := dvd_add (dvd_add step1 step2) hS
  rw [hFL] at this
  convert this using 1
  ring

lemma coeff_psi_cube (m : ℕ) :
    ((∑ x ∈ range (m + 1), X ^ (Tr x) : ℤ[X]) ^ 3).coeff m =
      (((range (m + 1) ×ˢ (range (m + 1) ×ˢ range (m + 1))).filter
        (fun v => Tr v.1 + Tr v.2.1 + Tr v.2.2 = m)).card : ℤ) := by
  have e : (∑ x ∈ range (m + 1), X ^ (Tr x) : ℤ[X]) ^ 3 =
      ∑ v ∈ range (m + 1) ×ˢ (range (m + 1) ×ˢ range (m + 1)),
        X ^ (Tr v.1 + Tr v.2.1 + Tr v.2.2) := by
    rw [pow_three, sum_mul, sum_product]
    refine sum_congr rfl (fun a _ => ?_)
    rw [sum_mul_sum, sum_product, mul_sum]
    refine sum_congr rfl (fun b _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun c _ => ?_)
    ring
  rw [e, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [sum_boole]
  congr 2
  ext v
  simp [eq_comm]

theorem main (m : ℕ) :
    ((∏ i ∈ Icc 1 m, ((1 + X ^ i) * (1 - X ^ (2 * i)) : ℤ[X])) ^ 3).coeff m =
      (((range (m + 1) ×ˢ (range (m + 1) ×ˢ range (m + 1))).filter
        (fun v => Tr v.1 + Tr v.2.1 + Tr v.2.2 = m)).card : ℤ) := by
  rw [← coeff_psi_cube]
  have h := dvd_trans (gauss_cong m) (sub_dvd_pow_sub_pow _ _ 3)
  have := (X_pow_dvd_iff.mp h) m (by omega)
  rw [coeff_sub, sub_eq_zero] at this
  exact this

end

end OMA.GaussPsi

theorem OMA.solution : OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro m
  exact OMA.GaussPsi.main m
