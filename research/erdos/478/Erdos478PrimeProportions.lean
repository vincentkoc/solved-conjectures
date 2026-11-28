import Erdos478DensityOne

/-!
# Prime harmonic and ordinary proportions

Summation by parts transfers the checked log(p)/p estimate to reciprocal prime
weights. A separate theorem records exactly the ordinary prime ideal theorem
input needed for natural density.
-/

namespace Erdos478.GapDensity
noncomputable section
open NumberField Finset Filter Topology RootMoments GapVariance MeanDeficit

private def total (X : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ p ∈ Nat.primesLE X, a p
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by simp [mul_sum]

private theorem total_apply (X : ℕ) (a : ℕ → ℝ) : total X a = ∑ p ∈ Nat.primesLE X, a p := rfl

def ordinary (X : ℕ) : (ℕ → ℝ) →ₗ[ℝ] ℝ := ((Nat.primeCounting X : ℝ)⁻¹) • total X

private theorem total_mono (X : ℕ) {a b : ℕ → ℝ} (h : ∀ p, p.Prime → a p ≤ b p) :
    total X a ≤ total X b := sum_le_sum fun p hp => h p (Nat.mem_primesLE.mp hp).2

private theorem total_succ (a : ℕ → ℝ) (X : ℕ) :
    total (X+1) a = total X a + if (X+1).Prime then a (X+1) else 0 := by
  by_cases h : (X+1).Prime <;> simp [total,Nat.primesLE_succ,h,Nat.notMem_primesLE,add_comm]

private theorem ordinary_change {a b : ℕ → ℝ} (B : ℕ) (h : ∀ p > B, p.Prime → a p = b p) :
    Tendsto (fun X => ordinary X a - ordinary X b) atTop (𝓝 0) := by
  have eq : ∀ᶠ X : ℕ in atTop, ordinary X a - ordinary X b = total B (a-b) / Nat.primeCounting X := by
    filter_upwards [eventually_ge_atTop B] with X hx
    rw [← map_sub]
    simp only [ordinary,LinearMap.smul_apply,smul_eq_mul,div_eq_inv_mul]
    congr 1
    symm
    simp only [total_apply]
    apply sum_subset
    · intro p hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hx,(Nat.mem_primesLE.mp hp).2⟩
    · intro p hp hnot
      have hp' := (Nat.mem_primesLE.mp hp).2
      have hB : B < p := lt_of_not_ge fun hle => hnot (Nat.mem_primesLE.mpr ⟨hle,hp'⟩)
      simp [h p hB hp']
  exact (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp Nat.tendsto_primeCounting)).congr'
    (eq.mono fun _ h => h.symm)

/-- The degree-one consequence of the classical prime ideal theorem, stated
with ordinary rational-prime weights. It is a hypothesis of the natural-density
specialization below. -/
def DegreeOnePrimeIdealTheorem : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], Tendsto
    (fun X => ordinary X (fun p => (linearCount K p : ℝ))) atTop (𝓝 1)


/-- Degree-one counts for the rational field have ordinary prime mean one. -/
theorem ordinary_rational : Tendsto
    (fun X => ordinary X (fun p => (linearCount ℚ p : ℝ))) atTop (𝓝 1) := by
  obtain ⟨B,hB⟩ := RootPairs.order_maps_count ℚ (algebraMap ℤ (𝓞 ℚ))
    (algebraMap ℤ (𝓞 ℚ)).injective_int (by simp)
  have h := ordinary_change (a := fun p => (linearCount ℚ p : ℝ)) (b := 1) B (by
    intro p hp hpr
    rw [← hB p hp hpr]
    let : Nonempty (ℤ →+* ZMod p) := ⟨Int.castRingHom _⟩
    simp)
  have h1 : Tendsto (fun X => ordinary X 1) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Nat.tendsto_primeCounting.eventually_gt_atTop 0] with X hx
    simp [ordinary,total,Nat.primesLE_card_eq_primeCounting,hx.ne']
  simpa using h.add h1

/-- If every field has the same asymptotic for the number of degree-one
primes, division by the count for the rational field recovers the ordinary
rational-prime normalization. -/
theorem prime_ideal_input_of_common_scale (s : ℕ → ℝ) (hs : ∀ᶠ X in atTop, s X ≠ 0)
    (h : ∀ (K : Type) [Field K] [NumberField K], Tendsto
      (fun X => (∑ p ∈ Nat.primesLE X, (linearCount K p : ℝ)) / s X) atTop (𝓝 1)) :
    DegreeOnePrimeIdealTheorem := by
  intro K _ _
  have ht := ((h K).div (h ℚ) one_ne_zero).mul ordinary_rational
  simp only [div_one,one_mul] at ht
  apply ht.congr'
  filter_upwards [hs,(h ℚ).eventually_ne one_ne_zero] with X hsX hq
  have hq' : (∑ p ∈ Nat.primesLE X, (linearCount ℚ p : ℝ)) ≠ 0 := by
    intro hz
    exact hq (by simp [hz])
  change ((_ / s X) / (_ / s X)) * ((Nat.primeCounting X : ℝ)⁻¹ * _) =
    (Nat.primeCounting X : ℝ)⁻¹ * _
  dsimp only [total_apply]
  field_simp [hsX,hq']

private def countingAverage (h : DegreeOnePrimeIdealTheorem) : PrimeAverage where
  avg := ordinary
  mono X _ _ hab := mul_le_mul_of_nonneg_left (total_mono X hab) (by positivity)
  finite_change := ordinary_change
  ideal_mean := h

/-- With the ordinary degree-one prime ideal theorem supplied, the ordinary
proportion of primes missing any fixed number of residues tends to one. -/
theorem natural_density_of_prime_ideal_theorem (h : DegreeOnePrimeIdealTheorem) (D : ℕ) :
    Tendsto (fun X : ℕ => (((Nat.primesLE X).filter (fun p => D ≤ deficit p)).card : ℝ) /
      (Nat.primesLE X).card) atTop (𝓝 1) := by
  let A := countingAverage h
  have ht := (constant_mean A).sub (vanishing_for_average A D)
  rw [sub_zero] at ht
  apply ht.congr
  intro X
  rw [← map_sub]
  change (Nat.primeCounting X : ℝ)⁻¹*(∑ p ∈ Nat.primesLE X, (1-below D p)) = _
  rw [← Nat.primesLE_card_eq_primeCounting,div_eq_inv_mul]
  congr 1
  rw [card_filter]
  push_cast
  apply sum_congr rfl
  intro p _
  by_cases hd : D ≤ deficit p <;> simp [below,hd,not_lt.mpr,lt_of_not_ge]

/-- Abel summation with a nonincreasing nonnegative weight. A one-sided
bound for all partial sums transfers with its additive error multiplied by
the initial weight. -/
private theorem weight_transfer (a b w : ℕ → ℝ) (hw : Antitone w) (hw' : ∀ n, 0 ≤ w n)
    (C : ℝ) (h : ∀ X, total X a ≤ total X b + C) (X : ℕ) :
    total X (w*a) ≤ total X (w*b) + w 0*C := by
  let G := fun n => total n b+C-total n a
  let E := fun n => total n (w*b)+w 0*C-total n (w*a)
  have hg (n) : 0 ≤ G n := sub_nonneg.mpr (h n)
  have step (n) : E (n+1) = E n + w (n+1)*(G (n+1)-G n) := by
    simp only [G,E,total_succ,Pi.mul_apply]
    split <;> ring
  have lb (n) : w n * G n ≤ E n := by
    induction n with
    | zero => simp [G,E,total]
    | succ n ih =>
      rw [step]
      have := mul_le_mul_of_nonneg_right (hw (Nat.le_succ n)) (hg n)
      linarith
  exact sub_nonneg.mp ((mul_nonneg (hw' X) (hg X)).trans (lb X))


private theorem uniform_error (a b : ℕ → ℝ) (h : ∀ᶠ X : ℕ in atTop, total X a ≤ total X b) :
    ∃ C : ℝ, ∀ X, total X a ≤ total X b + C := by
  obtain ⟨B,hB⟩ := eventually_atTop.mp h
  let C := ∑ i ∈ range B, |total i a-total i b|
  have hc : 0 ≤ C := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨C,fun X => ?_⟩
  by_cases hX : B ≤ X
  · linarith [hB X hX]
  · have hm := single_le_sum (f := fun i => |total i a-total i b|) (fun i _ => abs_nonneg _)
        (mem_range.mpr (lt_of_not_ge hX))
    exact (sub_le_iff_le_add'.mp ((le_abs_self _).trans hm))

private theorem total_congr {a b : ℕ → ℝ} (h : ∀ p, p.Prime → a p = b p) (X : ℕ) :
    total X a = total X b := sum_congr rfl fun p hp => h p (Nat.mem_primesLE.mp hp).2

private def reciprocal (p : ℕ) : ℝ := (p:ℝ)⁻¹

private theorem reciprocal_top : Tendsto (fun X => total X reciprocal) atTop atTop := by
  apply tendsto_atTop.mpr
  intro c
  obtain ⟨S,hS⟩ := unbounded_mass c
  filter_upwards [eventually_ge_atTop (S.sup Subtype.val)] with X hX
  apply hS.le.trans
  let T := S.map (Function.Embedding.subtype Nat.Prime)
  have eq : ∑ p ∈ T, reciprocal p = mass S := by
    exact (Finset.sum_map S (Function.Embedding.subtype Nat.Prime) reciprocal).trans
      (sum_congr rfl fun _ _ => (one_div _).symm)
  rw [← eq,total_apply]
  apply sum_le_sum_of_subset_of_nonneg
  · rintro p hp
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hp
    exact Nat.mem_primesLE.mpr ⟨(le_sup (f := Subtype.val) hi).trans hX,i.property⟩
  · intro p _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem harmonic_bound (D : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ C : ℝ, ∀ X, total X (below D * reciprocal) ≤ δ*total X reciprocal + C := by
  let l := fun p : ℕ => Real.log p / p
  let w := fun p : ℕ => (Real.log (max 2 p : ℕ))⁻¹
  have hwpos (p : ℕ) : 0 < Real.log (max 2 p : ℕ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) (le_max_left 2 p)))
  have hw : Antitone w := fun p q h => inv_anti₀ (hwpos p)
    (Real.strictMonoOn_log.monotoneOn (by change (0:ℝ)<(max 2 p : ℕ); positivity) (by change (0:ℝ)<(max 2 q : ℕ); positivity) (by exact_mod_cast max_le_max_left 2 h))
  have he (X : ℕ) (a : ℕ → ℝ) : mean X a = total X (a*l)/Real.log X := by
    simp [mean,total,l,mul_div_assoc]
  have hax : ∀ᶠ X : ℕ in atTop, total X (below D*l) ≤ total X (δ • l) := by
    have h₁ := (vanishing_below D).eventually_lt_const (half_pos hδ)
    have h₂ := (constant_mean mertensAverage).eventually_const_lt (show (1:ℝ)/2<1 by norm_num)
    filter_upwards [h₁,h₂,eventually_ge_atTop 2] with X ha hb hx
    change 1/2 < mean X 1 at hb
    have hl : 0 < Real.log X := Real.log_pos (by exact_mod_cast (by omega : 1<X))
    rw [he,one_mul,lt_div_iff₀ hl] at hb
    rw [he,div_lt_iff₀ hl] at ha
    rw [map_smul,smul_eq_mul]
    nlinarith [mul_lt_mul_of_pos_left hb hδ]
  obtain ⟨C,hC⟩ := uniform_error _ _ hax
  refine ⟨w 0*C,fun X => ?_⟩
  have hb := weight_transfer _ _ w hw (fun p => (inv_pos.mpr (hwpos p)).le) C hC X
  have prod (p : ℕ) (hp : p.Prime) : w p*l p = reciprocal p := by
    have hl := Real.log_pos (show (1:ℝ)<p by exact_mod_cast hp.one_lt)
    dsimp [w,l,reciprocal]
    rw [max_eq_right hp.two_le]
    field_simp
  rw [total_congr (a := w*(below D*l)) (b := below D*reciprocal) (by
    intro p hp; change w p*(below D p*l p) = below D p*reciprocal p; rw [← prod p hp]; ring) X,
    total_congr (a := w*(δ • l)) (b := δ • reciprocal) (by
    intro p hp; change w p*(δ*l p) = δ*reciprocal p; rw [← prod p hp]; ring) X,
    map_smul,smul_eq_mul] at hb
  exact hb

private theorem harmonic_below (D : ℕ) :
    Tendsto (fun X => total X (below D * reciprocal) / total X reciprocal) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    apply Eventually.of_forall
    intro X
    apply hx.trans_le
    simp only [total_apply]
    apply div_nonneg <;> apply sum_nonneg
    · intro p _
      exact mul_nonneg (below_nonneg D p) (inv_nonneg.mpr (Nat.cast_nonneg _))
    · intro p _; exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · intro ε hε
    obtain ⟨C,hC⟩ := harmonic_bound D (ε/2) (half_pos hε)
    have hc : Tendsto (fun X => C/total X reciprocal) atTop (𝓝 0) := tendsto_const_nhds.div_atTop reciprocal_top
    filter_upwards [hc.eventually_lt_const (half_pos hε),reciprocal_top.eventually_gt_atTop 0] with X hx hp
    rw [div_lt_iff₀ hp] at hx ⊢
    linarith [hC X]

private def good (D : ℕ) (p : ℕ) : ℝ := if D≤deficit p then 1 else 0

private theorem good_eq (D : ℕ) : good D = 1-below D := by
  ext p
  by_cases hd : D ≤ deficit p <;> simp [good,below,hd,not_lt.mpr,lt_of_not_ge]

private theorem good_harmonic (D : ℕ) :
    Tendsto (fun X => total X (good D*reciprocal) / total X reciprocal) atTop (𝓝 1) := by
  have h := tendsto_const_nhds (x := (1:ℝ)) |>.sub (harmonic_below D)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [reciprocal_top.eventually_gt_atTop 0] with X hx
  rw [good_eq,sub_mul,one_mul,map_sub,sub_div,div_self hx.ne']

/-- Relative logarithmic density one among the primes. -/
theorem harmonic_density_one (D : ℕ) :
    Tendsto (fun X : ℕ =>
      (∑ p ∈ (Nat.primesLE X).filter (fun p => D ≤ deficit p), (p:ℝ)⁻¹) /
      (∑ p ∈ Nat.primesLE X, (p:ℝ)⁻¹)) atTop (𝓝 1) := by
  apply (good_harmonic D).congr
  intro X
  rw [sum_filter]
  congr 1
  rw [total_apply]
  apply sum_congr rfl
  intro p _
  by_cases hd : D≤deficit p <;> simp [good,reciprocal,hd]


private theorem good_count (D X : ℕ) :
    total X (good D) = (((Nat.primesLE X).filter (fun p => D≤deficit p)).card : ℝ) := by
  rw [card_filter,total_apply]
  push_cast
  apply sum_congr rfl
  intro p _
  by_cases hd : D≤deficit p <;> simp [good,hd]

/-- Without any ordinary prime ideal theorem, the upper relative natural
density of the good primes is one. -/
theorem frequently_proportion (D : ℕ) {α : ℝ} (hα : α<1) :
    ∃ᶠ X : ℕ in atTop, α*((Nat.primesLE X).card : ℝ) <
      ((Nat.primesLE X).filter (fun p => D≤deficit p)).card := by
  by_contra hf
  have he := not_frequently.mp hf
  have ha : ∀ᶠ X : ℕ in atTop, total X (good D) ≤ total X (α • (1 : ℕ → ℝ)) := by
    filter_upwards [he] with X hx
    rw [good_count,map_smul,smul_eq_mul]
    simpa [total] using le_of_not_gt hx
  obtain ⟨C,hC⟩ := uniform_error _ _ ha
  let w := fun n : ℕ => ((max 1 n : ℕ):ℝ)⁻¹
  have hw : Antitone w := fun a b h => inv_anti₀ (by positivity)
    (by exact_mod_cast max_le_max_left 1 h)
  have hw' (p) (hp : p.Prime) : w p = reciprocal p := by
    dsimp only [w,reciprocal]
    rw [max_eq_right hp.one_le]
  have hr (X : ℕ) : total X (good D*reciprocal) ≤ α*total X reciprocal + w 0*C := by
    have hb := weight_transfer _ _ w hw (fun n => by dsimp [w]; positivity) C hC X
    rw [total_congr (a := w*good D) (b := good D*reciprocal) (by
      intro p hp; change w p*good D p=good D p*reciprocal p; rw [hw' p hp,mul_comm]) X,
      total_congr (a := w*(α • (1:ℕ → ℝ))) (b := α • reciprocal) (by
        intro p hp; change w p*(α*1)=α*reciprocal p; rw [hw' p hp,mul_one,mul_comm]) X,
      map_smul,smul_eq_mul] at hb
    exact hb
  have hc : Tendsto (fun X => (w 0*C)/total X reciprocal) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop reciprocal_top
  have hh := (good_harmonic D).eventually_const_lt (show (1+α)/2<1 by linarith)
  obtain ⟨X,hX,hE,hP⟩ := (hh.and ((hc.eventually_lt_const (show 0<(1-α)/2 by linarith)).and
    (reciprocal_top.eventually_gt_atTop 0))).exists
  rw [lt_div_iff₀ hP] at hX
  rw [div_lt_iff₀ hP] at hE
  linarith [hr X]

#print axioms frequently_proportion

#print axioms harmonic_density_one

#print axioms natural_density_of_prime_ideal_theorem

end
end Erdos478.GapDensity
