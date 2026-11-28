import Mathlib

/-! Dirichlet mass of prime seeds in the squarefree sieve. -/

namespace CunninghamChain
namespace PrimeMass
open Finset Filter Topology ArithmeticFunction
open ArithmeticFunction.vonMangoldt

/-- Prime logarithms restricted to a set of seeds. -/
noncomputable def weight (A : Set ℕ) (n : ℕ) : ℝ :=
  open Classical in if n.Prime ∧ n∈A then Real.log n else 0

/-- Dirichlet series of the prime logarithmic weights. -/
noncomputable def mass (A : Set ℕ) (s : ℝ) := ∑' n, weight A n/(n:ℝ)^s

theorem weight_nonneg (A : Set ℕ) (n : ℕ) : 0 ≤ weight A n := by
  unfold weight
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.1.one_le)
  · rfl

theorem summable_weight (A : Set ℕ) {s : ℝ} (hs : 1<s) :
    Summable fun n => weight A n/(n:ℝ)^s := by
  have H := LSeries.summable_real_of_abscissaOfAbsConv_lt
    (lt_of_le_of_lt (abscissaOfAbsConv_residueClass_le_one (0:ZMod 1)) (by exact_mod_cast hs))
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (weight_nonneg A n) (by positivity)) _ H
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  have eq : residueClass (0:ZMod 1) n=vonMangoldt n := by simp [residueClass,Subsingleton.elim (n:ZMod 1) 0]
  rw [eq,weight]
  split_ifs with h
  · rw [vonMangoldt_apply_prime h.1]
  · exact vonMangoldt_nonneg

private lemma weighted_sum_le {f g w : ℕ → ℝ} (hw : Antitone w) (hw₀ : ∀ n, 0≤w n)
    (h : ∀ n, ∑ i ∈ range n, f i ≤ ∑ i ∈ range n, g i) (n : ℕ) :
    ∑ i ∈ range n, w i * f i ≤ ∑ i ∈ range n, w i * g i := by
  have H := sum_range_by_parts w (fun i => g i-f i) n
  simp only [sum_sub_distrib,smul_eq_mul,mul_sub_left_distrib] at H
  have hsign : ∑ i ∈ range (n-1), (w (i+1)-w i)*((∑ j ∈ range (i+1),g j)-(∑ j ∈ range (i+1),f j)) ≤ 0 :=
    sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hw (Nat.le_succ i))) (sub_nonneg.mpr (h _))
  have hh := mul_nonneg (hw₀ (n-1)) (sub_nonneg.mpr (h n))
  simp only [mul_sub_left_distrib,sum_sub_distrib] at hsign hh
  linarith

/-- An eventual upper bound C X for the prime logarithmic sum gives an upper
bound C for its normalized Dirichlet mass as s approaches one from above. -/
theorem eventually_mass_lt_of_sum_le (A : Set ℕ) {C c : ℝ} (hC : 0≤C) (hc : C<c)
    (h : ∀ᶠ X : ℕ in atTop, ∑ n ∈ range X, weight A n ≤ C*X) :
    ∀ᶠ s : ℝ in 𝓝[>] 1, (s-1)*mass A s < c := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let B := ∑ n ∈ range N, weight A n
  have hB : 0≤B := sum_nonneg fun _ _ => weight_nonneg ..
  have comp (n : ℕ) : (∑ i ∈ range n,weight A i) ≤ C*n+B := by
    by_cases hn : N≤n
    · linarith only [hN n hn,hB]
    · have hh := sum_le_sum_of_subset_of_nonneg (range_mono (show n≤N by omega))
        (f:=weight A) (fun j _ _ => weight_nonneg A j)
      change _ ≤ B at hh
      linarith only [hh,mul_nonneg hC (Nat.cast_nonneg (α:=ℝ) n)]
  have upper {s : ℝ} (hs : 1<s) : mass A s ≤ C*(∑' n : ℕ, 1/(n:ℝ)^s)+(C+B) := by
    let w (n : ℕ) : ℝ := 1 / (max 1 (n:ℝ))^s
    let g (i : ℕ) := C+(if i=0 then B else 0)
    have hw : Antitone w := by
      intro i j hij
      have hbase : max 1 (i:ℝ) ≤ max 1 (j:ℝ) := max_le_max_left _ (by exact_mod_cast hij)
      exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow (by positivity) hbase (by linarith))
    have sums (n : ℕ) : ∑ i ∈ range n,weight A i ≤ ∑ i ∈ range n,g i := by
      cases n with
      | zero => simp
      | succ n =>
        simpa [g,sum_add_distrib,mul_comm] using comp (n+1)
    apply (summable_weight A hs).tsum_le_of_sum_range_le
    intro n
    have hf (i : ℕ) : weight A i/(i:ℝ)^s = w i * weight A i := by
      rcases i with _|i
      · simp [weight]
      · dsimp only [w]
        rw [max_eq_right (by exact_mod_cast Nat.succ_pos i : 1≤((i+1:ℕ):ℝ))]
        ring
    have hh := weighted_sum_le hw (fun i => by dsimp [w]; positivity) sums n
    simp_rw [hf]
    refine hh.trans ?_
    have hg (i : ℕ) : w i*g i = C*(1/(i:ℝ)^s)+(if i=0 then C+B else 0) := by
      rcases i with _|i
      · simp [w,g,Real.zero_rpow (by linarith : s≠0)]
      · simp [w,g,mul_comm]
    simp_rw [hg]
    rw [sum_add_distrib,←mul_sum]
    have part := (Real.summable_one_div_nat_rpow.mpr hs).sum_le_tsum (range n)
      (fun _ _ => by positivity)
    have hb : (∑ i ∈ range n, if i=0 then C+B else 0) ≤ C+B := by
      cases n <;> simp [add_nonneg hC hB]
    exact add_le_add (mul_le_mul_of_nonneg_left part hC) hb
  have h₀ : Tendsto (fun s : ℝ => s-1) (𝓝[>] 1) (𝓝 0) := by
    have hId : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) := continuousWithinAt_id
    simpa using hId.sub_const 1
  have lim : Tendsto (fun s : ℝ => C*((s-1)*∑' n : ℕ,1/(n:ℝ)^s)+(s-1)*(C+B))
      (𝓝[>] 1) (𝓝 C) := by simpa using (tendsto_sub_mul_tsum_nat_rpow.const_mul C).add (h₀.mul_const (C+B))
  filter_upwards [self_mem_nhdsWithin,lim.eventually_lt_const hc] with s hs hlt
  have hle := mul_le_mul_of_nonneg_left (upper hs) (sub_nonneg.mpr (le_of_lt hs))
  linarith only [hlt,hle]

#print axioms eventually_mass_lt_of_sum_le
/-- Reduced residue classes have their expected logarithmic Dirichlet mass at one. -/
theorem mass_progression {m : ℕ} [NeZero m] (a : ZMod m) (ha : IsUnit a) :
    Tendsto (fun s : ℝ => (s-1)*mass {n | (n:ZMod m)=a} s) (𝓝[>] 1)
      (𝓝 ((m.totient:ℝ)⁻¹)) := by
  classical
  let A := {n : ℕ | (n:ZMod m)=a}
  let F (s : ℝ) := ∑' n, residueClass a n/(n:ℝ)^s
  let E (s : ℝ) := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n)/(n:ℝ)^s
  have hId : Tendsto (fun x : ℝ => x) (𝓝[>] 1) (𝓝 1) := continuousWithinAt_id
  have hzero : Tendsto (fun x : ℝ => x-1) (𝓝[>] 1) (𝓝 0) := by simpa using hId.sub_const 1
  have hn (n : ℕ) : 0≤(if n.Prime then 0 else residueClass a n) := by
    split_ifs <;> first | rfl | exact residueClass_nonneg ..
  have small {s : ℝ} (hs : 1<s) (n : ℕ) :
      (if n.Prime then 0 else residueClass a n)/(n:ℝ)^s ≤ (if n.Prime then 0 else residueClass a n)/n := by
    rcases n.eq_zero_or_pos with rfl|hp
    · simp
    · apply div_le_div_of_nonneg_left (hn n) (by exact_mod_cast hp)
      conv_lhs => rw [←Real.rpow_one (n:ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) hs.le
  have esum {s : ℝ} (hs : 1<s) := Summable.of_nonneg_of_le
    (fun n => div_nonneg (hn n) (show 0 ≤ (n:ℝ)^s by positivity)) (small hs)
    (summable_residueClass_non_primes_div a)
  have decomp {s : ℝ} (hs : 1<s) : F s = mass A s+E s := by
    dsimp only [mass,E,F]
    rw [←(summable_weight A hs).tsum_add (esum hs)]
    apply tsum_congr
    intro n
    by_cases hp : n.Prime
    · simp [weight,A,hp,residueClass,Set.indicator_apply,vonMangoldt_apply_prime hp]
    · simp [weight,hp]
  have elimE : Tendsto (fun s : ℝ => (s-1)*E s) (𝓝[>] 1) (𝓝 0) := by
    let C := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n)/n
    have hi : Tendsto (fun s : ℝ => (s-1)*C) (𝓝[>] 1) (𝓝 0) := by simpa using hzero.mul_const C
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hi
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_nonneg (sub_nonneg.mpr (le_of_lt hs)) (tsum_nonneg fun n => div_nonneg (hn n) (by positivity))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_le_mul_of_nonneg_left ((esum hs).tsum_le_tsum (small hs) (summable_residueClass_non_primes_div a))
        (sub_nonneg.mpr (le_of_lt hs))
  let aux (x : ℝ) := (LFunctionResidueClassAux a x).re
  have hid {s : ℝ} (hs : 1<s) : F s=aux s+(m.totient:ℝ)⁻¹/(s-1) := by
    unfold F aux
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_tsum,Complex.ofReal_div,Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_inv,Complex.ofReal_sub,Complex.ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hs,
      eqOn_LFunctionResidueClassAux ha (Set.mem_ofPred.mpr (Complex.ofReal_re s ▸ hs)),sub_add_cancel,LSeries,LSeries.term]
    refine tsum_congr fun n => ?_
    split_ifs with h
    · simp [h]
    · rfl
  have haux : ContinuousOn aux (Set.Ici 1) :=
    Complex.continuous_re.continuousOn.comp (t:=Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun _ _ => trivial) |>.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        simpa only [Set.mem_ofPred_eq,Complex.ofReal_re,Set.mem_Ici] using hx
  have hcont : Tendsto aux (𝓝[>] 1) (𝓝 (aux 1)) :=
    (haux 1 (show (1:ℝ)∈Set.Ici 1 from Set.mem_Ici.mpr le_rfl)).mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hfull : Tendsto (fun s : ℝ => (s-1)*F s) (𝓝[>] 1) (𝓝 ((m.totient:ℝ)⁻¹)) := by
    have lim := (hzero.mul hcont).add_const ((m.totient:ℝ)⁻¹)
    simp only [zero_mul,zero_add] at lim
    apply lim.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hid hs,mul_add]
    have he : s-1≠0 := sub_ne_zero.mpr (ne_of_gt (show 1<s from hs))
    field_simp [he]
  have hx := hfull.sub elimE
  rw [sub_zero] at hx
  apply hx.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [decomp hs]
  ring

#print axioms mass_progression

/-- Compare the prime mass of a set with a finite cover and two exceptional sets. -/
theorem mass_le_cover {ι : Type*} (J : Finset ι) (S : ι → Set ℕ) (A B G : Set ℕ)
    (h : ∀ p ∈ A, p.Prime → (∃ i ∈ J, p∈S i) ∨ p∈B ∨ p∈G) {s : ℝ} (hs : 1<s) :
    mass A s ≤ (∑ i ∈ J,mass (S i) s)+mass B s+mass G s := by
  classical
  have comp (n : ℕ) : weight A n ≤ (∑ i ∈ J,weight (S i) n)+weight B n+weight G n := by
    have hsum := sum_nonneg (s:=J) (f:=fun i => weight (S i) n) (fun _ _ => weight_nonneg ..)
    by_cases ha : n.Prime ∧ n∈A
    · rw [weight,if_pos ha]
      rcases h n ha.2 ha.1 with ⟨i,hi,hh⟩|hb|hg
      · have hl := single_le_sum (f:=fun j => weight (S j) n) (fun _ _ => weight_nonneg ..) hi
        rw [weight,if_pos ⟨ha.1,hh⟩] at hl
        linarith only [hl,weight_nonneg B n,weight_nonneg G n]
      · have hB : weight B n=Real.log n := if_pos ⟨ha.1,hb⟩
        linarith only [hB,hsum,weight_nonneg G n]
      · have hG : weight G n=Real.log n := if_pos ⟨ha.1,hg⟩
        linarith only [hG,hsum,weight_nonneg B n]
    · rw [weight,if_neg ha]
      linarith only [hsum, weight_nonneg B n,weight_nonneg G n]
  have hj := summable_sum (s:=J) (f:=fun i n => weight (S i) n/(n:ℝ)^s) (fun i _ => summable_weight (S i) hs)
  unfold mass
  rw [←Summable.tsum_finsetSum (fun i (_ : i∈J) => summable_weight (S i) hs),
    ←hj.tsum_add (summable_weight B hs),←(hj.add (summable_weight B hs)).tsum_add (summable_weight G hs)]
  apply (summable_weight A hs).tsum_le_tsum _ ((hj.add (summable_weight B hs)).add (summable_weight G hs))
  intro n
  simpa [add_div,sum_div] using div_le_div_of_nonneg_right (comp n) (show 0 ≤ (n:ℝ)^s by positivity)

theorem finite_mass_tendsto {G : Set ℕ} (hG : G.Finite) :
    Tendsto (fun s : ℝ => (s-1)*mass G s) (𝓝[>] 1) (𝓝 0) := by
  classical
  let C := ∑ n ∈ hG.toFinset, weight G n
  have lim : Tendsto (fun s : ℝ => (s-1)*C) (𝓝[>] 1) (𝓝 0) := by
    have id' : Tendsto (fun s : ℝ => s) (𝓝[>] 1) (𝓝 1) := continuousWithinAt_id
    simpa using (id'.sub_const 1).mul_const C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds lim
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact mul_nonneg (sub_nonneg.mpr (le_of_lt hs)) (tsum_nonneg fun n => div_nonneg (weight_nonneg G n) (by positivity))
  · filter_upwards [self_mem_nhdsWithin] with s hs
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (le_of_lt hs))
    unfold mass
    rw [tsum_eq_sum (s:=hG.toFinset) (fun n hn => by
      have hn' : n∉G := fun hh => hn (hG.mem_toFinset.mpr hh)
      simp [weight,hn'])]
    apply sum_le_sum
    intro n _
    by_cases hp : n.Prime
    · exact div_le_self (weight_nonneg G n) (Real.one_le_rpow (by exact_mod_cast hp.one_le) (by linarith [show (1:ℝ)<s from hs]))
    · simp [weight,hp]

#print axioms mass_le_cover
#print axioms finite_mass_tendsto

end PrimeMass
end CunninghamChain
