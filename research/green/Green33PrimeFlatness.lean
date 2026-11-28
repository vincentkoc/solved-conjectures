import Green33WeightedStability
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic

/-! Support bounds for exact constant convolutions on a cyclic group of prime order.
The characteristic-prime moment argument gives the support inequality underlying
the prime uncertainty principle of Biró and Tao. -/

open Finset
open scoped Classical

namespace Green33PrimeFlatness

private def momentOn {ι K : Type*} [Field K] (S : Finset ι) (x w : ι → K) (j : ℕ) : K :=
  ∑ i ∈ S, w i * x i ^ j

private theorem sparse_moment {ι K : Type*} [Field K] (x : ι → K) (hx : Function.Injective x)
    (S : Finset ι) (w : ι → K) (hne : S.Nonempty) (hw : ∀ i ∈ S, w i ≠ 0) :
    ∃ j < S.card, momentOn S x w j ≠ 0 := by
  classical
  induction S using Finset.induction_on generalizing w with
  | empty => simp at hne
  | @insert a S ha ih =>
    by_cases hs : S = ∅
    · subst S
      exact ⟨0, by simp, by simpa [momentOn] using hw a (by simp)⟩
    let v (i : ι) := (x i - x a) * w i
    have hv (i : ι) (hi : i ∈ S) : v i ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr (fun e => ha (hx e ▸ hi))) (hw i (mem_insert_of_mem hi))
    obtain ⟨j, hj, hm⟩ := ih v (nonempty_iff_ne_empty.mpr hs) hv
    have step : momentOn (insert a S) x w (j+1) - x a * momentOn (insert a S) x w j =
        momentOn S x v j := by
      simp only [momentOn, sum_insert ha, mul_add, mul_sum]
      rw [add_sub_add_comm, ← sum_sub_distrib]
      simp only [pow_succ]
      have e : w a * (x a ^ j * x a) - x a * (w a * x a ^ j) = 0 := by ring
      rw [e, zero_add]
      exact sum_congr rfl fun i _ => by dsimp [v]; ring
    by_cases h : momentOn (insert a S) x w j = 0
    · refine ⟨j+1, by rw [card_insert_of_notMem ha]; omega, ?_⟩
      rw [h, mul_zero, sub_zero] at step
      exact step ▸ hm
    · exact ⟨j, by rw [card_insert_of_notMem ha]; omega, h⟩

/-- The sites carrying a nonzero coefficient. -/
noncomputable def sites {ι K : Type*} [Fintype ι] [Zero K] (f : ι → K) : Finset ι :=
  letI := Classical.decEq K
  univ.filter fun i => f i ≠ 0

private lemma mem_sites {ι K : Type*} [Fintype ι] [Zero K] (f : ι → K) (i : ι) :
    i ∈ sites f ↔ f i ≠ 0 := by classical simp [sites]

private def moment {ι K : Type*} [Fintype ι] [Field K] (x f : ι → K) (j : ℕ) : K :=
  ∑ i, f i * x i ^ j

private theorem first_moment {ι K : Type*} [Fintype ι] [Field K] (x : ι → K)
    (hx : Function.Injective x) (f : ι → K) (hf : ∃ i, f i ≠ 0) :
    ∃ j < (sites f).card, moment x f j ≠ 0 ∧ ∀ k < j, moment x f k = 0 := by
  classical
  obtain ⟨a, ha⟩ := hf
  obtain ⟨j, hj, hm⟩ := sparse_moment x hx (sites f) f ⟨a, (mem_sites ..).mpr ha⟩
    (fun i hi => (mem_sites ..).mp hi)
  have eq : momentOn (sites f) x f j = moment x f j := by
    simp only [momentOn, moment, sites, sum_filter]
    exact sum_congr rfl fun i _ => by by_cases h : f i = 0 <;> simp [h]
  have ex : ∃ t, moment x f t ≠ 0 := ⟨j, eq ▸ hm⟩
  exact ⟨Nat.find ex, (Nat.find_min' ex (eq ▸ hm)).trans_lt hj, Nat.find_spec ex,
    fun k hk => not_ne_iff.mp (Nat.find_min ex hk)⟩

/-- Cyclic convolution with one coefficient per site. -/
def conv {p : ℕ} [NeZero p] {K : Type*} [Field K] (f g : ZMod p → K) (z : ZMod p) : K :=
  ∑ i, f i * g (z - i)

private theorem moment_conv {p : ℕ} [NeZero p] {K : Type*} [Field K] (x : ZMod p →+* K)
    (f g : ZMod p → K) (t : ℕ) :
    moment x (conv f g) t = ∑ j ∈ range (t+1),
      moment x f j * moment x g (t-j) * (t.choose j : K) := by
  classical
  unfold moment conv
  simp only [sum_mul]
  rw [sum_comm]
  have shift (i : ZMod p) : ∑ z, f i * g (z-i) * x z ^ t =
      ∑ b, f i * g b * (x i + x b) ^ t := by
    exact Fintype.sum_equiv (Equiv.subRight i) _ _ (fun z => by simp)
  simp_rw [shift, add_pow, mul_sum]
  calc
    _ = ∑ i, ∑ j ∈ range (t+1), ∑ b, f i * g b *
        (x i ^ j * x b ^ (t-j) * (t.choose j : K)) := sum_congr rfl fun _ _ => sum_comm
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [sum_mul]
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl fun b _ => by ring

private lemma choose_ne_zero {p t j : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K]
    [CharP K p] (ht : t < p) (hj : j ≤ t) : (t.choose j : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K p]
  intro hd
  have hfac : p ∣ t.factorial := Nat.choose_mul_factorial_mul_factorial hj ▸
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
  exact ht.not_ge ((Nat.Prime.dvd_factorial hp.out).mp hfac)

private theorem vanishing_support {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (x : ZMod p →+* K) (f g : ZMod p → K) (hf : ∃ i, f i ≠ 0) (hg : ∃ i, g i ≠ 0)
    (d : ℕ) (hd : d ≤ p) (hv : ∀ t < d, moment x (conv f g) t = 0) :
    d+2 ≤ (sites f).card + (sites g).card := by
  classical
  obtain ⟨a, ha, ha0, hamin⟩ := first_moment x x.injective f hf
  obtain ⟨b, hb, hb0, hbmin⟩ := first_moment x x.injective g hg
  by_contra! small
  have hab : a+b < d := by omega
  have h := hv (a+b) hab
  rw [moment_conv, sum_eq_single a] at h
  · rw [Nat.add_sub_cancel_left] at h
    exact (mul_ne_zero (mul_ne_zero ha0 hb0) (choose_ne_zero (hab.trans_le hd) (by omega))) h
  · intro j hj hja
    by_cases hlt : j < a
    · simp [hamin _ hlt]
    · have hle := mem_range.mp hj
      simp [hbmin (a+b-j) (by omega)]
  · simp

private theorem residue_support {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [CharP K p]
    (f g : ZMod p → K) (hf : ∃ i, f i ≠ 0) (hg : ∃ i, g i ≠ 0)
    (c : K) (hu : ∀ z, conv f g z = c) :
    p + (if c = 0 then 2 else 1) ≤ (sites f).card + (sites g).card := by
  classical
  let x := ZMod.castHom (dvd_refl p) K
  by_cases hc : c = 0
  · simpa [hc] using vanishing_support x f g hf hg p (le_refl p)
      (fun t _ => by simp [moment, hu, hc])
  · have h := vanishing_support x f g hf hg (p-1) (by omega) (fun t ht => by
      have hz := FiniteField.sum_pow_lt_card_sub_one (ZMod p) t (by simpa using ht)
      have hm := congrArg x hz
      simp only [map_sum, map_pow, map_zero] at hm
      simp only [moment, hu, ← mul_sum, hm, mul_zero])
    simp only [if_neg hc]
    have := hp.out.two_le
    omega

private theorem exists_residue_char (K : Type*) [Field K] [CharZero K] (p : ℕ) [hp : Fact p.Prime] :
    ∃ V : ValuationSubring K, CharP (IsLocalRing.ResidueField V) p := by
  classical
  let h : ℤ →+* K := Int.castRingHom K
  let e : ℤ ≃+* h.range := RingEquiv.ofBijective h.rangeRestrict
    ⟨fun _ _ eq => (Int.cast_injective (α := K)) (congrArg Subtype.val eq), h.rangeRestrict_surjective⟩
  let r : h.range →+* ZMod p := (Int.castRingHom _).comp e.symm.toRingHom
  obtain ⟨V, _, hV⟩ := (RingHom.ker r).image_subset_nonunits_valuationSubring (RingHom.ker_ne_top r)
  refine ⟨V, (CharP.charP_iff_prime_eq_zero hp.out).mpr ?_⟩
  have hm : (p : h.range) ∈ RingHom.ker r := by rw [RingHom.mem_ker]; simp
  have hn : (p : K) ∈ V.nonunits := hV ⟨(p : h.range), hm, by simp⟩
  have hpV : (p : V) ∈ IsLocalRing.maximalIdeal V :=
    V.coe_mem_nonunits_iff.mp (by simpa using hn)
  simpa using (IsLocalRing.residue_eq_zero_iff (p : V)).mpr hpV

private theorem integral_scale {K ι : Type*} [Field K] [Fintype ι] (V : ValuationSubring K)
    (f : ι → K) (hf : ∃ i, f i ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ ∃ F : ι → V, (∀ i, (F i : K) = f i / a) ∧ ∃ i, F i = 1 := by
  classical
  obtain ⟨i, hi⟩ := hf
  obtain ⟨j, hj, hmax⟩ := (sites f).exists_max_image (fun i => V.valuation (f i))
    ⟨i, (mem_sites ..).mpr hi⟩
  have hj' := (mem_sites ..).mp hj
  have hm (i : ι) : f i / f j ∈ V := by
    rw [← V.valuation_le_one_iff, map_div₀, div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero V.valuation).mpr hj'))]
    by_cases hi : f i = 0
    · simp [hi]
    · exact hmax i ((mem_sites ..).mpr hi)
  exact ⟨f j, hj', fun i => ⟨_, hm i⟩, fun _ => rfl, j, Subtype.ext (div_self hj')⟩

/-- An exact constant convolution on a prime cyclic group requires at least `p+1`
nonzero sites across the two nonzero inputs. A zero convolution requires `p+2`. -/
theorem constant_support {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharZero K]
    (f g : ZMod p → K) (hf : ∃ i, f i ≠ 0) (hg : ∃ i, g i ≠ 0)
    (c : K) (hu : ∀ z, conv f g z = c) :
    p + (if c = 0 then 2 else 1) ≤ (sites f).card + (sites g).card := by
  classical
  obtain ⟨V, hc⟩ := exists_residue_char K p
  obtain ⟨a, ha, F, hF, j, hj⟩ := integral_scale V f hf
  obtain ⟨b, hb, G, hG, k, hk⟩ := integral_scale V g hg
  let π := IsLocalRing.residue V
  let S (z : ZMod p) := ∑ i, F i * G (z-i)
  have hS (z : ZMod p) : (S z : K) = c / (a*b) := by
    change V.toSubring.subtype (∑ i, F i * G (z-i)) = _
    rw [map_sum]
    simp only [map_mul, Subring.subtype_apply, hF, hG, div_mul_div_comm, ← sum_div]
    exact congrArg (· / (a*b)) (hu z)
  have hπ (z : ZMod p) : conv (π ∘ F) (π ∘ G) z = π (S z) := by simp [conv, S]
  have hcard (u : ZMod p → V) (v : ZMod p → K) (d : K)
      (h : ∀ i, (u i : K) = v i / d) : (sites (π ∘ u)).card ≤ (sites v).card := by
    refine card_le_card (fun i hi => (mem_sites ..).mpr ?_)
    intro he
    have hzero : u i = 0 := Subtype.ext (by simp [h, he])
    exact (mem_sites ..).mp hi (by simp [hzero])
  have bound := residue_support (π ∘ F) (π ∘ G) ⟨j, by simp [hj]⟩ ⟨k, by simp [hk]⟩
    (π (S 0)) (fun z => (hπ z).trans (congrArg π (Subtype.ext ((hS z).trans (hS 0).symm))))
  have hfg := Nat.add_le_add (hcard F f a hF) (hcard G g b hG)
  by_cases hz : c = 0
  · have hs : S 0 = 0 := Subtype.ext (by simp [hS, hz])
    simpa [hz, hs] using bound.trans hfg
  · simp only [if_neg hz]
    split at bound <;> omega

open Green33WeightedStability

private theorem conv_pmf {p : ℕ} [Fact p.Prime] (u v : PMF (ZMod p)) (z : ZMod p) :
    conv (fun i => (u i).toReal) (fun i => (v i).toReal) z =
      ((law u v (· + ·)) z).toReal := by
  classical
  have translate (i : ZMod p) : (v.map (i + ·)) z = v (z-i) := by
    rw [PMF.map_apply, tsum_fintype, sum_eq_single (z-i)]
    · simp
    · intro j _ hj
      exact if_neg (fun e => hj (by rw [e]; abel))
    · simp
  simp only [conv, law, PMF.bind_apply, tsum_fintype, translate, ENNReal.toReal_sum
    (fun i _ => ENNReal.mul_ne_top (u.apply_ne_top _) (v.apply_ne_top _)), ENNReal.toReal_mul]

private lemma real_atom_ne {α : Type*} (u : PMF α) (i : α) : (u i).toReal ≠ 0 ↔ i ∈ u.support := by
  simp only [ne_eq, ENNReal.toReal_eq_zero_iff, u.apply_ne_top, or_false, PMF.mem_support_iff]

private lemma image_sites {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (u : PMF ι) (l : ι → β) : sites (fun z => ((u.map l) z).toReal) =
      (sites (fun i => (u i).toReal)).image l := by
  classical
  ext z
  simp only [mem_sites, real_atom_ne, PMF.mem_support_map_iff, mem_image]

private theorem project_flat {G : Type*} [AddCommGroup G] [Fintype G] {p : ℕ} [Fact p.Prime]
    (π : G →+ ZMod p) (onto : Function.Surjective π) (r : PMF G)
    (flat : ∀ i, (r i).toReal = (r 0).toReal) (z : ZMod p) :
    (r.map π) z = (r.map π) 0 := by
  classical
  obtain ⟨a, ha⟩ := onto z
  have hr (i : G) : r i = r 0 := (ENNReal.toReal_eq_toReal_iff' (r.apply_ne_top _) (r.apply_ne_top _)).mp (flat i)
  simp only [PMF.map_apply, tsum_fintype]
  apply Fintype.sum_equiv (Equiv.subRight a)
  intro i
  simp only [Equiv.subRight_apply, map_sub, ha, hr]
  by_cases h : z = π i
  · simp [h]
  · simp [h, Ne.symm h, eq_comm (a := (0 : ZMod p)), sub_eq_zero]

/-- In any finite abelian group with a prime cyclic quotient, an exactly uniform
independent sum needs at least `p+1` occupied sites across the projected marginals. -/
theorem quotient_support {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G] {p : ℕ}
    [Fact p.Prime] (π : G →+ ZMod p) (onto : Function.Surjective π) (u v : PMF ι)
    (l : ι → G) (flat : ∀ z, ((law u v (fun i j => l i + l j)) z).toReal = (Fintype.card G:ℝ)⁻¹) :
    p+1 ≤ ((sites (fun i => (u i).toReal)).image (π ∘ l)).card +
      ((sites (fun i => (v i).toReal)).image (π ∘ l)).card := by
  classical
  let U := u.map (π ∘ l)
  let V := v.map (π ∘ l)
  let R := law u v (fun i j => l i + l j)
  have hmap : law U V (·+·) = R.map π := by
    simp [U, V, R, law, PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have nonzero (w : PMF (ZMod p)) : ∃ i, (w i).toReal ≠ 0 := by
    obtain ⟨i, hi⟩ := w.support_nonempty
    exact ⟨i, (real_atom_ne ..).mpr hi⟩
  have h := constant_support (fun i => (U i).toReal) (fun i => (V i).toReal)
    (nonzero U) (nonzero V) (((R.map π) 0).toReal) (fun z => by
      rw [conv_pmf, hmap, project_flat π onto R (fun i => (flat i).trans (flat 0).symm)])
  dsimp only [U, V] at h
  rw [image_sites, image_sites] at h
  split at h <;> omega

/-- For a cyclic modulus and any prime divisor, the common seed must have at
least `(p+1)/2` labels to support an exactly uniform sum. -/
theorem prime_divisor_budget {M : ℕ+} {p : ℕ} [Fact p.Prime] (h : p ∣ M.val)
    (A : Finset (ZMod M)) (u v : PMF A)
    (flat : ∀ z, ((law u v (cyclicSum A)) z).toReal = (M.val:ℝ)⁻¹) :
    p+1 ≤ 2*A.card := by
  classical
  let π := ZMod.castHom h (ZMod p)
  have hf (z : ZMod M) : ((law u v (fun i j => (i : ZMod M) + j)) z).toReal =
      (Fintype.card (ZMod M):ℝ)⁻¹ := by
    have e : cyclicSum A = (fun i j : A => (i : ZMod M) + j) := by rfl
    rw [← e, ZMod.card]
    exact flat z
  have bound := quotient_support π.toAddMonoidHom (ZMod.castHom_surjective h) u v
    (fun i => (i : ZMod M)) hf
  have hs (w : PMF A) :
      ((sites (fun i => (w i).toReal)).image (π.toAddMonoidHom ∘ fun i : A => (i : ZMod M))).card ≤ A.card :=
    card_image_le.trans ((card_le_univ _).trans_eq (Fintype.card_coe A))
  exact bound.trans (by simpa [two_mul] using Nat.add_le_add (hs u) (hs v))

#print axioms constant_support
#print axioms quotient_support
#print axioms prime_divisor_budget
end Green33PrimeFlatness
