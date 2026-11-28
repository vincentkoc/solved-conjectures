import Green33MaximalOrders

/-! Rectangular lifts of finite strict sum covers to cyclic orders with a prescribed divisor. -/

open Finset Filter Green33StrictReduction
open scoped Pointwise Topology

namespace Green33DivisibleOrder

private lemma digit (d l q x : ℤ) (hq : 0 < q) (hd : d * l = q + 1) :
    ∃ v e : ℤ, 0 ≤ v ∧ v < q ∧ x = d * v + q * e := by
  let y := l * x
  refine ⟨y % q, d * (y / q) - x, Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq, ?_⟩
  calc
    x = d * y - q * x := by dsimp [y]; linear_combination -x * hd
    _ = d * (y % q + q * (y / q)) - q * x := by rw [Int.emod_add_mul_ediv]
    _ = _ := by ring

/-- Two short progressions cover a rectangular modulus p(p−1). The common
first digit is one, so p is free to carry prescribed small prime factors. -/
theorem rectangular_pair (i d h l q x : ℤ) (hq : 0 < q) (hh : 0 < h)
    (h1 : d * h = i + 1) (h2 : d * l = q + 1) :
    let p := q + 1
    ∃ t u : ℤ, 0 ≤ t ∧ t < p + h ∧ 0 ≤ u ∧ u < p + h ∧
      ∃ e : ℤ, x = (1 + i * p) * t + (1 + (i + d) * p) * u + p * q * e := by
  intro p
  have hp : 0 < p := by dsimp only [p]; omega
  let a := x % p
  let b := x / p
  have ha : 0 ≤ a := Int.emod_nonneg _ hp.ne'
  have hap : a < p := Int.emod_lt_of_pos _ hp
  have hx : x = a + p * b := (Int.emod_add_mul_ediv x p).symm
  obtain ⟨v, e, hv, hvq, hb⟩ := digit d l q (b - i * a - (i + 1)) hq h2
  by_cases H : v + h ≤ a
  · refine ⟨a - v - h, v + h, by omega, by omega, by omega, by omega, e, ?_⟩
    linear_combination hx + p * hb - p * h1
  · refine ⟨a + p - v, v, by dsimp only [p] at *; omega, by omega, hv, by dsimp only [p]; omega, e - i, ?_⟩
    dsimp only [p] at *
    linear_combination hx + (q + 1) * hb

/-- Positive heights with every pairwise gap dividing its lower endpoint. -/
theorem height_family (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ (∀ a ∈ S, 0 < a) ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → b - a ∣ a := by
  induction k with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨S, hk, hpos, hgap⟩ := ih
    let L := (S.sup id).factorial
    have hL : 0 < L := Nat.factorial_pos _
    have hall (a : ℕ) (ha : a ∈ S) : a ∣ L :=
      Nat.dvd_factorial (hpos a ha) (le_sup (f := id) ha)
    let f : ℕ ↪ ℕ := ⟨(L+·), fun _ _ h => Nat.add_left_cancel h⟩
    have hnot : L ∉ S.map f := by
      intro h
      obtain ⟨a, ha, he⟩ := mem_map.mp h
      change L + a = L at he
      have := hpos a ha; omega
    refine ⟨insert L (S.map f), by simp [hnot, hk], ?_, ?_⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · exact hL
      obtain ⟨a, _, rfl⟩ := mem_map.mp hx
      change 0 < L + a; omega
    · intro x hx y hy hxy
      rcases mem_insert.mp hy with rfl | hy
      · rcases mem_insert.mp hx with rfl | hx
        · omega
        obtain ⟨a, _, rfl⟩ := mem_map.mp hx
        change L + a < L at hxy; omega
      obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
      rcases mem_insert.mp hx with rfl | hx
      · change L + b - L ∣ L
        simpa using hall b hb
      obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
      change L + a < L + b at hxy
      have hab : a < b := by omega
      have hda := hgap a ha b hb hab
      change (L + b) - (L + a) ∣ L + a
      rw [show (L + b) - (L + a) = b - a by omega]
      exact dvd_add (hda.trans (hall a ha)) hda

/-- Each residue is a label plus M times an integer. The carry in the labels
can be absorbed by the two progressions, including when M and P share factors. -/
private lemma assemble {M P : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A)
    {L : ℕ} (T : A → Fin L → ℤ)
    (hT : ∀ a b : A, a ≠ b → ∀ v : ℤ, ∃ t u, ∃ e : ℤ, v = T a t + T b u + P.val * e) :
    ∃ B : Finset (ZMod (M * P)), StrictCover B ∧ B.card ≤ A.card * L := by
  classical
  let rep (a : A) (t : Fin L) : ℤ := a.val.val + M.val * T a t
  let arm (p : A × Fin L) : ZMod (M * P) := (rep p.1 p.2 : ℤ)
  let B := univ.image arm
  have memB (a : A) (t : Fin L) : arm (a, t) ∈ B := mem_image_of_mem _ (mem_univ _)
  let π : ZMod (M * P) →+* ZMod M := ZMod.castHom (show M.val ∣ (M * P).val from dvd_mul_right _ _) _
  have red (a : A) (t : Fin L) : π (arm (a, t)) = a.val := by
    change π ((rep a t : ℤ) : ZMod (M * P)) = _
    rw [map_intCast]
    simp [rep]
  refine ⟨B, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha, b, hb, hab, hs⟩ := hA (x.val : ZMod M)
    let i : A := ⟨a, ha⟩
    let j : A := ⟨b, hb⟩
    have hy : (M.val : ℤ) ∣ (x.val : ℤ) - (a.val + b.val : ℤ) := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
      simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] using hs
    obtain ⟨v, hv⟩ := hy
    obtain ⟨t, u, e, he⟩ := hT i j (fun h => hab (congrArg Subtype.val h)) v
    refine ⟨_, memB i t, _, memB j u, ?_, ?_⟩
    · intro h
      have h' := congrArg π h
      rw [red, red] at h'
      exact hab h'
    · have hx : (x.val : ℤ) = rep i t + rep j u + ((M * P).val : ℤ) * e := by
        change (x.val : ℤ) = ((a.val : ℤ) + M.val * T i t) + ((b.val : ℤ) + M.val * T j u) +
          ((M.val * P.val : ℕ) : ℤ) * e
        push_cast
        linear_combination hv + (M.val : ℤ) * he
      have h := congrArg (fun z : ℤ => (z : ZMod (M * P))) hx
      have hzero : ((M * P).val : ZMod (M * P)) = 0 := ZMod.natCast_self _
      simpa only [arm, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_add, Int.cast_mul,
        hzero, zero_mul, add_zero] using h.symm
  · simpa [B, Fintype.card_prod] using (card_image_le (s := univ) (f := arm))

/-- Every finite strict cyclic seed has an arithmetic progression of lift widths
p, all divisible by D, with order M p(p−1) and size at most |A|(p+C). -/
theorem divisible_seed_lifts {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A)
    (D : ℕ+) : ∃ s C : ℕ, 0 < s ∧ D.val ∣ s ∧ ∀ l : ℕ, 2 ≤ s * l →
      ∃ N : ℕ+, N.val = M.val * (s * l) * (s * l - 1) ∧ D.val ∣ N.val ∧
        ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ A.card * (s * l + C) := by
  classical
  obtain ⟨S, hcard, hpos, hgap⟩ := height_family A.card
  let height : A ≃ S := A.equivFin.trans ((finCongr hcard.symm).trans S.equivFin.symm)
  let H (a : A) := (height a).val
  let C := S.sup id
  have hH (a : A) : 0 < H a := hpos _ (height a).property
  have hC (a : A) : H a ≤ C := le_sup (f := id) (height a).property
  let s := D.val * C.factorial
  have hs : 0 < s := Nat.mul_pos D.pos C.factorial_pos
  refine ⟨s, C, hs, dvd_mul_right _ _, ?_⟩
  intro l hp
  let p := s * l
  let q := p - 1
  have hq : 0 < q := by dsimp [q, p]; omega
  have hpq : (q:ℤ) + 1 = p := by exact_mod_cast (show q + 1 = p by dsimp [q, p]; omega)
  let P : ℕ+ := ⟨p * q, Nat.mul_pos (by dsimp [p]; omega) hq⟩
  let T (a : A) (t : Fin (p + C)) : ℤ := (1 + ((H a : ℤ) - 1) * p) * t.val
  have hit {a b : A} (hab : H a < H b) (v : ℤ) :
      ∃ t u, ∃ e : ℤ, v = T a t + T b u + P.val * e := by
    let d := H b - H a
    have hd : 0 < d := Nat.sub_pos_of_lt hab
    obtain ⟨h, hh⟩ := hgap _ (height a).property _ (height b).property hab
    change H a = d * h at hh
    have hpos' : 0 < h := by by_contra! he; have := hH a; simp [Nat.eq_zero_of_le_zero he] at hh; omega
    have hhC : h ≤ C := (Nat.le_mul_of_pos_left h hd).trans (hh ▸ hC a)
    have hdp : d ∣ p := dvd_trans (Nat.dvd_factorial hd ((Nat.sub_le _ _).trans (hC b)))
      (dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _))
    obtain ⟨m, hm⟩ := hdp
    have h1 : (d:ℤ) * h = ((H a:ℤ) - 1) + 1 := by rw [sub_add_cancel]; exact_mod_cast hh.symm
    have h2 : (d:ℤ) * m = (q:ℤ) + 1 := by rw [hpq]; exact_mod_cast hm.symm
    obtain ⟨t, u, ht, ht', hu, hu', e, he⟩ := rectangular_pair ((H a:ℤ) - 1) d h m q v
      (by exact_mod_cast hq) (by exact_mod_cast hpos') h1 h2
    rw [hpq] at ht' hu' he
    have hdval : (H a : ℤ) - 1 + d = (H b : ℤ) - 1 := by
      dsimp [d]; rw [Nat.cast_sub hab.le]; ring
    rw [hdval] at he
    refine ⟨⟨t.toNat, by omega⟩, ⟨u.toNat, by omega⟩, e, ?_⟩
    change v = (1 + ((H a:ℤ) - 1) * p) * (t.toNat:ℤ) + (1 + ((H b:ℤ) - 1) * p) * (u.toNat:ℤ) +
      ((p * q:ℕ):ℤ) * e
    simpa only [Int.toNat_of_nonneg ht, Int.toNat_of_nonneg hu, Nat.cast_mul] using he
  obtain ⟨B, hB, hk⟩ := assemble (P := P) hA T (fun a b hab v => by
    have hh : H a ≠ H b := fun h => hab (height.injective (Subtype.ext h))
    rcases lt_or_gt_of_ne hh with H | H
    · exact hit H v
    · obtain ⟨t, u, e, he⟩ := hit H v
      exact ⟨u, t, e, by simpa only [add_comm (T b t) (T a u)] using he⟩)
  refine ⟨M * P, Nat.mul_assoc _ _ _ |>.symm, ?_, B, hB, hk⟩
  change D.val ∣ M.val * (p * q)
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _

/-- Interpolation costs only a fixed number of labels for a fixed seed and
divisor. Every sufficiently large budget admits the stated strict cover. -/
theorem divisible_all_budgets {M : ℕ+} {A : Finset (ZMod M)} (hA : StrictCover A) (D : ℕ+) :
    ∃ C : ℕ, ∀ K ≥ C, ∃ N : ℕ+, D.val ∣ N.val ∧ M.val * (K - C)^2 ≤ A.card^2 * N.val ∧
      ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ K := by
  obtain ⟨s, c, hs, _, H⟩ := divisible_seed_lifts hA D
  let k := A.card
  have hk : 0 < k := by
    obtain ⟨a, ha, _, _, _, _⟩ := hA 0
    exact card_pos.mpr ⟨_, ha⟩
  let d := k * s
  let b := k * c
  have hd : 0 < d := Nat.mul_pos hk hs
  let C := b + 3 * d + k
  refine ⟨C, ?_⟩
  intro K hK
  let n := (K - b) / d
  have hb : b ≤ K := by dsimp [C] at hK; omega
  have hn : 2 ≤ n := (Nat.le_div_iff_mul_le hd).mpr (by dsimp [C] at hK; omega)
  let p := s * n
  have hp : 2 ≤ p := hn.trans (Nat.le_mul_of_pos_left n hs)
  obtain ⟨N, hN, hD, B, hB, hsize⟩ := H n hp
  have hlo := Nat.div_mul_le_self (K - b) d
  change n * d ≤ K - b at hlo
  have hhi := Nat.lt_mul_div_succ (K - b) hd
  change K - b < d * (n + 1) at hhi
  have hK' := Nat.sub_add_cancel hb
  have hcap : k * (p + c) ≤ K := by
    change n * (k * s) ≤ K - k * c at hlo
    change K - k * c + k * c = K at hK'
    dsimp only [p]
    nlinarith only [hlo, hK']
  have hnear : K - C ≤ k * (p - 1) := by
    have he := Nat.sub_add_cancel hK
    have hpred : p - 1 + 1 = p := by omega
    have hv := congrArg (k*·) hpred
    change K - b < k * s * (n + 1) at hhi
    change K - C + (b + 3 * (k * s) + k) = K at he
    change k * (p - 1 + 1) = k * (s * n) at hv
    nlinarith only [hhi, hK', he, hv]
  refine ⟨N, hD, ?_, B, hB, hsize.trans hcap⟩
  calc
    M.val * (K - C)^2 ≤ M.val * (k * (p - 1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnear 2)
    _ = k^2 * (M.val * (p - 1) * (p - 1)) := by ring
    _ ≤ k^2 * (M.val * p * (p - 1)) := by gcongr; exact Nat.sub_le _ _
    _ = _ := by rw [hN]

/-- For any density below the Graham–Sloane limiting constant and any fixed
divisor, every sufficiently large budget realizes at least that density at a
multiple of the divisor, with distinct summands. -/
theorem densities_on_multiples (D : ℕ+) {a : ℝ} (ha : a < Green33MaximalOrders.orderConstant) :
    ∀ᶠ k : ℕ in atTop, ∃ N : ℕ+, D.val ∣ N.val ∧ a * (k:ℝ)^2 < (N:ℝ) ∧
      ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ k := by
  have hne : Green33MaximalOrders.strictDensities.Nonempty := by
    by_contra! h
    have hh := Green33MaximalOrders.orderConstant_bounds.1
    simp [Green33MaximalOrders.orderConstant, h] at hh
    norm_num at hh
  obtain ⟨v, ⟨M, A, hA, rfl⟩, hv⟩ : ∃ v ∈ Green33MaximalOrders.strictDensities, a < v := by
    by_contra! h
    exact ha.not_ge (csSup_le hne h)
  obtain ⟨C, H⟩ := divisible_all_budgets hA D
  let z := (M:ℝ) / (A.card:ℝ)^2
  have hlim : Tendsto (fun k : ℕ => z * (1 - (C:ℝ) / k)^2) atTop (𝓝 z) := by
    have h := ((tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (C:ℝ))).pow 2
    simpa using h.const_mul z
  filter_upwards [hlim.eventually_const_lt hv, eventually_ge_atTop C, eventually_ge_atTop 1]
    with k hlt hk hk'
  obtain ⟨N, hD, h, B, hB, hkB⟩ := H k hk
  refine ⟨N, hD, ?_, B, hB, hkB⟩
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hak : 0 < (A.card:ℝ) := by
    obtain ⟨c, hc, _, _, _, _⟩ := hA 0
    exact_mod_cast card_pos.mpr ⟨_, hc⟩
  have hr : (M:ℝ) * ((k:ℝ) - C)^2 ≤ (A.card:ℝ)^2 * (N:ℝ) := by exact_mod_cast h
  have hh : z * (1 - (C:ℝ) / k)^2 ≤ (N:ℝ) / (k:ℝ)^2 := by
    dsimp only [z]
    field_simp [hkp.ne', hak.ne']
    nlinarith only [hr]
  exact (lt_div_iff₀ (sq_pos_of_pos hkp)).mp (hlt.trans_le hh)

/-- Green's conjecture holds iff it admits strict witnesses at arbitrarily
large multiples of each prescribed positive divisor. -/
theorem green_iff_divisible_strict : OrdinaryLimit ↔
    ∀ D : ℕ+, ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ+ in atTop, D.val ∣ N.val ∧
      ∃ B : Finset (ZMod N), StrictCover B ∧
        |(B.card:ℝ) / Real.sqrt N - Real.sqrt 2| < ε := by
  constructor
  · intro h D ε hε
    have hS := Green33MaximalOrders.green_iff_orderConstant.mp h
    let t := Real.sqrt 2 + ε
    let a : ℝ := 1 / t^2
    have ht : 0 < t := by dsimp only [t]; positivity
    have ha : 0 < a := by dsimp only [a]; positivity
    have has : a < Green33MaximalOrders.orderConstant := by
      rw [hS]
      dsimp only [a]
      rw [div_lt_div_iff₀ (sq_pos_of_pos ht) (by norm_num : (0:ℝ) < 2)]
      have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg 2) ht.le).mpr
        (show Real.sqrt 2 < t by dsimp only [t]; linarith)
      linarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    apply frequently_atTop.mpr
    intro R
    obtain ⟨J, hJ⟩ := exists_nat_gt ((R:ℝ) / a)
    obtain ⟨k, hw, hkJ, hk1⟩ := ((densities_on_multiples D has).and
      ((eventually_ge_atTop J).and (eventually_ge_atTop 1))).exists
    obtain ⟨N, hD, hd, B, hB, hBk⟩ := hw
    have hkp : 1 ≤ (k:ℝ) := by exact_mod_cast hk1
    have hRk : (R:ℝ) < k * a := (div_lt_iff₀ ha).mp
      (hJ.trans_le (by exact_mod_cast hkJ))
    have hRN : (R:ℝ) ≤ (N:ℝ) := by nlinarith [mul_nonneg (sub_nonneg.mpr hkp) (mul_nonneg
        (by linarith : 0 ≤ (k:ℝ)) ha.le)]
    refine ⟨N, by exact_mod_cast hRN, hD, B, hB, abs_lt.mpr ⟨?_, ?_⟩⟩
    · have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast N.pos)
      have hl : Real.sqrt 2 ≤ (B.card:ℝ) / Real.sqrt N := (le_div_iff₀ hN).mpr (by
        linarith [strict_size_gap hB])
      linarith
    · have hN : 0 < (N:ℝ) := by exact_mod_cast N.pos
      have hb : (B.card:ℝ) ≤ k := by exact_mod_cast hBk
      have h' : (k:ℝ)^2 / t^2 < (N:ℝ) := by simpa [a, div_eq_mul_inv, mul_comm] using hd
      have hs : (k:ℝ)^2 < (t * Real.sqrt N)^2 := by
        rw [mul_pow, Real.sq_sqrt hN.le, mul_comm]
        exact (div_lt_iff₀ (sq_pos_of_pos ht)).mp h'
      have hh := (sq_lt_sq₀ (Nat.cast_nonneg k) (mul_nonneg ht.le (Real.sqrt_nonneg _))).mp hs
      have := (div_lt_iff₀ (Real.sqrt_pos.mpr hN)).mpr (hb.trans_lt hh)
      dsimp only [t] at this
      linarith
  · intro h
    apply ordinary_iff_strict.mpr
    intro ε hε
    exact (h 1 ε hε).mono fun _ h => h.2

#print axioms green_iff_divisible_strict

#print axioms divisible_all_budgets
#print axioms densities_on_multiples
#print axioms rectangular_pair
#print axioms height_family
#print axioms divisible_seed_lifts

end Green33DivisibleOrder
