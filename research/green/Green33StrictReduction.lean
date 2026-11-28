import Green33StrictCoverLift

/-! Green 33 is equivalent to the finite strict sum-cover ratio having infimum √2. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33StrictReduction

/-- Every group element has a representation as the sum of two distinct members. -/
def StrictCover {G : Type*} [Add G] (A : Finset G) : Prop :=
  ∀ x : G, ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b = x

section Patch

variable {H : Type*} [AddCommGroup H] [DecidableEq H]

private def low (m : ℕ) (r : ℕ) : ZMod m × H := (r, 0)

private def high (m L : ℕ) (v : ℕ × H) : ZMod m × H := (↑(L * v.1), v.2)

private def patch (m L C : ℕ) (E : Finset H) : Finset (ZMod m × H) :=
  insert (-1, 0) ((range L).image (low m) ∪ ((range C) ×ˢ E).image (high m L))

private lemma patch_card (m L C : ℕ) (E : Finset H) : (patch m L C E).card ≤ L + C * E.card + 1 := by
  unfold patch
  calc
    _ ≤ _ := card_insert_le _ _
    _ ≤ ((range L).image (low m (H := H))).card +
        (((range C) ×ˢ E).image (high m L)).card + 1 := by gcongr; exact card_union_le _ _
    _ ≤ _ := by
      have h₁ := card_image_le (f := low m (H := H)) (s := range L)
      have h₂ := card_image_le (f := high m L) (s := (range C) ×ˢ E)
      simp only [card_range, card_product] at h₁ h₂
      omega

private lemma patch_covers {m L C : ℕ} [NeZero m] (hm : 2 < m) (hL : 1 < L) (hcap : m ≤ L * C)
    (E : Finset H) (x : ZMod m) {z : H} (hz : z ∈ E) :
    ∃ a ∈ patch m L C E, ∃ b ∈ patch m L C E, a ≠ b ∧ a + b = (x, z) := by
  have hlo {r : ℕ} (hr : r < L) : low m r ∈ patch m L C E :=
    mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ (mem_range.mpr hr)))
  have hhi {j : ℕ} (hj : j < C) : high m L (j, z) ∈ patch m L C E :=
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨mem_range.mpr hj, hz⟩)))
  by_cases hzero : x = 0 ∧ z = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    refine ⟨low m 1, hlo hL, (-1, 0), mem_insert_self .., ?_, by simp [low]⟩
    intro he
    have he' : (1 : ZMod m) = -1 := by simpa only [low, Nat.cast_one] using congrArg Prod.fst he
    have h₂ : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination he'
    have hv := congrArg ZMod.val h₂
    rw [ZMod.val_natCast_of_lt hm, ZMod.val_zero] at hv
    contradiction
  let r := x.val % L
  let j := x.val / L
  have hr : r < L := Nat.mod_lt _ (by omega)
  have hj : j < C := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [mul_comm]; exact x.val_lt.trans_le hcap)
  have hx : r + L * j = x.val := Nat.mod_add_div _ _
  refine ⟨low m r, hlo hr, high m L (j, z), hhi hj, ?_, ?_⟩
  · intro he
    have hv := congrArg (fun u : ZMod m × H => u.1.val) he
    change (r : ZMod m).val = ((L * j : ℕ) : ZMod m).val at hv
    rw [ZMod.val_natCast_of_lt (show r < m by have := x.val_lt; omega),
      ZMod.val_natCast_of_lt (show L * j < m by have := x.val_lt; omega)] at hv
    have hj0 : j = 0 := by
      by_contra hn
      have := Nat.mul_le_mul_left L (Nat.one_le_iff_ne_zero.mpr hn)
      omega
    have hx0 : x.val = 0 := by simp [hj0] at hv hx; omega
    exact hzero ⟨x.val_eq_zero.mp hx0, (congrArg Prod.snd he).symm⟩
  · apply Prod.ext
    · change (r : ZMod m) + ((L * j : ℕ) : ZMod m) = x
      rw [← Nat.cast_add, hx, ZMod.natCast_zmod_val]
    · simp [low, high]

end Patch

section Lift

variable {M : ℕ}

private def slope {k : ℕ} (label : Fin k → ZMod M) (s Q : ℕ)
    (v : Fin k × Fin (s + Q)) : ZMod (Q ^ 2) × ZMod M :=
  (((s + v.1.val * Q : ℕ) : ZMod (Q ^ 2)) * (v.2.val : ZMod (Q ^ 2)), label v.1)

/-- Finite ordinary-to-strict lift. A common interval repairs all diagonal layers. -/
private lemma finite_lift {k s Q l b : ℕ} [NeZero Q] (label : Fin k → ZMod M)
    (hinj : Function.Injective label) (hcover : ∀ z, ∃ i j, label i + label j = z)
    (hs : 0 < s) (hQ : s * l + 1 = Q) (hgap : ∀ d, 0 < d → d < k → d ∣ s)
    (hq : 2 ≤ Q) (hb : 0 < b) (hk : k ≤ b ^ 2) (hlarge : k * s + k + 1 ≤ Q) :
    ∃ A : Finset (ZMod (Q ^ 2) × ZMod M), StrictCover A ∧ A.card ≤ (k + 2 * b + 1) * Q := by
  let D := univ.image (fun i : Fin k => label i + label i)
  let T := (univ : Finset (Fin k × Fin (s + Q))).image (slope label s Q)
  let P := patch (Q ^ 2) (b * Q) (Q / b + 1) D
  have memT (i : Fin k) (a : Fin (s + Q)) : slope label s Q (i, a) ∈ T :=
    mem_image_of_mem _ (mem_univ _)
  have offdiag (x : ZMod (Q ^ 2)) {i j : Fin k} (hij : i < j) :
      ∃ a ∈ T, ∃ c ∈ T, a ≠ c ∧ a + c = (x, label i + label j) := by
    have hd : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
    have hdk : j.val - i.val < k := (Nat.sub_le _ _).trans_lt j.isLt
    obtain ⟨t, ht, u, hu, hv⟩ := Green33StrictCoverLift.progression_pair hs hij
      (hgap _ hd hdk) hQ x
    refine ⟨_, memT i ⟨t, ht⟩, _, memT j ⟨u, hu⟩, ?_, Prod.ext hv rfl⟩
    exact fun he => hij.ne (hinj (congrArg Prod.snd he))
  refine ⟨T ∪ P, ?_, ?_⟩
  · rintro ⟨x, z⟩
    obtain ⟨i, j, rfl⟩ := hcover z
    by_cases hij : i = j
    · subst j
      have hz : label i + label i ∈ D := mem_image_of_mem _ (mem_univ _)
      have hcap : Q ^ 2 ≤ b * Q * (Q / b + 1) := by
        have hdiv := Nat.mod_lt Q hb
        have hrep := Nat.mod_add_div Q b
        have hceil : Q ≤ b * (Q / b + 1) := by rw [Nat.mul_add]; omega
        simpa only [sq, mul_assoc, mul_left_comm, mul_comm] using Nat.mul_le_mul_left Q hceil
      obtain ⟨a, ha, c, hc, hne, he⟩ := patch_covers (by nlinarith : 2 < Q ^ 2)
        (by nlinarith [Nat.mul_le_mul_right Q (show 1 ≤ b by omega)] : 1 < b * Q)
        hcap D x hz
      exact ⟨a, mem_union_right _ ha, c, mem_union_right _ hc, hne, he⟩
    · have h : ∃ a ∈ T, ∃ c ∈ T, a ≠ c ∧ a + c = (x, label i + label j) := by
        rcases lt_or_gt_of_ne hij with h | h
        · exact offdiag x h
        · simpa only [add_comm (label j) (label i)] using offdiag x h
      obtain ⟨a, ha, c, hc, hne, he⟩ := h
      exact ⟨a, mem_union_left _ ha, c, mem_union_left _ hc, hne, he⟩
  · have hT : T.card ≤ k * (s + Q) := by
      simpa only [card_univ, Fintype.card_prod, Fintype.card_fin] using
        (card_image_le (f := slope label s Q) (s := univ))
    have hD : D.card ≤ k := by
      simpa [D] using (card_image_le (f := fun i : Fin k => label i + label i) (s := univ))
    have hP := patch_card (Q ^ 2) (b * Q) (Q / b + 1) D
    have h1 : Q / b * k ≤ Q / b * (b * b) := Nat.mul_le_mul_left _ (by simpa only [sq] using hk)
    have h2 : Q / b * b ≤ Q := Nat.div_mul_le_self Q b
    have h3 := Nat.mul_le_mul_right b h2
    have h4 := Nat.mul_le_mul_left (Q / b + 1) hD
    have h5 := card_union_le T P
    change P.card ≤ _ at hP
    nlinarith only [hT, hP, h1, h3, h4, h5, hlarge]

end Lift

private lemma map_strict {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    {A : Finset H} (h : StrictCover A) : StrictCover (A.map e.symm.toEmbedding) := by
  intro x
  obtain ⟨a, ha, b, hb, hab, he⟩ := h (e x)
  refine ⟨e.symm a, mem_map.mpr ⟨_, ha, rfl⟩, e.symm b, mem_map.mpr ⟨_, hb, rfl⟩,
    fun hf => hab (e.symm.injective hf), ?_⟩
  rw [← map_add, he, AddEquiv.symm_apply_apply]

private lemma cyclic_transfer {Q M k b : ℕ} [NeZero M] [NeZero Q] (hc : (Q ^ 2).Coprime M)
    {T : Finset (ZMod (Q ^ 2) × ZMod M)} (hT : StrictCover T) (hcard : T.card ≤ (k + 2 * b + 1) * Q) :
    ∃ N : ℕ+, M ≤ N.val ∧ ∃ B : Finset (ZMod N), StrictCover B ∧
      (B.card : ℝ) / Real.sqrt N ≤ ((k : ℝ) + 2 * b + 1) / Real.sqrt M := by
  let N : ℕ+ := ⟨Q ^ 2 * M, Nat.mul_pos (pow_pos (NeZero.pos Q) _) (NeZero.pos M)⟩
  let e : ZMod N ≃+ ZMod (Q ^ 2) × ZMod M := (ZMod.chineseRemainder hc).toAddEquiv
  refine ⟨N, Nat.le_mul_of_pos_left _ (pow_pos (NeZero.pos Q) _), T.map e.symm.toEmbedding,
    map_strict e hT, ?_⟩
  rw [card_map]
  change (T.card : ℝ) / Real.sqrt (((Q ^ 2 * M : ℕ) : ℝ)) ≤ _
  push_cast
  have hq : 0 < (Q : ℝ) := by exact_mod_cast NeZero.pos Q
  have hm : 0 < (M : ℝ) := by exact_mod_cast NeZero.pos M
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hq.le, div_le_div_iff₀ (by positivity) (by positivity)]
  have hcast : (T.card : ℝ) ≤ ((k : ℝ) + 2 * b + 1) * Q := by exact_mod_cast hcard
  nlinarith [mul_le_mul_of_nonneg_right hcast (Real.sqrt_nonneg M)]

/-- An ordinary cyclic two-basis of size k gives a strict cyclic two-basis at a
modulus at least as large, with additive normalized overhead at most
(2⌊√k⌋+3)/√M. The new modulus may depend on the entire seed. -/
theorem exists_strict_lift {M : ℕ+} (A : Finset (ZMod M)) (hA : A + A = univ) :
    ∃ N : ℕ+, M ≤ N ∧ ∃ B : Finset (ZMod N), StrictCover B ∧
      (B.card : ℝ) / Real.sqrt N ≤ ((A.card : ℝ) + 2 * (A.card.sqrt + 1 : ℕ) + 1) / Real.sqrt M := by
  classical
  let k := A.card
  let e : A ≃ Fin k := A.equivFin
  let label (i : Fin k) : ZMod M := (e.symm i).val
  have hinj : Function.Injective label := fun i j he => e.symm.injective (Subtype.ext he)
  have cover (z : ZMod M) : ∃ i j, label i + label j = z := by
    obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_add.mp (show z ∈ A + A by simp [hA])
    exact ⟨e ⟨a, ha⟩, e ⟨b, hb⟩, by simpa [label] using he⟩
  let s := k.factorial * M.val
  let l := k * s + k + 3
  let Q := s * l + 1
  have hs : 0 < s := Nat.mul_pos k.factorial_pos M.property
  have hl : 0 < l := by dsimp [l]; omega
  have hq : 2 ≤ Q := by dsimp [Q]; have := Nat.mul_pos hs hl; omega
  let : NeZero Q := ⟨by omega⟩
  have large : k * s + k + 1 ≤ Q := by
    calc
      _ ≤ l := by dsimp [l]; omega
      _ ≤ s * l := Nat.le_mul_of_pos_left l hs
      _ ≤ Q := Nat.le_succ _
  have gap (d : ℕ) (hd : 0 < d) (hdk : d < k) : d ∣ s :=
    dvd_mul_of_dvd_left (Nat.dvd_factorial hd hdk.le) _
  have hc : (Q ^ 2).Coprime M.val := by
    apply Nat.Coprime.pow_left
    have hQ : Q = M.val * (k.factorial * l) + 1 := by dsimp only [Q, s]; ring
    rw [hQ, Nat.coprime_mul_left_add_left]; simp
  obtain ⟨T, hT, ht⟩ := finite_lift label hinj cover hs (show s * l + 1 = Q from rfl) gap hq
    (Nat.succ_pos k.sqrt) (Nat.lt_succ_sqrt' k).le large
  exact @cyclic_transfer Q M.val k (k.sqrt + 1) ⟨M.property.ne'⟩ ⟨by omega⟩ hc T hT ht

/-- The squared size bound for distinct sums gives a uniform half-element gap. -/
theorem strict_size_gap {N : ℕ+} {A : Finset (ZMod N)} (hA : StrictCover A) :
    Real.sqrt 2 * Real.sqrt N + 1 / 2 ≤ (A.card : ℝ) := by
  classical
  let U := (A.powersetCard 2).image (fun T => ∑ a ∈ T, a)
  have hU : U = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨a, ha, b, hb, hab, rfl⟩ := hA x
    exact mem_image.mpr ⟨{a, b}, mem_powersetCard.mpr
      ⟨insert_subset ha (singleton_subset_iff.mpr hb), by simp [hab]⟩, by simp [hab]⟩
  have h : U.card ≤ (A.powersetCard 2).card := card_image_le
  rw [hU, card_univ, ZMod.card, card_powersetCard, Nat.choose_two_right] at h
  have hn := N.property
  have hk : 1 ≤ A.card := by
    by_contra! h₀
    have hh : A.card = 0 := by omega
    simp [hh] at h
  have hcount : 2 * N.val ≤ A.card * (A.card - 1) := by omega
  have hr : (2 : ℝ) * N.val ≤ (A.card : ℝ) * ((A.card : ℝ) - 1) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk, Nat.cast_one]
      using (show ((2 * N.val : ℕ) : ℝ) ≤ ((A.card * (A.card - 1) : ℕ) : ℝ) by exact_mod_cast hcount)
  have hk' : (1 : ℝ) ≤ A.card := by exact_mod_cast hk
  rw [← Real.sqrt_mul (by norm_num)]
  have hs : Real.sqrt (2 * (N.val : ℝ)) ≤ (A.card : ℝ) - 1 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  linarith

/-- The literal predicate in the pinned statement of Green 33. -/
def OrdinaryLimit : Prop := ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ+ in atTop, ∃ A : Finset (ZMod N),
  A + A = univ ∧ |(A.card : ℝ) / Real.sqrt N - Real.sqrt 2| < ε

/-- Green's limiting constant with distinct summands for every residue. -/
def StrictLimit : Prop := ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ+ in atTop, ∃ A : Finset (ZMod N),
  StrictCover A ∧ |(A.card : ℝ) / Real.sqrt N - Real.sqrt 2| < ε

private lemma strict_sumset {N : ℕ+} {A : Finset (ZMod N)} (h : StrictCover A) : A + A = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨a, ha, b, hb, _, he⟩ := h x
  exact Finset.mem_add.mpr ⟨a, ha, b, hb, he⟩

private lemma overhead_small {k m : ℕ} (h : 4 * m + 4 ≤ k.sqrt) :
    (2 * (k.sqrt + 1) + 1) * m ≤ k := by
  calc
    _ ≤ (3 * k.sqrt) * m := Nat.mul_le_mul_right m (by omega)
    _ = k.sqrt * (3 * m) := by ring
    _ ≤ k.sqrt * k.sqrt := Nat.mul_le_mul_left _ (by omega)
    _ ≤ k := Nat.sqrt_le k

/-- Requiring distinct summands for every residue leaves Green 33 equivalent to
its original formulation on arbitrarily large cyclic groups. -/
theorem ordinary_iff_strict : OrdinaryLimit ↔ StrictLimit := by
  constructor
  · intro h ε hε
    apply frequently_atTop.mpr
    intro B
    let δ := min 1 (ε/2)
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
    obtain ⟨m, hm⟩ := exists_nat_gt (6/ε)
    have hm' : 6 < (m : ℝ)*ε := (div_lt_iff₀ hε).mp hm
    have hmpos : 0 < (m : ℝ) := (div_pos (by norm_num) hε).trans hm
    let t := 4 * m + 4
    let bound : ℕ+ := ⟨t ^ 4 + 1, Nat.succ_pos _⟩
    obtain ⟨M, hM, A, hA, hratio⟩ := frequently_atTop.mp (h δ hδ) (max B bound)
    have hMb : B ≤ M := (le_max_left ..).trans hM
    have hMt : t ^ 4 ≤ M.val := (Nat.le_succ _).trans (show bound ≤ M from (le_max_right ..).trans hM)
    have hsize : (A + A).card ≤ A.card * A.card := Finset.card_add_le
    rw [hA, card_univ, ZMod.card] at hsize
    have hroot : t ≤ A.card.sqrt := by
      apply Nat.le_sqrt.mpr
      apply Nat.mul_self_le_mul_self_iff.mp
      calc
        (t * t) * (t * t) = t ^ 4 := by ring
        _ ≤ M.val := hMt
        _ ≤ A.card * A.card := hsize
    have hcost := overhead_small hroot
    let K := (A.card : ℝ) / Real.sqrt M
    let D := (2 * (A.card.sqrt + 1 : ℕ) + 1 : ℕ)
    have hmroot : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast M.property)
    have hK : K < Real.sqrt 2 + δ := by dsimp [K]; have := (abs_lt.mp hratio).2; linarith
    have hs2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have hδ₁ : δ ≤ 1 := min_le_left _ _
    have hδε : δ ≤ ε/2 := min_le_right _ _
    have hK₃ : K < 3 := by linarith
    have hD : (D : ℝ) * m ≤ (A.card : ℝ) := by exact_mod_cast hcost
    have hDm : (D : ℝ) / Real.sqrt M * m ≤ K := by
      dsimp [K]
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hD hmroot.le
    have hDε : (D : ℝ) / Real.sqrt M < ε/2 := by
      apply (lt_of_le_of_lt ((le_div_iff₀ hmpos).mpr hDm))
      apply (div_lt_iff₀ hmpos).mpr
      nlinarith
    obtain ⟨N, hMN, S, hS, hSR⟩ := exists_strict_lift A hA
    have hupper : (S.card : ℝ) / Real.sqrt N < Real.sqrt 2 + ε := by
      apply lt_of_le_of_lt hSR
      have heq : ((A.card : ℝ) + 2 * (A.card.sqrt + 1 : ℕ) + 1) / Real.sqrt M = K + D / Real.sqrt M := by
        dsimp [K, D]; push_cast; ring
      rw [heq]; linarith
    have hNr : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast N.property)
    have hlo : Real.sqrt 2 ≤ (S.card : ℝ) / Real.sqrt N :=
      (le_div_iff₀ hNr).mpr (by linarith [strict_size_gap hS])
    refine ⟨N, hMb.trans hMN, S, hS, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  · intro h ε hε
    exact (h ε hε).mono fun N ⟨A, hA, hr⟩ => ⟨A, strict_sumset hA, hr⟩

/-- A finite strict cover within every positive one-sided tolerance suffices.
The half-element counting gap forces its modulus to grow. -/
theorem ordinary_iff_finite_strict : OrdinaryLimit ↔
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ+, ∃ A : Finset (ZMod N), StrictCover A ∧
      (A.card : ℝ) / Real.sqrt N < Real.sqrt 2 + ε := by
  rw [ordinary_iff_strict]
  constructor
  · intro h ε hε
    obtain ⟨N, A, hA, hr⟩ := (h ε hε).exists
    exact ⟨N, A, hA, by linarith [(abs_lt.mp hr).2]⟩
  · intro h ε hε
    apply frequently_atTop.mpr
    intro B
    have hB : 0 < Real.sqrt B := Real.sqrt_pos.mpr (by exact_mod_cast B.property)
    let δ := min ε (1 / (2 * Real.sqrt B))
    obtain ⟨N, A, hA, hr⟩ := h δ (lt_min hε (by positivity))
    have hN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast N.property)
    have hgap := strict_size_gap hA
    have hlo : Real.sqrt 2 ≤ (A.card : ℝ) / Real.sqrt N := (le_div_iff₀ hN).mpr (by linarith)
    have hBN : B ≤ N := by
      by_contra! smaller
      have hs : Real.sqrt N ≤ Real.sqrt B := Real.sqrt_le_sqrt (by exact_mod_cast smaller.le)
      have hd : δ ≤ 1 / (2 * Real.sqrt B) := min_le_right _ _
      have hd' := (le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt B)).mp hd
      have hδ : 0 ≤ δ := (le_min hε.le (by positivity))
      have hw := mul_le_mul_of_nonneg_left hs hδ
      have hraw := (div_lt_iff₀ hN).mp hr
      nlinarith
    exact ⟨N, hBN, A, hA, abs_lt.mpr ⟨by linarith, by linarith [show δ ≤ ε from min_le_left _ _]⟩⟩

/-- All normalized sizes of finite cyclic strict sum covers. -/
def strictRatios : Set ℝ :=
  {r | ∃ N : ℕ+, ∃ A : Finset (ZMod N), StrictCover A ∧ r = (A.card : ℝ) / Real.sqrt N}

/-- Green 33 holds exactly when √2 is the greatest lower bound of the finite
strict-cover ratios. -/
theorem ordinary_iff_infimum : OrdinaryLimit ↔ IsGLB strictRatios (Real.sqrt 2) := by
  rw [ordinary_iff_finite_strict]
  constructor
  · intro h
    constructor
    · rintro r ⟨N, A, hA, rfl⟩
      have hn : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast N.property)
      exact (le_div_iff₀ hn).mpr (by linarith [strict_size_gap hA])
    · intro b hb
      by_contra! hg
      obtain ⟨N, A, hA, hr⟩ := h (b - Real.sqrt 2) (sub_pos.mpr hg)
      have hlow := hb (show (A.card : ℝ) / Real.sqrt N ∈ strictRatios from ⟨N, A, hA, rfl⟩)
      linarith
  · intro h ε hε
    by_contra! hf
    have hlow : Real.sqrt 2 + ε ∈ lowerBounds strictRatios := by
      rintro r ⟨N, A, hA, rfl⟩
      exact hf N A hA
    linarith [h.2 hlow]

#print axioms exists_strict_lift
#print axioms strict_size_gap
#print axioms ordinary_iff_strict
#print axioms ordinary_iff_finite_strict
#print axioms ordinary_iff_infimum

end Green33StrictReduction
