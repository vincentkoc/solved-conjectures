import Green33DivisibleOrder

/-! Inverse pairs and exceptional layers of a symmetric cyclic two-basis. -/

open Finset Filter
open scoped Pointwise Topology

namespace Green33UndirectedOrders

/-- Connection sets of an undirected circulant of diameter at most two. The
identity is inserted only for counting paths of length at most two. -/
def DiameterTwo {M : ℕ+} (S : Finset (ZMod M)) : Prop :=
  0 ∉ S ∧ -S = S ∧ insert 0 S + insert 0 S = univ

/-- Vertex-to-vertex interpretation in terms of zero, one, or two steps. -/
theorem two_steps_iff {M : ℕ+} (S : Finset (ZMod M)) :
    insert 0 S + insert 0 S = univ ↔
      ∀ x y : ZMod M, x = y ∨ y - x ∈ S ∨ ∃ z, z - x ∈ S ∧ y - z ∈ S := by
  constructor
  · intro h x y
    obtain ⟨a, ha, b, hb, he⟩ := mem_add.mp (show y - x ∈ insert 0 S + insert 0 S by simp [h])
    rcases mem_insert.mp ha with rfl | ha <;> rcases mem_insert.mp hb with rfl | hb
    · left; simpa using (sub_eq_zero.mp (by simpa using he.symm)).symm
    · right; left; simpa [← he] using hb
    · right; left; simpa [← he] using ha
    · right; right; refine ⟨x + a, by simpa using ha, ?_⟩
      rwa [show y - (x + a) = b by linear_combination -he]
  · intro h
    apply eq_univ_of_forall
    intro y
    rcases h 0 y with he | hy | ⟨z, hz, hy⟩
    · subst y; exact mem_add.mpr ⟨0, mem_insert_self _ _, 0, mem_insert_self _ _, zero_add _⟩
    · exact mem_add.mpr ⟨0, mem_insert_self _ _, y, mem_insert_of_mem (by simpa using hy), zero_add _⟩
    · exact mem_add.mpr ⟨z, mem_insert_of_mem (by simpa using hz), y - z, mem_insert_of_mem hy, by abel⟩

/-- The order cut in the exact optimization means that some pair of distinct
vertices has no connecting edge. Together with two-step coverage this gives
diameter exactly two. -/
theorem exact_diameter_cut_iff {M : ℕ+} (S : Finset (ZMod M)) (hz : 0 ∉ S) :
    S.card + 1 < M.val ↔ ∃ x y : ZMod M, x ≠ y ∧ y - x ∉ S := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ : ∃ y : ZMod M, y ∉ insert 0 S := by
      by_contra! ha
      have hc := congrArg Finset.card (eq_univ_of_forall ha)
      rw [card_univ, ZMod.card, card_insert_of_notMem hz] at hc
      omega
    have hh : y ≠ 0 ∧ y ∉ S := by simpa only [mem_insert, not_or] using hy
    exact ⟨0, y, Ne.symm hh.1, by simpa using hh.2⟩
  · rintro ⟨x, y, hxy, hy⟩
    have hn : y - x ∉ insert 0 S := by
      simp only [mem_insert, not_or, sub_eq_zero]
      exact ⟨Ne.symm hxy, hy⟩
    have hc := card_lt_univ_of_notMem hn
    simpa only [card_univ, ZMod.card, card_insert_of_notMem hz] using hc

private def representatives {M : ℕ+} (A : Finset (ZMod M)) : Finset (ZMod M) :=
  A.filter fun a => a.val < (-a).val

private def fixed {M : ℕ+} (A : Finset (ZMod M)) : Finset (ZMod M) :=
  A.filter fun a => a = -a

private lemma fixed_card {M : ℕ+} (A : Finset (ZMod M)) : (fixed A).card ≤ 2 := by
  let T : Finset (ZMod M) := {0, ((M.val / 2 : ℕ) : ZMod M)}
  have hs : fixed A ⊆ T := by
    intro a ha
    have he := (mem_filter.mp ha).2
    by_cases hz : a = 0
    · simp [T, hz]
    let : NeZero a := ⟨hz⟩
    have hh := congrArg ZMod.val he
    rw [ZMod.val_neg_of_ne_zero] at hh
    have hlt := a.val_lt
    have hv : a.val = M.val / 2 := by omega
    have hc := ZMod.natCast_zmod_val a
    rw [hv] at hc
    exact mem_insert_of_mem (mem_singleton.mpr hc.symm)
  exact (card_le_card hs).trans ((card_insert_le _ _).trans (by simp))

private lemma rep_card {M : ℕ+} {A : Finset (ZMod M)} (hA : -A = A) :
    2 * (representatives A).card ≤ A.card := by
  let R := representatives A
  have hs : R ∪ -R ⊆ A := by
    apply union_subset
    · exact filter_subset _ _
    · intro x hx
      have h : -x ∈ R := by simpa using hx
      have h' : -x ∈ A := (mem_filter.mp h).1
      rw [← hA]; simpa using h'
  have hdis : Disjoint R (-R) := by
    apply disjoint_left.mpr
    intro x hx h
    have hx' := (mem_filter.mp hx).2
    have hn : -x ∈ R := by simpa using h
    have hh := (mem_filter.mp hn).2
    simp only [neg_neg] at hh
    omega
  have h := card_le_card hs
  rw [card_union_of_disjoint hdis, card_neg] at h
  change 2 * R.card ≤ _
  omega

/-- Only diagonals, opposite pairs and pairs meeting a self-inverse label
need a separate fiber in a symmetric lift. -/
private def exceptional {M : ℕ+} (A : Finset (ZMod M)) : Finset (ZMod M) :=
  insert 0 (A.image (fun a => a + a) ∪ (fixed A + A))

private lemma exceptional_card {M : ℕ+} (A : Finset (ZMod M)) :
    (exceptional A).card ≤ 3 * A.card + 1 := by
  have hi : (A.image (fun a => a + a)).card ≤ A.card := card_image_le
  have hf : (fixed A + A).card ≤ (fixed A).card * A.card := card_add_le
  have hu := card_union_le (A.image (fun a => a + a)) (fixed A + A)
  have h := card_insert_le 0 (A.image (fun a => a + a) ∪ (fixed A + A))
  dsimp only [exceptional]
  nlinarith only [h, hu, hf, hi, Nat.mul_le_mul_right A.card (fixed_card A)]

private def signed {G : Type*} [Neg G] (s : Bool) (a : G) : G := if s then a else -a

private lemma orient {M : ℕ+} {A : Finset (ZMod M)} (hA : -A = A) {a : ZMod M}
    (ha : a ∈ A) (hn : a ≠ -a) : ∃ r ∈ representatives A, ∃ s : Bool, signed s r = a := by
  have hne : a.val ≠ (-a).val := fun h => hn (ZMod.val_injective _ h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨a, mem_filter.mpr ⟨ha, h⟩, true, rfl⟩
  · have hm : -a ∈ A := by rw [← hA]; simpa using ha
    exact ⟨-a, mem_filter.mpr ⟨hm, by simpa using h⟩, false, by simp [signed]⟩

private lemma layers {M : ℕ+} {A : Finset (ZMod M)} (hs : -A = A) (hA : A + A = univ)
    (z : ZMod M) : z ∈ exceptional A ∨
    ∃ a ∈ representatives A, ∃ b ∈ representatives A, a ≠ b ∧
      ∃ s t : Bool, signed s a + signed t b = z := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp (show z ∈ A + A by simp [hA])
  have fixed_left {x y : ZMod M} (hx : x ∈ A) (hy : y ∈ A) (he : x = -x) :
      x + y ∈ exceptional A := mem_insert_of_mem (mem_union_right _ (mem_add.mpr
        ⟨x, mem_filter.mpr ⟨hx, he⟩, y, hy, rfl⟩))
  by_cases hfa : a = -a
  · exact Or.inl (fixed_left ha hb hfa)
  by_cases hfb : b = -b
  · exact Or.inl (add_comm b a ▸ fixed_left hb ha hfb)
  by_cases hab : a = b
  · subst b
    exact Or.inl (mem_insert_of_mem (mem_union_left _ (mem_image_of_mem _ ha)))
  by_cases hneg : a = -b
  · simp [hneg, exceptional]
  obtain ⟨r, hr, s, es⟩ := orient hs ha hfa
  obtain ⟨u, hu, t, et⟩ := orient hs hb hfb
  refine Or.inr ⟨r, hr, u, hu, ?_, s, t, by rw [es, et]⟩
  rintro rfl
  cases s <;> cases t <;> dsimp [signed] at es et <;> rw [← es, ← et] at hab hneg
  · exact hab rfl
  · exact hneg rfl
  · exact hneg (neg_neg _).symm
  · exact hab rfl

/-- In a group with a unique nonzero involution, reserve it for the last
generator when the budget has the opposite parity. -/
theorem pad_connection_set {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (t : G) (ht : t ≠ 0) (htneg : -t = t) (hfixed : ∀ x : G, x = -x → x = 0 ∨ x = t)
    (S : Finset G) (hz : 0 ∉ S) (htS : t ∉ S) (hn : ∀ x ∈ S, -x ∈ S)
    (d : ℕ) (hd : S.card ≤ d) (horder : d < Fintype.card G) :
    ∃ T : Finset G, S ⊆ T ∧ T.card = d ∧ 0 ∉ T ∧ ∀ x ∈ T, -x ∈ T := by
  classical
  by_cases h0 : S.card = d
  · exact ⟨S, Subset.rfl, h0, hz, hn⟩
  by_cases h1 : S.card + 1 = d
  · refine ⟨insert t S, subset_insert _ _, by simpa [htS] using h1,
      by simpa [Ne.symm ht] using hz, ?_⟩
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · rw [htneg]; exact mem_insert_self _ _
    · exact mem_insert_of_mem (hn _ hx)
  let F := insert 0 (insert t S)
  have hcardF : F.card < Fintype.card G := by
    have h := card_insert_le 0 (insert t S)
    have h' := card_insert_le t S
    change (insert 0 (insert t S)).card < _
    omega
  obtain ⟨x, hx⟩ : ∃ x, x ∉ F := by
    by_contra! h
    rw [eq_univ_of_forall h, card_univ] at hcardF
    exact lt_irrefl _ hcardF
  have hxm : x ≠ 0 ∧ x ≠ t ∧ x ∉ S := by simpa [F, not_or] using hx
  have hneg : x ≠ -x := fun he => (hfixed x he).elim hxm.1 hxm.2.1
  have hnS : -x ∉ S := fun h => hxm.2.2 (by simpa using hn (-x) h)
  let V := insert x (insert (-x) S)
  have hc : V.card = S.card + 2 := by simp [V, hxm.2.2, hnS, hneg, Nat.add_assoc]
  have hzV : 0 ∉ V := by
    simp [V, Ne.symm hxm.1, hxm.1, hz]
  have htV : t ∉ V := by
    have hh : t ≠ -x := fun he => hxm.2.1 (by simpa only [neg_neg, htneg] using
      (congrArg Neg.neg he).symm)
    simp [V, Ne.symm hxm.2.1, hh, htS]
  have hnV (y : G) (hy : y ∈ V) : -y ∈ V := by
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_insert_of_mem (mem_insert_self _ _)
    rcases mem_insert.mp hy with rfl | hy
    · simp [V]
    · exact mem_insert_of_mem (mem_insert_of_mem (hn _ hy))
  obtain ⟨T, hT, hrest⟩ := pad_connection_set t ht htneg hfixed V hzV htV hnV d (by omega) horder
  exact ⟨T, (fun x hx => hT (mem_insert_of_mem (mem_insert_of_mem hx))), hrest⟩
termination_by d - S.card
decreasing_by
  change d - V.card < d - S.card
  rw [hc]
  omega

private lemma zero_or_twice_val {M : ℕ+} {x : ZMod M} (h : x = -x) :
    x = 0 ∨ 2 * x.val = M.val := by
  by_cases hz : x = 0
  · exact Or.inl hz
  let : NeZero x := ⟨hz⟩
  have hv := congrArg ZMod.val h
  rw [ZMod.val_neg_of_ne_zero] at hv
  have := x.val_lt
  exact Or.inr (by omega)

private lemma reduction_cast {M P : ℕ+} (n : ℕ) :
    (((n : ZMod (M * P)).val : ℕ) : ZMod M) = (n : ZMod M) := by
  let π : ZMod (M * P) →+* ZMod M := ZMod.castHom (show M.val ∣ (M * P).val from dvd_mul_right _ _) _
  have h := congrArg π (ZMod.natCast_zmod_val (n : ZMod (M * P)))
  simpa only [map_natCast] using h

private lemma fixed_reduces_zero {M p q : ℕ+} (hp : Even p.val) {x : ZMod (M * (p * q))}
    (h : x = -x) : (x.val : ZMod M) = 0 := by
  rcases zero_or_twice_val (M := M * (p * q)) h with hz | hv
  · rw [(ZMod.val_eq_zero _).mpr hz, Nat.cast_zero]
  obtain ⟨u, hu⟩ := hp
  change 2 * x.val = M.val * (p.val * q.val) at hv
  have he := congrArg (fun t => M.val * (t * q.val)) hu
  have hh : x.val = M.val * (u * q.val) := by nlinarith only [he, hv]
  rw [hh, Nat.cast_mul, ZMod.natCast_self, zero_mul]

private def lowDigit (M P : ℕ+) (j : ℕ) : ZMod (M * P) := ↑(M.val * j)
private def highDigit (M P : ℕ+) (L : ℕ) (v : ℕ × ZMod M) : ZMod (M * P) :=
  ↑(v.2.val + M.val * (L * v.1))

private def digits (M p q : ℕ+) (b : ℕ) (E : Finset (ZMod M)) : Finset (ZMod (M * (p * q))) :=
  ((range (b * p.val)).image (lowDigit M (p * q))) ∪
  (((range (p.val / b + 1)) ×ˢ E).image (highDigit M (p * q) (b * p.val)))

private lemma digit_count (M p q : ℕ+) (b : ℕ) (E : Finset (ZMod M)) :
    (digits M p q b E).card ≤ b * p.val + (p.val / b + 1) * E.card := by
  apply (card_union_le _ _).trans
  exact Nat.add_le_add (card_image_le.trans_eq (card_range _))
    (card_image_le.trans_eq (by rw [card_product, card_range]))

private lemma digit_cover {M p q : ℕ+} {b : ℕ} (hb : 0 < b) (hq : q ≤ p)
    (E : Finset (ZMod M)) {x : ZMod (M * (p * q))} (hx : (x.val : ZMod M) ∈ E) :
    x ∈ digits M p q b E + digits M p q b E := by
  let z := (x.val : ZMod M)
  let v := x.val / M.val
  let L := b * p.val
  have hL : 0 < L := Nat.mul_pos hb p.pos
  have hvm : v < p.val * q.val := (Nat.div_lt_iff_lt_mul M.pos).mpr (by
    have := x.val_lt; change x.val < M.val * (p.val * q.val) at this; simpa [mul_comm] using this)
  have hvp : v / p.val < q.val := by
    apply (Nat.div_lt_iff_lt_mul p.pos).mpr; simpa only [mul_comm] using hvm
  have hj : v / L < p.val / b + 1 := by
    have hq' : q.val ≤ p.val := hq
    have h := Nat.div_le_div_right (hvp.le.trans hq') (c := b)
    dsimp only [L]; rw [mul_comm b p.val, ← Nat.div_div_eq_div_mul]
    omega
  let i := v % L
  let j := v / L
  have hlow : lowDigit M (p * q) i ∈ digits M p q b E :=
    mem_union_left _ (mem_image_of_mem _ (mem_range.mpr (Nat.mod_lt _ hL)))
  have hhigh : highDigit M (p * q) L (j, z) ∈ digits M p q b E :=
    mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨mem_range.mpr hj, hx⟩))
  apply Finset.mem_add.mpr
  refine ⟨_, hlow, _, hhigh, ?_⟩
  have hmod : z.val = x.val % M.val := ZMod.val_natCast _ _
  have h1 := Nat.mod_add_div x.val M.val
  have h2 : i + L * j = v := Nat.mod_add_div _ _
  have h : M.val * i + (z.val + M.val * (L * j)) = x.val := by
    rw [hmod]
    change x.val % M.val + M.val * v = x.val at h1
    nlinarith only [h1, congrArg (M.val*·) h2]
  change (↑(M.val * i) : ZMod (M * (p * q))) + ↑(z.val + M.val * (L * j)) = x
  rw [← Nat.cast_add, h, ZMod.natCast_zmod_val]

private lemma digit_fixed {M p q : ℕ+} {b : ℕ} (hp : Even p.val) (hq : Odd q.val)
    (hsmall : 2 * b ≤ q.val) (E : Finset (ZMod M)) {x : ZMod (M * (p * q))}
    (hx : x ∈ digits M p q b E) (h : x = -x) : x = 0 := by
  rcases mem_union.mp hx with hlow | hhigh
  · obtain ⟨j, hj, rfl⟩ := mem_image.mp hlow
    rcases zero_or_twice_val (M := M * (p * q)) h with hz | hv
    · exact hz
    have hj' := mem_range.mp hj
    have hlt : 2 * j < p.val * q.val := by nlinarith only [hj', Nat.mul_le_mul_left p.val hsmall]
    have hlt' : M.val * (2 * j) < M.val * (p.val * q.val) := Nat.mul_lt_mul_of_pos_left hlt M.pos
    have hl : M.val * j < (M * (p * q)).val := by change M.val * j < M.val * (p.val * q.val); nlinarith
    change 2 * ((M.val * j : ℕ) : ZMod (M * (p * q))).val = M.val * (p.val * q.val) at hv
    erw [ZMod.val_natCast_of_lt hl] at hv
    nlinarith only [hv, hlt']
  · obtain ⟨⟨j, z⟩, _, rfl⟩ := mem_image.mp hhigh
    have hr := fixed_reduces_zero hp h
    change (((↑(z.val + M.val * (b * p.val * j)) : ZMod (M * (p * q))).val : ℕ) : ZMod M) = 0 at hr
    have he := (reduction_cast (M := M) (P := p * q) (z.val + M.val * (b * p.val * j))).symm.trans hr
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val] at he
    subst z
    let y : ZMod (M * (p * q)) := highDigit M (p * q) (b * p.val) (j, 0)
    have h2 : 2 • y = 0 := by rw [two_nsmul]; exact add_eq_zero_iff_eq_neg.mpr h
    have hmul : q.val • y = 0 := by
      have hN : ((M.val * (p.val * q.val) : ℕ) : ZMod (M * (p * q))) = 0 := ZMod.natCast_self _
      have hy : y = ((M.val * (b * p.val * j) : ℕ) : ZMod (M * (p * q))) := by
        simp only [y, highDigit, ZMod.val_zero, zero_add]
        rfl
      erw [hy, nsmul_eq_mul]
      push_cast at hN ⊢
      linear_combination (b : ZMod (M * (p * q))) * (j : ZMod (M * (p * q))) * hN
    obtain ⟨v, hv⟩ := hq
    change y = 0
    have heq : (2 * v + 1) • y = 0 := (congrArg (fun n : ℕ => n • y) hv).symm.trans hmul
    rw [add_nsmul, mul_nsmul, h2, smul_zero, one_nsmul, zero_add] at heq
    exact heq

private lemma turn_interval {L : ℕ} (s : Bool) (w : ℤ) :
    ∃ c : ℤ, ∀ t : Fin L, ∃ u : Fin L, signed s (w * u.val) = w * t.val + c := by
  cases s
  · refine ⟨-w * (L - 1 : ℤ), ?_⟩
    intro t
    refine ⟨⟨L - 1 - t.val, by omega⟩, ?_⟩
    have h : ((L - 1 - t.val : ℕ) : ℤ) = L - 1 - t.val := by omega
    change -(w * ((L - 1 - t.val : ℕ) : ℤ)) = _
    rw [h]; ring
  · exact ⟨0, fun t => ⟨t, by simp [signed]⟩⟩

/-- Each pair of different directions covers the high digit for all four choices
of signs. Reversing a coefficient interval changes its translate. -/
private lemma directional_grid {G : Type*} (R : Finset G) :
    ∃ s C : ℕ, 0 < s ∧ Even s ∧
      ∀ p q : ℕ+, s ∣ p.val → q.val + 1 = p.val → ∃ w : R → ℤ,
        ∀ a b : R, a ≠ b → ∀ σ τ : Bool, ∀ v : ℤ, ∃ t u : Fin (p.val + C),
          ∃ e : ℤ, v = signed σ (w a * t.val) + signed τ (w b * u.val) + (p.val * q.val : ℕ) * e := by
  classical
  obtain ⟨S, hS, hpos, hgap⟩ := Green33DivisibleOrder.height_family R.card
  let idx : R ≃ S := R.equivFin.trans ((finCongr hS.symm).trans S.equivFin.symm)
  let H (a : R) := (idx a).val
  let C := S.sup id
  have hC (a : R) : H a ≤ C := le_sup (f := id) (idx a).property
  let s := 2 * C.factorial
  refine ⟨s, C, by dsimp [s]; positivity, ⟨C.factorial, by dsimp [s]; omega⟩, ?_⟩
  intro p q hsp hqp
  have hpq : (q.val : ℤ) + 1 = p.val := by exact_mod_cast hqp
  let w (a : R) : ℤ := 1 + ((H a : ℤ) - 1) * p.val
  have ordered {a b : R} (hab : H a < H b) (v : ℤ) :
      ∃ t u : Fin (p.val + C), ∃ e : ℤ, v = w a * t.val + w b * u.val + (p.val * q.val : ℕ) * e := by
    let d := H b - H a
    have hd : 0 < d := Nat.sub_pos_of_lt hab
    obtain ⟨h, hh⟩ := hgap _ (idx a).property _ (idx b).property hab
    change H a = d * h at hh
    have hz : 0 < H a := hpos _ (idx a).property
    have hhpos : 0 < h := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at hh; omega
    have hhC : h ≤ C := (Nat.le_mul_of_pos_left h hd).trans (hh ▸ hC a)
    obtain ⟨m, hm⟩ := (Nat.dvd_factorial hd ((Nat.sub_le _ _).trans (hC b))).trans
      ((show C.factorial ∣ s from dvd_mul_left _ _).trans hsp)
    have h1 : (d : ℤ) * h = ((H a : ℤ) - 1) + 1 := by rw [sub_add_cancel]; exact_mod_cast hh.symm
    have h2 : (d : ℤ) * m = (q.val : ℤ) + 1 := by rw [hpq]; exact_mod_cast hm.symm
    obtain ⟨t, u, ht, ht', hu, hu', e, he⟩ := Green33DivisibleOrder.rectangular_pair ((H a : ℤ) - 1)
      d h m q.val v (by exact_mod_cast q.pos) (by exact_mod_cast hhpos) h1 h2
    rw [hpq] at ht' hu' he
    have dh : (H a : ℤ) - 1 + d = (H b : ℤ) - 1 := by dsimp [d]; rw [Nat.cast_sub hab.le]; ring
    rw [dh] at he
    exact ⟨⟨t.toNat, by omega⟩, ⟨u.toNat, by omega⟩, e, by
      simpa only [w, Int.toNat_of_nonneg ht, Int.toNat_of_nonneg hu, Nat.cast_mul] using he⟩
  refine ⟨w, ?_⟩
  intro a b hne σ τ v
  obtain ⟨c, hc⟩ := turn_interval (L := p.val + C) σ (w a)
  obtain ⟨f, hf⟩ := turn_interval (L := p.val + C) τ (w b)
  have hh : H a ≠ H b := fun h => hne (idx.injective (Subtype.ext h))
  obtain ⟨t, u, e, he⟩ : ∃ t u : Fin (p.val + C), ∃ e : ℤ,
      v - c - f = w a * t.val + w b * u.val + (p.val * q.val : ℕ) * e := by
    rcases lt_or_gt_of_ne hh with h | h
    · exact ordered h _
    · obtain ⟨u, t, e, he⟩ := ordered h (v - c - f)
      exact ⟨t, u, e, by simpa only [add_comm (w a * t.val) (w b * u.val)] using he⟩
  obtain ⟨t', ht'⟩ := hc t
  obtain ⟨u', hu'⟩ := hf u
  exact ⟨t', u', e, by rw [ht', hu']; linarith⟩

private lemma signed_intCast {n : ℕ} (σ : Bool) (a : ℤ) :
    ((signed σ a : ℤ) : ZMod n) = signed σ (a : ZMod n) := by cases σ <;> simp [signed]

private lemma signed_linear (σ : Bool) (a m t : ℤ) :
    signed σ (a + m * t) = signed σ a + m * signed σ t := by cases σ <;> simp [signed, add_comm]

/-- A symmetric lift of an ordinary seed. Its only possible self-inverse
member is zero, leaving the involution available for exact-degree padding. -/
private lemma symmetric_assemble {M p q : ℕ+} {A : Finset (ZMod M)}
    (hs : -A = A) (hA : A + A = univ) (hp : Even p.val) (hq : Odd q.val) (hpq : q ≤ p)
    (b C : ℕ) (hb : 0 < b) (hsmall : 2 * b ≤ q.val)
    (w : representatives A → ℤ)
    (hw : ∀ a c : representatives A, a ≠ c → ∀ σ τ : Bool, ∀ v : ℤ,
      ∃ t u : Fin (p.val + C), ∃ e : ℤ,
        v = signed σ (w a * t.val) + signed τ (w c * u.val) + (p.val * q.val : ℕ) * e) :
    ∃ B : Finset (ZMod (M * (p * q))), -B = B ∧ B + B = univ ∧
      (∀ x ∈ B, x = -x → x = 0) ∧
      B.card ≤ A.card * (p.val + C) + 2 * (b * p.val + (p.val / b + 1) * (3 * A.card + 1)) := by
  classical
  let R := representatives A
  let L := p.val + C
  let rep (a : R) (t : Fin L) : ℤ := a.val.val + M.val * (w a * t.val)
  let arm (v : R × Fin L) : ZMod (M * (p * q)) := (rep v.1 v.2 : ℤ)
  let arms := univ.image arm
  let D := digits M p q b (exceptional A)
  let U := arms ∪ D
  let B := U ∪ -U
  have armU (a : R) (t : Fin L) : arm (a, t) ∈ U :=
    mem_union_left _ (mem_image_of_mem _ (mem_univ _))
  have inB {x : ZMod (M * (p * q))} (hx : x ∈ U) (σ : Bool) : signed σ x ∈ B := by
    cases σ
    · exact mem_union_right _ (by simpa [signed] using hx)
    · exact mem_union_left _ hx
  have redhom : M.val ∣ (M * (p * q)).val := dvd_mul_right _ _
  let π : ZMod (M * (p * q)) →+* ZMod M := ZMod.castHom redhom _
  have red (x : ZMod (M * (p * q))) : π x = (x.val : ZMod M) := by
    have h := congrArg π (ZMod.natCast_zmod_val x)
    simpa only [map_natCast] using h.symm
  have redArm (a : R) (t : Fin L) : π (arm (a, t)) = a.val := by
    change π ((rep a t : ℤ) : ZMod (M * (p * q))) = _
    rw [map_intCast]; simp [rep]
  have nofix {x : ZMod (M * (p * q))} (hx : x ∈ U) (he : x = -x) : x = 0 := by
    rcases mem_union.mp hx with ha | hd
    · obtain ⟨⟨a, t⟩, _, rfl⟩ := mem_image.mp ha
      have hz := (red _).trans (fixed_reduces_zero hp he)
      rw [redArm] at hz
      have hlt := (mem_filter.mp a.property).2
      change a.val.val < (-a.val).val at hlt
      rw [hz, neg_zero] at hlt
      exact (lt_irrefl _ hlt).elim
    · exact digit_fixed hp hq hsmall _ hd he
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · ext x
    change x ∈ -(U ∪ -U) ↔ x ∈ U ∪ -U
    simp [or_comm]
  · apply eq_univ_of_forall
    intro x
    rcases layers hs hA (x.val : ZMod M) with hx | ⟨a, ha, c, hc, hac, σ, τ, hz⟩
    · have hDB : D ⊆ B := fun _ h => mem_union_left _ (mem_union_right _ h)
      exact add_subset_add hDB hDB (digit_cover hb hpq _ hx)
    let i : R := ⟨a, ha⟩
    let j : R := ⟨c, hc⟩
    have hd : (M.val : ℤ) ∣ (x.val : ℤ) - (signed σ (a.val : ℤ) + signed τ (c.val : ℤ)) := by
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
      simpa only [Int.cast_add, signed_intCast, Int.cast_natCast, ZMod.natCast_zmod_val] using hz
    obtain ⟨v, hv⟩ := hd
    obtain ⟨t, u, e, he⟩ := hw i j (fun h => hac (congrArg Subtype.val h)) σ τ v
    refine Finset.mem_add.mpr ⟨_, inB (armU i t) σ, _, inB (armU j u) τ, ?_⟩
    have hh : (x.val : ℤ) = signed σ (rep i t) + signed τ (rep j u) + ((M * (p * q)).val : ℤ) * e := by
      change (x.val : ℤ) = signed σ ((a.val : ℤ) + M.val * (w i * t.val)) +
        signed τ ((c.val : ℤ) + M.val * (w j * u.val)) + ((M.val * (p.val * q.val) : ℕ) : ℤ) * e
      rw [signed_linear, signed_linear]
      push_cast at he ⊢
      linear_combination hv + (M.val : ℤ) * he
    have hh' := congrArg (fun z : ℤ => (z : ZMod (M * (p * q)))) hh
    have hzero : ((M * (p * q)).val : ZMod (M * (p * q))) = 0 := ZMod.natCast_self _
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_add, Int.cast_mul, hzero,
      zero_mul, add_zero, signed_intCast, arm] using hh'.symm
  · intro x hx he
    rcases mem_union.mp hx with hx | hx
    · exact nofix hx he
    · exact nofix (he.symm ▸ (show -x ∈ U by simpa using hx)) he
  · have hB := card_union_le U (-U)
    rw [card_neg] at hB
    have hU := card_union_le arms D
    have hR : arms.card ≤ R.card * L := by
      simpa [arms, Fintype.card_prod] using (card_image_le (s := univ) (f := arm))
    have hD := digit_count M p q b (exceptional A)
    have hE := Nat.mul_le_mul_left (p.val / b + 1) (exceptional_card A)
    have hmass := Nat.mul_le_mul_right L (rep_card hs)
    change B.card ≤ _
    change B.card ≤ U.card + U.card at hB
    change U.card ≤ arms.card + D.card at hU
    change D.card ≤ _ at hD
    change (2 * R.card) * L ≤ A.card * L at hmass
    change B.card ≤ A.card * L + _
    nlinarith only [hB, hU, hR, hD, hE, hmass]

private lemma exact_degree {N : ℕ+} (hN : Even N.val) (B : Finset (ZMod N))
    (hB : -B = B) (hcov : B + B = univ) (hfree : ∀ x ∈ B, x = -x → x = 0)
    {d : ℕ} (hsize : B.card ≤ d) (hd : d < N.val) :
    ∃ T : Finset (ZMod N), T.card = d ∧ DiameterTwo T := by
  obtain ⟨v, hv⟩ := hN
  have hv0 : 0 < v := by have := N.pos; omega
  let t := (v : ZMod N)
  have htv : t.val = v := ZMod.val_natCast_of_lt (show v < N.val by omega)
  have ht : t ≠ 0 := fun he => (by have := (ZMod.val_eq_zero _).mpr he; omega)
  have htneg : -t = t := by
    apply ZMod.val_injective
    let : NeZero t := ⟨ht⟩
    rw [ZMod.val_neg_of_ne_zero, htv]
    omega
  have hfix (x : ZMod N) (hx : x = -x) : x = 0 ∨ x = t := by
    rcases zero_or_twice_val hx with hz | h
    · exact Or.inl hz
    · right; apply ZMod.val_injective; omega
  have hneg (x : ZMod N) (hx : x ∈ B.erase 0) : -x ∈ B.erase 0 := by
    have hm := mem_erase.mp hx
    apply mem_erase.mpr
    refine ⟨neg_ne_zero.mpr hm.1, ?_⟩
    rw [← hB]; simpa using hm.2
  obtain ⟨T, hT, hcard, hzero, hsym⟩ := pad_connection_set t ht htneg hfix (B.erase 0)
    (notMem_erase _ _) (fun h => ht (hfree t (mem_erase.mp h).2 htneg.symm)) hneg d
    ((card_le_card (erase_subset _ _)).trans hsize) (by simpa [ZMod.card] using hd)
  refine ⟨T, hcard, hzero, ?_, ?_⟩
  · ext x
    rw [Finset.mem_neg']
    exact ⟨fun h => by simpa using hsym _ h, hsym x⟩
  · have hsub : B ⊆ insert 0 T := by
      intro x hx
      by_cases hz : x = 0
      · simp [hz]
      · exact mem_insert_of_mem (hT (mem_erase.mpr ⟨hz, hx⟩))
    exact eq_univ_of_forall fun x => add_subset_add hsub hsub (show x ∈ B + B by simp [hcov])

/-- Size coefficient of the lifted symmetric seed, with a sublinear cost for
the exceptional layers and one unit to absorb the finitely many endpoints. -/
def liftCost (d : ℕ) : ℕ := (d + 1) + 8 * ((d + 1).sqrt + 1) + 1

/-- Every sufficiently wide grid point lifts an arbitrary undirected
diameter-two seed, with every affordable exact degree available. -/
theorem symmetric_seed_lifts {M : ℕ+} {S : Finset (ZMod M)} (hS : DiameterTwo S) :
    ∃ s H : ℕ, 0 < s ∧ ∀ l : ℕ, H ≤ s * l → ∀ d : ℕ,
      liftCost S.card * (s * l) ≤ d → d < M.val * (s * l) * (s * l - 1) →
        ∃ N : ℕ+, N.val = M.val * (s * l) * (s * l - 1) ∧ Even N.val ∧
          ∃ T : Finset (ZMod N), T.card = d ∧ DiameterTwo T := by
  classical
  let A := insert 0 S
  have hs : -A = A := by
    simp only [A, Finset.neg_insert, neg_zero, hS.2.1]
  let k := S.card + 1
  let b := 2 * (k.sqrt + 1)
  have hk : A.card = k := card_insert_of_notMem hS.1
  have hb : 0 < b := by dsimp only [b]; omega
  have hbk : 3 * k + 1 ≤ b * b := by
    dsimp only [b]; nlinarith only [Nat.lt_succ_sqrt' k]
  obtain ⟨s, C, hs0, hseven, grid⟩ := directional_grid (representatives A)
  let H := k * C + 2 * b * b + 2 * b + 3
  refine ⟨s, H, hs0, ?_⟩
  intro l hp d hd hmax
  let p : ℕ+ := ⟨s * l, by dsimp only [H] at hp; omega⟩
  let q : ℕ+ := ⟨s * l - 1, by dsimp only [H] at hp; omega⟩
  have hqp : q.val + 1 = p.val := by change s * l - 1 + 1 = s * l; dsimp only [H] at hp; omega
  have he : Even p.val := hseven.mul_right l
  have ho : Odd q.val := by
    obtain ⟨r, hr⟩ := he
    refine ⟨r - 1, by omega⟩
  have hsmall : 2 * b ≤ q.val := by change 2 * b ≤ s * l - 1; dsimp only [H] at hp; omega
  obtain ⟨w, hw⟩ := grid p q (dvd_mul_right _ _) hqp
  obtain ⟨B, hB, hcov, hfree, hsize⟩ := symmetric_assemble hs hS.2.2 he ho
    (show q ≤ p by change q.val ≤ p.val; omega) b C hb hsmall w hw
  have hpatch : (p.val / b + 1) * (3 * k + 1) ≤ b * p.val + b * b := by
    calc
      _ ≤ (p.val / b + 1) * (b * b) := Nat.mul_le_mul_left _ hbk
      _ = b * ((p.val / b) * b) + b * b := by ring
      _ ≤ _ := by gcongr; exact Nat.div_mul_le_self _ _
  have hend : k * C + 2 * b * b ≤ p.val := by change _ ≤ s * l; dsimp only [H] at hp; omega
  have hcost : B.card ≤ liftCost S.card * p.val := by
    rw [hk] at hsize
    have ceq : liftCost S.card = k + 4 * b + 1 := by dsimp [liftCost, k, b]; ring
    rw [ceq]
    nlinarith only [hsize, hpatch, hend]
  have hEN : Even (M * (p * q)).val := (he.mul_right q.val).mul_left M.val
  refine ⟨M * (p * q), (Nat.mul_assoc _ _ _).symm, hEN, ?_⟩
  exact exact_degree hEN B hB hcov hfree (hcost.trans hd)
    (by change d < M.val * (s * l * (s * l - 1)); simpa only [Nat.mul_assoc] using hmax)

private def Feasible (d n : ℕ) : Prop :=
  n = 0 ∨ ∃ N : ℕ+, N.val = n ∧ d + 1 < n ∧ ∃ S : Finset (ZMod N), S.card = d ∧ DiameterTwo S

/-- Largest order of an undirected cyclic Cayley graph of exact degree d and
exact diameter two. An empty set of positive feasible orders has maximum zero. -/
noncomputable def circulantOrder (d : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Feasible d) ((d + 1)^2)

private lemma maximal (d : ℕ) : Feasible d (circulantOrder d) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (show Feasible d 0 from Or.inl rfl)

private lemma order_bound {M : ℕ+} {S : Finset (ZMod M)} (h : DiameterTwo S) :
    M.val ≤ (S.card + 1)^2 := by
  have hc : (insert 0 S + insert 0 S).card ≤ (insert 0 S).card * (insert 0 S).card := card_add_le
  simpa only [h.2.2, card_univ, ZMod.card, card_insert_of_notMem h.1, sq] using hc

theorem le_circulantOrder {M : ℕ+} {S : Finset (ZMod M)} (h : DiameterTwo S)
    (hexact : S.card + 1 < M.val) : M.val ≤ circulantOrder S.card := by
  classical
  exact Nat.le_findGreatest (order_bound h)
    (show Feasible S.card M.val from Or.inr ⟨M, rfl, hexact, S, rfl, h⟩)

/-- All sufficiently large exact budgets retain the seed's density after
charging its explicit sublinear repair cost. -/
theorem symmetric_all_degrees {M : ℕ+} {S : Finset (ZMod M)} (hS : DiameterTwo S) :
    ∃ C : ℕ, ∀ K ≥ C, M.val * (K - C)^2 ≤ (liftCost S.card)^2 * circulantOrder K := by
  obtain ⟨s, H, hs, lifts⟩ := symmetric_seed_lifts hS
  let h := liftCost S.card
  have hh : 0 < h := by dsimp [h, liftCost]; positivity
  let e := h * s
  have he : 0 < e := Nat.mul_pos hh hs
  let C := e * (H + 4 * h + s + 4) + e + h
  refine ⟨C, ?_⟩
  intro K hK
  let n := K / e
  let p := s * n
  have hn : H + 4 * h + s + 4 ≤ n := (Nat.le_div_iff_mul_le he).mpr (by
    rw [Nat.mul_comm]; dsimp only [C] at hK; omega)
  have hnp : n ≤ p := Nat.le_mul_of_pos_left _ hs
  have hlo : n * e ≤ K := Nat.div_mul_le_self K e
  have hhi : K < e * (n + 1) := Nat.lt_mul_div_succ K he
  have hex : h * p ≤ K := by simpa only [e, p, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hlo
  have hkp : K < h * p + h * s := by simpa only [e, p, Nat.mul_add, Nat.mul_one, Nat.mul_assoc] using hhi
  have hnear : K - C ≤ h * (p - 1) := by
    have hpcut : p - 1 + 1 = p := by omega
    have hv := congrArg (h*·) hpcut
    change h * (p - 1 + 1) = h * p at hv
    have heC : e + h ≤ C := by dsimp only [C]; omega
    change h * s + h ≤ C at heC
    have hKC := Nat.sub_add_cancel hK
    nlinarith only [hkp.le, hv, heC, hKC]
  have hlarge : K + 1 < M.val * p * (p - 1) := by
    have hsp : s ≤ p := by omega
    have hn2 : 2 * h + 1 ≤ p - 1 := by omega
    have hc := Nat.mul_le_mul_left h hsp
    have hp2 := Nat.mul_le_mul_left p hn2
    have hm := Nat.le_mul_of_pos_left (p * (p - 1)) M.pos
    have hp0 : 1 ≤ p := by omega
    nlinarith only [hkp, hc, hp2, hm, hp0]
  obtain ⟨N, hN, _, T, hT, ht⟩ := lifts n (by omega) K hex (by omega : K < M.val * p * (p - 1))
  have horder := le_circulantOrder ht (by rw [hT, hN]; exact hlarge)
  rw [hT, hN] at horder
  calc
    M.val * (K - C)^2 ≤ M.val * (h * (p - 1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnear 2)
    _ = h^2 * (M.val * (p - 1) * (p - 1)) := by ring
    _ ≤ h^2 * (M.val * p * (p - 1)) := by gcongr; exact Nat.sub_le _ _
    _ ≤ _ := Nat.mul_le_mul_left _ horder

/-- Finite seed efficiencies with the repair cost included in the denominator.
Seeds may have diameter zero, one, or two. -/
def seedDensities : Set ℝ :=
  {x | ∃ N : ℕ+, ∃ S : Finset (ZMod N), DiameterTwo S ∧
    x = (N : ℝ) / (liftCost S.card : ℝ)^2}

noncomputable def undirectedConstant : ℝ := sSup seedDensities

private lemma cost_pos (d : ℕ) : 0 < liftCost d := by unfold liftCost; positivity

private lemma densities_nonempty : seedDensities.Nonempty := by
  let M : ℕ+ := ⟨1, by decide⟩
  let S := (∅ : Finset (ZMod M))
  refine ⟨_, M, S, ?_, rfl⟩
  refine ⟨notMem_empty _, by change -(∅ : Finset (ZMod M)) = ∅; exact Finset.neg_empty, ?_⟩
  apply eq_univ_of_forall
  intro x
  have hx : x = 0 := by
    apply (ZMod.val_eq_zero x).mp
    have h := x.val_lt
    change x.val < 1 at h
    omega
  subst x
  exact Finset.mem_add.mpr ⟨0, mem_insert_self _ _, 0, mem_insert_self _ _, zero_add _⟩

private lemma densities_bounded : BddAbove seedDensities := by
  refine ⟨1, ?_⟩
  rintro _ ⟨M, S, h, rfl⟩
  have hcost : S.card + 1 ≤ liftCost S.card := by unfold liftCost; omega
  have hr := (order_bound h).trans (Nat.pow_le_pow_left hcost 2)
  have hp : 0 < (liftCost S.card : ℝ) := by exact_mod_cast cost_pos _
  rw [div_le_iff₀ (sq_pos_of_pos hp), one_mul]
  exact_mod_cast hr

private lemma seed_le {M : ℕ+} {S : Finset (ZMod M)} (hS : DiameterTwo S) :
    (M : ℝ) / (liftCost S.card : ℝ)^2 ≤ undirectedConstant :=
  le_csSup densities_bounded ⟨M, S, hS, rfl⟩

theorem undirectedConstant_pos : 0 < undirectedConstant := by
  obtain ⟨_, M, S, h, rfl⟩ := densities_nonempty
  have hm : 0 < (M : ℝ) := by exact_mod_cast M.pos
  have hc : 0 < (liftCost S.card : ℝ) := by exact_mod_cast cost_pos _
  exact (div_pos hm (sq_pos_of_pos hc)).trans_le (seed_le h)

private lemma cost_ratio_limit :
    Tendsto (fun d : ℕ => (liftCost d : ℝ) / d) atTop (𝓝 1) := by
  have hs : Tendsto (fun d : ℕ => Real.sqrt d / d) atTop (𝓝 0) := by
    simp only [Real.sqrt_div_self']
    exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hnat : Tendsto (fun d : ℕ => ((d + 1).sqrt : ℝ) / d) atTop (𝓝 0) := by
    apply squeeze_zero (fun d => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
      (show Tendsto (fun d : ℕ => 2 * (Real.sqrt d / d)) atTop (𝓝 0) by simpa using hs.const_mul 2)
    intro d
    by_cases hz : d = 0
    · simp [hz]
    have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hroot : ((d + 1).sqrt : ℝ)^2 ≤ (d : ℝ) + 1 := by exact_mod_cast Nat.sqrt_le' (d + 1)
    have hle : ((d + 1).sqrt : ℝ) ≤ 2 * Real.sqrt d := by
      apply (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
      nlinarith only [hroot, Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity), hd]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hle (Nat.cast_nonneg d)
  have hl := ((tendsto_const_nhds (x := (1 : ℝ))).add (hnat.const_mul 8)).add
    (tendsto_const_div_atTop_nhds_zero_nat (10 : ℝ))
  apply (show Tendsto (fun d : ℕ => 1 + 8 * (((d + 1).sqrt : ℝ) / d) + 10 / d) atTop (𝓝 1) by
    simpa using hl).congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hn : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d≠0)
  dsimp [liftCost]
  push_cast
  field_simp [hn]
  ring

/-- The exact-degree, exact-diameter-two undirected circulant orders converge
after division by d². The limit is the supremum of the explicit finite seed
efficiencies, including the repair cost. -/
theorem circulant_order_limit :
    Tendsto (fun d : ℕ => (circulantOrder d : ℝ) / (d : ℝ)^2) atTop (𝓝 undirectedConstant) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨v, ⟨M, S, hS, rfl⟩, hv⟩ := (lt_csSup_iff densities_bounded densities_nonempty).mp ha
    obtain ⟨C, H⟩ := symmetric_all_degrees hS
    let z := (M : ℝ) / (liftCost S.card : ℝ)^2
    have hl : Tendsto (fun d : ℕ => z * (1 - (C : ℝ) / d)^2) atTop (𝓝 z) := by
      have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (C : ℝ))).pow 2
      simpa using h.const_mul z
    filter_upwards [hl.eventually_const_lt hv, eventually_ge_atTop C, eventually_ge_atTop 1]
      with d hlt hd hd'
    apply hlt.trans_le
    have hR : (M : ℝ) * ((d : ℝ) - C)^2 ≤ (liftCost S.card : ℝ)^2 * (circulantOrder d : ℝ) := by
      exact_mod_cast H d hd
    have hp : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hc : 0 < (liftCost S.card : ℝ) := by exact_mod_cast cost_pos _
    dsimp only [z]
    field_simp [hp.ne', hc.ne']
    nlinarith only [hR]
  · intro b hb
    have hl : Tendsto (fun d : ℕ => undirectedConstant * ((liftCost d : ℝ) / d)^2) atTop
        (𝓝 undirectedConstant) := by simpa using (cost_ratio_limit.pow 2).const_mul undirectedConstant
    filter_upwards [hl.eventually_lt_const hb, eventually_ge_atTop 1] with d hlt hd
    apply lt_of_le_of_lt _ hlt
    have hp : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    rcases maximal d with hz | ⟨M, hM, _, S, hcard, hS⟩
    · rw [hz, Nat.cast_zero, zero_div]
      exact mul_nonneg undirectedConstant_pos.le (sq_nonneg _)
    have hc : 0 < (liftCost S.card : ℝ) := by exact_mod_cast cost_pos _
    have h := (div_le_iff₀ (sq_pos_of_pos hc)).mp (seed_le hS)
    rw [hcard, hM] at h
    rw [div_pow, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h (sq_nonneg _)

/-- Undirected two-step sets are ordinary cyclic two-bases after adjoining zero. -/
theorem undirected_le_ordinary : undirectedConstant ≤ Green33MaximalOrders.orderConstant := by
  have hc (d : ℕ) : circulantOrder d ≤ Green33MaximalOrders.maxOrder false (d + 1) := by
    rcases maximal d with hz | ⟨M, hM, _, S, hT, hS⟩
    · simp [hz]
    · rw [← hM]
      exact Green33MaximalOrders.le_maxOrder
        (show (insert 0 S).card ≤ d + 1 by rw [card_insert_of_notMem hS.1, hT])
        (Green33MaximalOrders.covers_false_iff.mpr hS.2.2)
  have hratio : Tendsto (fun d : ℕ => ((d : ℝ) + 1) / d) atTop (𝓝 1) := by
    have ho := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    have ht : Tendsto (fun d : ℕ => 1 + (1 : ℝ) / d) atTop (𝓝 1) := by simpa using ho
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with d hd
    have hn : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    field_simp
  have hl := ((Green33MaximalOrders.budget_limits false).comp (tendsto_add_atTop_nat 1)).mul
    (hratio.pow 2)
  apply le_of_tendsto_of_tendsto circulant_order_limit (show Tendsto (fun d : ℕ =>
      (Green33MaximalOrders.maxOrder false (d + 1) : ℝ) / ((d : ℝ) + 1)^2 * (((d : ℝ) + 1) / d)^2)
      atTop (𝓝 Green33MaximalOrders.orderConstant) by simpa using hl)
  filter_upwards [eventually_ge_atTop 1] with d hd
  have hn : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hr : (circulantOrder d : ℝ) ≤ (Green33MaximalOrders.maxOrder false (d + 1) : ℝ) := by
    exact_mod_cast hc d
  field_simp
  exact hr
#print axioms undirected_le_ordinary

#print axioms undirectedConstant_pos
#print axioms circulant_order_limit

#print axioms le_circulantOrder
#print axioms symmetric_all_degrees

#print axioms symmetric_seed_lifts

#print axioms pad_connection_set

#print axioms two_steps_iff
#print axioms exact_diameter_cut_iff

end Green33UndirectedOrders
