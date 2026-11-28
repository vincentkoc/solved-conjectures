import FormalConjecturesForMathlib.Combinatorics.Hypergraph.Finite
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

/-!
# Denniston's maximal arcs

The level sets of an anisotropic quadratic form over a finite field of
characteristic two meet every secant in a fixed number of points. The construction is due
to R. H. F. Denniston, *Some maximal arcs in finite projective planes* (1969).
-/

namespace Erdos722.Denniston
variable {G : Type*} [AddCommGroup G] [Finite G]

omit [Finite G] in
private theorem indexTwo_sup {W H : AddSubgroup G} (hW : W.index = 2)
    {z : G} (hz : z ∈ H) (hzW : z ∉ W) : W ⊔ H = ⊤ := by
  have hle : W ≤ W ⊔ H := le_sup_left
  have hd := AddSubgroup.index_dvd_of_le hle
  rw [hW, Nat.dvd_prime Nat.prime_two] at hd
  rcases hd with h | h
  · exact AddSubgroup.index_eq_one.mp h
  · have hr := AddSubgroup.relIndex_mul_index hle
    rw [h, hW] at hr
    have hl : W ⊔ H ≤ W := AddSubgroup.relIndex_eq_one.mp (by omega : W.relIndex (W ⊔ H) = 1)
    exact (hzW (hl ((show H ≤ W ⊔ H from le_sup_right) hz))).elim

/-- A translate of an endomorphism with index-two image cuts an additive
subgroup in exactly its order when the translate misses zero and meets the subgroup. -/
theorem affine_secant_card (H : AddSubgroup G) (f : G →+ G) (c t₀ : G)
    (hi : f.range.index = 2) (hc : c ∉ f.range) (ht : f t₀ + c ∈ H) :
    Nat.card {t : G // f t + c ∈ H} = Nat.card H := by
  have hout : f t₀ + c ∉ f.range := by
    intro h
    apply hc
    simpa using f.range.sub_mem h (show f t₀ ∈ f.range from ⟨t₀, rfl⟩)
  have hs := indexTwo_sup hi ht hout
  have he : {t : G // f t + c ∈ H} ≃ H.comap f :=
    { toFun := fun t => ⟨t.val - t₀, by
        change f (t.val - t₀) ∈ H
        rw [map_sub]
        convert H.sub_mem t.property ht using 1
        abel⟩
      invFun := fun u => ⟨u.val + t₀, by
        rw [map_add, add_assoc]
        exact H.add_mem u.property ht⟩
      left_inv := by intro t; ext; simp
      right_inv := by intro u; ext; simp }
  have hi' : (H.comap f).index = H.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_right, hs,
      AddSubgroup.relIndex_top_right]
  rw [Nat.card_congr he]
  have hcard := (H.comap f).card_mul_index.trans H.card_mul_index.symm
  rw [hi'] at hcard
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (AddSubgroup.FiniteIndex.index_ne_zero (H := H))) hcard

variable {K : Type*} [Field K] [CharP K 2] [Finite K]

/-- The additive part of the restriction of a binary quadratic form to an affine line. -/
def restrictionMap (A B : K) : K →+ K where
  toFun t := A * t ^ 2 + B * t
  map_zero' := by simp
  map_add' x y := by rw [CharTwo.add_sq]; ring

omit [Finite K] in
private theorem restriction_ker_iff {A B t : K} (hA : A ≠ 0) :
    t ∈ (restrictionMap A B).ker ↔ t = 0 ∨ t = B / A := by
  change A * t ^ 2 + B * t = 0 ↔ _
  rw [show A * t ^ 2 + B * t = t * (A * t + B) by ring, mul_eq_zero,
    CharTwo.add_eq_zero, eq_div_iff hA, mul_comm A t]

private theorem restriction_index {A B : K} (hA : A ≠ 0) (hB : B ≠ 0) :
    (restrictionMap A B).range.index = 2 := by
  rw [AddSubgroup.index_range, Nat.card_eq_two_iff' (0 : (restrictionMap A B).ker)]
  let v : (restrictionMap A B).ker := ⟨B / A, (restriction_ker_iff hA).mpr (Or.inr rfl)⟩
  refine ⟨v, ?_, ?_⟩
  · intro hv
    exact div_ne_zero hB hA (congrArg Subtype.val hv)
  · intro x hx
    rcases (restriction_ker_iff hA).mp x.property with h | h
    · exact (hx (Subtype.ext h)).elim
    · exact Subtype.ext h

/-- Anisotropic parameters exist over every finite field of characteristic two. -/
theorem exists_parameter : ∃ a : K, ∀ t : K, t ^ 2 + t ≠ a := by
  have hi := restriction_index (K := K) one_ne_zero one_ne_zero
  have hn : (restrictionMap (1 : K) 1).range ≠ ⊤ := by
    intro h
    rw [h, AddSubgroup.index_top] at hi
    omega
  obtain ⟨a, _, ha⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hn)
  refine ⟨a, fun t h => ha ⟨t, ?_⟩⟩
  simpa [restrictionMap] using h

/-- The quadratic form whose additive-subgroup level sets give Denniston's arcs. -/
def form (a x y : K) : K := x ^ 2 + x * y + a * y ^ 2

omit [Finite K] in
theorem form_eq_zero_iff {a : K} (ha : ∀ t : K, t ^ 2 + t ≠ a) (x y : K) :
    form a x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst y
      simpa [form] using h
    · exfalso
      apply ha (x / y)
      apply (mul_right_cancel₀ (pow_ne_zero 2 hy))
      have h' : x ^ 2 + x * y = a * y ^ 2 := CharTwo.add_eq_zero.mp h
      calc
        ((x / y) ^ 2 + x / y) * y ^ 2 = x ^ 2 + x * y := by field_simp
        _ = _ := h'
  · rintro ⟨rfl, rfl⟩
    simp [form]

/-- Along a secant the additive-subgroup constraint has exactly `Nat.card H` solutions. -/
theorem quadratic_secant_card (H : AddSubgroup K) {A B C t₀ : K} (hA : A ≠ 0)
    (hline : B ≠ 0 → ∀ t : K, A * t ^ 2 + B * t + C ≠ 0)
    (ht : A * t₀ ^ 2 + B * t₀ + C ∈ H) :
    Nat.card {t : K // A * t ^ 2 + B * t + C ∈ H} = Nat.card H := by
  by_cases hB : B = 0
  · subst B
    let e : K ≃ K := Equiv.ofBijective (fun t => A * t ^ 2 + C) <| by
      have hi : Function.Injective (fun t : K => A * t ^ 2 + C) := by
        intro x y h
        exact CharTwo.sq_injective (mul_left_cancel₀ hA (add_right_cancel h))
      exact ⟨hi, Finite.surjective_of_injective hi⟩
    exact Nat.card_congr (e.subtypeEquiv (fun t => by change _ ↔ A * t ^ 2 + C ∈ H; simp))
  · apply affine_secant_card H (restrictionMap A B) C t₀ (restriction_index hA hB) _ ht
    rintro ⟨t, he⟩
    exact hline hB t (CharTwo.add_eq_zero.mpr he)

/-- Vertical lines have direction `none`; the other directions are slopes. -/
def point : Option K → K → K → K × K
  | none, b, t => (b, t)
  | some m, b, t => (t, m * t + b)

def intercept : Option K → K × K → K
  | none, p => p.1
  | some m, p => p.2 - m * p.1

def coordinate : Option K → K × K → K
  | none, p => p.2
  | some _, p => p.1

omit [CharP K 2] [Finite K] in
private theorem point_coords (d : Option K) (p : K × K) :
    point d (intercept d p) (coordinate d p) = p := by
  cases d <;> simp [intercept, coordinate, point]

omit [CharP K 2] [Finite K] in
private theorem coords_point (d : Option K) (b t : K) :
    intercept d (point d b t) = b ∧ coordinate d (point d b t) = t := by
  cases d <;> simp [intercept, coordinate, point]

omit [CharP K 2] [Finite K] in
/-- Distinct affine points determine their common direction and intercept. -/
theorem line_through {p q : K × K} (hpq : p ≠ q) :
    ∃! l : Option K × K, intercept l.1 p = l.2 ∧ intercept l.1 q = l.2 := by
  obtain ⟨x,y⟩ := p
  obtain ⟨u,v⟩ := q
  by_cases h : x = u
  · subst u
    have hn : y ≠ v := fun hh => hpq (Prod.ext rfl hh)
    refine ⟨(none, x), ⟨rfl, rfl⟩, ?_⟩
    rintro ⟨_ | m,b⟩ ⟨hp,hq⟩
    · exact Prod.ext rfl hp.symm
    · exact (hn (sub_left_inj.mp (hp.trans hq.symm))).elim
  · let m := (y - v) / (x - u)
    have hxu : x - u ≠ 0 := sub_ne_zero.mpr h
    have hm : m * (x - u) = y - v := div_mul_cancel₀ _ hxu
    have hb : v - m * u = y - m * x := by linear_combination hm
    refine ⟨(some m, y - m * x), ⟨rfl, hb⟩, ?_⟩
    rintro ⟨_ | m',b⟩ ⟨hp,hq⟩
    · exact (h (hp.trans hq.symm)).elim
    · change y - m' * x = b at hp
      change v - m' * u = b at hq
      have he : m' = m := by
        apply (eq_div_iff hxu).mpr
        linear_combination hq - hp
      subst m'
      exact Prod.ext rfl hp.symm

def onArc (a : K) (H : AddSubgroup K) (p : K × K) : Prop := form a p.1 p.2 ∈ H

/-- Every affine line meeting the selected arc has exactly the subgroup order in points. -/
theorem secant_card {a : K} (ha : ∀ t : K, t ^ 2 + t ≠ a) (H : AddSubgroup K)
    (d : Option K) (b t₀ : K) (h₀ : onArc a H (point d b t₀)) :
    Nat.card {t : K // onArc a H (point d b t)} = Nat.card H := by
  cases d with
  | none =>
    have hA : a ≠ 0 := by simpa using (ha 0).symm
    have hid (t : K) : form a b t = a * t ^ 2 + b * t + b ^ 2 := by unfold form; ring
    change form a b t₀ ∈ H at h₀
    change Nat.card {t : K // form a b t ∈ H} = _
    simp_rw [hid] at h₀ ⊢
    apply quadratic_secant_card H hA _ h₀
    intro hb t he
    exact hb (((form_eq_zero_iff ha b t).mp ((hid t).trans he)).1)
  | some m =>
    have hA : form a 1 m ≠ 0 := fun h => one_ne_zero (((form_eq_zero_iff ha 1 m).mp h).1)
    have hid (t : K) : form a t (m * t + b) = form a 1 m * t ^ 2 + b * t + a * b ^ 2 := by
      simp only [form, CharTwo.add_sq]
      ring
    change form a t₀ (m * t₀+b) ∈ H at h₀
    change Nat.card {t : K // form a t (m * t + b) ∈ H} = _
    simp_rw [hid] at h₀ ⊢
    apply quadratic_secant_card H hA _ h₀
    intro hb t he
    obtain ⟨ht, hb'⟩ := (form_eq_zero_iff ha t _).mp ((hid t).trans he)
    exact hb (by simpa [ht] using hb')

variable {V : Type*} [Fintype V]

/-- The points of a single affine line that lie in the labelled arc. -/
noncomputable def block {a : K} {H : AddSubgroup K} (e : V ≃ {p // onArc a H p})
    (l : Option K × K) : Finset V := by
  classical
  exact Finset.univ.filter fun v => intercept l.1 (e v).val = l.2

omit [CharP K 2] [Finite K] in
private theorem mem_block {a : K} {H : AddSubgroup K} (e : V ≃ {p // onArc a H p})
    (l : Option K × K) (v : V) : v ∈ block e l ↔ intercept l.1 (e v).val = l.2 := by
  classical
  simp [block]

theorem block_card {a : K} (ha : ∀ t : K, t ^ 2 + t ≠ a) {H : AddSubgroup K}
    (e : V ≃ {p // onArc a H p}) (l : Option K × K) (hn : (block e l).Nonempty) :
    (block e l).card = Nat.card H := by
  classical
  have hpt (v : V) (hv : v ∈ block e l) :
      point l.1 l.2 (coordinate l.1 (e v).val) = (e v).val := by
    rw [← (mem_block e l v).mp hv, point_coords]
  let f : (block e l) ≃ {t // onArc a H (point l.1 l.2 t)} :=
    { toFun := fun v => ⟨coordinate l.1 (e v.val).val,
        (hpt v.val v.property).symm ▸ (e v.val).property⟩
      invFun := fun t => ⟨e.symm ⟨point l.1 l.2 t.val, t.property⟩, by
        rw [mem_block, e.apply_symm_apply]
        exact (coords_point _ _ _).1⟩
      left_inv := by
        intro v
        apply Subtype.ext
        apply e.injective
        rw [e.apply_symm_apply]
        exact Subtype.ext (hpt v.val v.property)
      right_inv := by
        intro t
        apply Subtype.ext
        change coordinate l.1 (e (e.symm _)).val = _
        rw [e.apply_symm_apply]
        exact (coords_point _ _ _).2 }
  obtain ⟨v,hv⟩ := hn
  calc
    (block e l).card = Nat.card (block e l) := by simp
    _ = _ := Nat.card_congr f
    _ = _ := secant_card ha H _ _ _ (f ⟨v,hv⟩).property

/-- Nonempty secants on the labelled arc give the exact upstream pair-design predicate. -/
theorem exists_arc_design {a : K} (ha : ∀ t : K, t ^ 2 + t ≠ a) {H : AddSubgroup K}
    (e : V ≃ {p // onArc a H p}) :
    ∃ D : Finset (Finset V), D.IsBlockDesign 2 (Nat.card H) := by
  classical
  let D : Finset (Finset V) :=
    Finset.univ.filter fun B => B.Nonempty ∧ ∃ l : Option K × K, B = block e l
  have hD (B) : B ∈ D ↔ B.Nonempty ∧ ∃ l, B = block e l := by simp [D]
  refine ⟨D, ?_, ?_⟩
  · intro B hB
    obtain ⟨hn,l,rfl⟩ := (hD B).mp hB
    exact block_card ha e l hn
  · intro S hS
    obtain ⟨v,w,hvw,rfl⟩ := Finset.card_eq_two.mp hS
    have hne : (e v).val ≠ (e w).val := fun h => hvw (e.injective (Subtype.ext h))
    obtain ⟨l, ⟨hv,hw⟩, hu⟩ := line_through hne
    have h₁ := (mem_block e l v).mpr hv
    have h₂ := (mem_block e l w).mpr hw
    refine ⟨block e l, ⟨(hD _).mpr ⟨⟨v,h₁⟩, l, rfl⟩, by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro h₁ h₂⟩, ?_⟩
    rintro B ⟨hB,hsub⟩
    obtain ⟨_,m,rfl⟩ := (hD B).mp hB
    apply congrArg (block e)
    apply hu
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff, mem_block] using hsub

private theorem punctured_card {T : Type*} [Finite T] (z : T) :
    Nat.card {t : T // t ≠ z} = Nat.card T - 1 := by
  classical
  let : Fintype T := Fintype.ofFinite T
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

omit [CharP K 2] [Finite K] in
private theorem point_origin (d : Option K) : point d (0 : K) 0 = (0, 0) := by
  cases d <;> simp [point]

omit [CharP K 2] [Finite K] in
private theorem origin_intercept (d : Option K) : intercept d ((0, 0) : K × K) = 0 := by
  cases d <;> simp [intercept]

/-- The pencil through the origin partitions the other points of the arc. -/
theorem arc_card {a : K} (ha : ∀ t : K, t ^ 2 + t ≠ a) (H : AddSubgroup K) :
    Nat.card {p // onArc a H p} = Nat.card K * (Nat.card H - 1) + Nat.card H := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let O : {p // onArc a H p} := ⟨(0, 0), by simp [onArc, form]⟩
  let R (d : Option K) := {t : K // onArc a H (point d 0 t)}
  let z (d : Option K) : R d := ⟨0, by rw [point_origin]; exact O.property⟩
  let P := {p : {p // onArc a H p} // p ≠ O}
  let rays := (d : Option K) × {t : R d // t ≠ z d}
  let f : rays → P := fun ⟨d,t⟩ =>
    ⟨⟨point d 0 t.val.val, t.val.property⟩, by
      intro h
      apply t.property
      apply Subtype.ext
      have hp : point d 0 t.val.val = point d 0 0 := (congrArg Subtype.val h).trans (point_origin d).symm
      exact ((coords_point d 0 t.val.val).2.symm.trans (congrArg (coordinate d) hp)).trans
        (coords_point d 0 0).2⟩
  have bij : Function.Bijective f := by
    constructor
    · rintro ⟨d,t⟩ ⟨d',s⟩ he
      have hp : point d 0 t.val.val = point d' 0 s.val.val := congrArg (fun p : P => p.val.val) he
      have hne : (0, 0) ≠ point d 0 t.val.val := fun h =>
        (f ⟨d,t⟩).property (Subtype.ext h.symm)
      obtain ⟨_,_,hu⟩ := line_through hne
      have hd := hu (d,0) ⟨origin_intercept d, (coords_point d 0 t.val.val).1⟩
      have hd' := hu (d',0) ⟨origin_intercept d', hp ▸ (coords_point d' 0 s.val.val).1⟩
      have hdd := congrArg Prod.fst (hd.trans hd'.symm)
      change d = d' at hdd
      subst d'
      have hts := congrArg (coordinate d) hp
      rw [(coords_point _ _ _).2, (coords_point _ _ _).2] at hts
      congr 1
      exact Subtype.ext (Subtype.ext hts)
    · intro p
      have hne : (0, 0) ≠ p.val.val := fun h => p.property (Subtype.ext h.symm)
      obtain ⟨⟨d,b⟩,⟨hb,hp⟩,_⟩ := line_through hne
      change intercept d (0, 0) = b at hb
      rw [origin_intercept] at hb
      subst b
      let c := coordinate d p.val.val
      have he : point d 0 c = p.val.val := by
        change intercept d p.val.val = 0 at hp
        rw [← hp, point_coords]
      let t : R d := ⟨c, he.symm ▸ p.val.property⟩
      have hn : t ≠ z d := by
        intro h
        apply hne
        have hc : c = 0 := congrArg Subtype.val h
        rw [← he, hc, point_origin]
      exact ⟨⟨d,t,hn⟩, Subtype.ext (Subtype.ext he)⟩
  have hR (d : Option K) : Nat.card {t : R d // t ≠ z d} = Nat.card H - 1 := by
    rw [punctured_card]
    exact congrArg (· - 1) (secant_card ha H d 0 0 (z d).property)
  have hcount := Nat.card_congr (Equiv.ofBijective f bij)
  change Nat.card ((d : Option K) × {t : R d // t ≠ z d}) = Nat.card {p // p ≠ O} at hcount
  rw [Nat.card_sigma, punctured_card] at hcount
  simp only [hR, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hcount
  rw [Fintype.card_option, ← Nat.card_eq_fintype_card, Nat.add_mul, one_mul] at hcount
  have hpos : 0 < Nat.card {p // onArc a H p} := by
    let : Nonempty {p // onArc a H p} := ⟨O⟩
    exact Nat.card_pos
  have hH : 0 < Nat.card H := Nat.card_pos
  omega

/-- Denniston's construction for every field order `2^e` and subgroup order
`2^b`, including proper arcs when `0 < b < e`. -/
theorem exists_denniston_design (e b : ℕ) (he : 0 < e) (hbe : b ≤ e) :
    ∃ D : Finset (Finset (Fin (2 ^ e * (2 ^ b - 1) + 2 ^ b))),
      D.IsBlockDesign 2 (2 ^ b) := by
  classical
  let K := GaloisField 2 e
  have hK : Nat.card K = 2 ^ e := GaloisField.card 2 e he.ne'
  obtain ⟨S,hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := Multiplicative K) 2
    (show 2 ^ b ∣ Nat.card K from hK ▸ Nat.pow_dvd_pow 2 hbe)
  let H : AddSubgroup K := AddSubgroup.toSubgroup.symm S
  have hH : Nat.card H = 2 ^ b := hS
  obtain ⟨a, ha⟩ := exists_parameter (K := K)
  let : Fintype {p // onArc a H p} := Fintype.ofFinite _
  have hcard : Fintype.card {p // onArc a H p} = 2 ^ e * (2 ^ b - 1) + 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, arc_card ha H, hH, hK]
  obtain ⟨D,hD⟩ := exists_arc_design ha (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨D, by simpa only [hH] using hD⟩

/-- Positive proper subgroup exponents yield orders between successive powers of two. -/
theorem order_not_power (e b : ℕ) (hbe : b + 1 < e) (j : ℕ) :
    2 ^ e * (2 ^ (b + 1) - 1) + 2 ^ (b + 1) ≠ 2 ^ j := by
  have hq : (2 : ℕ) ^ (b + 1) < 2 ^ e := Nat.pow_lt_pow_right (by decide) hbe
  have hb : 0 < (2 : ℕ) ^ b := by positivity
  have h₁ : 2 ^ b ≤ 2 ^ (b + 1) - 1 := by rw [pow_succ]; omega
  have h₂ := Nat.mul_le_mul_left (2 ^ e) h₁
  have hpos : 0 < (2 : ℕ) ^ (b + 1) := by positivity
  have hid : 2 ^ (b + 1) - 1 + 1 = 2 ^ (b + 1) := by omega
  have hmul := congrArg ((2 ^ e) * ·) hid
  rw [Nat.mul_add, Nat.mul_one] at hmul
  by_cases hj : j ≤ e + b
  · have hj' := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    rw [pow_add] at hj'
    omega
  · have hj' := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : e + (b + 1) ≤ j)
    rw [pow_add] at hj'
    omega

/-- For each fixed block size `2^(b + 2)`, cofinally many orders outside the
powers of two carry the canonical Steiner pair design. -/
theorem frequently_denniston_design (b : ℕ) :
    ∃ᶠ n : ℕ in Filter.atTop, (∀ j : ℕ, n ≠ 2 ^ j) ∧
      ∃ D : Finset (Finset (Fin n)), D.IsBlockDesign 2 (2 ^ (b + 2)) := by
  apply Filter.frequently_atTop.mpr
  intro N
  let e := N + b + 3
  have hbe : b + 2 < e := by dsimp [e]; omega
  refine ⟨_, ?_, order_not_power e (b + 1) hbe, exists_denniston_design e (b + 2) (by omega) hbe.le⟩
  have h₁ := Nat.lt_pow_self (n := e) (by decide : 1 < 2)
  have h₂ : 1 ≤ 2 ^ (b + 2) - 1 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ b + 2)
    omega
  have h₃ := Nat.mul_le_mul_left (2 ^ e) h₂
  change N ≤ 2 ^ e * (2 ^ (b + 2) - 1) + 2 ^ (b + 2)
  have hN : N ≤ e := by dsimp [e]; omega
  rw [Nat.mul_one] at h₃
  exact hN.trans (h₁.le.trans (h₃.trans (Nat.le_add_right _ _)))

#print axioms affine_secant_card
#print axioms exists_parameter
#print axioms secant_card
#print axioms arc_card
#print axioms exists_arc_design
#print axioms exists_denniston_design
#print axioms order_not_power
#print axioms frequently_denniston_design

end Erdos722.Denniston
