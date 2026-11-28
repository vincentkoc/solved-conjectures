import Green28FourAtoms
import Green28UniformSums

/-! Positive weights on a four-by-four integer sum table. -/

open Finset Green28 Green28FourAtoms
open scoped ENNReal

namespace Green28FourAtomLaws

private def fiber {m n : ℕ} (a : Fin m → ℤ) (b : Fin n → ℤ) (z : ℤ) :
    Finset (Fin m × Fin n) := univ.filter fun p => a p.1+b p.2=z

private theorem contribution {m n : ℕ} (a : Fin m → ℤ) (b : Fin n → ℤ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (hf : ∀ i, 0 < f i) (hg : ∀ j, 0 < g j)
    (c : ℝ) (mass : ∀ i j, ∑ p ∈ fiber a b (a i+b j), f p.1*g p.2 = c) (i j) :
    f i*g j ≤ c ∧ (Alone a b i j ↔ f i*g j = c) := by
  classical
  let S := fiber a b (a i+b j)
  have mem : (i,j) ∈ S := by simp [S,fiber]
  have total : ∑ p ∈ S, f p.1*g p.2 = c := mass i j
  have pos (p : Fin m × Fin n) : 0 < f p.1*g p.2 := mul_pos (hf _) (hg _)
  refine ⟨total ▸ single_le_sum (f := fun p : Fin m × Fin n => f p.1*g p.2) (fun p _ => (pos p).le) mem, ?_⟩
  constructor
  · intro single
    rw [←total]
    symm
    apply sum_eq_single (i,j)
    · intro p hp ne
      have eq := (mem_filter.mp hp).2
      obtain ⟨ei,ej⟩ := single _ _ eq.symm
      exact (ne (Prod.ext ei.symm ej.symm)).elim
    · exact fun hm => (hm mem).elim
  · intro e k l he
    by_contra ne
    have distinct : (k,l) ≠ (i,j) := by rintro eq; exact ne ⟨(Prod.mk.inj eq).1.symm,(Prod.mk.inj eq).2.symm⟩
    have mem' : (k,l) ∈ S := by simpa [S,fiber] using he.symm
    have lt := single_lt_sum (f := fun p : Fin m × Fin n => f p.1*g p.2) distinct mem mem'
      (pos _) (fun p _ _ => (pos p).le)
    exact lt.ne (e.trans total.symm)

/-- Singleton representations form a rectangle of maximal rows and columns.
This criterion asks whether such a rectangle contains an entire side. -/
def GridTest (m n : ℕ) : Prop :=
  ∀ (a : Fin (m+1) → ℤ) (b : Fin (n+1) → ℤ), StrictMono a → StrictMono b →
    ∀ (u : Fin (m+1) → Prop) (v : Fin (n+1) → Prop),
      (∀ i j, Alone a b i j ↔ u i ∧ v j) → u 0 → u (Fin.last m) →
        v 0 → v (Fin.last n) → (∀ i, u i) ∨ (∀ j, v j)

private theorem weights_of_grid {m n : ℕ} (test : GridTest m n)
    (a : Fin (m+1) → ℤ) (b : Fin (n+1) → ℤ) (ha : StrictMono a) (hb : StrictMono b)
    (f : Fin (m+1) → ℝ) (g : Fin (n+1) → ℝ) (hf : ∀ i, 0 < f i) (hg : ∀ j, 0 < g j)
    (c : ℝ) (mass : ∀ i j, ∑ p ∈ univ.filter (fun p : Fin (m+1) × Fin (n+1) => a p.1+b p.2=a i+b j),
      f p.1*g p.2 = c) : (∀ i, f i=f 0) ∨ (∀ j, g j=g 0) := by
  have h := contribution a b f g hf hg c mass
  have av0 (i : Fin (m+1)) := ha.monotone (show 0 ≤ i from Fin.zero_le _)
  have bv0 (i : Fin (n+1)) := hb.monotone (show 0 ≤ i from Fin.zero_le _)
  have av3 (i : Fin (m+1)) := ha.monotone (Fin.le_last i)
  have bv3 (i : Fin (n+1)) := hb.monotone (Fin.le_last i)
  have first : Alone a b 0 0 := by
    intro k l eq
    have := av0 k; have := bv0 l
    exact ⟨ha.injective (by omega),hb.injective (by omega)⟩
  have last : Alone a b (Fin.last m) (Fin.last n) := by
    intro k l eq
    have := av3 k; have := bv3 l
    exact ⟨ha.injective (by omega),hb.injective (by omega)⟩
  have origin := (h 0 0).2.mp first
  have fbound (i) : f i ≤ f 0 := (mul_le_mul_iff_left₀ (hg 0)).mp ((h i 0).1.trans_eq origin.symm)
  have gbound (j) : g j ≤ g 0 := (mul_le_mul_iff_right₀ (hf 0)).mp ((h 0 j).1.trans_eq origin.symm)
  have rect (i j) : Alone a b i j ↔ f i=f 0 ∧ g j=g 0 := by
    rw [(h i j).2, ← origin]
    constructor
    · intro eq
      constructor
      · by_contra! ne
        have lt := mul_lt_mul_of_pos_right (lt_of_le_of_ne (fbound i) ne) (hg j)
        exact (lt.trans_le (mul_le_mul_of_nonneg_left (gbound j) (hf 0).le)).ne eq
      · by_contra! ne
        have lt := mul_lt_mul_of_pos_left (lt_of_le_of_ne (gbound j) ne) (hf i)
        exact (lt.trans_le (mul_le_mul_of_nonneg_right (fbound i) (hg 0).le)).ne eq
    · rintro ⟨e,r⟩; rw [e,r]
  have ends := (rect _ _).mp last
  exact test _ _ ha hb _ _ rect rfl ends.1 rfl ends.2

/-- Constant mass on all occupied sums forces one whole marginal to be flat
whenever each has at most four labelled sites. -/
theorem small_weights {m n : ℕ} (hm : m ≤ 3) (hn : n ≤ 3)
    (a : Fin (m+1) → ℤ) (b : Fin (n+1) → ℤ) (ha : StrictMono a) (hb : StrictMono b)
    (f : Fin (m+1) → ℝ) (g : Fin (n+1) → ℝ) (hf : ∀ i, 0 < f i) (hg : ∀ j, 0 < g j)
    (c : ℝ) (mass : ∀ i j, ∑ p ∈ univ.filter (fun p : Fin (m+1) × Fin (n+1) => a p.1+b p.2=a i+b j),
      f p.1*g p.2 = c) : (∀ i, f i=f 0) ∨ (∀ j, g j=g 0) := by
  exact weights_of_grid (small_grid hm hn) a b ha hb f g hf hg c mass

private theorem indexed_bind {P : PMF ℤ} {s : Finset ℤ} {n : ℕ}
    (supp : P.support = (s : Set ℤ)) (size : s.card = n) (F : ℤ → PMF ℤ) (z : ℤ) :
    ((P.bind F) z).toReal =
      ∑ i : Fin n, (P (s.orderEmbOfFin size i)).toReal * (F (s.orderEmbOfFin size i) z).toReal := by
  have off (x : ℤ) (hx : x ∉ s) : P x * F x z = 0 := by
    rw [(P.apply_eq_zero_iff _).mpr (by rw [supp]; exact hx),zero_mul]
  rw [PMF.bind_apply,tsum_eq_sum off,ENNReal.toReal_sum
    (fun x _ => ENNReal.mul_ne_top (P.apply_ne_top _) ((F x).apply_ne_top _))]
  simp only [ENNReal.toReal_mul]
  symm
  exact ((s.orderIsoOfFin size).toEquiv.sum_comp (fun x : s => (P x).toReal*(F x z).toReal)).trans
    (sum_coe_sort s (fun x => (P x).toReal*(F x z).toReal))

private theorem indexed_sum {P Q : PMF ℤ} {s t : Finset ℤ} {m n : ℕ}
    (ps : P.support = (s : Set ℤ)) (qs : Q.support = (t : Set ℤ))
    (ms : s.card=m) (ns : t.card=n) (z : ℤ) :
    (indepSum P Q z).toReal = ∑ ij ∈ fiber (s.orderEmbOfFin ms) (t.orderEmbOfFin ns) z,
      (P (s.orderEmbOfFin ms ij.1)).toReal * (Q (t.orderEmbOfFin ns ij.2)).toReal := by
  change ((P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z).toReal = _
  rw [indexed_bind ps ms,fiber,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  rw [indexed_bind qs ns,mul_sum]
  apply sum_congr rfl
  intro j _
  by_cases h : s.orderEmbOfFin ms i+t.orderEmbOfFin ns j=z
  · simp [PMF.pure_apply,h]
  · simp [PMF.pure_apply,h,Ne.symm h]

private theorem rational_of_constant {P : PMF ℤ} {s : Finset ℤ} {n : ℕ}
    (ps : P.support = (s : Set ℤ)) (hs : s.card=n) (w : ℝ)
    (flat : ∀ i, (P (s.orderEmbOfFin hs i)).toReal=w) : Green28UniformSums.RationalRatios P := by
  have values {z : ℤ} (hz : z ∈ P.support) : (P z).toReal = w := by
    rw [ps, ← s.range_orderEmbOfFin hs] at hz
    obtain ⟨i,rfl⟩ := hz
    exact flat i
  intro x y hy
  have pos := ENNReal.toReal_pos ((P.mem_support_iff _).mp hy) (P.apply_ne_top y)
  by_cases hx : x ∈ P.support
  · exact ⟨1,by rw [values hx,← values hy]; simp [pos.ne']⟩
  · exact ⟨0,by simp [(P.apply_eq_zero_iff _).mpr hx]⟩

/-- Apply a singleton-rectangle criterion at the actual marginal cardinalities. -/
theorem uniform_of_grid {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    (test : ∀ m n, P.support.ncard=m+1 → Q.support.ncard=n+1 → GridTest m n) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  obtain ⟨pf,qf⟩ := Green28UniformSums.finite_of_uniform_sum uniform
  let s := pf.toFinset
  let t := qf.toFinset
  have ps : P.support = (s : Set ℤ) := pf.coe_toFinset.symm
  have qs : Q.support = (t : Set ℤ) := qf.coe_toFinset.symm
  have sn : 0 < s.card := card_pos.mpr (pf.toFinset_nonempty.mpr P.support_nonempty)
  have tn : 0 < t.card := card_pos.mpr (qf.toFinset_nonempty.mpr Q.support_nonempty)
  have ms : s.card = s.card-1+1 := by omega
  have ns : t.card = t.card-1+1 := by omega
  let a := s.orderEmbOfFin ms
  let b := t.orderEmbOfFin ns
  have hp (i) : a i ∈ P.support := by rw [ps]; exact s.orderEmbOfFin_mem ms i
  have hq (j) : b j ∈ Q.support := by rw [qs]; exact t.orderEmbOfFin_mem ns j
  have fp (i) := ENNReal.toReal_pos ((P.mem_support_iff _).mp (hp i)) (P.apply_ne_top _)
  have gp (j) := ENNReal.toReal_pos ((Q.mem_support_iff _).mp (hq j)) (Q.apply_ne_top _)
  obtain ⟨v,hv,eq⟩ := uniform
  have mass (i j) : ∑ p ∈ fiber a b (a i+b j), (P (a p.1)).toReal*(Q (b p.2)).toReal = (v.card:ℝ)⁻¹ := by
    have hab : a i+b j ∈ (indepSum P Q).support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨a i,hp i,
        (PMF.mem_support_bind_iff _ _ _).mpr ⟨b j,hq j,(PMF.mem_support_pure_iff _ _).mpr rfl⟩⟩
    rw [eq,PMF.support_uniformOfFinset] at hab
    rw [←indexed_sum ps qs ms ns,eq,PMF.uniformOfFinset_apply_of_mem hv hab,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  apply Green28UniformSums.uniform_of_rational_ratios ⟨v,hv,eq⟩
  have grid := test _ _ ((Set.ncard_eq_toFinset_card _ pf).trans ms) ((Set.ncard_eq_toFinset_card _ qf).trans ns)
  rcases weights_of_grid grid a b a.strictMono b.strictMono _ _ fp gp _ mass with h|h
  · exact Or.inl (rational_of_constant ps ms _ h)
  · exact Or.inr (rational_of_constant qs ns _ h)

/-- Positive answer to the pinned Green 28 conclusion when both integer laws have
at most four atoms, with arbitrary integer spacings and arbitrary positive real masses. -/
theorem uniform_of_at_most_four_atoms {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    (pc : P.support.ncard ≤ 4) (qc : Q.support.ncard ≤ 4) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply uniform_of_grid uniform
  intro m n pm qn
  exact small_grid (by omega) (by omega)

#print axioms uniform_of_grid
#print axioms uniform_of_at_most_four_atoms
#print axioms small_weights

end Green28FourAtomLaws
