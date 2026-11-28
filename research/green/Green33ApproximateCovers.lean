import Green33MaximalOrders

/-! Approximate cyclic sum covers, unordered pair excess, and the cost of
repairing missing layers after lifting the modulus. -/

open Finset Filter Green33MaximalOrders Green33StrictReduction
open scoped Pointwise Topology

namespace Green33ApproximateCovers

/-- Unordered pairs of distinct seed elements, represented by two-element subsets. -/
def pairSum {G : Type*} [AddCommMonoid G] (p : Finset G) : G := p.sum id

/-- Sums represented by two distinct elements of the seed. -/
def strictSums {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) : Finset G :=
  (A.powersetCard 2).image pairSum

theorem mem_strictSums {G : Type*} [AddCommMonoid G] [DecidableEq G] {A : Finset G} {x : G} :
    x ∈ strictSums A ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a+b=x := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hp
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hcard
    exact ⟨a,hsub (by simp),b,hsub (by simp),hab, by simp [pairSum,hab]⟩
  · rintro ⟨a,ha,b,hb,hab,rfl⟩
    exact mem_image.mpr ⟨{a,b}, mem_powersetCard.mpr
      ⟨insert_subset ha (singleton_subset_iff.mpr hb), by simp [hab]⟩, by simp [pairSum,hab]⟩

/-- Omitting the diagonal loses at most one residue per seed element. -/
theorem diagonal_loss {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    strictSums A ⊆ A+A ∧ (A+A).card ≤ (strictSums A).card + A.card := by
  constructor
  · intro x hx
    obtain ⟨a,ha,b,hb,_,he⟩ := mem_strictSums.mp hx
    exact mem_add.mpr ⟨a,ha,b,hb,he⟩
  · have hsub : A+A ⊆ strictSums A ∪ A.image (fun a => a+a) := by
      intro x hx
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hx
      by_cases hab : a=b
      · subst b
        exact mem_union_right _ (mem_image_of_mem _ ha)
      · exact mem_union_left _ (mem_strictSums.mpr ⟨a,ha,b,hb,hab,rfl⟩)
    exact (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_image_le _))

/-- Total number of representations beyond the first in each occupied fiber. -/
def excess {P G : Type*} [DecidableEq G] (pairs : Finset P) (sumOf : P → G) : ℕ :=
  ∑ x ∈ pairs.image sumOf, ((pairs.filter (fun p => sumOf p = x)).card - 1)

theorem excess_add_occupied {P G : Type*} [DecidableEq G] (pairs : Finset P) (sumOf : P → G) :
    excess pairs sumOf + (pairs.image sumOf).card = pairs.card := by
  classical
  unfold excess
  rw [card_eq_sum_ones (pairs.image sumOf), ← sum_add_distrib]
  calc
    _ = ∑ x ∈ pairs.image sumOf, (pairs.filter (fun p => sumOf p = x)).card := by
      apply sum_congr rfl
      intro x hx
      obtain ⟨p,hp,he⟩ := mem_image.mp hx
      have h := card_pos.mpr (show (pairs.filter (fun p => sumOf p=x)).Nonempty from
        ⟨p,mem_filter.mpr ⟨hp,he⟩⟩)
      omega
    _ = _ := (card_eq_sum_card_image sumOf pairs).symm

/-- The ordinary convention counts each diagonal pair once. -/
def ordinarySum {G : Type*} [AddCommMonoid G] : Sym2 G → G :=
  Sym2.lift ⟨(·+·), add_comm⟩

private theorem ordinary_image {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    A.sym2.image ordinarySum = A+A := by
  ext x
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hp,rfl⟩ := mem_image.mp h
    obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hp
    exact mem_add.mpr ⟨a,ha,b,hb,rfl⟩
  · intro h
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp h
    exact mem_image.mpr ⟨Sym2.mk a b, mk_mem_sym2_iff.mpr ⟨ha,hb⟩, rfl⟩

/-- In either convention, the number of unordered pairs minus the ambient
order is exactly the excess mass minus the number of holes. -/
theorem pair_balances {M : ℕ+} (A : Finset (ZMod M)) :
    excess (A.powersetCard 2) pairSum + M.val =
      (strictSums A)ᶜ.card + A.card.choose 2 ∧
    excess A.sym2 ordinarySum + M.val =
      (A+A)ᶜ.card + (A.card+1).choose 2 := by
  have hs := excess_add_occupied (A.powersetCard 2) pairSum
  have ho := excess_add_occupied A.sym2 ordinarySum
  change _ + (strictSums A).card = _ at hs
  rw [card_powersetCard] at hs
  rw [ordinary_image, card_sym2] at ho
  have h₁ := card_add_card_compl (strictSums A)
  have h₂ := card_add_card_compl (A+A)
  simp only [ZMod.card] at h₁ h₂
  omega

/-- A shared low digit and one high digit set per missing layer. The
coefficient of Q is 2√e, where e is the actual number of missing layers. -/
private theorem repair {M : ℕ+} (E : Finset (ZMod M)) (Q : ℕ) [NeZero Q] :
    ∃ P : Finset (ZMod (Q^2) × ZMod M),
      (∀ x : ZMod (Q^2), ∀ z ∈ E, (x,z) ∈ P+P) ∧
      (P.card : ℝ) ≤ 2*(Q : ℝ)*Real.sqrt E.card + E.card+1 := by
  let r := Real.sqrt E.card
  let L := ⌊(Q : ℝ)*r⌋₊+1
  let C := Q^2/L+1
  let low (i : ℕ) : ZMod (Q^2) × ZMod M := (i,0)
  let high (p : ℕ × ZMod M) : ZMod (Q^2) × ZMod M := (↑(L*p.1),p.2)
  let lo := (range L).image low
  let hi := ((range C) ×ˢ E).image high
  have hL : 0<L := Nat.succ_pos _
  refine ⟨lo ∪ hi, ?_, ?_⟩
  · intro x z hz
    let i := x.val % L
    let j := x.val / L
    have hi' : i < L := Nat.mod_lt _ hL
    have hj : j < C := Nat.lt_succ_of_le (Nat.div_le_div_right x.val_lt.le)
    refine mem_add.mpr ⟨low i,mem_union_left _ (mem_image_of_mem _ (mem_range.mpr hi')),
      high (j,z),mem_union_right _ (mem_image_of_mem _ (mem_product.mpr ⟨mem_range.mpr hj,hz⟩)),?_⟩
    apply Prod.ext
    · change (i : ZMod (Q^2)) + ((L*j : ℕ) : ZMod (Q^2)) = x
      rw [← Nat.cast_add, show i+L*j=x.val from Nat.mod_add_div _ _, ZMod.natCast_zmod_val]
    · simp [low,high]
  · have hlo : lo.card ≤ L := by simpa [lo] using (card_image_le (f := low) (s := range L))
    have hhi : hi.card ≤ C*E.card := by
      simpa [hi] using (card_image_le (f := high) (s := (range C) ×ˢ E))
    have hn := (card_union_le lo hi).trans (Nat.add_le_add hlo hhi)
    have hr : 0 ≤ r := Real.sqrt_nonneg _
    have hrs : r^2 = (E.card : ℝ) := Real.sq_sqrt (by positivity)
    have hLL : (Q : ℝ)*r < L := by simpa [L] using Nat.lt_floor_add_one ((Q : ℝ)*r)
    have hLU : (L : ℝ) ≤ (Q : ℝ)*r+1 := by
      simpa [L] using add_le_add_right (Nat.floor_le (show 0 ≤ (Q : ℝ)*r by positivity)) 1
    have hqL : ((Q^2/L : ℕ) : ℝ)*(L : ℝ) ≤ (Q : ℝ)^2 := by
      exact_mod_cast Nat.div_mul_le_self (Q^2) L
    have hprod : ((Q^2/L : ℕ) : ℝ)*E.card ≤ (Q : ℝ)*r := by
      apply (mul_le_mul_iff_left₀ (show 0 < (L : ℝ) by exact_mod_cast hL)).mp
      calc
        ((Q^2/L : ℕ) : ℝ)*E.card*(L : ℝ) ≤ (Q : ℝ)^2*E.card := by
          nlinarith only [mul_le_mul_of_nonneg_right hqL (Nat.cast_nonneg E.card : 0 ≤ (E.card : ℝ))]
        _ = ((Q : ℝ)*r)*((Q : ℝ)*r) := by rw [← hrs]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hLL.le (by positivity)
    have hc : ((lo ∪ hi).card : ℝ) ≤ (L : ℝ) + (((Q^2/L : ℕ) : ℝ)+1)*E.card := by
      exact_mod_cast hn
    change _ ≤ 2*(Q : ℝ)*r + E.card+1
    linarith

/-- Distinct seed pairs cover their entire layers. Radix digits cover the
remaining layers, sharing their low digits across all missing labels. -/
theorem approximate_lifts {M : ℕ+} (A : Finset (ZMod M)) :
    ∃ s : ℕ, 0<s ∧ ∀ l : ℕ, let Q := s*l+1
      ∃ N : ℕ+, N.val = Q^2*M.val ∧ ∃ B : Finset (ZMod N), B+B=univ ∧
        (B.card : ℝ) ≤ ((A.card : ℝ)+2*Real.sqrt (strictSums A)ᶜ.card)*Q +
          A.card*s + (strictSums A)ᶜ.card+1 := by
  classical
  let k := A.card
  let s := k.factorial*M.val
  have hs : 0<s := Nat.mul_pos k.factorial_pos M.pos
  refine ⟨s,hs,?_⟩
  intro l
  let Q := s*l+1
  let : NeZero Q := ⟨Nat.succ_ne_zero _⟩
  have hc : (Q^2).Coprime M.val := by
    apply Nat.Coprime.pow_left
    have h : Q = M.val*(k.factorial*l)+1 := by dsimp [Q,s]; ring
    rw [h,Nat.coprime_mul_left_add_left]; simp
  let N : ℕ+ := ⟨Q^2*M.val, Nat.mul_pos (pow_pos (NeZero.pos Q) _) M.pos⟩
  let f : ZMod N ≃+ ZMod (Q^2) × ZMod M := (ZMod.chineseRemainder hc).toAddEquiv
  let label (i : Fin k) := (A.equivFin.symm i).val
  let arm (p : Fin k × Fin (s+Q)) : ZMod (Q^2) × ZMod M :=
    (((s+p.1.val*Q : ℕ) : ZMod (Q^2))*(p.2.val : ZMod (Q^2)),label p.1)
  let T := univ.image arm
  have hT : T.card ≤ k*(s+Q) := by
    simpa [T] using (card_image_le (s := univ) (f := arm))
  obtain ⟨P,hP,hcard⟩ := repair (strictSums A)ᶜ Q
  let U := T ∪ P
  have lift {i j : Fin k} (h : i<j) (x : ZMod (Q^2)) :
      (x,label i+label j) ∈ U+U := by
    have hd : j.val-i.val ∣ s := dvd_mul_of_dvd_left (Nat.dvd_factorial
      (Nat.sub_pos_of_lt h) ((Nat.sub_le _ _).trans j.isLt.le)) M.val
    obtain ⟨t,ht,u,hu,he⟩ := Green33StrictCoverLift.progression_pair hs h hd
      (show s*l+1=Q from rfl) x
    exact mem_add.mpr ⟨arm (i,⟨t,ht⟩),mem_union_left _ (mem_image_of_mem _ (mem_univ _)),
      arm (j,⟨u,hu⟩),mem_union_left _ (mem_image_of_mem _ (mem_univ _)),Prod.ext he rfl⟩
  refine ⟨N,rfl,U.map f.symm.toEmbedding,?_,?_⟩
  · apply eq_univ_of_forall
    intro x
    have hx : f x ∈ U+U := by
      obtain ⟨y,z⟩ := f x
      by_cases hz : z ∈ strictSums A
      · obtain ⟨a,ha,b,hb,hab,rfl⟩ := mem_strictSums.mp hz
        let i := A.equivFin ⟨a,ha⟩
        let j := A.equivFin ⟨b,hb⟩
        have hi : label i = a := by simp [label,i]
        have hj : label j = b := by simp [label,j]
        have hij : i ≠ j := fun h => hab (by simpa only [hi,hj] using congrArg label h)
        rcases lt_or_gt_of_ne hij with h | h
        · simpa only [hi,hj] using lift h y
        · simpa only [hi,hj,add_comm b a] using lift h y
      · exact (add_subset_add (subset_union_right (s₁ := T)) (subset_union_right (s₁ := T)))
          (hP y z (mem_compl.mpr hz))
    obtain ⟨a,ha,b,hb,he⟩ := mem_add.mp hx
    exact mem_add.mpr ⟨_,mem_map.mpr ⟨a,ha,rfl⟩,_,mem_map.mpr ⟨b,hb,rfl⟩,
      by change f.symm a+f.symm b=x; rw [← map_add,he,AddEquiv.symm_apply_apply]⟩
  · rw [card_map]
    have hc' : (U.card : ℝ) ≤ (T.card : ℝ)+P.card := by exact_mod_cast card_union_le T P
    have ht' : (T.card : ℝ) ≤ (A.card : ℝ)*((s : ℝ)+Q) := by exact_mod_cast hT
    change _ ≤ ((A.card : ℝ)+2*Real.sqrt (strictSums A)ᶜ.card)*Q+
      A.card*s+(strictSums A)ᶜ.card+1
    linarith

/-- Finite certificate for the optimal cyclic order constant. If a k-element
seed misses e distinct-pair sum residues, then M ≤ S (k+2√e)². -/
theorem finite_certificate {M : ℕ+} (A : Finset (ZMod M)) :
    (M : ℝ) ≤ orderConstant*((A.card : ℝ)+2*Real.sqrt (strictSums A)ᶜ.card)^2 := by
  obtain ⟨s,hs,H⟩ := approximate_lifts A
  let c := (A.card : ℝ)+2*Real.sqrt (strictSums A)ᶜ.card
  let C := A.card*s+(strictSums A)ᶜ.card+1
  have hc : 0<c := by
    by_cases h : A=∅
    · subst A
      have hm : 0 < (M.val : ℝ) := by exact_mod_cast M.pos
      have he : (∅ : Finset (ZMod M)).powersetCard 2 = ∅ := powersetCard_eq_empty.mpr (by simp)
      simp [c,strictSums,he,ZMod.card,hm]
    · have hk : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr h)
      dsimp only [c]; positivity
  let Q (l : ℕ) := s*l+1
  let K (l : ℕ) := ⌈c*(Q l : ℝ)⌉₊+C
  have hQ : Tendsto Q atTop atTop := tendsto_atTop_mono
    (fun l => show l ≤ Q l by dsimp [Q]; nlinarith [Nat.mul_le_mul_right l hs]) tendsto_id
  have hQr : Tendsto (fun l => (Q l : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hQ
  have hK : Tendsto K atTop atTop := (tendsto_add_atTop_nat C).comp
    (tendsto_nat_ceil_atTop.comp (hQr.const_mul_atTop hc))
  have hscale : Tendsto (fun l => (K l : ℝ)/(Q l : ℝ)) atTop (𝓝 c) := by
    have h := ((tendsto_nat_ceil_mul_div_atTop hc.le).comp hQr).add
      ((tendsto_const_nhds (x := (C : ℝ))).div_atTop hQr)
    simpa [K,add_div,Function.comp_def] using h
  apply ge_of_tendsto (((budget_limits false).comp hK).mul (hscale.pow 2))
  filter_upwards with l
  obtain ⟨N,hN,B,hB,hsize⟩ := H l
  have hsize' : (B.card : ℝ) ≤ c*(Q l : ℝ)+(C : ℝ) := by
    simpa [c,C,Q,Nat.cast_add,Nat.cast_mul,add_assoc] using hsize
  have hk : B.card ≤ K l := by
    have : (B.card : ℝ) ≤ (⌈c*(Q l : ℝ)⌉₊ : ℝ)+(C : ℝ) :=
      hsize'.trans (add_le_add_left (Nat.le_ceil _) _)
    exact_mod_cast this
  have hmax := le_maxOrder hk (covers_false_iff.mpr hB)
  have hn : (Q l : ℝ)^2*(M : ℝ) ≤ (maxOrder false (K l) : ℝ) := by
    rw [hN] at hmax
    exact_mod_cast hmax
  have hq : 0 < (Q l : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hkp : 0 < (K l : ℝ) := by
    have hp : 0 < K l := Nat.add_pos_right _ (Nat.succ_pos _)
    exact_mod_cast hp
  change (M : ℝ) ≤ (maxOrder false (K l) : ℝ)/(K l : ℝ)^2*((K l : ℝ)/(Q l : ℝ))^2
  field_simp [hq.ne',hkp.ne']
  nlinarith

/-- An unbounded sequence of cyclic moduli, with optimal size ratio and a
defect whose mass divided by the modulus tends to zero. -/
def ApproximateLimit (defect : (M : ℕ+) → Finset (ZMod M) → ℕ) : Prop :=
  ∃ N : ℕ → ℕ+, Tendsto (fun n => (N n).val) atTop atTop ∧
    ∃ A : (n : ℕ) → Finset (ZMod (N n)),
      Tendsto (fun n => ((A n).card : ℝ)/Real.sqrt (N n)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun n => (defect (N n) (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0)

private lemma normalized_certificate {M : ℕ+} (A : Finset (ZMod M)) :
    1 ≤ orderConstant*((A.card : ℝ)/Real.sqrt M+
      2*Real.sqrt (((strictSums A)ᶜ.card : ℝ)/M))^2 := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast M.pos
  have hr := Real.sq_sqrt hm.le
  have hrp := Real.sqrt_pos_of_pos hm
  rw [Real.sqrt_div (by positivity),← mul_div_assoc,← add_div,div_pow,hr]
  rw [← mul_div_assoc, le_div_iff₀ hm,one_mul]
  exact finite_certificate A

/-- Missing a vanishing fraction of the distinct-pair sum residues suffices
for Green's original full-cover statement. -/
theorem green_iff_approximate_strict : OrdinaryLimit ↔
    ApproximateLimit (fun _ A => (strictSums A)ᶜ.card) := by
  constructor
  · intro h
    have H := ordinary_iff_strict.mp h
    have W (n : ℕ) : ∃ N : ℕ+, n ≤ N.val ∧ ∃ A : Finset (ZMod N), StrictCover A ∧
        |(A.card : ℝ)/Real.sqrt N - Real.sqrt 2| < 1/((n : ℝ)+1) := by
      obtain ⟨N,hN,A,hA,he⟩ := frequently_atTop.mp
        (H (1/((n : ℝ)+1)) (by positivity)) (Nat.succPNat n)
      exact ⟨N,(Nat.le_succ n).trans hN,A,hA,he⟩
    choose N hN A hA he using W
    refine ⟨N,tendsto_atTop_mono hN tendsto_id,A,?_,?_⟩
    · apply (tendsto_iff_dist_tendsto_zero).mpr
      simpa only [Real.dist_eq] using squeeze_zero (fun n => abs_nonneg _)
        (fun n => (he n).le) tendsto_one_div_add_atTop_nhds_zero_nat
    · have hall (n : ℕ) : strictSums (A n) = univ :=
        eq_univ_of_forall (fun x => mem_strictSums.mpr (hA n x))
      simp [hall]
  · rintro ⟨N,_,A,hsize,hholes⟩
    have hh := (Real.continuous_sqrt.tendsto 0).comp hholes
    have he : Tendsto (fun n => orderConstant*(((A n).card : ℝ)/Real.sqrt (N n)+
        2*Real.sqrt (((strictSums (A n))ᶜ.card : ℝ)/(N n : ℝ)))^2) atTop
        (𝓝 (orderConstant*2)) := by
      have h := (tendsto_const_nhds (x := orderConstant)).mul
        ((hsize.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hh)).pow 2)
      simpa [Function.comp_def,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)] using h
    have hle := ge_of_tendsto he (Eventually.of_forall (fun n => normalized_certificate (A n)))
    exact green_iff_orderConstant.mpr (le_antisymm orderConstant_bounds.2 (by linarith))

/-- Missing residues, either with distinct summands or with diagonal pairs allowed. -/
def holes (strict : Bool) {M : ℕ+} (A : Finset (ZMod M)) : ℕ :=
  if strict then (strictSums A)ᶜ.card else (A+A)ᶜ.card

/-- Excess unordered representations. Each occupied residue of multiplicity t
contributes t-1, including residues of high multiplicity. -/
def pairExcess (strict : Bool) {M : ℕ+} (A : Finset (ZMod M)) : ℕ :=
  if strict then excess (A.powersetCard 2) pairSum else excess A.sym2 ordinarySum

private theorem hole_gap {M : ℕ+} (A : Finset (ZMod M)) :
    holes false A ≤ holes true A ∧ holes true A ≤ holes false A + A.card := by
  obtain ⟨hin,hle⟩ := diagonal_loss A
  have h₁ := card_add_card_compl (strictSums A)
  have h₂ := card_add_card_compl (A+A)
  have h₃ := card_le_card hin
  simp only [holes,Bool.false_eq_true,if_false,if_true]
  omega

private lemma zero_iff_of_difference {f g : ℕ → ℝ}
    (h : Tendsto (fun n => f n-g n) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) ↔ Tendsto g atTop (𝓝 0) := by
  constructor
  · intro hf
    simpa using hf.sub h
  · intro hg
    simpa using h.add hg

private theorem small_card_ratio {N : ℕ → ℕ+} (hN : Tendsto (fun n => (N n).val) atTop atTop)
    (A : (n : ℕ) → Finset (ZMod (N n)))
    (h : Tendsto (fun n => ((A n).card : ℝ)/Real.sqrt (N n)) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun n => ((A n).card : ℝ)/(N n : ℝ)) atTop (𝓝 0) := by
  have hr := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hl := h.div_atTop hr
  refine hl.congr (fun n => ?_)
  change ((A n).card : ℝ)/Real.sqrt (N n)/Real.sqrt (N n) = _
  rw [div_div,← sq,Real.sq_sqrt (by positivity)]

/-- On each particular optimal-size sequence, diagonal sums change the
normalized number of holes by a quantity tending to zero. -/
theorem holes_zero_iff {N : ℕ → ℕ+} (hN : Tendsto (fun n => (N n).val) atTop atTop)
    (A : (n : ℕ) → Finset (ZMod (N n)))
    (h : Tendsto (fun n => ((A n).card : ℝ)/Real.sqrt (N n)) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun n => (holes true (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0) ↔
    Tendsto (fun n => (holes false (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0) := by
  apply zero_iff_of_difference
  apply squeeze_zero _ _ (small_card_ratio hN A h)
  · intro n
    exact sub_nonneg.mpr (div_le_div_of_nonneg_right (by exact_mod_cast (hole_gap (A n)).1)
      (by positivity))
  · intro n
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have ht : (holes true (A n) : ℝ) ≤ holes false (A n) + ((A n).card : ℝ) := by
      exact_mod_cast (hole_gap (A n)).2
    linarith

private theorem excess_minus_holes (strict : Bool) {M : ℕ+} (A : Finset (ZMod M)) :
    (pairExcess strict A : ℝ)-holes strict A = (A.card : ℝ)^2/2+
      (if strict then (-1:ℝ) else 1)*A.card/2-M := by
  have h := pair_balances A
  cases strict
  · have hh : (excess A.sym2 ordinarySum : ℝ)+M.val =
        ((A+A)ᶜ.card : ℝ)+((A.card+1).choose 2 : ℝ) := by exact_mod_cast h.2
    rw [Nat.cast_choose_two] at hh
    push_cast at hh
    simp only [pairExcess,holes, Bool.false_eq_true,if_false]
    nlinarith
  · have hh : (excess (A.powersetCard 2) pairSum : ℝ)+M.val =
        ((strictSums A)ᶜ.card : ℝ)+(A.card.choose 2 : ℝ) := by exact_mod_cast h.1
    rw [Nat.cast_choose_two] at hh
    simp only [pairExcess,holes,if_true]
    nlinarith

/-- For either diagonal convention and on the same sequence of seeds,
sublinear unordered-pair excess is equivalent to sublinear missing mass. -/
theorem excess_zero_iff (strict : Bool) {N : ℕ → ℕ+}
    (hN : Tendsto (fun n => (N n).val) atTop atTop)
    (A : (n : ℕ) → Finset (ZMod (N n)))
    (h : Tendsto (fun n => ((A n).card : ℝ)/Real.sqrt (N n)) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun n => (pairExcess strict (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0) ↔
    Tendsto (fun n => (holes strict (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0) := by
  let t : ℝ := if strict then -1 else 1
  have hs := ((h.pow 2).div_const 2).add
    (((tendsto_const_nhds (x := t)).mul (small_card_ratio hN A h)).div_const 2)
  have hl := hs.sub (tendsto_const_nhds (x := (1 : ℝ)))
  apply zero_iff_of_difference
  have hval : (Real.sqrt 2)^2/2+t*0/2-1=0 := by
    rw [Real.sq_sqrt (by norm_num)]; ring
  rw [hval] at hl
  refine hl.congr (fun n => ?_)
  rw [← sub_div,excess_minus_holes,div_pow,Real.sq_sqrt (by positivity)]
  have hn : (N n : ℝ) ≠ 0 := by exact_mod_cast (N n).ne_zero
  dsimp only [t]
  field_simp

private theorem approximate_congr {d e : (M : ℕ+) → Finset (ZMod M) → ℕ}
    (H : ∀ (N : ℕ → ℕ+) (_ : Tendsto (fun n => (N n).val) atTop atTop)
      (A : (n : ℕ) → Finset (ZMod (N n))),
      Tendsto (fun n => ((A n).card : ℝ)/Real.sqrt (N n)) atTop (𝓝 (Real.sqrt 2)) →
      (Tendsto (fun n => (d (N n) (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0) ↔
       Tendsto (fun n => (e (N n) (A n) : ℝ)/(N n : ℝ)) atTop (𝓝 0))) :
    ApproximateLimit d ↔ ApproximateLimit e := by
  constructor <;> rintro ⟨N,hN,A,h,h₀⟩
  · exact ⟨N,hN,A,h,(H N hN A h).mp h₀⟩
  · exact ⟨N,hN,A,h,(H N hN A h).mpr h₀⟩

/-- Green 33 is equivalent to optimal-size seeds covering all but o(M)
residues, in either the ordinary or the strict sum convention. -/
theorem green_iff_approximate (strict : Bool) :
    OrdinaryLimit ↔ ApproximateLimit (fun _ A => holes strict A) := by
  cases strict
  · exact green_iff_approximate_strict.trans
      (approximate_congr (fun _ hN A h => holes_zero_iff hN A h))
  · exact green_iff_approximate_strict

/-- Green 33 is equivalent to optimal-size seeds with o(M) excess unordered
representations, in either the ordinary or the strict convention. -/
theorem green_iff_pairExcess (strict : Bool) :
    OrdinaryLimit ↔ ApproximateLimit (fun _ A => pairExcess strict A) :=
  (green_iff_approximate strict).trans
    (approximate_congr (fun _ hN A h => (excess_zero_iff strict hN A h).symm))

/-- The finite certificates have supremum exactly S. Complete strict seeds
already have the same supremum, with zero repair cost. -/
theorem certificate_supremum : IsLUB
    {z : ℝ | ∃ M : ℕ+, ∃ A : Finset (ZMod M),
      z = (M : ℝ)/((A.card : ℝ)+2*Real.sqrt (strictSums A)ᶜ.card)^2} orderConstant := by
  constructor
  · rintro z ⟨M,A,rfl⟩
    have h := finite_certificate A
    have hm : 0<(M : ℝ) := by exact_mod_cast M.pos
    have hpos : 0 < ((A.card : ℝ)+2*Real.sqrt (strictSums A)ᶜ.card)^2 := by
      by_contra! hz
      rw [le_antisymm hz (sq_nonneg _),mul_zero] at h
      linarith
    exact (div_le_iff₀ hpos).mpr h
  · intro b hb
    apply csSup_le _ _
    · let M : ℕ+ := ⟨3,by decide⟩
      refine ⟨_,M,univ,?_,rfl⟩
      change ∀ x : ZMod 3, ∃ a ∈ univ, ∃ b ∈ univ, a≠b ∧ a+b=x
      decide +kernel
    · rintro z ⟨M,A,h,rfl⟩
      have hh : strictSums A=univ := eq_univ_of_forall (fun x => mem_strictSums.mpr (h x))
      exact hb ⟨M,A,by simp [hh]⟩

#print axioms mem_strictSums
#print axioms diagonal_loss
#print axioms excess_add_occupied
#print axioms pair_balances
#print axioms approximate_lifts
#print axioms finite_certificate
#print axioms green_iff_approximate_strict
#print axioms holes_zero_iff
#print axioms excess_zero_iff
#print axioms green_iff_approximate
#print axioms green_iff_pairExcess
#print axioms certificate_supremum

end Green33ApproximateCovers
