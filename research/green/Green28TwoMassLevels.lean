import Green28AverageObstruction

/-! Quadratic restrictions on the normalized atom masses of two-level laws. -/

open Polynomial Finset

namespace Green28TwoMassLevels

open Green28 Green28UniformSums
open scoped ENNReal

/-- The positive atom probabilities take at most two distinct values. -/
def AtMostTwo (P : PMF ℤ) : Prop :=
  ∃ a b : ℝ, ∀ x∈P.support, (P x).toReal=a ∨ (P x).toReal=b

/-- The two mass classes, normalized at the rightmost support point. -/
structure Levels (P : PMF ℤ) where
  high : Finset ℤ
  low : Finset ℤ
  high_ne : high.Nonempty
  low_ne : low.Nonempty
  disjoint : Disjoint high low
  supp : P.support = ↑(high ∪ low)
  beyond : low.max' low_ne < high.max' high_ne
  scale : ℝ
  weight : ℝ
  scale_pos : 0 < scale
  pos : 0 < weight
  lt_one : weight < 1
  integral : IsIntegral ℤ weight
  irrational : ∀ q : ℚ, (q:ℝ)≠weight
  high_mass : ∀ x∈high, (P x).toReal=scale
  low_mass : ∀ x∈low, (P x).toReal=scale*weight

private theorem levels_or_rational {P : PMF ℤ} (fin : P.support.Finite)
    (endpoint : EndpointWeights P) (two : AtMostTwo P) : Nonempty (Levels P) ∨ RationalRatios P := by
  classical
  obtain ⟨e,he,top,weights⟩ := endpoint
  let W := (P e).toReal
  have wpos : 0 < W := ENNReal.toReal_pos ((P.mem_support_iff _).mp he) (P.apply_ne_top _)
  by_cases flat : ∀ x∈P.support, (P x).toReal=W
  · right
    intro x y hy
    by_cases hx : x∈P.support
    · exact ⟨1,by rw [flat x hx,flat y hy,div_self wpos.ne']; simp⟩
    · exact ⟨0,by simp [(P.apply_eq_zero_iff _).mpr hx]⟩
  · push Not at flat
    obtain ⟨l,hl,ne⟩ := flat
    let u := (P l).toReal/W
    obtain ⟨_,ub,integral,rat⟩ := weights l
    have pos : 0 < u := div_pos (ENNReal.toReal_pos ((P.mem_support_iff _).mp hl) (P.apply_ne_top _)) wpos
    have ltone : u<1 := lt_of_le_of_ne ub (fun h => ne ((div_eq_one_iff_eq wpos.ne').mp h))
    obtain ⟨a,b,classes⟩ := two
    have dich (x) (hx : x∈P.support) : (P x).toReal=W ∨ (P x).toReal=(P l).toReal := by
      have c := classes x hx
      have d := classes l hl
      have f : W=a ∨ W=b := classes e he
      grind
    let G := fin.toFinset.filter fun x => (P x).toReal=W
    let H := fin.toFinset.filter fun x => (P x).toReal≠W
    have gmem {x} : x∈G ↔ x∈P.support ∧ (P x).toReal=W := by simp only [G,mem_filter,fin.mem_toFinset]
    have hmem {x} : x∈H ↔ x∈P.support ∧ (P x).toReal≠W := by simp only [H,mem_filter,fin.mem_toFinset]
    have ge : e∈G := gmem.mpr ⟨he,rfl⟩
    have gn : G.Nonempty := ⟨e,ge⟩
    have hn : H.Nonempty := ⟨l,hmem.mpr ⟨hl,ne⟩⟩
    have ltop := hmem.mp (H.max'_mem hn)
    have bound : H.max' hn < e := lt_of_le_of_ne (top _ ltop.1)
      (fun eq => ltop.2 (by rw [eq]))
    left
    refine ⟨⟨G,H,gn,hn,Finset.disjoint_left.mpr (fun _ hg hh => (hmem.mp hh).2 (gmem.mp hg).2),
      ?_,bound.trans_le (G.le_max' e ge),W,u,wpos,pos,ltone,integral,?_,
      fun _ hx => (gmem.mp hx).2,?_⟩⟩
    · ext x
      simp only [coe_union,Set.mem_union,mem_coe,gmem,hmem]; tauto
    · intro q eq
      exact (rat ⟨q,eq⟩).elim pos.ne' ltone.ne
    · intro x hx
      have e' := (dich x (hmem.mp hx).1).resolve_left (hmem.mp hx).2
      rw [e']; dsimp [u]; field_simp

private theorem Levels.normalization {P : PMF ℤ} (a : Levels P) :
    a.scale*(a.high.card+a.low.card*a.weight)=1 := by
  have off (x : ℤ) (hx : x∉a.high∪a.low) : P x=0 :=
    (P.apply_eq_zero_iff x).mpr (a.supp ▸ hx)
  have h := congrArg ENNReal.toReal P.tsum_coe
  rw [tsum_eq_sum off,ENNReal.toReal_sum (fun x _ => P.apply_ne_top x),sum_union a.disjoint,
    sum_eq_card_nsmul a.high_mass,sum_eq_card_nsmul a.low_mass,ENNReal.toReal_one] at h
  simp only [nsmul_eq_mul] at h
  linear_combination h

/-- Number of pairs of occupied sites of the specified classes with sum `z`. -/
def pairsAt (A B : Finset ℤ) (z : ℤ) : ℕ := (A.filter fun x => z-x∈B).card

private theorem count_above {A B : Finset ℤ} (ha : A.Nonempty) (hb : B.Nonempty)
    {z : ℤ} (gt : A.max' ha+B.max' hb<z) : pairsAt A B z=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨xa,xb⟩ := mem_filter.mp hx
  have := A.le_max' _ xa
  have := B.le_max' _ xb
  omega

private theorem count_at_top {A B : Finset ℤ} (ha : A.Nonempty) (hb : B.Nonempty) :
    pairsAt A B (A.max' ha+B.max' hb)=1 := by
  have eq : A.filter (fun x => A.max' ha+B.max' hb-x∈B)={A.max' ha} := by
    ext x
    simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨xa,xb⟩
      have := A.le_max' _ xa
      have := B.le_max' _ xb
      omega
    · rintro rfl
      exact ⟨A.max'_mem _,by simpa using B.max'_mem hb⟩
  simp [pairsAt,eq]

private theorem Levels.row_sum {Q : PMF ℤ} (b : Levels Q) (A : Finset ℤ) (z : ℤ) :
    ∑ x ∈ A, (Q (z-x)).toReal =
      (pairsAt A b.high z:ℝ)*b.scale + (pairsAt A b.low z:ℝ)*(b.scale*b.weight) := by
  have masses (y : ℤ) : (Q y).toReal=(if y∈b.high then b.scale else 0) +
      (if y∈b.low then b.scale*b.weight else 0) := by
    by_cases h : y∈b.high
    · have n := Finset.disjoint_left.mp b.disjoint h
      simp [h,n,b.high_mass _ h]
    · by_cases l : y∈b.low
      · simp [h,l,b.low_mass _ l]
      · have off := (Q.apply_eq_zero_iff y).mpr (show y∉Q.support by rw [b.supp]; simpa using And.intro h l)
        simp [h,l,off]
  simp only [masses,sum_add_distrib,sum_ite, sum_const_zero,add_zero,sum_const,nsmul_eq_mul,pairsAt]

private def layer {P Q : PMF ℤ} (a : Levels P) (b : Levels Q) (z : ℤ) : ℝ :=
  pairsAt a.high b.high z + pairsAt a.high b.low z*b.weight +
    pairsAt a.low b.high z*a.weight + pairsAt a.low b.low z*(a.weight*b.weight)

private theorem layer_mass {P Q : PMF ℤ} (a : Levels P) (b : Levels Q) (z : ℤ) :
    (indepSum P Q z).toReal = a.scale*b.scale * layer a b z := by
  classical
  have convolution : indepSum P Q z = ∑' x, P x * Q (z-x) := by
    change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z = _
    rw [PMF.bind_apply]
    congr 1
    funext x
    rw [PMF.bind_apply,tsum_eq_single (z-x)]
    · simp [PMF.pure_apply]
    · intro y hy
      simp [PMF.pure_apply,show z≠x+y by omega]
  have off (x : ℤ) (hx : x∉a.high∪a.low) : P x * Q (z-x)=0 := by
    rw [(P.apply_eq_zero_iff x).mpr (a.supp ▸ hx),zero_mul]
  rw [convolution,tsum_eq_sum off,ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top (P.apply_ne_top _) (Q.apply_ne_top _))]
  simp only [ENNReal.toReal_mul,sum_union a.disjoint]
  rw [sum_congr rfl (fun x hx => congrArg (·*(Q (z-x)).toReal) (a.high_mass _ hx)),
    sum_congr rfl (fun x hx => congrArg (·*(Q (z-x)).toReal) (a.low_mass _ hx)),
    ← mul_sum,← mul_sum,b.row_sum,b.row_sum]
  dsimp only [layer]
  ring

private theorem layer_top {P Q : PMF ℤ} (a : Levels P) (b : Levels Q) :
    layer a b (a.high.max' a.high_ne+b.high.max' b.high_ne)=1 := by
  have ap := a.beyond; have bp := b.beyond
  simp only [layer,count_at_top a.high_ne b.high_ne,
    count_above a.high_ne b.low_ne (by omega : a.high.max' a.high_ne+b.low.max' b.low_ne < a.high.max' a.high_ne+b.high.max' b.high_ne),
    count_above a.low_ne b.high_ne (by omega : a.low.max' a.low_ne+b.high.max' b.high_ne < a.high.max' a.high_ne+b.high.max' b.high_ne),
    count_above a.low_ne b.low_ne (by omega : a.low.max' a.low_ne+b.low.max' b.low_ne < a.high.max' a.high_ne+b.high.max' b.high_ne),
    Nat.cast_one,Nat.cast_zero,zero_mul,add_zero]

private theorem binary_layers {P Q : PMF ℤ} (a : Levels P) (b : Levels Q) (s : Finset ℤ)
    (hs : s.Nonempty) (eq : indepSum P Q=PMF.uniformOfFinset s hs) :
    (a.scale*b.scale)*(s.card:ℝ)=1 ∧ ∀ z, layer a b z=0 ∨ layer a b z=1 := by
  let z₀ := a.high.max' a.high_ne+b.high.max' b.high_ne
  have mass : ∀ z, (indepSum P Q z).toReal=0 ∨ (indepSum P Q z).toReal=(s.card:ℝ)⁻¹ := by
    intro z; rw [eq,PMF.uniformOfFinset_apply]
    split <;> simp
  have pos := mul_pos a.scale_pos b.scale_pos
  have one : a.scale*b.scale=(s.card:ℝ)⁻¹ := by
    have t := mass z₀
    rw [layer_mass a b,show layer a b z₀=1 from layer_top a b,mul_one] at t
    exact t.resolve_left pos.ne'
  refine ⟨by rw [one,inv_mul_cancel₀ (by exact_mod_cast (card_pos.mpr hs).ne')],?_⟩
  intro z; have t := mass z
  rw [layer_mass a b,←one] at t
  rcases t with h|h
  · exact Or.inl ((mul_eq_zero.mp h).resolve_left pos.ne')
  · exact Or.inr ((mul_right_inj' pos.ne').mp (h.trans (mul_one _).symm))

private theorem complementary {P Q : PMF ℤ} (a : Levels P) (b : Levels Q)
    (binary : ∀ z, layer a b z=0 ∨ layer a b z=1) : a.weight+b.weight=1 := by
  let l := a.low.max' a.low_ne+b.high.max' b.high_ne
  let r := a.high.max' a.high_ne+b.low.max' b.low_ne
  have ap := a.beyond; have bp := b.beyond
  have u := a.pos; have v := b.pos; have U := a.lt_one; have V := b.lt_one
  have no_fiber (z : ℤ) (hl : l≤z) : pairsAt a.low b.low z=0 :=
    count_above a.low_ne b.low_ne (by dsimp [l] at hl; omega)
  rcases lt_trichotomy l r with lr|lr|lr
  · have h := binary r
    have none : pairsAt a.low b.high r=0 := count_above a.low_ne b.high_ne lr
    simp only [layer,none,no_fiber r lr.le,show pairsAt a.high b.low r=1 from count_at_top _ _,
      Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at h
    let n := pairsAt a.high b.high r
    change (n:ℝ)+b.weight=0 ∨ (n:ℝ)+b.weight=1 at h
    by_cases e : n=0
    · rw [e,Nat.cast_zero,zero_add] at h; rcases h with h|h <;> linarith
    · have p : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr e
      rcases h with h|h <;> linarith
  · have h := binary l
    simp only [layer,no_fiber l le_rfl,show pairsAt a.low b.high l=1 from count_at_top _ _,
      show pairsAt a.high b.low l=1 from lr ▸ count_at_top _ _,Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at h
    let n := pairsAt a.high b.high l
    change (n:ℝ)+b.weight+a.weight=0 ∨ (n:ℝ)+b.weight+a.weight=1 at h
    have pos := Nat.cast_nonneg (α := ℝ) n
    by_cases e : n=0
    · rw [e,Nat.cast_zero,zero_add] at h; rcases h with h|h <;> linarith
    · have p : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr e
      rcases h with h|h <;> linarith
  · have h := binary l
    have none : pairsAt a.high b.low l=0 := count_above a.high_ne b.low_ne lr
    simp only [layer,none,no_fiber l le_rfl,show pairsAt a.low b.high l=1 from count_at_top _ _,
      Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero] at h
    let n := pairsAt a.high b.high l
    change (n:ℝ)+a.weight=0 ∨ (n:ℝ)+a.weight=1 at h
    by_cases e : n=0
    · rw [e,Nat.cast_zero,zero_add] at h; rcases h with h|h <;> linarith
    · have p : (1:ℝ)≤n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr e
      rcases h with h|h <;> linarith

private theorem unit_root {x : ℝ} (hx : 0 < x) (hX : x < 1) (m : ℕ)
    (eq : m*x+x*(1-x)=1) : 2 ≤ m ∧ x^2-(m+1)*x+1=0 := by
  have quad : x^2-(m+1)*x+1=0 := by nlinarith only [eq]
  refine ⟨?_,quad⟩
  by_contra! small
  have sa : (m:ℝ) ≤ 1 := by exact_mod_cast (by omega : m ≤ 1)
  nlinarith [mul_le_mul_of_nonneg_right sa hx.le,mul_self_pos.mpr (by linarith : 1-x≠0)]

/-- An irrational coefficient separates the rational constant and slope. -/
private theorem slope_zero {x : ℝ} (irr : ∀ q : ℚ, (q:ℝ)≠x) (a b : ℤ)
    (eq : (a:ℝ)*x=(b:ℝ)) : a=0 := by
  by_contra ne
  apply irr ((b:ℚ)/a)
  push_cast
  exact (div_eq_iff (by exact_mod_cast ne)).mpr (by linarith only [eq])

/-- Candidate smaller weight, together with the exact numbers of high and low
sites permitted on the two sides. The counts are ordered with the smaller weight first. -/
def Pattern (x : ℝ) (G H K L m : ℕ) : Prop :=
  x^2-(m+1)*x+1=0 ∧ H*K=G*L+m*H*L

private theorem pattern_of_total {x : ℝ} (irr : ∀ q : ℚ, (q:ℝ)≠x)
    {m G H K L S : ℕ} (quad : x^2-(m+1)*x+1=0)
    (total : (G+H*x)*(K+L*(1-x))=(S:ℝ)) : Pattern x G H K L m := by
  refine ⟨quad,?_⟩
  let a : ℤ := H*K-G*L-(m:ℤ)*H*L
  let b : ℤ := S-(G:ℤ)*K-G*L-H*L
  have e : (a:ℝ)*x=(b:ℝ) := by
    dsimp [a,b]; push_cast
    linear_combination total + (H:ℝ)*L*quad
  have zero := slope_zero irr a b e
  dsimp [a] at zero
  exact_mod_cast (show (H:ℤ)*K=G*L+(m:ℤ)*H*L by omega)

private theorem local_root {P Q : PMF ℤ} (a : Levels P) (b : Levels Q)
    (binary : ∀ z, layer a b z=0 ∨ layer a b z=1) (comp : a.weight+b.weight=1) :
    ∃ m : ℕ, 2 ≤ m ∧ (a.weight^2-(m+1)*a.weight+1=0 ∨ b.weight^2-(m+1)*b.weight+1=0) := by
  let z := a.low.max' a.low_ne+b.low.max' b.low_ne
  have one : pairsAt a.low b.low z=1 := count_at_top _ _
  let X := pairsAt a.low b.high z
  let Y := pairsAt a.high b.low z
  let D := pairsAt a.high b.high z
  have eq := binary z
  simp only [layer,one,Nat.cast_one,one_mul] at eq
  change (D:ℝ)+Y*b.weight+X*a.weight+a.weight*b.weight=0 ∨
    (D:ℝ)+Y*b.weight+X*a.weight+a.weight*b.weight=1 at eq
  have pos := mul_pos a.pos b.pos
  have yn := mul_nonneg (Nat.cast_nonneg Y) b.pos.le
  have xn := mul_nonneg (Nat.cast_nonneg X) a.pos.le
  have dn := Nat.cast_nonneg (α := ℝ) D
  have h := eq.resolve_left (by linarith)
  have zero : D=0 := by
    by_contra d
    have : (1:ℝ)≤D := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr d
    linarith
  rw [zero,Nat.cast_zero,zero_add] at h
  by_cases y : Y=0
  · have e : (X:ℝ)*a.weight+a.weight*(1-a.weight)=1 := by
      rw [y,Nat.cast_zero,zero_mul,zero_add] at h
      simpa only [show 1-a.weight=b.weight by linarith] using h
    obtain ⟨m,quad⟩ := unit_root a.pos a.lt_one X e
    exact ⟨X,m,Or.inl quad⟩
  · have y1 : (1:ℝ)≤Y := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr y
    have x0 : X=0 := by
      by_contra ne
      have x1 : (1:ℝ)≤X := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ne
      linarith [mul_le_mul_of_nonneg_right y1 b.pos.le,mul_le_mul_of_nonneg_right x1 a.pos.le]
    rw [x0,Nat.cast_zero,zero_mul,add_zero] at h
    have e : (Y:ℝ)*b.weight+b.weight*(1-b.weight)=1 := by
      simp only [show 1-b.weight=a.weight by linarith]
      linarith only [h]
    obtain ⟨m,quad⟩ := unit_root b.pos b.lt_one Y e
    exact ⟨Y,m,Or.inr quad⟩

/-- A nonuniform factorization with at most two positive weights per law has
complementary normalized lower weights. The smaller one is a quadratic unit, and
the ratio of high to low counts differs by the corresponding integer parameter. -/
theorem two_level_alternative {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (p : AtMostTwo P) (q : AtMostTwo Q) :
    (IsUniformOnSupport P ∧ IsUniformOnSupport Q) ∨
      ∃ (a : Levels P) (b : Levels Q) (m : ℕ), 2 ≤ m ∧ a.weight+b.weight=1 ∧
        (Pattern a.weight a.high.card a.low.card b.high.card b.low.card m ∨
         Pattern b.weight b.high.card b.low.card a.high.card a.low.card m) := by
  obtain ⟨pf,qf⟩ := finite_of_uniform_sum sum
  obtain ⟨pe,qe⟩ := endpoint_weights sum
  rcases levels_or_rational pf pe p with aa|r
  · obtain ⟨a⟩ := aa
    rcases levels_or_rational qf qe q with bb|r
    · obtain ⟨b⟩ := bb
      obtain ⟨s,hs,eq⟩ := sum
      obtain ⟨sc,binary⟩ := binary_layers a b s hs eq
      have comp := complementary a b binary
      obtain ⟨m,size,quad⟩ := local_root a b binary comp
      have total : ((a.high.card:ℝ)+a.low.card*a.weight)*(b.high.card+b.low.card*b.weight)=s.card := by
        apply mul_left_cancel₀ (mul_pos a.scale_pos b.scale_pos).ne'
        calc a.scale*b.scale*(_*_) =
              (a.scale*(a.high.card+a.low.card*a.weight))*(b.scale*(b.high.card+b.low.card*b.weight)) := by ring
             _ = a.scale*b.scale*s.card := by rw [a.normalization,b.normalization,sc,mul_one]
      right; refine ⟨a,b,m,size,comp,?_⟩
      rcases quad with ha|hb
      · exact Or.inl (pattern_of_total a.irrational (S := s.card) ha (by rwa [show 1-a.weight=b.weight by linarith]))
      · apply Or.inr (pattern_of_total b.irrational hb (S := s.card) ?_)
        rw [show 1-b.weight=a.weight by linarith,mul_comm]; exact total
    · exact Or.inl (uniform_of_rational_ratios sum (Or.inr r))
  · exact Or.inl (uniform_of_rational_ratios sum (Or.inl r))

private theorem no_prime_counts {p G H K L m : ℕ} (prime : p.Prime)
    (g : 0<G) (h : 0<H) (k : 0<K) (l : 0<L) (mpos : 0 < m)
    (left : G+H=p) (right : K+L=p) (identity : H*K=G*L+m*H*L) : False := by
  have balance : H*p=L*p+m*H*L := by
    calc H*p = H*(K+L) := by rw [right]
         _ = (G+H)*L+m*H*L := by rw [mul_add,identity]; ring
         _ = L*p+m*H*L := by rw [left,mul_comm p L]
  have dv : p ∣ m*H*L := (Nat.dvd_add_right (dvd_mul_left p L)).mp (balance ▸ dvd_mul_left p H)
  have nh : ¬p∣H := fun d => (by omega : H<p).not_ge (Nat.le_of_dvd h d)
  have nl : ¬p∣L := fun d => (by omega : L<p).not_ge (Nat.le_of_dvd l d)
  have dm : p∣m := (prime.dvd_mul.mp ((prime.dvd_mul.mp dv).resolve_right nl)).resolve_right nh
  have big := Nat.le_of_dvd mpos dm
  have bound : m*H ≤ H*K := by
    calc m*H ≤ m*H*L := Nat.le_mul_of_pos_right _ l
         _ ≤ G*L+m*H*L := Nat.le_add_left _ _
         _ = H*K := identity.symm
  rw [mul_comm m H] at bound
  have := Nat.le_of_mul_le_mul_left bound h
  omega

private theorem Levels.card {P : PMF ℤ} (a : Levels P) :
    a.high.card+a.low.card=P.support.ncard := by rw [a.supp,Set.ncard_coe_finset,card_union_of_disjoint a.disjoint]

/-- For any common prime number of atoms, two positive mass levels per marginal
already force both laws to be uniform, irrespective of the integer supports. -/
theorem uniform_of_equal_prime_sizes {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (twoP : AtMostTwo P) (twoQ : AtMostTwo Q) (prime : P.support.ncard.Prime)
    (same : Q.support.ncard=P.support.ncard) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  rcases two_level_alternative sum twoP twoQ with fair|bad
  · exact fair
  · obtain ⟨a,b,m,size,_,cases⟩ := bad
    have ag := card_pos.mpr a.high_ne
    have al := card_pos.mpr a.low_ne
    have bg := card_pos.mpr b.high_ne
    have bl := card_pos.mpr b.low_ne
    have bc := b.card.trans same
    rcases cases with ha|hb
    · exact (no_prime_counts prime ag al bg bl (by omega : 0 < m) a.card bc ha.2).elim
    · exact (no_prime_counts prime bg bl ag al (by omega : 0 < m) bc a.card hb.2).elim

/-- Every sum has one of three occupied fiber types when the smaller normalized
weight is on the left. This counts all four classes, including absent sums. -/
theorem fiber_counts {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (a : Levels P) (b : Levels Q) (m : ℕ) (comp : a.weight+b.weight=1)
    (quad : a.weight^2-(m+1)*a.weight+1=0) (z : ℤ) :
    pairsAt a.low b.high z = pairsAt a.high b.low z + m*pairsAt a.low b.low z ∧
    pairsAt a.high b.high z + pairsAt a.high b.low z + pairsAt a.low b.low z ≤ 1 := by
  obtain ⟨s,hs,eq⟩ := sum
  have h := (binary_layers a b s hs eq).2 z
  obtain ⟨e,le,he⟩ : ∃ e : ℕ, e ≤ 1 ∧ layer a b z=(e:ℝ) := by
    rcases h with h|h
    · exact ⟨0,by decide,by simpa using h⟩
    · exact ⟨1,by decide,by simpa using h⟩
  let X := pairsAt a.low b.high z
  let Y := pairsAt a.high b.low z
  let D := pairsAt a.high b.high z
  let C := pairsAt a.low b.low z
  change (D:ℝ)+Y*b.weight+X*a.weight+C*(a.weight*b.weight)=e at he
  rw [show b.weight=1-a.weight by linarith] at he
  have slope : (((X:ℤ)-Y-m*C:ℤ):ℝ)*a.weight=(((e:ℤ)-D-Y-C:ℤ):ℝ) := by
    push_cast
    linear_combination he + (C:ℝ)*quad
  have zero := slope_zero a.irrational _ _ slope
  change X=Y+m*C ∧ D+Y+C ≤ 1
  have xeq : X=Y+m*C := by
    exact_mod_cast (show (X:ℤ)=Y+(m:ℤ)*C by omega)
  rw [zero,Int.cast_zero,zero_mul] at slope
  have se : (e:ℤ)=(D:ℤ)+Y+C := by
    exact_mod_cast (show (e:ℝ)=(D:ℝ)+Y+C by push_cast at slope; linarith only [slope])
  exact ⟨xeq,by omega⟩

private theorem Levels.two_high {P Q : PMF ℤ} (a : Levels P)
    (sum : IsUniformOnSupport (indepSum P Q)) : 2 ≤ a.high.card := by
  classical
  let S := a.high∪a.low
  have sn : S.Nonempty := a.high_ne.mono subset_union_left
  let b := S.min' sn
  have bm : b ∈ S := S.min'_mem _
  have bottom {x} (hx : x ∈ P.support) : b ≤ x := S.min'_le _ (by rw [a.supp] at hx; exact hx)
  have bh : b ∈ a.high := by
    by_contra not_high
    have low := (mem_union.mp bm).resolve_left not_high
    let e := a.high.max' a.high_ne
    have lt : P b < P e := by
      apply (ENNReal.toReal_lt_toReal (P.apply_ne_top _) (P.apply_ne_top _)).mp
      rw [a.low_mass _ low,a.high_mass _ (a.high.max'_mem _)]
      nlinarith [mul_lt_mul_of_pos_left a.lt_one a.scale_pos]
    obtain ⟨t,ht,_,f,hf,total⟩ := Green28AverageObstruction.average_of_nonmax sum
      (a.supp ▸ bm) ⟨e,lt⟩
    have greater (i) (hi : i∈range t) : b < f i := by
      obtain ⟨mem,ne⟩ := hf i (mem_range.mp hi)
      exact lt_of_le_of_ne (bottom mem) ne.symm
    have h := sum_lt_sum_of_nonempty (show (range t).Nonempty from ⟨0,mem_range.mpr ht⟩) greater
    simp [total] at h
  have bound := bottom (x := a.low.max' a.low_ne) (a.supp ▸ mem_union_right _ (a.low.max'_mem _))
  have ne : b ≠ a.high.max' a.high_ne := (bound.trans_lt a.beyond).ne
  exact (one_lt_card.mpr ⟨b,bh,a.high.max' a.high_ne,a.high.max'_mem _,ne⟩)

private theorem oriented_sizes {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (a : Levels P) (b : Levels Q) (m : ℕ) (size : 2 ≤ m) (comp : a.weight+b.weight=1)
    (quad : a.weight^2-(m+1)*a.weight+1=0) :
    5 ≤ P.support.ncard ∧ 5 ≤ Q.support.ncard := by
  classical
  let h := a.low.max' a.low_ne
  let l := b.low.max' b.low_ne
  have hm : h∈a.low := a.low.max'_mem _
  have lm : l∈b.low := b.low.max'_mem _
  have enough (u v : ℤ) (hu : u∈a.low) (hv : v∈b.low) : m ≤ pairsAt a.low b.high (u+v) := by
    have non : 0<pairsAt a.low b.low (u+v) := card_pos.mpr
      ⟨u,mem_filter.mpr ⟨hu,by simpa only [add_sub_cancel_left] using hv⟩⟩
    have cnt := (fiber_counts sum a b m comp quad (u+v)).1
    have le := Nat.le_mul_of_pos_right m non
    omega
  have low_count : m+1 ≤ a.low.card := by
    let U := a.low.filter fun x => h+l-x∈b.high
    have subset : U ⊆ a.low.erase h := by
      intro x hx
      obtain ⟨mem,high⟩ := mem_filter.mp hx
      apply mem_erase.mpr
      refine ⟨?_,mem⟩
      rintro rfl
      apply disjoint_left.mp b.disjoint (by simpa using high) lm
    have bound := card_le_card subset
    rw [card_erase_of_mem hm] at bound
    have le : m ≤ U.card := enough h l hm lm
    omega
  let lo := b.high.filter fun y => y < b.low.min' b.low_ne
  let hi := b.high.filter fun y => b.low.max' b.low_ne < y
  have pack (u v : ℤ) (hu : u∈a.low) (hv : v∈b.low) (C : Finset ℤ)
      (put : ∀ x∈a.low, u+v-x∈b.high → u+v-x∈C) : m ≤ C.card := by
    refine (enough u v hu hv).trans ?_
    apply card_le_card_of_injOn (fun x => u+v-x)
    · intro x hx; obtain ⟨xm,high⟩ := mem_filter.mp hx; exact put x xm high
    · intro x _ y _ e; dsimp only at e; omega
  have toplo : ∀ x∈a.low, h+l-x∈b.high → h+l-x∈hi := by
    intro x hx high
    have le := a.low.le_max' x hx
    have ne : h+l-x≠l := fun eq => disjoint_left.mp b.disjoint high (by rwa [eq])
    exact mem_filter.mpr ⟨high,by change l < h+l-x; change x ≤ h at le; omega⟩
  have bound_hi := pack h l hm lm hi toplo
  let h' := a.low.min' a.low_ne
  let l' := b.low.min' b.low_ne
  have hm' : h'∈a.low := a.low.min'_mem _
  have lm' : l'∈b.low := b.low.min'_mem _
  have bound_lo := pack h' l' hm' lm' lo (by
    intro x hx high
    have le : h' ≤ x := a.low.min'_le x hx
    have ne : h'+l'-x≠l' := fun eq => disjoint_left.mp b.disjoint high (by rwa [eq])
    exact mem_filter.mpr ⟨high,by change h'+l'-x < l'; omega⟩)
  have separation : Disjoint lo hi := disjoint_left.mpr (by
    intro y yl yh
    have one := (mem_filter.mp yl).2
    have two := (mem_filter.mp yh).2
    have mid := b.low.min'_le _ lm
    change b.low.min' b.low_ne ≤ b.low.max' b.low_ne at mid
    omega)
  have sub : lo∪hi ⊆ b.high := union_subset (filter_subset _ _) (filter_subset _ _)
  have both := card_le_card sub
  rw [card_union_of_disjoint separation] at both
  have high_count := a.two_high sum
  have ps := a.card
  have qs := b.card
  have bl := card_pos.mpr b.low_ne
  omega

/-- One marginal with four atoms suffices, with arbitrary support on the other
side, when each law uses at most two distinct positive atom probabilities. -/
theorem uniform_of_one_small_support {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (twoP : AtMostTwo P) (twoQ : AtMostTwo Q) (size : P.support.ncard ≤ 4 ∨ Q.support.ncard ≤ 4) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  rcases two_level_alternative sum twoP twoQ with fair|bad
  · exact fair
  · obtain ⟨a,b,m,hm,comp,pat⟩ := bad
    rcases pat with p|p
    · have := oriented_sizes sum a b m hm comp p.1
      omega
    · have swap : indepSum Q P=indepSum P Q := by
        unfold indepSum
        change Q.bind (fun y => P.bind fun x => PMF.pure (y+x)) = _
        rw [PMF.bind_comm]; simp only [add_comm]; rfl
      have := oriented_sizes (swap ▸ sum) b a m hm (by linarith) p.1
      omega

#print axioms two_level_alternative
#print axioms uniform_of_equal_prime_sizes
#print axioms fiber_counts
#print axioms uniform_of_one_small_support

end Green28TwoMassLevels
