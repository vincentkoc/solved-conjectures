import Green28FiveSiteCertificate
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Restricting a uniform independent sum to a union of complete representation fibers. -/

namespace Green28IsolatedTables

open Green28 Green28UniformSums Finset
open scoped ENNReal

/-- If one representation uses a selected row, all representations do. -/
def ClosedRows (P Q : PMF ℤ) (S : Set ℤ) : Prop :=
  ∀ a ∈ S, a ∈ P.support → ∀ b ∈ Q.support, ∀ x ∈ P.support, ∀ y ∈ Q.support,
    a + b = x + y → x ∈ S

private theorem occupied {P Q : PMF ℤ} {z : ℤ} :
    z ∈ (indepSum P Q).support ↔ ∃ x ∈ P.support, ∃ y ∈ Q.support, x+y=z := by
  simp only [indepSum, Bind.bind, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, eq_comm]

private theorem sum_apply (P Q : PMF ℤ) (z : ℤ) :
    indepSum P Q z = ∑' x, P x * Q (z-x) := by
  change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z = _
  rw [PMF.bind_apply]
  congr 1
  funext x
  rw [PMF.bind_apply, tsum_eq_single (z-x)]
  · simp [PMF.pure_apply]
  · intro y hy
    have h : z ≠ x+y := by omega
    simp [PMF.pure_apply,h]

private theorem uniform_of_constant {P : PMF ℤ} (finite : P.support.Finite) (v : ℝ≥0∞)
    (flat : ∀ x ∈ P.support, P x = v) : IsUniformOnSupport P := by
  classical
  let S := finite.toFinset
  have ne := finite.toFinset_nonempty.mpr P.support_nonempty
  have off (x : ℤ) (hx : x ∉ S) : P x = 0 :=
    (P.apply_eq_zero_iff _).mpr (fun h => hx (finite.mem_toFinset.mpr h))
  have total := congrArg ENNReal.toReal P.tsum_coe
  have eq (x : ℤ) (hx : x ∈ S) : (P x).toReal = v.toReal :=
    congrArg ENNReal.toReal (flat _ (finite.mem_toFinset.mp hx))
  rw [tsum_eq_sum off, ENNReal.toReal_sum (fun x _ => P.apply_ne_top x),
    sum_eq_card_nsmul eq, nsmul_eq_mul, ENNReal.toReal_one] at total
  refine ⟨S,ne,PMF.ext fun x => ?_⟩
  by_cases hx : x ∈ S
  · rw [PMF.uniformOfFinset_apply_of_mem ne hx]
    apply (ENNReal.toReal_eq_toReal_iff' (P.apply_ne_top _) (by simp [ne.card_ne_zero])).mp
    rw [eq _ hx,ENNReal.toReal_inv,ENNReal.toReal_natCast]
    exact (eq_inv_of_mul_eq_one_right total)
  · rw [off _ hx,PMF.uniformOfFinset_apply_of_notMem ne hx]

/-- Conditioning one input on closed rows preserves uniformity of the sum. -/
theorem restrict_left {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    {S : Set ℤ} (h : ∃ x ∈ S, x ∈ P.support) (closed : ClosedRows P Q S) :
    IsUniformOnSupport (indepSum (P.filter S h) Q) := by
  classical
  obtain ⟨V,ne,law⟩ := uniform
  have sub : (indepSum (P.filter S h) Q).support ⊆ (indepSum P Q).support := by
    intro z hz
    obtain ⟨x,hx,y,hy,e⟩ := occupied.mp hz
    exact occupied.mpr ⟨x,((PMF.mem_support_filter_iff h).mp hx).2,y,hy,e⟩
  have finite : (indepSum P Q).support.Finite := by rw [law,PMF.support_uniformOfFinset]; exact V.finite_toSet
  let t := (∑' x, (S.indicator P) x)⁻¹
  apply uniform_of_constant (finite.subset sub) ((V.card : ℝ≥0∞)⁻¹*t)
  intro z hz
  obtain ⟨a,ha,b,hb,e⟩ := occupied.mp hz
  obtain ⟨as,ap⟩ := (PMF.mem_support_filter_iff h).mp ha
  have mem := sub hz
  rw [law,PMF.support_uniformOfFinset] at mem
  have v : indepSum P Q z = (V.card : ℝ≥0∞)⁻¹ := by rw [law,PMF.uniformOfFinset_apply_of_mem ne mem]
  rw [←v,sum_apply,sum_apply,←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x
  rw [PMF.filter_apply]
  by_cases xs : x ∈ S
  · rw [Set.indicator_of_mem xs]; dsimp only [t]; ring
  · rw [Set.indicator_of_notMem xs,zero_mul,zero_mul]
    by_cases xp : x ∈ P.support
    · have bad : z-x ∉ Q.support := fun y => xs (closed a as ap b hb x xp (z-x) y (by omega))
      rw [(Q.apply_eq_zero_iff _).mpr bad,mul_zero,zero_mul]
    · rw [(P.apply_eq_zero_iff _).mpr xp,zero_mul,zero_mul]

private theorem swap (P Q : PMF ℤ) : indepSum P Q = indepSum Q P := by
  change (P.bind fun x => Q.bind fun y => PMF.pure (x+y)) = _
  rw [PMF.bind_comm]
  simp only [indepSum, Bind.bind, add_comm]

private theorem ratios {P : PMF ℤ} (flat : IsUniformOnSupport P) : RationalRatios P := by
  obtain ⟨S,ne,rfl⟩ := flat
  intro x y hy
  have ys := (PMF.mem_support_uniformOfFinset_iff ne _).mp hy
  rw [PMF.uniformOfFinset_apply_of_mem ne ys]
  by_cases xs : x ∈ S
  · rw [PMF.uniformOfFinset_apply_of_mem ne xs]
    exact ⟨1,by simp [ne.card_ne_zero]⟩
  · exact ⟨0,by simp [PMF.uniformOfFinset_apply_of_notMem ne xs]⟩

/-- A fair restricted law on either side of an isolated rectangle forces the
original two laws to be fair. The other components can have arbitrary sizes. -/
theorem rectangle_transfer {P Q : PMF ℤ} (uniform : IsUniformOnSupport (indepSum P Q))
    {S T : Set ℤ} (hs : ∃ x ∈ S, x ∈ P.support) (ht : ∃ y ∈ T, y ∈ Q.support)
    (rows : ClosedRows P Q S) (cols : ClosedRows Q P T)
    (test : IsUniformOnSupport (indepSum (P.filter S hs) (Q.filter T ht)) →
      IsUniformOnSupport (P.filter S hs) ∨ IsUniformOnSupport (Q.filter T ht)) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  have left := restrict_left uniform hs rows
  have right := restrict_left (swap P Q ▸ uniform) ht cols
  have cols' : ClosedRows Q (P.filter S hs) T := by
    intro a ha hq b hb x hx y hy eq
    exact cols a ha hq b ((PMF.mem_support_filter_iff hs).mp hb).2 x hx y
      ((PMF.mem_support_filter_iff hs).mp hy).2 eq
  have small := restrict_left (swap (P.filter S hs) Q ▸ left) ht cols'
  rcases test (swap (Q.filter T ht) (P.filter S hs) ▸ small) with f|g
  · have fq := (uniform_of_rational_ratios left (Or.inl (ratios f))).2
    exact uniform_of_rational_ratios uniform (Or.inr (ratios fq))
  · have fp := (uniform_of_rational_ratios right (Or.inl (ratios g))).2
    exact uniform_of_rational_ratios uniform (Or.inl (ratios fp))

/-- The rows cannot be split into two nonempty sets with disjoint sumsets
against the opposite support. Equivalently, the common-sum graph is connected. -/
def CollisionConnected (P Q : PMF ℤ) : Prop :=
  ∀ S ⊆ P.support, S.Nonempty → ClosedRows P Q S → S = P.support

/-- Green 28 in its pinned form is equivalent to testing pairs in which the
occupied rows and occupied columns are each connected by common sums. -/
theorem connected_iff :
    (∀ P Q : PMF ℤ, P.support.Finite ∧ Q.support.Finite ∧ IsUniformOnSupport (indepSum P Q) →
      IsUniformOnSupport P ∧ IsUniformOnSupport Q) ↔
    (∀ P Q : PMF ℤ, CollisionConnected P Q → CollisionConnected Q P →
      IsUniformOnSupport (indepSum P Q) → IsUniformOnSupport P ∧ IsUniformOnSupport Q) := by
  classical
  constructor
  · intro test P Q _ _ uniform
    obtain ⟨pf,qf⟩ := finite_of_uniform_sum uniform
    exact test _ _ ⟨pf,qf,uniform⟩
  intro test
  have prove (n : ℕ) : ∀ P Q : PMF ℤ, IsUniformOnSupport (indepSum P Q) →
      P.support.ncard+Q.support.ncard = n → IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P Q sum size
      have smaller (U V : PMF ℤ) (su : IsUniformOnSupport (indepSum U V))
          (size' : U.support.ncard+V.support.ncard=n) (split : ¬CollisionConnected U V) :
          IsUniformOnSupport U ∧ IsUniformOnSupport V := by
        unfold CollisionConnected at split
        push Not at split
        obtain ⟨S,sub,ne,closed,proper⟩ := split
        obtain ⟨x,hx⟩ := ne
        have live : ∃ a ∈ S, a ∈ U.support := ⟨x,hx,sub hx⟩
        let R := U.filter S live
        have support : R.support=S := (PMF.support_filter live).trans (Set.inter_eq_left.mpr sub)
        have less := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨sub,proper⟩)
          (finite_of_uniform_sum su).1
        have strict : R.support.ncard+V.support.ncard < n := by rw [support]; omega
        have both := ih _ strict R V (restrict_left su live closed) rfl
        exact uniform_of_rational_ratios su (Or.inr (ratios both.2))
      by_cases rows : CollisionConnected P Q
      · by_cases cols : CollisionConnected Q P
        · exact test _ _ rows cols sum
        · exact (smaller Q P (swap P Q ▸ sum) (by omega) cols).symm
      · exact smaller P Q sum size rows
  rintro P Q ⟨_,_,u⟩
  exact prove _ P Q u rfl

/-- A nonempty isolated set of at most five rows and an independently isolated
set of at most five columns suffice. Each is tested against the full opposite law. -/
theorem uniform_of_five_site_pieces {P Q : PMF ℤ} (sum : IsUniformOnSupport (indepSum P Q))
    (S T : Finset ℤ) (sn : S.Nonempty) (tn : T.Nonempty)
    (sp : (S : Set ℤ) ⊆ P.support) (tq : (T : Set ℤ) ⊆ Q.support)
    (rows : ClosedRows P Q S) (cols : ClosedRows Q P T)
    (sc : S.card ≤ 5) (tc : T.card ≤ 5) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨x,hx⟩ := sn
  obtain ⟨y,hy⟩ := tn
  apply rectangle_transfer sum ⟨x,hx,sp hx⟩ ⟨y,hy,tq hy⟩ rows cols
  intro flat
  apply Or.inl
  apply (Green28FiveSiteCertificate.uniform_of_at_most_five_atoms flat ?_ ?_).1
  · simpa [PMF.support_filter,Set.inter_eq_left.mpr sp] using sc
  · simpa [PMF.support_filter,Set.inter_eq_left.mpr tq] using tc

#print axioms uniform_of_five_site_pieces
#print axioms connected_iff
#print axioms restrict_left
#print axioms rectangle_transfer

end Green28IsolatedTables
