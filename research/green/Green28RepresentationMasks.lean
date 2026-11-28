import Green28UnpairedSites
import Mathlib.Data.ZMod.Basic

/-! Representation counts modulo a prime and support masks of integer sums. -/

namespace Green28RepresentationMasks

open Finset Polynomial
open scoped Polynomial

/-- The support mask over the indicated coefficient ring. -/
noncomputable def mask (R : Type*) [Semiring R] (A : Finset ℕ) : R[X] := ∑ a ∈ A, X^a

/-- Pairs of occupied offsets with a prescribed sum. -/
def fibre (A B : Finset ℕ) (n : ℕ) : Finset (ℕ×ℕ) :=
  (A×ˢB).filter fun z => z.1+z.2 = n

theorem coeff_mask (R : Type*) [Semiring R] (A : Finset ℕ) (i : ℕ) :
    (mask R A).coeff i = if i ∈ A then 1 else 0 := by
  classical
  simp [mask,finsetSum_coeff,coeff_X_pow]

/-- Mask multiplication records the full representation counts, including
both orders when they are distinct pairs of the two input supports. -/
theorem mask_mul_coeff (R : Type*) [CommSemiring R] (A B : Finset ℕ) (n : ℕ) :
    (mask R A*mask R B).coeff n = ((fibre A B n).card:R) := by
  classical
  have prod : mask R A*mask R B = ∑ x ∈ A×ˢB, (X:R[X])^(x.1+x.2) := by
    simp only [mask,sum_product,sum_mul,mul_sum,pow_add]
    rw [sum_comm]
  rw [prod,finsetSum_coeff]
  simp only [coeff_X_pow]
  simp only [fibre,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply sum_congr rfl
  intro x _
  simp [eq_comm]

private theorem mask_monic {R : Type*} [Semiring R] [Nontrivial R] {A : Finset ℕ}
    {d : ℕ} (top : d ∈ A) (le : ∀ a ∈ A, a ≤ d) : (mask R A).natDegree = d ∧ (mask R A).Monic := by
  have hi : (mask R A).natDegree ≤ d := natDegree_le_iff_coeff_eq_zero.mpr (fun i h => by
    simp [coeff_mask,show i ∉ A from fun mem => (le i mem).not_gt h])
  have cd : (mask R A).coeff d = 1 := by simp [coeff_mask,top]
  have eq := le_antisymm hi (le_natDegree_of_ne_zero (cd ▸ one_ne_zero))
  exact ⟨eq,by rwa [Monic,leadingCoeff,eq]⟩

private theorem mask_injective (R : Type*) [Semiring R] [Nontrivial R] :
    Function.Injective (mask R) := by
  intro A B eq
  ext i
  have e := congrArg (fun P : R[X] => P.coeff i) eq
  rw [coeff_mask,coeff_mask] at e
  by_cases a : i ∈ A <;> by_cases b : i ∈ B <;> simp_all

private theorem mem_fibre {A B : Finset ℕ} {n : ℕ} {x : ℕ×ℕ} :
    x ∈ fibre A B n ↔ x.1 ∈ A ∧ x.2 ∈ B ∧ x.1+x.2 = n := by
  simp [fibre,and_assoc]

private theorem unique_iff_card {A B : Finset ℕ} {x y : ℕ} (hx : x ∈ A) (hy : y ∈ B) :
    (fibre A B (x+y)).card = 1 ↔
      ∀ i ∈ A, ∀ j ∈ B, x+y = i+j → x = i ∧ y = j := by
  have mem : (x,y) ∈ fibre A B (x+y) := mem_fibre.mpr ⟨hx,hy,rfl⟩
  constructor
  · intro one i hi j hj eq
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp one
    have mem' : (i,j) ∈ fibre A B (x+y) := mem_fibre.mpr ⟨hi,hj,eq.symm⟩
    rw [ht,mem_singleton] at mem mem'
    exact ⟨congrArg Prod.fst (mem.trans mem'.symm),congrArg Prod.snd (mem.trans mem'.symm)⟩
  · intro un
    refine Finset.card_eq_one.mpr ⟨(x,y),?_⟩
    ext ⟨i,j⟩
    constructor
    · intro m
      obtain ⟨hi,hj,e⟩ := mem_fibre.mp m
      obtain ⟨rfl,rfl⟩ := un i hi j hj e.symm
      exact mem_singleton_self _
    · intro m; rwa [mem_singleton.mp m]

/-- When all nonsingle fibre sizes are multiples of the modulus, the
product of the support masks reduces to the singleton rectangle. -/
theorem product_of_multiplicities {p : ℕ} {A B H K : Finset ℕ} (hs : H ⊆ A) (ks : K ⊆ B)
    (rect : ∀ x ∈ A, ∀ y ∈ B, (fibre A B (x+y)).card = 1 ↔ x ∈ H ∧ y ∈ K)
    (mult : ∀ n, (fibre A B n).card ≠ 1 → p ∣ (fibre A B n).card) :
    mask (ZMod p) A*mask (ZMod p) B = mask (ZMod p) H*mask (ZMod p) K := by
  ext n
  rw [mask_mul_coeff,mask_mul_coeff]
  by_cases one : (fibre A B n).card = 1
  · suffices same : fibre A B n = fibre H K n by rw [same]
    ext ⟨x,y⟩
    simp only [mem_fibre]
    constructor
    · rintro ⟨hx,hy,e⟩
      obtain ⟨a,b⟩ := (rect x hx y hy).mp (e ▸ one)
      exact ⟨a,b,e⟩
    · rintro ⟨hx,hy,e⟩; exact ⟨hs hx,ks hy,e⟩
  · have empty : fibre H K n = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro ⟨x,y⟩ mem
      obtain ⟨a,b,e⟩ := mem_fibre.mp mem
      exact one (e ▸ (rect x (hs a) y (ks b)).mpr ⟨a,b⟩)
    simpa [empty] using (ZMod.natCast_eq_zero_iff _ _).mpr (mult n one)

open Green28 Green28UniformSums Green28UnpairedSites

/-- Occupied integer sites written as offsets from their minimum. -/
structure Offsets (P : PMF ℤ) (a : ℤ) (A : Finset ℕ) : Prop where
  zero : 0 ∈ A
  support : ∀ z : ℤ, z ∈ P.support ↔ ∃ i ∈ A, z = a+(i:ℤ)

private theorem Offsets.occupied {P : PMF ℤ} {a : ℤ} {A : Finset ℕ}
    (h : Offsets P a A) {i : ℕ} (hi : i ∈ A) : a+(i:ℤ) ∈ P.support :=
  (h.support _).mpr ⟨i,hi,rfl⟩

private def Offsets.ends {P : PMF ℤ} {a : ℤ} {A : Finset ℕ}
    (h : Offsets P a A) {d : ℕ} (top : d ∈ A) (le : ∀ i ∈ A, i ≤ d) : Extremes P.support where
  lo := a
  hi := a+(d:ℤ)
  least := ⟨by simpa using h.occupied h.zero, by
    intro z hz; obtain ⟨i,_,rfl⟩ := (h.support z).mp hz; omega⟩
  greatest := ⟨h.occupied top,by
    intro z hz; obtain ⟨i,hi,rfl⟩ := (h.support z).mp hz; have := le i hi; omega⟩

private theorem shift_unique {P Q : PMF ℤ} {A B : Finset ℕ} {a b : ℤ}
    (pa : Offsets P a A) (qb : Offsets Q b B) {i j : ℕ} (hi : i ∈ A) (hj : j ∈ B) :
    (fibre A B (i+j)).card = 1 ↔
    ∀ u ∈ P.support, ∀ v ∈ Q.support, (a+i)+(b+j) = u+v → a+i = u ∧ b+j = v := by
  rw [unique_iff_card hi hj]
  constructor
  · intro un u hu v hv e
    obtain ⟨k,hk,rfl⟩ := (pa.support _).mp hu
    obtain ⟨l,hl,rfl⟩ := (qb.support _).mp hv
    obtain ⟨rfl,rfl⟩ := un k hk l hl (by omega)
    exact ⟨rfl,rfl⟩
  · intro un k hk l hl e
    obtain ⟨x,y⟩ := un _ (pa.occupied hk) _ (qb.occupied hl) (by omega)
    exact ⟨by omega,by omega⟩

/-- Columns whose pair with the least row has a unique sum. -/
def singleColumns (A B : Finset ℕ) : Finset ℕ := B.filter fun j => (fibre A B j).card = 1

/-- A coprimality test using only the two supports and their representation
counts. The second mask is computed from singleton sums along the least row. -/
theorem uniform_of_coprime_column_mask {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {A B : Finset ℕ} {a b : ℤ} (pa : Offsets P a A) (qb : Offsets Q b B)
    {p : ℕ} [Fact p.Prime]
    (cop : IsCoprime (mask (ZMod p) A) (mask (ZMod p) (singleColumns A B)))
    (mult : ∀ n, (fibre A B n).card ≠ 1 → p ∣ (fibre A B n).card) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  classical
  let d := A.max' ⟨0,pa.zero⟩
  let e := B.max' ⟨0,qb.zero⟩
  have dt : d ∈ A := max'_mem _ _
  have et : e ∈ B := max'_mem _ _
  have da : ∀ i ∈ A, i ≤ d := fun i hi => le_max' A i hi
  have eb : ∀ i ∈ B, i ≤ e := fun i hi => le_max' B i hi
  obtain ⟨hp,hq,un⟩ := maximal_rectangle flat (pa.ends dt da) (qb.ends et eb)
  let H := A.filter fun i : ℕ => (P (a+(i:ℤ))).toReal = (P a).toReal
  let K := B.filter fun j : ℕ => (Q (b+(j:ℤ))).toReal = (Q b).toReal
  have hs : H ⊆ A := filter_subset _ _
  have ks : K ⊆ B := filter_subset _ _
  have rect (i) (hi : i ∈ A) (j) (hj : j ∈ B) :
      (fibre A B (i+j)).card = 1 ↔ i ∈ H ∧ j ∈ K := by
    rw [shift_unique pa qb hi hj,un _ (pa.occupied hi) _ (qb.occupied hj)]
    simp [H,K,hi,hj,Offsets.ends]
  have eq := product_of_multiplicities hs ks rect mult
  have columns : singleColumns A B = K := by
    have zero : 0 ∈ H := mem_filter.mpr ⟨pa.zero,by simp⟩
    ext j
    by_cases live : j ∈ B
    · simpa [singleColumns,live,zero] using (rect 0 pa.zero j live)
    · simp [singleColumns,K,live]
  rw [columns] at cop
  have adiv : mask (ZMod p) A ∣ mask (ZMod p) H*mask (ZMod p) K := ⟨mask _ B,eq.symm⟩
  obtain ⟨ad,am⟩ := mask_monic (R:=ZMod p) dt da
  obtain ⟨hd,hm⟩ := mask_monic (R:=ZMod p) (mem_filter.mpr ⟨dt,hp⟩ : d ∈ H) (fun i hi => da i (hs hi))
  have full : H = A := mask_injective (ZMod p)
    (eq_of_monic_of_dvd_of_natDegree_le am hm (cop.dvd_of_dvd_mul_right adiv) (hd.trans ad.symm).le)
  have const (z : ℤ) (hz : z ∈ P.support) : (P z).toReal = (P a).toReal := by
    obtain ⟨i,hi,rfl⟩ := (pa.support _).mp hz
    have m : i ∈ H := full ▸ hi
    exact (mem_filter.mp m).2
  apply uniform_of_rational_ratios flat
  left
  intro x y hy
  by_cases hx : x ∈ P.support
  · have pos := ENNReal.toReal_pos ((P.mem_support_iff _).mp hy) (P.apply_ne_top _)
    have he := (const x hx).trans (const y hy).symm
    exact ⟨1,by rw [he,div_self pos.ne']; simp⟩
  · exact ⟨0,by simp [(P.apply_eq_zero_iff _).mpr hx]⟩

/-- A wider irreducible support mask over the prime field guarantees
uniformity when every non-singleton representation count is divisible
by the characteristic. The hypotheses involve only the two supports. -/
theorem uniform_of_irreducible_mask {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {A B : Finset ℕ} {a b : ℤ} (pa : Offsets P a A) (qb : Offsets Q b B)
    {p : ℕ} [Fact p.Prime] (irr : Irreducible (mask (ZMod p) A))
    (width : B.max' ⟨0,qb.zero⟩<A.max' ⟨0,pa.zero⟩)
    (mult : ∀ n, (fibre A B n).card ≠ 1 → p ∣ (fibre A B n).card) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply uniform_of_coprime_column_mask flat pa qb (p:=p) ?_ mult
  apply (irr.isCoprime_or_dvd _).resolve_right
  intro dvd
  let K := singleColumns A B
  have origin : (fibre A B 0).card = 1 := by
    simpa only [Nat.zero_add] using (unique_iff_card pa.zero qb.zero).mpr
      (fun i _ j _ eq => ⟨by omega,by omega⟩)
  have kz : 0 ∈ K := mem_filter.mpr ⟨qb.zero,origin⟩
  have kn : mask (ZMod p) K ≠ 0 := by
    intro z
    have c := congrArg (fun f : (ZMod p)[X] => f.coeff 0) z
    simp [coeff_mask,kz] at c
  have bound := natDegree_le_of_dvd dvd kn
  obtain ⟨ad,_⟩ := mask_monic (R:=ZMod p) (A.max'_mem ⟨0,pa.zero⟩) (fun i hi => A.le_max' i hi)
  have kd : (mask (ZMod p) K).natDegree ≤ B.max' ⟨0,qb.zero⟩ := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    have absent : i ∉ K := fun m => hi.not_ge (B.le_max' i (mem_filter.mp m).1)
    simp [coeff_mask,absent]
  exact width.not_ge (ad ▸ (bound.trans kd))

/-- In characteristic two a failure therefore has a total with at least
three representations and odd multiplicity. -/
theorem exists_odd_fibre {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {A B : Finset ℕ} {a b : ℤ} (pa : Offsets P a A) (qb : Offsets Q b B)
    (irr : Irreducible (mask (ZMod 2) A))
    (width : B.max' ⟨0,qb.zero⟩<A.max' ⟨0,pa.zero⟩)
    (bad : ¬(IsUniformOnSupport P ∧ IsUniformOnSupport Q)) :
    ∃ n : ℕ, 3 ≤ (fibre A B n).card ∧ Odd (fibre A B n).card := by
  by_contra! no
  apply bad (uniform_of_irreducible_mask flat pa qb irr width ?_)
  intro n ne
  by_contra odd
  have h : Odd (fibre A B n).card := Nat.not_even_iff_odd.mp (fun ev => odd (even_iff_two_dvd.mp ev))
  apply no n _ h
  obtain ⟨i,hi⟩ := h
  omega

/-- An odd number of rows and just two singleton columns in the least row,
separated by a power of two, force uniformity if nonsingle fibres are even. -/
theorem uniform_of_two_single_columns {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    {A B : Finset ℕ} {a b : ℤ} (pa : Offsets P a A) (qb : Offsets Q b B)
    (odd : Odd A.card) (k : ℕ) (single : singleColumns A B = {0,2^k})
    (mult : ∀ n, (fibre A B n).card ≠ 1 → 2 ∣ (fibre A B n).card) :
    IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  apply uniform_of_coprime_column_mask flat pa qb (p:=2) ?_ mult
  let F := mask (ZMod 2) A
  have val : F.eval 1 ≠0 := by
    have e : F.eval 1 = (A.card:ZMod 2) := by simp [F,mask,eval_finsetSum]
    rw [e]
    exact fun z => odd.not_two_dvd_nat ((ZMod.natCast_eq_zero_iff _ _).mp z)
  have cop : IsCoprime F (X-C (1:ZMod 2)) := by
    apply IsCoprime.symm
    apply ((irreducible_X_sub_C (1:ZMod 2)).isCoprime_or_dvd _).resolve_right
    exact fun dvd => val (dvd_iff_isRoot.mp dvd)
  have ez : (0:ℕ) ≠ 2^k := (pow_pos (by decide : 0<(2:ℕ)) k).ne
  have shape : mask (ZMod 2) (singleColumns A B) = (X-C (1:ZMod 2))^(2^k) := by
    rw [single,sub_eq_add_neg,CharTwo.neg_eq,add_pow_char_pow _ _ 2 k]
    simp [mask,ez,add_comm]
  rw [shape]
  exact cop.pow_right

#print axioms coeff_mask
#print axioms mask_mul_coeff
#print axioms product_of_multiplicities
#print axioms uniform_of_irreducible_mask
#print axioms exists_odd_fibre
#print axioms uniform_of_coprime_column_mask
#print axioms uniform_of_two_single_columns
end Green28RepresentationMasks
