import Green28RootLocation
import Green28UnpairedSites

/-! Reflected prefixes of a uniform output and of its two original marginals. -/

namespace Green28ReflectedPrefix

open Polynomial Finset Green28PolynomialReduction Green28RootLocation
open scoped Polynomial

/-- Agreement with the reversal at every offset strictly below the cutoff. -/
def Matches (f : ℝ[X]) (t : ℕ) : Prop :=
  ∀ i < t, f.coeff i = f.reverse.coeff i

private theorem first_mul_coeff (a b : ℝ[X]) (n : ℕ) (prior : ∀ j < n, a.coeff j = 0) :
    (a*b).coeff n = a.coeff n*b.coeff 0 := by
  rw [coeff_mul,Finset.sum_eq_single_of_mem (n,0) (mem_antidiagonal.mpr (Nat.add_zero n))]
  rintro ⟨i,j⟩ hij neq
  have eq : i+j = n := mem_antidiagonal.mp hij
  have lt : i < n := by
    by_contra! h
    exact neq (Prod.ext (by change i = n; omega) (by change j = 0; omega))
  simp [prior i lt]

private theorem difference_at (f g : ℝ[X]) (fm : f.Monic) (gc : g.coeff 0 = 1) (n : ℕ)
    (before : ∀ i < n, f.coeff i = f.reverse.coeff i ∧ g.coeff i = g.reverse.coeff i) :
    (f*g).coeff n-(f*g).reverse.coeff n =
      (f.coeff n-f.reverse.coeff n)+(g.coeff n-g.reverse.coeff n) := by
  have p := first_mul_coeff (f-f.reverse) g n (fun i hi => by simp [(before i hi).1])
  have q := first_mul_coeff (g-g.reverse) f.reverse n (fun i hi => by simp [(before i hi).2])
  rw [reverse_mul_of_domain,←coeff_sub,
    show f*g-f.reverse*g.reverse = (f-f.reverse)*g+(g-g.reverse)*f.reverse by ring,
    coeff_add,p,q,coeff_sub,coeff_sub,coeff_zero_reverse,fm.leadingCoeff,gc,mul_one,mul_one]

/-- The output agrees with its reversal up to precisely the offsets where
both factors do. At the first differing offset the two differences cannot cancel. -/
theorem matches_mul_iff {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) (t : ℕ) : Matches (f*g) t ↔ Matches f t ∧ Matches g t := by
  constructor
  · intro agree
    suffices both : ∀ n < t, f.coeff n = f.reverse.coeff n ∧ g.coeff n = g.reverse.coeff n from
      ⟨fun n hn => (both n hn).1,fun n hn => (both n hn).2⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ht
      rcases Nat.eq_zero_or_pos n with rfl|pos
      · simp [fc,gc,coeff_zero_reverse,fm.leadingCoeff,gm.leadingCoeff]
      have eq := difference_at f g fm gc n (fun i hi => ih i hi (hi.trans ht))
      rw [agree n ht,sub_self] at eq
      have f' : 0 ≤ f.reverse.coeff n := by rw [coeff_reverse]; exact fp _
      have g' : 0 ≤ g.reverse.coeff n := by rw [coeff_reverse]; exact gp _
      have ff := fp n
      have gg := gp n
      rcases reverse_coeff_eq_zero_or fm gc fp gp bin pos with a|a <;>
        rcases reverse_coeff_eq_zero_or gm fc gp fp (mul_comm f g ▸ bin) pos with b|b <;>
        constructor <;> linarith
  · rintro ⟨left,right⟩ n hn
    have diff := difference_at f g fm gc n (fun i hi => ⟨left i (hi.trans hn),right i (hi.trans hn)⟩)
    rw [left n hn,right n hn] at diff
    linarith

private theorem reverse_of_short {f : ℝ[X]} {t : ℕ} (match_ : Matches f t)
    (bound : f.natDegree ≤ 2*t) : f.reverse = f := by
  ext n
  by_cases nd : n ≤ f.natDegree
  · rw [coeff_reverse,revAt_le nd]
    by_cases small : n < t
    · simpa only [coeff_reverse,revAt_le nd] using (match_ n small).symm
    · by_cases mid : f.natDegree-n = n
      · rw [mid]
      · have k : f.natDegree-n < t := by omega
        have h := match_ _ k
        rw [coeff_reverse,revAt_le (Nat.sub_le _ _),Nat.sub_sub_self nd] at h
        exact h
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge nd),
      coeff_eq_zero_of_natDegree_lt (f.reverse_natDegree_le.trans_lt (lt_of_not_ge nd))]

/-- Agreement of the sum and its reversal at offsets below `t` suffices if
the shorter marginal polynomial has degree at most `2*t`. -/
theorem binary_of_short_factor {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1) (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i)
    (bin : Binary (f*g)) {t : ℕ} (match_ : Matches (f*g) t)
    (bound : min f.natDegree g.natDegree ≤ 2*t) : Binary f ∧ Binary g := by
  obtain ⟨hf,hg⟩ := (matches_mul_iff fm gm fc gc fp gp bin t).mp match_
  rcases min_le_iff.mp bound with h|h
  · exact binary_of_reciprocal fm gm fc gc fp gp bin (reverse_of_short hf h)
  · exact (binary_of_reciprocal gm fm gc fc gp fp (mul_comm f g ▸ bin) (reverse_of_short hg h)).symm

open Green28 Green28UniformSums Green28PrimitiveSupport Green28UnpairedSites

private theorem occupied {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (pf : Models P f a s) (i : ℕ) : a+(i:ℤ) ∈ P.support ↔ f.coeff i ≠ 0 := by
  rw [P.mem_support_iff]
  have e : (P (a+i)).toReal ≠ 0 ↔ P (a+i) ≠ 0 := by simp [ENNReal.toReal_eq_zero_iff,P.apply_ne_top]
  rw [←e,pf.coeff,mul_ne_zero_iff]
  simp [pf.pos.ne']

private theorem extremes {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (pf : Models P f a s) (fm : f.Monic) (fc : f.coeff 0 = 1) :
    IsLeast P.support a ∧ IsGreatest P.support (a+(f.natDegree:ℤ)) := by
  have left : a ∈ P.support := by simpa using (occupied pf 0).mpr (by simp [fc])
  have right := (occupied pf f.natDegree).mpr (by simp [fm.coeff_natDegree])
  have low (z : ℤ) (hz : z ∈ P.support) : a ≤ z := by
    by_contra! h
    exact (P.mem_support_iff z).mp hz (pf.below _ h)
  refine ⟨⟨left,fun z hz => low z hz⟩,right,?_⟩
  intro z hz
  by_contra! h
  have nz : f.coeff (z-a).toNat ≠ 0 := (occupied pf _).mp (by rwa [show a+↑(z-a).toNat = z by omega])
  exact nz (coeff_eq_zero_of_natDegree_lt (by omega))

private theorem unpaired_of_short_window {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (pf : Models P f a s) (fm : f.Monic) (fc : f.coeff 0 = 1) {t : ℕ}
    (match_ : Matches f t) (short : f.natDegree ≤ 2*t+2) : AtMostOneUnpaired P.support := by
  classical
  obtain ⟨lo,hi⟩ := extremes pf fm fc
  let b := a+(f.natDegree:ℤ)
  refine ⟨a,b,if a+(t:ℤ) ∈ P.support then a+t else b-t,lo,hi,?_⟩
  intro x hx missing
  have low := lo.2 hx
  have high := hi.2 hx
  let i := (x-a).toNat
  let j := f.natDegree-i
  have xi : a+(i:ℤ) = x := by dsimp [i]; omega
  have nd : i ≤ f.natDegree := by dsimp [i]; omega
  have jd : j ≤ f.natDegree := Nat.sub_le _ _
  have xj : a+(j:ℤ) = a+b-x := by dsimp [b,j,i]; omega
  have fi := (occupied pf i).mp (xi ▸ hx)
  have fj : f.coeff j = 0 := by
    by_contra h
    exact missing (xj ▸ (occupied pf j).mpr h)
  have bounds : t ≤ i ∧ t ≤ j := by
    constructor
    · by_contra! h
      have e := match_ i h
      rw [coeff_reverse,revAt_le nd] at e
      exact fi (e.trans fj)
    · by_contra! h
      have e := match_ j h
      rw [coeff_reverse,revAt_le jd,show f.natDegree-j = i by dsimp [j]; omega] at e
      exact fi (e ▸ fj)
  have diff : i ≠ j := fun h => fi (h ▸ fj)
  have edge : i = t ∨ j = t := by dsimp [j] at *; omega
  split_ifs with site
  · rcases edge with h|h
    · omega
    · exact False.elim (missing (by rwa [←xj,h]))
  · rcases edge with h|h
    · exact False.elim (site (by rwa [←h,xi]))
    · dsimp [b,j] at *; omega

private theorem output_window {R : PMF ℤ} {P : ℝ[X]} {a : ℤ} {s : ℝ}
    (model : Models R P a s) (pm : P.Monic) (pc : P.coeff 0 = 1) (bin : Binary P)
    {S : Finset ℤ} (ne : S.Nonempty) (law : R = PMF.uniformOfFinset S ne) {t : ℕ}
    (edges : ∀ i : ℕ, i < t → (S.min' ne+(i:ℤ) ∈ S ↔ S.max' ne-(i:ℤ) ∈ S)) :
    Matches P t ∧ (P.natDegree:ℤ) = S.max' ne-S.min' ne := by
  obtain ⟨lo,hi⟩ := extremes model pm pc
  have supp : R.support = (S:Set ℤ) := by rw [law,PMF.support_uniformOfFinset]
  rw [supp] at lo hi
  have aeq := lo.unique (S.isLeast_min' ne)
  have beq := hi.unique (S.isGreatest_max' ne)
  refine ⟨?_,by omega⟩
  intro i it
  by_cases id : i ≤ P.natDegree
  · let j := P.natDegree-i
    have reflected : a+(j:ℤ) = S.max' ne-(i:ℤ) := by dsimp [j]; omega
    have left := occupied model i
    have right := occupied model j
    rw [supp,Finset.mem_coe,aeq] at left
    rw [supp,Finset.mem_coe,reflected] at right
    have h := left.symm.trans ((edges i it).trans right)
    rw [coeff_reverse,revAt_le id]
    change P.coeff i = P.coeff j
    rcases bin i with p|p <;> rcases bin j with q|q <;> simp_all
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge id),
      coeff_eq_zero_of_natDegree_lt (P.reverse_natDegree_le.trans_lt (lt_of_not_ge id))]

/-- Only the outer offsets of the actual sum support are tested. The middle
may be arbitrary. A width of `4*t+3` includes the case where both
marginals may have a single unpaired site. -/
theorem uniform_of_reflected_prefix {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) (t : ℕ)
    (edges : ∀ i : ℕ, i < t → (S.min' ne+(i:ℤ) ∈ S ↔ S.max' ne-(i:ℤ) ∈ S))
    (width : S.max' ne-S.min' ne ≤ 4*(t:ℤ)+3) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨f,g,_,_,_,_,pf,pg,fm,gm,_,_,fc,gc,_⟩ := mask_factorization ne sum
  have flat : IsUniformOnSupport (indepSum P Q) := ⟨S,ne,sum⟩
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp flat
  obtain ⟨match_,deg⟩ := output_window (pf.mul pg) (fm.mul gm)
    (by simp [mul_coeff_zero,fc,gc]) bin ne sum edges
  rw [natDegree_mul fm.ne_zero gm.ne_zero] at deg
  by_cases short : min f.natDegree g.natDegree ≤ 2*t
  · obtain ⟨fb,gb⟩ := binary_of_short_factor fm gm fc gc pf.nonneg pg.nonneg bin match_ short
    exact ⟨(pf.uniform_iff fm).mpr fb,(pg.uniform_iff gm).mpr gb⟩
  · obtain ⟨ff,gg⟩ := (matches_mul_iff fm gm fc gc pf.nonneg pg.nonneg bin t).mp match_
    exact uniform_of_one_unpaired_each flat (unpaired_of_short_window pf fm fc ff (by omega))
      (unpaired_of_short_window pg gm gc gg (by omega))

#print axioms matches_mul_iff
#print axioms binary_of_short_factor
#print axioms uniform_of_reflected_prefix
end Green28ReflectedPrefix
