import Green28FiniteSearch
import Green28UniformSums

/-! A finite real quadratic system equivalent to Green 28 for a fixed outcome budget. -/

open Finset Green28 Green28FiniteSearch
open scoped ENNReal

namespace Green28QuadraticTest

abbrev sites (B : ℕ) := Finset.Icc (0 : ℤ) (B : ℤ)
abbrev Site (B : ℕ) := ↥(sites B)

def Simplex {B : ℕ} (u : Site B → ℝ) : Prop := (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1

noncomputable def table (s : Finset ℤ) (z : ℤ) : ℝ :=
  if z ∈ s then (s.card : ℝ)⁻¹ else 0

/-- Comparison with a uniform table on a subset of the same interval. -/
def Flat {B : ℕ} (u : Site B → ℝ) : Prop :=
  ∃ t ∈ (sites B).powerset, t.Nonempty ∧ ∀ i : Site B, u i = table t i

/-- A coordinate of the discrete convolution as a bilinear expression. -/
noncomputable def sumWeight {B : ℕ} (u v : Site B → ℝ) (z : ℤ) : ℝ :=
  ∑ i : Site B, ∑ j : Site B, if (i : ℤ)+(j : ℤ) = z then u i * v j else 0

/-- All discrete indices run through explicit finite sets. The real unknowns
are normalized nonnegative vectors and the constraints have degree at most two. -/
def QuadraticTest (k B : ℕ) : Prop :=
  ∀ s ∈ (sites B).powerset, s.Nonempty → s.card ≤ k →
    ∀ u v : Site B → ℝ, Simplex u → Simplex v →
      (∀ z ∈ sites (2*B), sumWeight u v z = table s z) → Flat u ∧ Flat v

private def vector (B : ℕ) (P : PMF ℤ) (i : Site B) : ℝ := (P i).toReal

private theorem zero_off {B : ℕ} {P : PMF ℤ} (hp : P.support ⊆ Set.Icc 0 (B : ℤ))
    {z : ℤ} (hz : z ∉ sites B) : P z = 0 :=
  (P.apply_eq_zero_iff z).mpr (fun h => hz (mem_Icc.mpr (hp h)))

private theorem simplex_vector {B : ℕ} {P : PMF ℤ} (hp : P.support ⊆ Set.Icc 0 (B : ℤ)) :
    Simplex (vector B P) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,?_⟩
  have total := congrArg ENNReal.toReal P.tsum_coe
  rw [tsum_eq_sum (s := sites B) (fun _ hz => zero_off hp hz),
    ENNReal.toReal_sum (fun x _ => P.apply_ne_top x),ENNReal.toReal_one] at total
  exact (sum_coe_sort (sites B) (fun x => (P x).toReal)).trans total

private theorem realize {B : ℕ} {u : Site B → ℝ} (simp : Simplex u) :
    ∃ P : PMF ℤ, P.support ⊆ Set.Icc 0 (B : ℤ) ∧ vector B P = u := by
  classical
  let w (z : ℤ) : ℝ≥0∞ := if h : z ∈ sites B then ENNReal.ofReal (u ⟨z,h⟩) else 0
  have off (z : ℤ) (hz : z ∉ sites B) : w z = 0 := dif_neg hz
  have total : ∑ z ∈ sites B, w z = 1 := by
    rw [← sum_coe_sort]
    have atSite (i : Site B) : w i = ENNReal.ofReal (u i) := dif_pos i.property
    simp_rw [atSite]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => simp.1 i),simp.2,ENNReal.ofReal_one]
  let P := PMF.ofFinset w (sites B) total off
  refine ⟨P,?_,?_⟩
  · intro z hz
    by_contra h
    exact (P.mem_support_iff z).mp hz (off z (fun hi => h (mem_Icc.mp hi)))
  · funext i
    change (w i).toReal = u i
    rw [show w i = ENNReal.ofReal (u i) from dif_pos i.property, ENNReal.toReal_ofReal (simp.1 i)]

private theorem uniform_real (s : Finset ℤ) (hs : s.Nonempty) (z : ℤ) :
    (PMF.uniformOfFinset s hs z).toReal = table s z := by
  classical
  by_cases hz : z ∈ s <;> simp [PMF.uniformOfFinset_apply,table,hz]

private theorem eq_uniform {B : ℕ} {P : PMF ℤ} {s : Finset ℤ}
    (hp : P.support ⊆ Set.Icc 0 (B : ℤ)) (hs : s.Nonempty) (sub : s ⊆ sites B)
    (vals : ∀ z ∈ sites B, (P z).toReal = table s z) : P = PMF.uniformOfFinset s hs := by
  apply PMF.ext
  intro z
  by_cases hz : z ∈ sites B
  · apply (ENNReal.toReal_eq_toReal_iff' (P.apply_ne_top _) ((PMF.uniformOfFinset s hs).apply_ne_top _)).mp
    exact (vals z hz).trans (uniform_real s hs z).symm
  · exact (zero_off hp hz).trans (PMF.uniformOfFinset_apply_of_notMem hs (fun hs => hz (sub hs))).symm

private theorem flat_iff {B : ℕ} {P : PMF ℤ} (hp : P.support ⊆ Set.Icc 0 (B : ℤ)) :
    Flat (vector B P) ↔ IsUniformOnSupport P := by
  constructor
  · rintro ⟨t,sub,ht,h⟩
    exact ⟨t,ht,eq_uniform hp ht (mem_powerset.mp sub) (fun z hz => h ⟨z,hz⟩)⟩
  · rintro ⟨s,hs,rfl⟩
    rw [PMF.support_uniformOfFinset] at hp
    exact ⟨s,mem_powerset.mpr (fun _ h => mem_Icc.mpr (hp h)),hs,fun i => uniform_real s hs i⟩

private theorem bind_real {B : ℕ} {P : PMF ℤ} (hp : P.support ⊆ Set.Icc 0 (B : ℤ))
    (f : ℤ → PMF ℤ) (z : ℤ) :
    (P.bind f z).toReal = ∑ i : Site B, (P i).toReal * (f i z).toReal := by
  rw [PMF.bind_apply,tsum_eq_sum (s := sites B) (fun i hi => by rw [zero_off hp hi,zero_mul]),
    ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (P.apply_ne_top i) ((f i).apply_ne_top _)),
    sum_coe_sort (sites B) (fun x => (P x).toReal * (f x z).toReal)]
  simp only [ENNReal.toReal_mul]

private theorem sum_real {B : ℕ} {P Q : PMF ℤ} (hp : P.support ⊆ Set.Icc 0 (B : ℤ))
    (hq : Q.support ⊆ Set.Icc 0 (B : ℤ)) (z : ℤ) :
    (indepSum P Q z).toReal = sumWeight (vector B P) (vector B Q) z := by
  change ((P.bind fun x => Q.bind fun y => PMF.pure (x+y)) z).toReal = _
  rw [bind_real hp]
  unfold sumWeight
  apply sum_congr rfl
  intro i _
  rw [bind_real hq, mul_sum]
  apply sum_congr rfl
  intro j _
  by_cases eq : (i:ℤ)+(j:ℤ)=z
  · simp [PMF.pure_apply,vector,eq]
  · simp [PMF.pure_apply,eq,Ne.symm eq]

private theorem sum_bounded {B : ℕ} {P Q : PMF ℤ} (hp : P.support ⊆ Set.Icc 0 (B : ℤ))
    (hq : Q.support ⊆ Set.Icc 0 (B : ℤ)) : (indepSum P Q).support ⊆ Set.Icc 0 (↑(2*B) : ℤ) := by
  intro z hz
  obtain ⟨x,hx,y,hy,rfl⟩ := mem_support_indepSum.mp hz
  obtain ⟨_,_⟩ := hp hx
  obtain ⟨_,_⟩ := hq hy
  exact ⟨by omega,by omega⟩

/-- Every feasible pair of vectors is realized by bounded integer laws with that uniform sum. -/
theorem realize_pair {B : ℕ} {s : Finset ℤ} (hs : s.Nonempty) (sub' : s ⊆ sites B)
    {u v : Site B → ℝ} (hu : Simplex u) (hv : Simplex v)
    (vals : ∀ z ∈ sites (2*B), sumWeight u v z = table s z) :
    ∃ P Q : PMF ℤ, P.support ⊆ Set.Icc 0 (B : ℤ) ∧ Q.support ⊆ Set.Icc 0 (B : ℤ) ∧
      (fun i : Site B => (P i).toReal) = u ∧ (fun i : Site B => (Q i).toReal) = v ∧
      indepSum P Q = PMF.uniformOfFinset s hs := by
  obtain ⟨P,hp,eu⟩ := realize hu
  obtain ⟨Q,hq,ev⟩ := realize hv
  have wide : s ⊆ sites (2*B) := by
    intro z hz
    obtain ⟨lo,hi⟩ := mem_Icc.mp (sub' hz)
    exact mem_Icc.mpr ⟨lo,by omega⟩
  have eq := eq_uniform (sum_bounded hp hq) hs wide (fun z hz => by
    rw [sum_real hp hq,eu,ev]; exact vals z hz)
  exact ⟨P,Q,hp,hq,eu,ev,eq⟩

/-- Exact correspondence between bounded integer laws and the finite real system. -/
theorem onInterval_iff_quadraticTest (k B : ℕ) : OnInterval k B ↔ QuadraticTest k B := by
  constructor
  · intro h s sub hs hk u v hu hv vals
    have sub' := mem_powerset.mp sub
    obtain ⟨P,Q,hp,hq,eu,ev,eq⟩ := realize_pair hs sub' hu hv vals
    change vector B P = u at eu
    change vector B Q = v at ev
    have both := h P Q s hs hk hp hq (fun _ hz => mem_Icc.mp (sub' hz)) eq
    exact ⟨eu ▸ (flat_iff hp).mpr both.1,ev ▸ (flat_iff hq).mpr both.2⟩
  · intro h P Q s hs hk hp hq sub eq
    have vals (z : ℤ) (_ : z ∈ sites (2*B)) :
        sumWeight (vector B P) (vector B Q) z = table s z := by
      rw [← sum_real hp hq,eq,uniform_real]
    have both := h s (mem_powerset.mpr (fun _ hz => mem_Icc.mpr (sub hz))) hs hk
      (vector B P) (vector B Q) (simplex_vector hp) (simplex_vector hq) vals
    exact ⟨(flat_iff hp).mp both.1,(flat_iff hq).mp both.2⟩

/-- Bounded outcome cardinality, with no diameter assumption on the original laws. -/
theorem atMost_iff_quadraticTest (k : ℕ) : AtMost k ↔ QuadraticTest k (5^(k+1)) :=
  (atMost_iff_onInterval k).trans (onInterval_iff_quadraticTest _ _)

/-- The left side is the literal type of the pinned open declaration. -/
theorem green_28_iff_quadraticTests :
    (type_of% Green28.green_28) ↔ ∀ k : ℕ, QuadraticTest k (5^(k+1)) := by
  constructor
  · intro h k
    apply (atMost_iff_quadraticTest k).mp
    intro P Q s hs _ eq
    have u : IsUniformOnSupport (indepSum P Q) := ⟨s,hs,eq⟩
    obtain ⟨hp,hq⟩ := Green28UniformSums.finite_of_uniform_sum u
    exact h P Q ⟨hp,hq,u⟩
  · intro h P Q ⟨_,_,s,hs,eq⟩
    exact (atMost_iff_quadraticTest s.card).mpr (h _) P Q s hs le_rfl eq

#print axioms realize_pair
#print axioms onInterval_iff_quadraticTest
#print axioms atMost_iff_quadraticTest
#print axioms green_28_iff_quadraticTests

end Green28QuadraticTest
