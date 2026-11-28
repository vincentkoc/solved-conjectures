import Green28SupportCompression
import FormalConjectures.GreensOpenProblems.«28»

/-! Transfer of integer probability laws under compression of the output support. -/

open Green28 Finset
open scoped ENNReal

namespace Green28FiniteSearch

private theorem bind_eq {P : PMF ℤ} {u v : ℤ → PMF ℤ}
    (h : ∀ x ∈ P.support, u x = v x) : P.bind u = P.bind v := by
  ext z
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ P.support
  · rw [h x hx]
  · rw [(P.apply_eq_zero_iff x).mpr hx]; simp

private theorem mapped_sum {P Q : PMF ℤ} {f g h : ℤ → ℤ}
    (eq : ∀ x ∈ P.support, ∀ y ∈ Q.support, f x + g y = h (x+y)) :
    indepSum (P.map f) (Q.map g) = (indepSum P Q).map h := by
  simp only [indepSum, Bind.bind, PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
  apply bind_eq
  intro x hx
  apply bind_eq
  intro y hy
  exact congrArg PMF.pure (eq x hx y hy)

private theorem map_mass {P : PMF ℤ} {f : ℤ → ℤ} (inj : Set.InjOn f P.support)
    {x : ℤ} (hx : x ∈ P.support) : P.map f (f x) = P x := by
  classical
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y hy
    by_cases hys : y ∈ P.support
    · simp [show f x ≠ f y from fun eq => hy (inj hx hys eq).symm]
    · simp [(P.apply_eq_zero_iff _).mpr hys]

private theorem uniform_image {P : PMF ℤ} {f : ℤ → ℤ} {s : Finset ℤ} (hs : s.Nonempty)
    (eq : P = PMF.uniformOfFinset s hs) (inj : Set.InjOn f P.support) :
    P.map f = PMF.uniformOfFinset (s.image f) (hs.image f) := by
  classical
  subst P
  have sinj : Set.InjOn f (s : Set ℤ) := by simpa using inj
  apply PMF.ext
  intro z
  by_cases hz : z ∈ s.image f
  · obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    rw [map_mass inj (by simpa using hx),PMF.uniformOfFinset_apply_of_mem _ hx,
      PMF.uniformOfFinset_apply_of_mem _ hz,Finset.card_image_of_injOn sinj]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr (by simpa using hz),PMF.uniformOfFinset_apply_of_notMem _ hz]

private theorem uniform_map {P : PMF ℤ} {f : ℤ → ℤ}
    (inj : Set.InjOn f P.support) (u : IsUniformOnSupport P) :
    IsUniformOnSupport (P.map f) := by
  obtain ⟨s,hs,eq⟩ := u
  exact ⟨s.image f,hs.image _,uniform_image hs eq inj⟩

/-- Relabelling injectively on a law's support preserves and reflects uniformity. -/
theorem uniform_map_iff {P : PMF ℤ} {f : ℤ → ℤ} (inj : Set.InjOn f P.support) :
    IsUniformOnSupport (P.map f) ↔ IsUniformOnSupport P := by
  refine ⟨fun u => ?_,uniform_map inj⟩
  let g := Function.invFunOn f P.support
  have back : (P.map f).map g = P := by
    rw [PMF.map_comp]
    trans P.map id
    · change P.bind _ = P.bind _
      apply bind_eq
      intro x hx
      exact congrArg PMF.pure (inj.leftInvOn_invFunOn hx)
    · exact PMF.map_id P
  rw [← back]
  exact uniform_map (by rw [PMF.support_map]; exact Function.invFunOn_injOn_image f _) u

private theorem support_model (s : Finset ℤ) (hne : s.Nonempty) :
    ∃ F : ℤ → ℤ, (∀ x ∈ s, 0 ≤ F x ∧ F x ≤ (5^(s.card+1) : ℕ)) ∧
      (∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s, ∀ l ∈ s,
        i+j ≤ k+l ↔ F i+F j ≤ F k+F l) := by
  classical
  let lo := s.min' hne
  let hi := s.max' hne
  let a (i : Fin s.card) := (s.equivFin.symm i : ℤ)-lo
  have limits (i : Fin s.card) : 0 ≤ a i ∧ a i ≤ (hi-lo).toNat := by
    have h := (s.equivFin.symm i).property
    have hl := s.min'_le _ h
    have hu := s.le_max' _ h
    dsimp [a,lo,hi]
    omega
  obtain ⟨b,range,rel⟩ := Green28SupportCompression.bounded_sites a limits
  let F (z : ℤ) := if hz : z ∈ s then b (s.equivFin ⟨z,hz⟩) else 0
  refine ⟨F,fun z hz => by simpa [F,hz] using range (s.equivFin ⟨z,hz⟩),?_⟩
  intro i hi j hj k hk l hl
  have he := rel (s.equivFin ⟨i,hi⟩) (s.equivFin ⟨j,hj⟩) (s.equivFin ⟨k,hk⟩) (s.equivFin ⟨l,hl⟩)
  simp only [a,Equiv.symm_apply_apply] at he
  simpa [F,hi,hj,hk,hl] using (show (i+j ≤ k+l ↔ _) from (by omega : i+j ≤ k+l ↔ i-lo+(j-lo) ≤ k-lo+(l-lo)).trans he)

/-- The three maps preserve each sum and inject separately on the three supports.
All the resulting sites lie in the same integer interval. -/
structure Relabelling (P Q : PMF ℤ) (s : Finset ℤ) (B : ℕ) where
  left : ℤ → ℤ
  right : ℤ → ℤ
  output : ℤ → ℤ
  left_inj : Set.InjOn left P.support
  right_inj : Set.InjOn right Q.support
  output_inj : Set.InjOn output (s : Set ℤ)
  left_bound : ∀ x ∈ P.support, left x ∈ Set.Icc 0 (B : ℤ)
  right_bound : ∀ y ∈ Q.support, right y ∈ Set.Icc 0 (B : ℤ)
  output_bound : ∀ z ∈ s, output z ∈ Set.Icc 0 (B : ℤ)
  add : ∀ x ∈ P.support, ∀ y ∈ Q.support, left x + right y = output (x+y)

/-- The support of the sum consists of sums of occupied sites. -/
theorem mem_support_indepSum {P Q : PMF ℤ} {z : ℤ} :
    z ∈ (indepSum P Q).support ↔ ∃ x ∈ P.support, ∃ y ∈ Q.support, x+y=z := by
  simp only [indepSum,Bind.bind,PMF.mem_support_bind_iff,PMF.mem_support_pure_iff,eq_comm]

/-- A finite sum support suffices even when its masses are unequal. -/
theorem compress {P Q : PMF ℤ} {s : Finset ℤ}
    (hs : (indepSum P Q).support = (s : Set ℤ)) :
    Nonempty (Relabelling P Q s (5^(s.card+1))) := by
  classical
  have hn : s.Nonempty := by
    obtain ⟨z,hz⟩ := (indepSum P Q).support_nonempty
    exact ⟨z,by rwa [hs] at hz⟩
  let m := s.min' hn
  have hm : m ∈ s := s.min'_mem hn
  have hm' : m ∈ (indepSum P Q).support := by rw [hs]; exact hm
  obtain ⟨x,hx,y,hy,anchor⟩ := mem_support_indepSum.mp hm'
  have pair {a b : ℤ} (ha : a ∈ P.support) (hb : b ∈ Q.support) : a+b ∈ s := by
    change a+b ∈ (s : Set ℤ)
    rw [← hs]
    exact mem_support_indepSum.mpr ⟨a,ha,b,hb,rfl⟩
  obtain ⟨F,bounds,rel⟩ := support_model s hn
  have ord {u v : ℤ} (hu : u ∈ s) (hv : v ∈ s) : u ≤ v ↔ F u ≤ F v := by
    have h := rel u hu u hu v hv v hv
    omega
  have inj : Set.InjOn F (s : Set ℤ) := by
    intro u hu v hv e
    exact le_antisymm ((ord hu hv).mpr e.le) ((ord hv hu).mpr e.ge)
  refine ⟨⟨fun a => F (a+y)-F m,fun b => F (x+b),F,?_,?_,inj,?_,?_,bounds,?_⟩⟩
  · intro a ha b hb eq
    dsimp at eq
    have := inj (pair ha hy) (pair hb hy) (sub_left_inj.mp eq)
    omega
  · intro a ha b hb eq
    have := inj (pair hx ha) (pair hx hb) eq
    omega
  · intro a ha
    have low := (ord hm (pair ha hy)).mp (s.min'_le _ (pair ha hy))
    have high := bounds (a+y) (pair ha hy)
    have nonneg := (bounds _ hm).1
    exact ⟨sub_nonneg.mpr low,(sub_le_self _ nonneg).trans high.2⟩
  · intro b hb
    exact bounds _ (pair hx hb)
  · intro a ha b hb
    have fwd := (rel (a+y) (pair ha hy) (x+b) (pair hx hb) (a+b) (pair ha hb) m hm).mp (by omega)
    have back := (rel (a+b) (pair ha hb) m hm (a+y) (pair ha hy) (x+b) (pair hx hb)).mp (by omega)
    omega

/-- Every original atom keeps its mass, as does each point of the sum support. -/
theorem Relabelling.preserves {P Q : PMF ℤ} {s : Finset ℤ} {B : ℕ}
    (r : Relabelling P Q s B) (hs : (indepSum P Q).support = (s : Set ℤ)) :
    (∀ x ∈ P.support, P.map r.left (r.left x) = P x) ∧
    (∀ y ∈ Q.support, Q.map r.right (r.right y) = Q y) ∧
    (∀ z ∈ s, indepSum (P.map r.left) (Q.map r.right) (r.output z) = indepSum P Q z) := by
  refine ⟨fun _ hx => map_mass r.left_inj hx,fun _ hy => map_mass r.right_inj hy,?_⟩
  intro z hz
  rw [mapped_sum r.add]
  exact map_mass (hs ▸ r.output_inj) (by rw [hs]; exact hz)

/-- The unrestricted Green question for uniform sums with at most `k` outcomes. -/
def AtMost (k : ℕ) : Prop :=
  ∀ (P Q : PMF ℤ) (s : Finset ℤ) (hs : s.Nonempty), s.card ≤ k →
    indepSum P Q = PMF.uniformOfFinset s hs → IsUniformOnSupport P ∧ IsUniformOnSupport Q

/-- Test only marginals and outcomes in the interval from zero through `B`. -/
def OnInterval (k B : ℕ) : Prop :=
  ∀ (P Q : PMF ℤ) (s : Finset ℤ) (hs : s.Nonempty), s.card ≤ k →
    P.support ⊆ Set.Icc 0 (B : ℤ) → Q.support ⊆ Set.Icc 0 (B : ℤ) →
    (s : Set ℤ) ⊆ Set.Icc 0 (B : ℤ) →
    indepSum P Q = PMF.uniformOfFinset s hs → IsUniformOnSupport P ∧ IsUniformOnSupport Q

/-- Lossless cutoff specified solely by the number of outcomes of the sum. -/
theorem atMost_iff_onInterval (k : ℕ) : AtMost k ↔ OnInterval k (5^(k+1)) := by
  refine ⟨fun h P Q s hs hk _ _ _ => h P Q s hs hk,?_⟩
  intro h P Q s hs hk eq
  have support : (indepSum P Q).support = (s : Set ℤ) := by rw [eq,PMF.support_uniformOfFinset]
  obtain ⟨r⟩ := compress support
  have inc : Set.Icc (0:ℤ) (↑(5^(s.card+1) : ℕ)) ⊆ Set.Icc 0 (↑(5^(k+1) : ℕ)) :=
    Set.Icc_subset_Icc_right (by exact_mod_cast Nat.pow_le_pow_right (by decide : 0<5) (by omega : s.card+1 ≤ k+1))
  let u := s.image r.output
  have uc : u.card = s.card := Finset.card_image_of_injOn r.output_inj
  have pe : (P.map r.left).support ⊆ Set.Icc 0 (↑(5^(k+1) : ℕ)) := by
    rw [PMF.support_map]; rintro _ ⟨x,hx,rfl⟩; exact inc (r.left_bound _ hx)
  have qe : (Q.map r.right).support ⊆ Set.Icc 0 (↑(5^(k+1) : ℕ)) := by
    rw [PMF.support_map]; rintro _ ⟨x,hx,rfl⟩; exact inc (r.right_bound _ hx)
  have ue : (u : Set ℤ) ⊆ Set.Icc 0 (↑(5^(k+1) : ℕ)) := by
    intro z hz; obtain ⟨x,hx,rfl⟩ := mem_image.mp hz; exact inc (r.output_bound _ hx)
  have push := uniform_image hs eq (support ▸ r.output_inj)
  have he := h (P.map r.left) (Q.map r.right) u (hs.image _) (uc ▸ hk) pe qe ue
    ((mapped_sum r.add).trans push)
  exact ⟨(uniform_map_iff r.left_inj).mp he.1,(uniform_map_iff r.right_inj).mp he.2⟩

#print axioms compress
#print axioms Relabelling.preserves
#print axioms uniform_map_iff
#print axioms atMost_iff_onInterval

end Green28FiniteSearch
