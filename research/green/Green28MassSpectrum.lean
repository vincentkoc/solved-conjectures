import Green28SubsetResolvent
import Green28QuadraticTest

/-! A finite alphabet of algebraic marginal masses at each output cardinality. -/

namespace Green28MassSpectrum
open Finset Polynomial Green28 Green28UniformSums Green28PrimitiveSupport
open scoped ENNReal

/-- Normalization of a shifted polynomial model for an actual probability law. -/
theorem model_total {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ} (h : Models P f a s) :
    s * f.eval 1 = 1 := by
  classical
  let v := fun i : ℕ => a+(i:ℤ)
  let T := f.support.image v
  have inj : Function.Injective v := by intro i j eq;dsimp [v] at eq;omega
  have outside (z : ℤ) (hz : z ∉ T) : P z = 0 := by
    by_cases low : z < a
    · exact h.below z low
    let i := (z-a).toNat
    have atSite : v i = z := by dsimp [i,v];omega
    have empty : f.coeff i = 0 := notMem_support_iff.mp (fun hi => hz (atSite ▸ mem_image_of_mem v hi))
    have eq := h.coeff i
    change (P (v i)).toReal = _ at eq
    rw [atSite,empty,mul_zero] at eq
    exact (ENNReal.toReal_eq_zero_iff _).mp eq |>.resolve_right (P.apply_ne_top z)
  have total := congrArg ENNReal.toReal P.tsum_coe
  rw [tsum_eq_sum outside,ENNReal.toReal_sum (fun i _ => P.apply_ne_top i),ENNReal.toReal_one] at total
  change ∑ z ∈ f.support.image v, (P z).toReal = 1 at total
  rw [sum_image inj.injOn] at total
  simpa only [v,h.coeff,←mul_sum,eval_eq_sum,Polynomial.sum,one_pow,mul_one] using total

theorem mask_eval_one (S : Finset ℤ) (ne : S.Nonempty) : (outputMask S ne).eval 1 = (S.card:ℤ) := by
  classical
  let v := fun z : ℤ => (z-S.min' ne).toNat
  have inj : Set.InjOn v (S:Set ℤ) := by
    intro x hx y hy eq
    have := S.min'_le _ hx
    have := S.min'_le _ hy
    dsimp only [v] at eq;omega
  simp only [outputMask,eval_finsetSum,eval_monomial,one_pow,mul_one,sum_const,nsmul_eq_mul]
  rw [show (S.image (fun z => (z-S.min' ne).toNat)).card = S.card from card_image_of_injOn inj]

/-- Every atom occurs among the normalized coefficients of a monic divisor
of the shifted mask, or is zero. -/
theorem atom_of_model {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ} (model : Models P f a s) (z : ℤ) :
    (P z).toReal = 0 ∨ ∃ j ∈ f.support, (P z).toReal = f.coeff j / f.eval 1 := by
  by_cases small : z<a
  · left;rw [model.below z small];rfl
  let j := (z-a).toNat
  have offset : a+(j:ℤ)=z := by dsimp [j];omega
  have eq := model.coeff j
  rw [offset] at eq
  by_cases mem : j ∈ f.support
  · refine Or.inr ⟨j,mem,?_⟩
    have total := model_total model
    have nz : f.eval 1 ≠ 0 := right_ne_zero_of_mul_eq_one total
    apply (eq_div_iff nz).mpr
    rw [eq]
    calc
      _ = (s*f.eval 1)*f.coeff j := by ring
      _ = _ := by rw [total,one_mul]
  · exact Or.inl (by rw [eq,notMem_support_iff.mp mem,mul_zero])

/-- The positive entries for a fixed output belong to the polynomial
divisor catalogue; zero is included for unoccupied integer sites. -/
noncomputable def candidates (S : Finset ℤ) (ne : S.Nonempty) : Finset ℝ := by
  classical
  let F := (outputMask S ne).map (Int.castRingHom ℝ)
  let _ := Polynomial.fintypeSubtypeMonicDvd F ((Green28SubsetResolvent.mask_monic S ne).map _).ne_zero
  exact insert 0 (univ.biUnion fun f : {g : ℝ[X] // g.Monic ∧ g ∣ F} =>
    f.val.support.image (fun j => f.val.coeff j / f.val.eval 1))

theorem atoms_in_candidates {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) :
    (∀ x, (P x).toReal ∈ candidates S ne) ∧ (∀ y, (Q y).toReal ∈ candidates S ne) := by
  classical
  obtain ⟨f,g,_,_,_,_,fp,gp,fm,gm,_,_,_,_,prod⟩ := mask_factorization ne sum
  let F := (outputMask S ne).map (Int.castRingHom ℝ)
  let _ := Polynomial.fintypeSubtypeMonicDvd F ((Green28SubsetResolvent.mask_monic S ne).map _).ne_zero
  change f*g = F at prod
  have one {R : PMF ℤ} {u : ℝ[X]} {a : ℤ} {s : ℝ} (h : Models R u a s) (um : u.Monic) (dv : u ∣ F) (x : ℤ) :
      (R x).toReal ∈ candidates S ne := by
    rcases atom_of_model h x with zero|⟨i,hi,eq⟩
    · rw [zero];exact mem_insert_self ..
    · apply mem_insert_of_mem
      let f : {g : ℝ[X] // g.Monic ∧ g ∣ F} := ⟨u,um,dv⟩
      exact mem_biUnion.mpr ⟨f,mem_univ _,mem_image.mpr ⟨i,hi,eq.symm⟩⟩
  exact ⟨one fp fm (prod ▸ dvd_mul_right f g),one gp gm (prod ▸ dvd_mul_left g f)⟩

open Green28FiniteSearch Green28QuadraticTest

/-- Every catalogue entry times the output size is an algebraic integer, even for a divisor
whose coefficients do not define a probability law. -/
theorem candidate_integral {S : Finset ℤ} (ne : S.Nonempty) {x : ℝ} (hx : x ∈ candidates S ne) :
    IsIntegral ℤ ((S.card:ℝ)*x) := by
  classical
  rcases mem_insert.mp hx with rfl|hx
  · simpa using (isIntegral_zero : IsIntegral ℤ (0:ℝ))
  obtain ⟨⟨u,um,ud⟩,_,hx⟩ := mem_biUnion.mp hx
  obtain ⟨j,_,rfl⟩ := mem_image.mp hx
  let H := outputMask S ne
  have hm := Green28SubsetResolvent.mask_monic S ne
  change u ∣ H.map (Int.castRingHom ℝ) at ud
  obtain ⟨v,prod⟩ := ud
  have vm : v.Monic := um.of_mul_monic_left (prod ▸ hm.map (Int.castRingHom ℝ))
  have vd : v ∣ H.map (Int.castRingHom ℝ) := prod ▸ dvd_mul_left v u
  have ui := isIntegral_coeff_of_dvd H u hm um (show u ∣ H.map (Int.castRingHom ℝ) from ⟨v,prod⟩) j
  have vi : IsIntegral ℤ (v.eval 1) := by
    rw [eval_eq_sum,Polynomial.sum]
    simpa only [one_pow,mul_one] using IsIntegral.sum (s:=v.support) (fun i => v.coeff i)
      (fun i _ => isIntegral_coeff_of_dvd H v hm vm vd i)
  have total : u.eval 1 * v.eval 1 = (S.card:ℝ) := by
    rw [←eval_mul,←prod,eval_map,eval₂_at_one]
    simpa only [map_natCast] using congrArg (Int.castRingHom ℝ) (mask_eval_one S ne)
  have nz : u.eval 1 ≠ 0 := by
    intro zero
    rw [zero,zero_mul] at total
    exact (Nat.cast_ne_zero.mpr ne.card_pos.ne' : (S.card:ℝ) ≠ 0) total.symm
  change IsIntegral ℤ ((S.card:ℝ)*(u.coeff j/u.eval 1))
  rw [←total,show u.eval 1 * v.eval 1 * (u.coeff j / u.eval 1) = u.coeff j * v.eval 1 by field_simp]
  exact ui.mul vi

/-- The number of outcomes clears the denominator of every marginal atom. -/
theorem scaled_integral {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (sum : indepSum P Q = PMF.uniformOfFinset S ne) :
    (∀ z, IsIntegral ℤ ((S.card:ℝ)*(P z).toReal)) ∧
    (∀ z, IsIntegral ℤ ((S.card:ℝ)*(Q z).toReal)) :=
  let masses := atoms_in_candidates ne sum
  ⟨fun z => candidate_integral ne (masses.1 z),fun z => candidate_integral ne (masses.2 z)⟩

private noncomputable def options (S : Finset ℤ) : Finset ℝ :=
  if ne : S.Nonempty then candidates S ne else ∅

/-- A finite set of possible atom masses, specified solely by the outcome budget. -/
noncomputable def alphabet (k : ℕ) : Finset ℝ := by
  classical
  exact insert 0 (((sites (5^(k+1))).powerset.filter (fun S => S.card ≤ k)).biUnion options)

private theorem included {k : ℕ} {S : Finset ℤ} (ne : S.Nonempty) (size : S.card ≤ k)
    (sub : S ⊆ sites (5^(k+1))) {x : ℝ} (hx : x ∈ candidates S ne) : x ∈ alphabet k := by
  classical
  apply mem_insert_of_mem
  exact mem_biUnion.mpr ⟨S,mem_filter.mpr ⟨mem_powerset.mpr sub,size⟩,by simpa [options,ne] using hx⟩

/-- Every atom of either original law lies in the same finite alphabet, at arbitrary
integer locations and without a bound on the original diameter. -/
theorem atoms_in_alphabet {k : ℕ} {P Q : PMF ℤ} {S : Finset ℤ} (ne : S.Nonempty)
    (size : S.card ≤ k) (sum : indepSum P Q = PMF.uniformOfFinset S ne) :
    (∀ z, (P z).toReal ∈ alphabet k) ∧ (∀ z, (Q z).toReal ∈ alphabet k) := by
  classical
  have support : (indepSum P Q).support = (S : Set ℤ) := by rw [sum,PMF.support_uniformOfFinset]
  obtain ⟨r⟩ := compress support
  let T := S.image r.output
  have card : T.card = S.card := card_image_of_injOn r.output_inj
  have sub : T ⊆ sites (5^(k+1)) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨lo,hi⟩ := r.output_bound x hx
    apply mem_Icc.mpr
    exact ⟨lo,hi.trans (by exact_mod_cast Nat.pow_le_pow_right (by decide : 0<5) (by omega : S.card+1 ≤ k+1))⟩
  have neT : T.Nonempty := ne.image _
  have inc := fun {x : ℝ} (hx : x ∈ candidates T neT) => included neT (card ▸ size) sub hx
  have cat := atoms_in_candidates neT (r.uniform_sum ne sum)
  have kept := r.preserves support
  have liftMass {R : PMF ℤ} {f : ℤ → ℤ} (keep : ∀ z ∈ R.support, R.map f (f z) = R z)
      (mem : ∀ z, ((R.map f) z).toReal ∈ candidates T neT) (z : ℤ) : (R z).toReal ∈ alphabet k := by
    by_cases hz : z ∈ R.support
    · rw [←keep z hz];exact inc (mem _)
    · rw [(R.apply_eq_zero_iff z).mpr hz,ENNReal.toReal_zero];exact mem_insert_self ..
  exact ⟨liftMass kept.1 cat.1,liftMass kept.2.1 cat.2⟩

/-- A single integer denominator works over all masks and budgets up to `k`. -/
theorem alphabet_integral {k : ℕ} {x : ℝ} (hx : x ∈ alphabet k) :
    IsIntegral ℤ ((k.factorial:ℝ)*x) := by
  classical
  rcases mem_insert.mp hx with rfl|hx
  · simpa using (isIntegral_zero : IsIntegral ℤ (0:ℝ))
  obtain ⟨S,hs,hx⟩ := mem_biUnion.mp hx
  by_cases ne : S.Nonempty
  · have int := candidate_integral ne (by simpa [options,ne] using hx : x ∈ candidates S ne)
    obtain ⟨q,eq⟩ := Nat.dvd_factorial ne.card_pos (mem_filter.mp hs).2
    rw [eq,Nat.cast_mul,show (S.card:ℝ)*q*x = q*(S.card*x) by ring]
    exact (isIntegral_natCast q).mul int
  · simp [options,ne] at hx

/-- A common monic integer polynomial annihilates all scaled entries in the alphabet. -/
theorem common_polynomial (k : ℕ) : ∃ H : ℤ[X], H.Monic ∧
    ∀ x ∈ alphabet k, aeval ((k.factorial:ℝ)*x) H = 0 := by
  classical
  let poly (x : ℝ) := minpoly ℤ ((k.factorial:ℝ)*x)
  refine ⟨∏ x ∈ alphabet k, poly x,Polynomial.monic_prod_of_monic _ _ (fun x hx => minpoly.monic (alphabet_integral hx)),?_⟩
  intro x hx
  rw [map_prod]
  exact prod_eq_zero hx (minpoly.aeval ℤ _)

/-- At fixed budget all the laws tested here range over finite sets. -/
def AlphabetTest (k : ℕ) : Prop :=
  let B := 5^(k+1)
  ∀ s ∈ (sites B).powerset, s.Nonempty → s.card ≤ k →
    ∀ u v : Site B → ↥(alphabet k),
      Simplex (fun i => (u i : ℝ)) → Simplex (fun i => (v i : ℝ)) →
      (∀ z ∈ sites (2*B), sumWeight (fun i => (u i : ℝ)) (fun i => (v i : ℝ)) z = table s z) →
      Flat (fun i => (u i : ℝ)) ∧ Flat (fun i => (v i : ℝ))

/-- Restricting real entries to the finite alphabet loses no feasible table. -/
theorem quadratic_iff_alphabet (k : ℕ) : QuadraticTest k (5^(k+1)) ↔ AlphabetTest k := by
  constructor
  · intro h s sub ne size u v
    exact h s sub ne size (fun i => (u i : ℝ)) (fun i => (v i : ℝ))
  · intro h s sub ne size u v hu hv vals
    obtain ⟨P,Q,_,_,rfl,rfl,eq⟩ := realize_pair ne (mem_powerset.mp sub) hu hv vals
    have masses := atoms_in_alphabet ne size eq
    exact h s sub ne size (fun i => ⟨(P i).toReal,masses.1 i⟩)
      (fun i => ⟨(Q i).toReal,masses.2 i⟩) hu hv vals

/-- The literal pinned Green question is equivalent to one finite discrete test per outcome budget. -/
theorem green_28_iff_alphabet_tests : (type_of% Green28.green_28) ↔ ∀ k : ℕ, AlphabetTest k :=
  green_28_iff_quadraticTests.trans (forall_congr' quadratic_iff_alphabet)

#print axioms model_total
#print axioms mask_eval_one
#print axioms atom_of_model
#print axioms atoms_in_candidates
#print axioms candidate_integral
#print axioms scaled_integral
#print axioms atoms_in_alphabet
#print axioms alphabet_integral
#print axioms common_polynomial
#print axioms quadratic_iff_alphabet
#print axioms green_28_iff_alphabet_tests
end Green28MassSpectrum
