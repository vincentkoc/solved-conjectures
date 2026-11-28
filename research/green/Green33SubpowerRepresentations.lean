import Green33QuadraticRadix
import Mathlib.NumberTheory.PrimesCongruentOne

/-! Cyclic lifts with a quadratic correction from the preceding digit. -/

open Finset
open scoped Pointwise

namespace Green33SubpowerRepresentations

/-- The original prime-radix block and encoding use the radix as the square modulus. -/
abbrev block (q : ℕ) := Green33QuadraticRadix.block q q

abbrev encode (q : ℕ) := Green33QuadraticRadix.encode q q

/-- Over an odd prime field the sum and sum of squares determine an unordered pair. -/
theorem quadratic_pair {q : ℕ} [Fact q.Prime] (hq : 2 < q) (a b c d : ZMod q)
    (hs : a+b=c+d) (hm : a^2+b^2=c^2+d^2) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := Green33QuadraticRadix.quadratic_pair hq a b c d hs hm

/-- Distinct arms still cover the whole d-digit modulus. Their earlier
coordinates merely translate the target for the next pair of progressions. -/
theorem twisted_pair {q s i j l : ℕ} (hs : 0<s) (hij : i<j) (gap : j-i ∣ s)
    (hq : s*l+1=q) (d : ℕ) (a b : ℕ) (z : ℤ) :
    ∃ t u : Fin d → Fin (q+s), ∃ e : ℤ,
      z = encode q s i d a t + (encode q s j d b u : ℤ) + ((q:ℤ)^2)^d*e := Green33QuadraticRadix.twisted_pair q hs hij gap hq d a b z

open Green33StrictReduction Green33Multiplicity

/-- Any finite strict cyclic seed lifts through a d-digit prime radix.
The cardinality grows in degree d while the ordered representation cap
grows only linearly in q for a fixed dimension and seed. -/
theorem finite_lift {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (q l d : ℕ) [Fact q.Prime] (hq : 2<q) (hsq : A.card.factorial<q)
    (form : A.card.factorial*l+1=q) :
    let N : ℕ+ := ⟨M.val*(q^2)^d,by positivity⟩
    ∃ B : Finset (ZMod N), StrictCover B ∧ B.card ≤ A.card*(q+A.card.factorial)^d ∧
      maxReps B ≤ A.card^2*(16*(4*A.card+7))^d*(q+A.card.factorial) := by
  exact Green33QuadraticRadix.finite_lift A hA q q l d 2 hq le_rfl hsq (by omega) form

open Filter
open scoped Topology

/-- A seed-dependent constant controls the peak at the sharper scale
exp(C sqrt(log N)). The same C works for every density tolerance at that seed. -/
theorem seed_sqrt_log {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A) :
    ∃ C : ℝ, 0<C ∧ ∀ ε : ℝ, 0<ε → ∃ᶠ N : ℕ+ in atTop, ∃ B : Finset (ZMod N),
      StrictCover B ∧ (B.card : ℝ)/Real.sqrt N < (A.card : ℝ)/Real.sqrt M+ε ∧
      (maxReps B : ℝ) ≤ Real.exp (C*Real.sqrt (Real.log N)) := by
  let k := A.card
  let s := k.factorial
  let K := 16*(4*k+7)
  let C : ℝ := 2*(k:ℝ)^2+K+1
  let v := (k:ℝ)/Real.sqrt M
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ε hε
  have small : Tendsto (fun q : ℕ => Real.log q/(q:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have lim : Tendsto (fun q : ℕ => v*Real.exp ((s:ℝ)*(Real.log q/q))) atTop (𝓝 v) := by
    simpa using ((small.const_mul (s:ℝ)).rexp).const_mul v
  have lg : Tendsto (fun q : ℕ => Real.log (q:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp ((lim.eventually_lt_const (show v<v+ε by linarith)).and
    (lg.eventually (eventually_ge_atTop 2)))
  apply frequently_atTop.mpr
  intro T
  obtain ⟨q,prime,big,one⟩ := Nat.exists_prime_gt_modEq_one (Q+T.val+s+2) (Nat.factorial_pos k).ne'
  have : Fact q.Prime := ⟨prime⟩
  have hq : 2<q := by omega
  have hsq : s<q := by omega
  obtain ⟨l,hl⟩ := (Nat.modEq_iff_dvd' (by omega : 1≤q)).mp one.symm
  change q-1=s*l at hl
  have form : s*l+1=q := by omega
  obtain ⟨density,Lbig⟩ := hQ q (by omega)
  let L := Real.log (q:ℝ)
  let d := ⌊L⌋₊
  change 2 ≤ L at Lbig
  have dlow : L < (d:ℝ)+1 := Nat.lt_floor_add_one _
  have dup : (d:ℝ) ≤ L := Nat.floor_le (by linarith)
  have dpos : 0<d := by
    by_contra! hh
    have he : d=0 := by omega
    rw [he] at dlow
    norm_num at dlow
    linarith only [Lbig,dlow]
  let N : ℕ+ := ⟨M.val*(q^2)^d,Nat.mul_pos M.pos (pow_pos (pow_pos prime.pos _) _)⟩
  obtain ⟨B,hB,size,peak⟩ := finite_lift A hA q l d hq hsq form
  change B.card ≤ k*(q+s)^d at size
  change maxReps B ≤ k^2*K^d*(q+s) at peak
  have hm : 0<(M:ℝ) := by exact_mod_cast M.pos
  have qp : 0<(q:ℝ) := by exact_mod_cast prime.pos
  have ord : q^(2*d) ≤ N.val := by
    dsimp [N]; rw [pow_mul]; exact Nat.le_mul_of_pos_left _ M.pos
  refine ⟨N,(show T.val ≤ q by omega).trans ((Nat.le_self_pow (by omega) _).trans ord),B,hB,?_,?_⟩
  · have root : Real.sqrt (N:ℝ)=Real.sqrt M*(q:ℝ)^d := by
      change Real.sqrt ((M.val*(q^2)^d:ℕ):ℝ)=_
      push_cast
      rw [Real.sqrt_mul hm.le,←pow_mul,Nat.mul_comm 2 d,pow_mul,Real.sqrt_sq (by positivity)]
    have card : (B.card:ℝ) ≤ (k:ℝ)*((q:ℝ)+s)^d := by exact_mod_cast size
    have hv : 0≤v := div_nonneg (by positivity) (Real.sqrt_nonneg _)
    change (B.card:ℝ)/Real.sqrt (N:ℝ)<v+ε
    rw [root]
    calc
      _ ≤ ((k:ℝ)*((q:ℝ)+s)^d)/(Real.sqrt M*(q:ℝ)^d) := by gcongr
      _ = v*(1+(s:ℝ)/q)^d := by
        have eq : 1+(s:ℝ)/q=((q:ℝ)+s)/q := by field_simp
        rw [eq,div_pow]; dsimp [v]; ring
      _ ≤ v*(Real.exp ((s:ℝ)/q))^d := by
        gcongr; linarith only [Real.add_one_le_exp ((s:ℝ)/q)]
      _ ≤ v*Real.exp ((s:ℝ)*(L/q)) := by
        rw [← Real.exp_nat_mul]
        apply mul_le_mul_of_nonneg_left _ hv
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ L*((s:ℝ)/q) := mul_le_mul_of_nonneg_right dup (by positivity)
          _ = _ := by ring
      _ < _ := density
  · have nreal : ((q:ℝ)^(2*d)) ≤ (N:ℝ) := by exact_mod_cast ord
    have logord := Real.log_le_log (by positivity) nreal
    rw [Real.log_pow] at logord
    push_cast at logord
    change 2*(d:ℝ)*L ≤ Real.log (N:ℝ) at logord
    have sq : L^2 ≤ Real.log (N:ℝ) := by
      have : L ≤ 2*(d:ℝ) := by linarith only [dlow,Lbig]
      nlinarith only [logord,mul_le_mul_of_nonneg_right this (by linarith only [Lbig] : 0≤L)]
    have root := Real.le_sqrt_of_sq_le sq
    have hsize : (maxReps B:ℝ) ≤ (k:ℝ)^2*(K:ℝ)^d*((q:ℝ)+s) := by exact_mod_cast peak
    have h2 : (q:ℝ)+s ≤ 2*q := by exact_mod_cast (show q+s≤2*q by omega)
    have e1 : 2*(k:ℝ)^2 ≤ Real.exp (2*(k:ℝ)^2) := by linarith only [Real.add_one_le_exp (2*(k:ℝ)^2)]
    have e2 : (K:ℝ) ≤ Real.exp K := by linarith only [Real.add_one_le_exp (K:ℝ)]
    calc
      _ ≤ (k:ℝ)^2*(K:ℝ)^d*(2*q) := hsize.trans (by gcongr)
      _ = (2*(k:ℝ)^2)*(K:ℝ)^d*q := by ring
      _ ≤ Real.exp (2*(k:ℝ)^2)*(Real.exp K)^d*q := by gcongr
      _ = Real.exp (2*(k:ℝ)^2+(d:ℝ)*K+L) := by rw [Real.exp_add,Real.exp_add,Real.exp_nat_mul,Real.exp_log qp]
      _ ≤ Real.exp (C*L) := by
        apply Real.exp_le_exp.mpr
        dsimp [C]
        nlinarith only [mul_le_mul_of_nonneg_left (show 1≤L by linarith only [Lbig]) (sq_nonneg (k:ℝ)),
          mul_le_mul_of_nonneg_right dup (Nat.cast_nonneg K)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left root hC.le)

/-- A strict seed keeps its normalized size to any tolerance on arbitrarily
large cyclic lifts whose peak ordered count satisfies any fixed power cap. -/
theorem seed_power_cap {M : ℕ+} (A : Finset (ZMod M)) (hA : StrictCover A)
    (h : ℕ) (ε : ℝ) (hε : 0 < ε) : ∃ᶠ N : ℕ+ in atTop, ∃ B : Finset (ZMod N),
    StrictCover B ∧ (B.card : ℝ)/Real.sqrt N < (A.card : ℝ)/Real.sqrt M+ε ∧
      (maxReps B)^h ≤ N.val := by
  obtain ⟨C,_,lifted⟩ := seed_sqrt_log A hA
  have tend : Tendsto (fun N : ℕ+ => Real.sqrt (Real.log (N:ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop))
  apply ((lifted ε hε).and_eventually (tend.eventually (eventually_ge_atTop ((h:ℝ)*C)))).mono
  rintro N ⟨⟨B,hB,size,cap⟩,large⟩
  refine ⟨B,hB,size,?_⟩
  have hn : 0<(N:ℝ) := by exact_mod_cast N.pos
  have ln : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast N.pos)
  have bound : ((maxReps B:ℝ)^h) ≤ (N:ℝ) := calc
    _ ≤ (Real.exp (C*Real.sqrt (Real.log N)))^h := pow_le_pow_left₀ (by positivity) cap h
    _ = Real.exp ((h:ℝ)*C*Real.sqrt (Real.log N)) := by rw [←Real.exp_nat_mul,mul_assoc]
    _ ≤ Real.exp (Real.log N) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.sqrt (Real.log N)*Real.sqrt (Real.log N) :=
          mul_le_mul_of_nonneg_right large (Real.sqrt_nonneg _)
        _ = _ := Real.mul_self_sqrt ln
    _ = _ := Real.exp_log hn
  exact_mod_cast bound

/-- Green 33 is equivalent to its strict form with subpolynomial peak ordered
representation count: the same witness meets both the size tolerance and
the prescribed power cap at arbitrarily large orders. -/
theorem ordinary_iff_subpower : OrdinaryLimit ↔ ∀ (h : ℕ) (ε : ℝ), 0<ε →
    ∃ᶠ N : ℕ+ in atTop, ∃ B : Finset (ZMod N), StrictCover B ∧
      |(B.card:ℝ)/Real.sqrt N-Real.sqrt 2| < ε ∧ (maxReps B)^h ≤ N.val := by
  constructor
  · intro green h ε hε
    obtain ⟨M,A,hA,small⟩ := ordinary_iff_finite_strict.mp green (ε/2) (by positivity)
    apply (seed_power_cap A hA h (ε/2) (by positivity)).mono
    rintro N ⟨B,hB,size,cap⟩
    have hn : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast N.pos)
    have lo : Real.sqrt 2 ≤ (B.card:ℝ)/Real.sqrt N := (le_div_iff₀ hn).mpr (by linarith only [strict_size_gap hB])
    refine ⟨B,hB,?_,cap⟩
    rw [abs_of_nonneg (sub_nonneg.mpr lo)]
    linarith only [size,small]
  · intro cond
    apply ordinary_iff_strict.mpr
    intro ε hε
    exact (cond 1 ε hε).mono (fun _ ⟨B,hB,size,_⟩ => ⟨B,hB,size⟩)

/-- A single conditional family simultaneously has diverging peak multiplicity
and a peak below every fixed positive power of the cyclic order. -/
theorem subpower_family (green : OrdinaryLimit) :
    ∃ (N : ℕ → ℕ+) (A : (t : ℕ) → Finset (ZMod (N t))),
      Tendsto (fun t => (N t).val) atTop atTop ∧ (∀ t, StrictCover (A t)) ∧
      Tendsto (fun t => ((A t).card:ℝ)/Real.sqrt (N t)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun t => maxReps (A t)) atTop atTop ∧
      ∀ h : ℕ, ∀ᶠ t : ℕ in atTop, (maxReps (A t))^h ≤ (N t).val := by
  have ex (t : ℕ) : ∃ N : ℕ+, t+1≤N.val ∧ ∃ A : Finset (ZMod N),
      StrictCover A ∧ |(A.card:ℝ)/Real.sqrt N-Real.sqrt 2| < 1/((t:ℝ)+1) ∧
        (maxReps A)^t ≤ N.val := by
    have f := ordinary_iff_subpower.mp green t (1/((t:ℝ)+1)) (by positivity)
    exact frequently_atTop.mp f ⟨t+1,by omega⟩
  choose N big A cover err cap using ex
  have tend : Tendsto (fun t => (N t).val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with t ht
    exact ht.trans ((Nat.le_succ _).trans (big t))
  have size : Tendsto (fun t => ((A t).card:ℝ)/Real.sqrt (N t)) atTop (𝓝 (Real.sqrt 2)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using squeeze_zero (fun t => abs_nonneg _)
      (fun t => (err t).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have ordinary (t : ℕ) : A t + A t = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨a,ha,b,hb,_,e⟩ := cover t z
    exact mem_add.mpr ⟨a,ha,b,hb,e⟩
  have divg := tendsto_maxReps_atTop N A tend ordinary size
  refine ⟨N,A,tend,cover,size,divg,?_⟩
  intro h
  filter_upwards [eventually_ge_atTop h,divg.eventually (eventually_ge_atTop 1)] with t ht hpos
  exact (Nat.pow_le_pow_right hpos ht).trans (cap t)

#print axioms subpower_family
#print axioms ordinary_iff_subpower
#print axioms seed_sqrt_log
#print axioms seed_power_cap
#print axioms finite_lift
#print axioms twisted_pair
#print axioms quadratic_pair

end Green33SubpowerRepresentations
