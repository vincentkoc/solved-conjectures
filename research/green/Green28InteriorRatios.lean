import Green28ReversalField
import Mathlib.RingTheory.EuclideanDomain

/-! Rational arithmetic of two polynomial families of marginal distributions. -/

namespace Green28InteriorRatios

open Finset Polynomial Green28PolynomialReduction Green28ReversalField Green28RootLocation
open scoped Polynomial

private noncomputable abbrev realMap : ℚ →+* ℝ := algebraMap ℚ ℝ

private theorem realMap_apply (q : ℚ) : realMap q = (q:ℝ) := rfl

/-- A rational product gives a genuine quadratic relation and fixes the
linear coefficient polynomial by comparing the rational and irrational parts. -/
theorem separate_coefficients (u : ℝ) (irr : ¬∃ q : ℚ, (q:ℝ) = u)
    (J K T : ℚ[X]) (nz : K ≠ 0)
    (eq : C u*(J.map (algebraMap ℚ ℝ))-C (u^2)*(K.map (algebraMap ℚ ℝ)) = T.map (algebraMap ℚ ℝ)) :
    ∃ a b : ℚ, u^2 = (a:ℝ)*u+(b:ℝ) ∧ J = C a*K := by
  classical
  let n := K.natDegree
  have kn : K.coeff n ≠ 0 := by simpa [n,coeff_natDegree] using (leadingCoeff_ne_zero.mpr nz)
  let a := J.coeff n/K.coeff n
  let b := -T.coeff n/K.coeff n
  have co (i : ℕ) : u*(J.coeff i:ℝ)-u^2*(K.coeff i:ℝ) = (T.coeff i:ℝ) := by
    have h := congrArg (fun P : ℝ[X] => P.coeff i) eq
    simp only [coeff_sub,coeff_C_mul,coeff_map] at h
    exact h
  have rel : u^2 = (a:ℝ)*u+(b:ℝ) := by
    dsimp [a,b]
    push_cast
    field_simp [show (K.coeff n:ℝ) ≠ 0 by exact_mod_cast kn]
    linarith [co n]
  refine ⟨a,b,rel,?_⟩
  ext i
  rw [coeff_C_mul]
  by_contra diff
  have val := co i
  rw [rel] at val
  have denom : (J.coeff i-a*K.coeff i:ℚ) ≠ 0 := sub_ne_zero.mpr diff
  apply irr
  refine ⟨(T.coeff i+b*K.coeff i)/(J.coeff i-a*K.coeff i),?_⟩
  push_cast
  apply (div_eq_iff (by exact_mod_cast denom)).mpr
  linarith

/-- A normalized deficient coefficient has no quadratic relation of trace
one over the rationals, by integrality of its product with its complement. -/
theorem trace_ne_one {u : ℝ} (lo : 0 < u) (hi : u < 1) (integ : IsIntegral ℤ u)
    {a b : ℚ} (rel : u^2 = (a:ℝ)*u+(b:ℝ)) : a ≠ 1 := by
  rintro rfl
  have eq : (b:ℝ) = u*(u-1) := by push_cast at rel; linarith
  have ir : IsIntegral ℤ (algebraMap ℚ ℝ b) := by
    change IsIntegral ℤ (b:ℝ)
    rw [eq]
    exact integ.mul (integ.sub isIntegral_one)
  have iq : IsIntegral ℤ b := (isIntegral_algebraMap_iff (B:=ℝ) (algebraMap ℚ ℝ).injective).mp ir
  obtain ⟨z,hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R:=ℤ) (K:=ℚ)).mp iq
  have realZ : (z:ℝ) = (b:ℝ) := by exact_mod_cast hz
  have neg : (z:ℝ) < 0 := by rw [realZ,eq]; exact mul_neg_of_pos_of_neg lo (by linarith)
  have lower : (-1:ℝ)<(z:ℝ) := by rw [realZ,eq]; nlinarith [sq_nonneg u]
  have zn : z < 0 := by exact_mod_cast neg
  have zl : (-1:ℤ) < z := by exact_mod_cast lower
  omega

/-- Remove the common polynomial denominator in the two rational-function
expressions. The two numerator polynomials differ by a scalar multiple of
the gcd of the interior shapes. -/
theorem reduce_shapes (A B L M : ℚ[X]) (ln : L ≠ 0) (mn : M ≠ 0)
    (lz : L.coeff 0 = 0) (mz : M.coeff 0 = 0) (c : ℚ) (eq : L*B-M*A = C c*L*M) :
    ∃ G U V P Q : ℚ[X], G ≠ 0 ∧ U ≠ 0 ∧ V ≠ 0 ∧ G.coeff 0 = 0 ∧ L = U*G ∧ M = V*G ∧
      A = U*P ∧ B = V*Q ∧ Q-P = C c*G := by
  let G := GCDMonoid.gcd L M
  let U := L/G
  let V := M/G
  have gn : G ≠ 0 := fun z => ln (zero_dvd_iff.mp (z ▸ (GCDMonoid.gcd_dvd_left L M : G ∣ L)))
  have lp : L = U*G := by rw [mul_comm]; exact (EuclideanDomain.mul_div_cancel' gn (GCDMonoid.gcd_dvd_left _ _)).symm
  have mp : M = V*G := by rw [mul_comm]; exact (EuclideanDomain.mul_div_cancel' gn (GCDMonoid.gcd_dvd_right _ _)).symm
  have cop : IsCoprime U V := isCoprime_div_gcd_div_gcd mn
  have un : U ≠ 0 := fun z => ln (by rw [lp,z,zero_mul])
  have vn : V ≠ 0 := fun z => mn (by rw [mp,z,zero_mul])
  have zero : G.coeff 0 = 0 := X_dvd_iff.mp (GCDMonoid.dvd_gcd (X_dvd_iff.mpr lz) (X_dvd_iff.mpr mz))
  have cancel : U*B-V*A = C c*U*V*G := by
    apply mul_right_cancel₀ gn
    rw [lp,mp] at eq
    linear_combination eq
  have ud : U ∣ V*A := ⟨B-C c*V*G,by linear_combination -cancel⟩
  have vd : V ∣ U*B := ⟨A+C c*U*G,by linear_combination cancel⟩
  obtain ⟨P,ap⟩ := cop.dvd_of_dvd_mul_left ud
  obtain ⟨Q,bq⟩ := cop.symm.dvd_of_dvd_mul_left vd
  refine ⟨G,U,V,P,Q,gn,un,vn,zero,lp,mp,ap,bq,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero un vn)
  rw [ap,bq] at cancel
  linear_combination cancel

/-- The scalar of reversal for a real polynomial whose roots all have
modulus one is its constant coefficient divided by its leading coefficient. -/
private theorem unit_reverse {p : ℝ[X]} (pn : p ≠ 0)
    (unit : ∀ z : ℂ, (p.map Complex.ofRealHom).eval z = 0 → ‖z‖=1) :
    p.reverse = C (p.coeff 0 / p.leadingCoeff)*p := by
  let t := p.leadingCoeff⁻¹
  have nt : t ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.mpr pn)
  have eq := reverse_eq_scaled_of_unit_roots (p*C t) (monic_mul_leadingCoeff_inv pn) (by
    intro z hz
    apply unit
    have h := (mem_roots'.mp hz).2
    simpa [IsRoot.def,Polynomial.map_mul,Polynomial.map_C,nt] using h)
  rw [reverse_mul_of_domain,reverse_C,mul_coeff_zero,coeff_C_zero] at eq
  apply mul_right_cancel₀ (C_ne_zero.mpr nt : (C t : ℝ[X]) ≠ 0)
  simpa only [div_eq_mul_inv,mul_assoc] using eq

/-- Shapes which differ only in lower-degree terms have the same
reversal scalar when their roots lie on the unit circle and their
constant coefficients agree. Every point of their affine line inherits it. -/
private theorem line_reverse {P G : ℝ[X]} (short : G.natDegree < P.natDegree)
    (zero : G.coeff 0 = 0) {c : ℝ} (cn : c ≠ 0)
    (unitP : ∀ z : ℂ, (P.map Complex.ofRealHom).eval z = 0 → ‖z‖=1)
    (unitQ : ∀ z : ℂ, ((P+C c*G).map Complex.ofRealHom).eval z = 0 → ‖z‖=1) (u : ℝ) :
    (P+C u*G).reverse = C (P.coeff 0/P.leadingCoeff)*(P+C u*G) := by
  have sh (v : ℝ) := (natDegree_C_mul_le v G).trans_lt short
  have nd (v : ℝ) := natDegree_add_eq_left_of_natDegree_lt (sh v)
  have pos : 0 < P.natDegree := lt_of_le_of_lt (Nat.zero_le _) short
  have pn : P ≠ 0 := fun h => by simp [h] at pos
  have qn : P+C c*G ≠ 0 := fun h => by simpa [h] using (nd c ▸ pos : 0<(P+C c*G).natDegree)
  have pr := unit_reverse pn unitP
  have qr := unit_reverse qn unitQ
  rw [coeff_add,coeff_C_mul,zero,mul_zero,add_zero,
    leadingCoeff_add_of_degree_lt' (degree_lt_degree (sh c))] at qr
  rw [reverse,nd,reflect_add,reflect_C_mul] at qr
  rw [reverse] at pr
  rw [pr] at qr
  rw [reverse,nd,reflect_add,reflect_C_mul,pr]
  have gr : reflect P.natDegree G = C (P.coeff 0/P.leadingCoeff)*G := by
    apply mul_left_cancel₀ (C_ne_zero.mpr cn)
    linear_combination qr
  rw [gr]
  ring

/-- Reversal forces both factors to have binary coefficients when their
rational endpoint shapes have all roots on the unit circle and their
remaining coefficients lie on complementary rational rays. -/
theorem binary_of_shapes {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1)
    (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i) (bin : Binary (f*g))
    (A B L M : ℚ[X]) (ln : L ≠ 0) (mn : M ≠ 0)
    (lz : L.coeff 0 = 0) (mz : M.coeff 0 = 0) (short : L.natDegree < A.natDegree)
    (unitA : ∀ z : ℂ, ((A.map (algebraMap ℚ ℝ)).map Complex.ofRealHom).eval z = 0 → ‖z‖=1)
    (unitB : ∀ z : ℂ, ((B.map (algebraMap ℚ ℝ)).map Complex.ofRealHom).eval z = 0 → ‖z‖=1)
    {u : ℝ} (lo : 0 < u) (hi : u < 1) (integ : IsIntegral ℤ u)
    (ef : f = A.map (algebraMap ℚ ℝ)+C u*(L.map (algebraMap ℚ ℝ)))
    (eg : g = B.map (algebraMap ℚ ℝ)+C (1-u)*(M.map (algebraMap ℚ ℝ))) : Binary f ∧ Binary g := by
  classical
  by_cases rat : ∃ q : ℚ, (q:ℝ) = u
  · obtain ⟨q,rfl⟩ := rat
    apply rational_factor fm gm fp gp bin
    intro i
    exact ⟨A.coeff i+q*L.coeff i,by simp [ef,coeff_C_mul,coeff_map]⟩
  obtain ⟨H,hH⟩ : ∃ H : ℚ[X], H.map realMap = f*g := by
    apply (Polynomial.mem_lifts (f:=realMap) _).mp
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro i
    rcases bin i with h|h
    · exact ⟨0,by simp [h]⟩
    · exact ⟨1,by simp [h]⟩
  let J := L*B-M*A+L*M
  have sep : C u*(J.map realMap)-C (u^2)*((L*M).map realMap) = (H-A*(B+M)).map realMap := by
    simp only [J,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_add,hH,ef,eg,map_sub,map_one,map_pow]
    ring
  obtain ⟨a,b,rel,prop⟩ := separate_coefficients u rat _ _ _ (mul_ne_zero ln mn) sep
  let c := a-1
  have cn : c ≠ 0 := sub_ne_zero.mpr (trace_ne_one lo hi integ rel)
  have eq : L*B-M*A = C c*L*M := by
    dsimp [J] at prop
    simp only [c,map_sub,map_one]
    linear_combination prop
  obtain ⟨G,U,V,P,Q,gn,un,_,gz,lp,_,ap,bq,pq⟩ :=
    reduce_shapes A B L M ln mn lz mz c eq
  have an : A ≠ 0 := fun h => by simp [h] at short
  have pn : P ≠ 0 := fun h => an (by simp [ap,h])
  rw [ap,lp,natDegree_mul un pn,natDegree_mul un gn] at short
  have sh : (G.map realMap).natDegree<(P.map realMap).natDegree := by
    simp only [natDegree_map_eq_of_injective realMap.injective]; omega
  have qp : Q = P+C c*G := by linear_combination pq
  have up : ∀ z : ℂ, ((P.map realMap).map Complex.ofRealHom).eval z = 0 → ‖z‖=1 := by
    intro z root
    apply unitA
    simp only [ap,Polynomial.map_mul,eval_mul,root,mul_zero]
  have uq : ∀ z : ℂ, ((P.map realMap+C (c:ℝ)*(G.map realMap)).map Complex.ofRealHom).eval z = 0 → ‖z‖=1 := by
    intro z root
    apply unitB
    simp only [bq,qp,Polynomial.map_mul,Polynomial.map_add,Polynomial.map_C,eval_mul,eval_add,eval_C,realMap_apply] at root ⊢
    rw [root,mul_zero]
  have mirror := line_reverse sh (by simp [coeff_map,gz]) (by exact_mod_cast cn : (c:ℝ) ≠ 0) up uq u
  apply binary_of_rational_times_reciprocal fm gm fc gc fp gp bin
    (L:=U.map realMap) (R:=P.map realMap+C u*(G.map realMap)) (c:=P.coeff 0/P.leadingCoeff)
  · rw [ef,ap,lp,Polynomial.map_mul,Polynomial.map_mul]; ring
  · intro i; exact ⟨U.coeff i,(coeff_map _ _).symm⟩
  · simpa only [leadingCoeff_map_of_injective realMap.injective,coeff_map,realMap_apply,Rat.cast_div] using mirror

private noncomputable def ends (d : ℕ) : ℚ[X] := X^d+1

private theorem ends_degree (d : ℕ) : (ends d).natDegree = d := by
  simpa only [ends,map_one] using (natDegree_X_pow_add_C (n:=d) (r:=(1:ℚ)))

private theorem ends_roots {d : ℕ} (hd : 0 < d) (z : ℂ)
    (hz : (((ends d).map realMap).map Complex.ofRealHom).eval z = 0) : ‖z‖=1 := by
  have eq : z^d = -1 := by simpa [ends,eq_neg_iff_add_eq_zero] using hz
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hd.ne').mp (by simpa using congrArg norm eq)

private def CoeffRatios (f : ℝ[X]) : Prop :=
  ∀ i j : ℕ, 0 < i → i < f.natDegree → 0 < j → j < f.natDegree → f.coeff j ≠ 0 →
    ∃ q : ℚ, f.coeff i = (q:ℝ)*f.coeff j

private theorem interior_shape {f : ℝ[X]} (fm : f.Monic) (fc : f.coeff 0 = 1)
    (rat : CoeffRatios f) {j : ℕ} (jp : 0 < j) (jl : j < f.natDegree) (nz : f.coeff j ≠ 0) :
    ∃ L : ℚ[X], L ≠ 0 ∧ L.coeff 0 = 0 ∧ L.natDegree < f.natDegree ∧
      f = (ends f.natDegree).map realMap+C (f.coeff j)*(L.map realMap) := by
  let d := f.natDegree
  let u := f.coeff j
  let E := (ends d).map realMap
  let W := C u⁻¹*(f-E)
  have dp : 0 < d := jp.trans jl
  have ec (i : ℕ) : E.coeff i = (if i = d then 1 else 0)+(if i = 0 then 1 else 0) := by
    simp [E,ends,coeff_one,coeff_X_pow]
  have wc (i : ℕ) : W.coeff i = u⁻¹*(f.coeff i-E.coeff i) := by simp [W,coeff_C_mul]
  have zero : W.coeff 0 = 0 := by simp [wc,ec,fc,dp.ne]
  have high (i : ℕ) (hi : d ≤ i) : W.coeff i = 0 := by
    rcases eq_or_lt_of_le hi with rfl|hi
    · simp [wc,ec,d,fm.coeff_natDegree,dp.ne']
    · simp [wc,ec,coeff_eq_zero_of_natDegree_lt (p:=f) hi,hi.ne', (dp.trans hi).ne']
  have inner (i : ℕ) (ip : 0 < i) (il : i < d) : W.coeff i = u⁻¹*f.coeff i := by
    simp [wc,ec,ip.ne',il.ne]
  obtain ⟨L,leq⟩ : ∃ L : ℚ[X], L.map realMap = W := by
    apply (Polynomial.mem_lifts (f:=realMap) _).mp
    apply (Polynomial.lifts_iff_coeff_lifts _).mpr
    intro i
    rcases Nat.eq_zero_or_pos i with rfl|ip
    · exact ⟨0,by simp [zero]⟩
    by_cases il : i < d
    · obtain ⟨q,hq⟩ := rat i j ip il jp jl nz
      exact ⟨q,by rw [inner i ip il,hq]; change (q:ℝ) = u⁻¹*((q:ℝ)*u); field_simp [show u ≠ 0 from nz]⟩
    · exact ⟨0,by simp [high i (le_of_not_gt il)]⟩
  have get (i : ℕ) : (L.coeff i:ℝ) = W.coeff i := by
    rw [←leq,coeff_map]; rfl
  have ln : L ≠ 0 := by
    intro h
    have e := get j
    rw [h,coeff_zero,inner j jp jl] at e
    exact (mul_ne_zero (inv_ne_zero nz) nz) (by simpa only [Rat.cast_zero] using e.symm)
  refine ⟨L,ln,by exact_mod_cast (get 0).trans zero,?_,?_⟩
  · by_contra! large
    have h := (get L.natDegree).trans (high _ large)
    exact (leadingCoeff_ne_zero.mpr ln) (by exact_mod_cast h : L.coeff L.natDegree = 0)
  · change f = E+C u*(L.map realMap)
    rw [leq,show W = C u⁻¹*(f-E) from rfl,←mul_assoc,←map_mul,mul_inv_cancel₀ (show u ≠ 0 from nz),map_one,one_mul]
    ring

private theorem first_sum {f g : ℝ[X]} (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1)
    {j : ℕ} (jp : 0 < j) (prior : ∀ i, 0 < i → i < j → f.coeff i = 0) :
    (f*g).coeff j = f.coeff j+g.coeff j := by
  have eq : ((f-1)*g).coeff j = (f-1).coeff j*g.coeff 0 := by
    rw [coeff_mul,Finset.sum_eq_single_of_mem (j,0) (mem_antidiagonal.mpr (Nat.add_zero j))]
    rintro ⟨a,b⟩ mem ne
    have ab : a+b = j := mem_antidiagonal.mp mem
    have lt : a < j := by
      by_contra! opp
      exact ne (Prod.ext (by change a = j; omega) (by change b = 0; omega))
    rcases Nat.eq_zero_or_pos a with rfl|ap
    · simp [fc]
    · simp [prior a ap lt,coeff_one,ap.ne']
  rw [sub_mul,one_mul,coeff_sub,coeff_sub,coeff_one,if_neg jp.ne',sub_zero,gc,mul_one] at eq
  linarith

private theorem exists_interior {f : ℝ[X]} (fm : f.Monic) (fc : f.coeff 0 = 1) (bad : ¬Binary f) :
    ∃ i : ℕ, 0 < i ∧ i < f.natDegree ∧ f.coeff i ≠ 0 := by
  by_contra! h
  apply bad
  intro i
  rcases Nat.eq_zero_or_pos i with rfl|ip
  · exact Or.inr fc
  rcases lt_trichotomy i f.natDegree with il|rfl|above
  · exact Or.inl (h i ip il)
  · exact Or.inr fm.coeff_natDegree
  · exact Or.inl (coeff_eq_zero_of_natDegree_lt above)

private theorem irrational_inside {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic) (fc : f.coeff 0 = 1)
    (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i) (bin : Binary (f*g))
    (rat : CoeffRatios f) (bad : ¬Binary f) {j : ℕ} (jp : 0 < j) (jl : j < f.natDegree) :
    f.coeff j ≠ 1 := by
  intro h
  apply bad
  apply (rational_factor fm gm fp gp bin ?_).1
  intro i
  rcases Nat.eq_zero_or_pos i with rfl|ip
  · exact ⟨1,by simp [fc]⟩
  rcases lt_trichotomy i f.natDegree with il|rfl|above
  · obtain ⟨q,e⟩ := rat i j ip il jp jl (h ▸ one_ne_zero)
    exact ⟨q,by simpa [h] using e.symm⟩
  · exact ⟨1,by simp [fm.coeff_natDegree]⟩
  · exact ⟨0,by simp [coeff_eq_zero_of_natDegree_lt above]⟩

private theorem binary_interiors {f g : ℝ[X]} (fm : f.Monic) (gm : g.Monic)
    (fc : f.coeff 0 = 1) (gc : g.coeff 0 = 1)
    (fp : ∀ i, 0 ≤ f.coeff i) (gp : ∀ i, 0 ≤ g.coeff i) (bin : Binary (f*g))
    (fr : CoeffRatios f) (gr : CoeffRatios g) : Binary f ∧ Binary g := by
  classical
  have flip : Binary (g*f) := mul_comm f g ▸ bin
  have ratOf {p : ℝ[X]} (bp : Binary p) (i : ℕ) : ∃ q : ℚ, (q:ℝ) = p.coeff i := by
    rcases bp i with h|h
    · exact ⟨0,by simp [h]⟩
    · exact ⟨1,by simp [h]⟩
  by_cases bf : Binary f
  · exact rational_factor fm gm fp gp bin (ratOf bf)
  by_cases bg : Binary g
  · exact (rational_factor gm fm gp fp flip (ratOf bg)).symm
  obtain ⟨i,ip,il,inon⟩ := exists_interior fm fc bf
  obtain ⟨k,kp,kl,knon⟩ := exists_interior gm gc bg
  let active (n : ℕ) := 0 < n ∧ (f.coeff n ≠ 0 ∨ g.coeff n ≠ 0)
  have any : ∃ n, active n := ⟨i,ip,Or.inl inon⟩
  let j := Nat.find any
  obtain ⟨jp,jn⟩ := (Nat.find_spec any : active j)
  have jf : j < f.natDegree := (Nat.find_min' any (show active i from ⟨ip,Or.inl inon⟩)).trans_lt il
  have jg : j < g.natDegree := (Nat.find_min' any (show active k from ⟨kp,Or.inr knon⟩)).trans_lt kl
  have first := first_sum fc gc jp (fun n np nj => by
    by_contra hn; exact Nat.find_min any nj (show active n from ⟨np,Or.inl hn⟩))
  have total : f.coeff j+g.coeff j = 1 := by
    rcases bin j with e|e
    · rw [first] at e
      rcases jn with h|h
      · exact (h (by linarith [fp j,gp j])).elim
      · exact (h (by linarith [fp j,gp j])).elim
    · exact first ▸ e
  have fu := irrational_inside fm gm fc fp gp bin fr bf jp jf
  have gu := irrational_inside gm fm gc gp fp flip gr bg jp jg
  have fnz : f.coeff j ≠ 0 := fun h => gu (by linarith)
  have gnz : g.coeff j ≠ 0 := fun h => fu (by linarith)
  obtain ⟨L,ln,lz,ls,fe⟩ := interior_shape fm fc fr jp jf fnz
  obtain ⟨M,mn,mz,_,ge⟩ := interior_shape gm gc gr jp jg gnz
  exact binary_of_shapes fm gm fc gc fp gp bin _ _ _ _ ln mn lz mz (by rwa [ends_degree])
    (ends_roots (jp.trans jf)) (ends_roots (jp.trans jg))
    (lt_of_le_of_ne (fp j) fnz.symm) (by linarith [lt_of_le_of_ne (gp j) gnz.symm])
    (integral_coefficient fm gm bin j) fe (by rwa [show 1-f.coeff j = g.coeff j by linarith])

open Green28 Green28UniformSums Green28PrimitiveSupport

/-- Positive masses strictly between two occupied sites have rational ratios.
The probabilities at the two outermost sites need not enter these ratios. -/
def InteriorRatios (P : PMF ℤ) : Prop :=
  ∀ a ∈ P.support, ∀ b ∈ P.support, ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b,
    y ∈ P.support → ∃ q : ℚ, (P x).toReal = (q:ℝ)*(P y).toReal

private theorem ratios_of_model {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (model : Models P f a s) (fm : f.Monic) (fc : f.coeff 0 = 1) (rat : InteriorRatios P) :
    CoeffRatios f := by
  have occ (i : ℕ) (nz : f.coeff i ≠ 0) : a+(i:ℤ) ∈ P.support := by
    apply (P.mem_support_iff _).mpr
    intro h
    have e := model.coeff i
    rw [h,ENNReal.toReal_zero] at e
    exact mul_ne_zero model.pos.ne' nz e.symm
  intro i j ip il jp jl nz
  have am : a ∈ P.support := by simpa using occ 0 (fc ▸ one_ne_zero)
  obtain ⟨q,e⟩ := rat a am _ (occ f.natDegree (fm.coeff_natDegree ▸ one_ne_zero))
    (a+i) ⟨by omega,by omega⟩ (a+j) ⟨by omega,by omega⟩ (occ j nz)
  rw [model.coeff,model.coeff] at e
  exact ⟨q,mul_left_cancel₀ model.pos.ne' (by linear_combination e)⟩

/-- Green 28 for laws of arbitrary support size and width whose strictly
interior atom masses are pairwise rationally proportional within each law. -/
theorem uniform_of_interior_ratios {P Q : PMF ℤ} (flat : IsUniformOnSupport (indepSum P Q))
    (pr : InteriorRatios P) (qr : InteriorRatios Q) : IsUniformOnSupport P ∧ IsUniformOnSupport Q := by
  obtain ⟨S,ne,sum⟩ := flat
  obtain ⟨f,g,_,_,_,_,pf,pg,fm,gm,_,_,fc,gc,_⟩ := mask_factorization ne sum
  have bin := ((pf.mul pg).uniform_iff (fm.mul gm)).mp ⟨S,ne,sum⟩
  obtain ⟨fb,gb⟩ := binary_interiors fm gm fc gc pf.nonneg pg.nonneg bin
    (ratios_of_model pf fm fc pr) (ratios_of_model pg gm gc qr)
  exact ⟨(pf.uniform_iff fm).mpr fb,(pg.uniform_iff gm).mpr gb⟩

/-- Extract the rational interior shape at any occupied interior offset of
the normalized model. This statement concerns just one marginal. -/
theorem shape_of_interior_ratios {P : PMF ℤ} {f : ℝ[X]} {a : ℤ} {s : ℝ}
    (model : Models P f a s) (fm : f.Monic) (fc : f.coeff 0 = 1) (rat : InteriorRatios P)
    {j : ℕ} (jp : 0 < j) (jl : j < f.natDegree) (nz : f.coeff j ≠ 0) :
    ∃ L : ℚ[X], L ≠ 0 ∧ L.coeff 0 = 0 ∧ L.natDegree < f.natDegree ∧
      f = X^f.natDegree+1+C (f.coeff j)*(L.map (algebraMap ℚ ℝ)) := by
  simpa only [ends,Polynomial.map_add,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_one] using
    interior_shape fm fc (ratios_of_model model fm fc rat) jp jl nz

#print axioms separate_coefficients
#print axioms trace_ne_one
#print axioms reduce_shapes
#print axioms binary_of_shapes
#print axioms uniform_of_interior_ratios
#print axioms shape_of_interior_ratios
end Green28InteriorRatios
