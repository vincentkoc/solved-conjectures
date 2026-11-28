import CunninghamLogarithmicReturnCounts

/-! From counts in the progression parameter to Dirichlet mass on the prime seeds. -/

namespace CunninghamChain.OrbitIsolation
open Finset Filter Topology Real PrimeMass

def returningClass (c : ℝ) (W A : ℕ) : Set ℕ :=
  {p | W<p ∧ p ≡ A [MOD W] ∧ EarlyReturn c p}

def isolatedClass (c : ℝ) (W A : ℕ) : Set ℕ :=
  {p | p.Prime ∧ p ≡ A [MOD W] ∧ ¬EarlyReturn c p}

private lemma weight_sum_to_parameters (c : ℝ) {W A : ℕ} (ap : A<W) (N : ℕ) :
    ∑ p∈range N, weight (returningClass c W A) p ≤
      ((returningParameters c A W (N/W+1)).card:ℝ)*log N := by
  classical
  let P := (range N).filter fun p => p.Prime ∧ p∈returningClass c W A
  have val {p : ℕ} (hp : p∈P) : A+W*(p/W)=p := by
    have eq := (mem_filter.mp hp).2.2.2.1
    change p%W=A%W at eq
    rw [Nat.mod_eq_of_lt ap] at eq
    rw [←eq]
    exact Nat.mod_add_div ..
  have card : P.card ≤ (returningParameters c A W (N/W+1)).card := by
    apply card_le_card_of_injOn (fun p => p/W)
    · intro p hp
      obtain ⟨bound,pr,large,_,ret⟩ := mem_filter.mp hp
      apply mem_filter.mpr
      exact ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp bound).le)),
        by simpa only [val hp] using pr,by simpa only [val hp] using large,by simpa only [val hp] using ret⟩
    · intro p hp q hq eq
      exact (val hp).symm.trans ((congrArg (fun t => A+W*t) eq).trans (val hq))
  have eq : ∑ p∈range N, weight (returningClass c W A) p = ∑ p∈P, log p := by simp only [P,sum_filter,weight]
  have ln : 0≤log (N:ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl|pn
    · simp
    · exact log_nonneg (by exact_mod_cast pn)
  rw [eq]
  calc _ ≤ ∑ _p∈P, log (N:ℝ) := by
            apply sum_le_sum
            intro p hp
            exact Real.log_le_log (by exact_mod_cast (mem_filter.mp hp).2.1.pos)
              (by exact_mod_cast (mem_range.mp (mem_filter.mp hp).1).le)
       _ ≤ _ := by simpa only [sum_const,nsmul_eq_mul] using
                      mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr card) ln

theorem weight_bound_of_parameter_bound {c δ : ℝ} (hd : 0≤δ) {W A : ℕ} (wp : 0<W) (ap : A<W)
    (par : ∀ᶠ X : ℕ in atTop, ((returningParameters c A W X).card:ℝ)*log X≤δ*X) :
    ∀ᶠ N : ℕ in atTop, ∑ p∈range N,weight (returningClass c W A) p ≤ (4*δ/(W:ℝ))*N := by
  obtain ⟨X0,good⟩ := eventually_atTop.mp par
  filter_upwards [eventually_ge_atTop ((X0+W+2)*W)] with N large
  let X := N/W+1
  have big := (Nat.le_div_iff_mul_le wp).mpr large
  have parBound := good X (by dsimp [X]; omega)
  have norm : W≤N := by
    have := Nat.le_mul_of_pos_left W (show 0<X0+W+2 by omega)
    omega
  have pos := wp.trans_le norm
  have sq : N≤X^2 := by
    have cut := Nat.lt_mul_div_succ N wp
    change N < W*X at cut
    have wx : W≤X := by dsimp [X]; omega
    nlinarith [Nat.mul_le_mul_right X wx]
  have logBound : log (N:ℝ)≤2*log (X:ℝ) := by
    calc _ ≤ log ((X:ℝ)^2) := Real.log_le_log (by exact_mod_cast pos) (by exact_mod_cast sq)
         _ = _ := by rw [Real.log_pow]; norm_num
  have wpos : 0<(W:ℝ) := by exact_mod_cast wp
  have xle : (X:ℝ)≤2*N/W := by
    have div : ((N/W:ℕ):ℝ)≤(N:ℝ)/W := Nat.cast_div_le
    have rat : (1:ℝ)≤N/W := (one_le_div wpos).mpr (by exact_mod_cast norm)
    dsimp [X]
    push_cast
    rw [mul_div_assoc]
    linarith only [div,rat]
  apply (weight_sum_to_parameters c ap N).trans
  change ((returningParameters c A W X).card:ℝ)*log N ≤ _
  let M : ℝ := (returningParameters c A W X).card
  calc _ ≤ 2*(M*log X) := by
            have h := mul_le_mul_of_nonneg_left logBound (show 0≤M by dsimp [M]; positivity)
            linarith only [h]
       _ ≤ 2*(δ*X) := by linarith only [parBound]
       _ ≤ 2*(δ*(2*N/W)) := by gcongr
       _ = _ := by ring

/-- On a suitably chosen prime progression the simultaneous vacant window
through c log p occupies at least a prescribed fraction of the progression's
normalized log-weighted Dirichlet mass near one. -/
theorem joint_isolation_progression_mass {c ε : ℝ} (hc : 0≤c) (he : 0<ε) :
    ∃ W A : ℕ, 0<W ∧ A<W ∧ A.Coprime W ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      (1-ε)/(W.totient:ℝ) ≤ (s-1)*mass (isolatedClass c W A) s := by
  classical
  obtain ⟨W,A,wp,ap,unit,params⟩ := sparse_returning_parameters hc (by positivity : 0<ε/32)
  let : NeZero W := ⟨wp.ne'⟩
  let u : ℝ := (W.totient:ℝ)⁻¹
  have tp : 0<(W.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr wp
  have up : 0<u := inv_pos.mpr tp
  have wide : (W:ℝ)⁻¹ ≤ u := inv_anti₀ tp (by exact_mod_cast Nat.totient_le W)
  let E := returningClass c W A
  let G := isolatedClass c W A
  let small := Set.Iic W
  let P := {p : ℕ | (p:ZMod W)=(A:ZMod W)}
  have pLimit := PrimeMass.mass_progression (A:ZMod W) ((ZMod.isUnit_iff_coprime ..).mpr unit)
  have pLow := pLimit.eventually_const_lt (show (1-ε/3)*u < (W.totient:ℝ)⁻¹ by dsimp [u]; nlinarith)
  have sLow := (finite_mass_tendsto (Set.finite_Iic W)).eventually_lt_const (show 0<ε*u/3 by positivity)
  have bound := weight_bound_of_parameter_bound (by positivity) wp ap params
  have hi : 4*(ε/32)/(W:ℝ) < ε*u/3 := by
    have t := mul_le_mul_of_nonneg_left wide he.le
    rw [div_eq_mul_inv]
    nlinarith only [t,mul_pos he up]
  have rem := eventually_mass_lt_of_sum_le E (by positivity) hi bound
  refine ⟨W,A,wp,ap,unit,?_⟩
  filter_upwards [pLow,sLow,rem,self_mem_nhdsWithin] with s pl sl el hs
  change 1<s at hs
  have union : ∀ p∈P, p.Prime → (∃ _i∈({()} : Finset Unit), p∈G) ∨ p∈E ∨ p∈small := by
    intro p hp prime
    have cl : p ≡ A [MOD W] := (ZMod.natCast_eq_natCast_iff ..).mp hp
    by_cases early : EarlyReturn c p
    · by_cases big : W<p
      · exact Or.inr (Or.inl ⟨big,cl,early⟩)
      · exact Or.inr (Or.inr (show p≤W by omega))
    · exact Or.inl ⟨(),mem_singleton_self _,prime,cl,early⟩
  have cover := mass_le_cover {()} (fun _ => G) P E small union hs
  simp only [sum_singleton] at cover
  have sum := mul_le_mul_of_nonneg_left cover (sub_nonneg.mpr hs.le)
  change (1-ε/3)*u < (s-1)*mass P s at pl
  change (s-1)*mass small s<ε*u/3 at sl
  change (s-1)*mass E s<ε*u/3 at el
  change (1-ε)/(W.totient:ℝ)≤(s-1)*mass G s
  rw [div_eq_mul_inv]
  change (1-ε)*u≤_
  linarith only [pl,sl,el,sum]

#print axioms weight_bound_of_parameter_bound
#print axioms joint_isolation_progression_mass

end CunninghamChain.OrbitIsolation
