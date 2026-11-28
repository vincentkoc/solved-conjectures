import CunninghamDyadicSpacing
import CunninghamPairedGaps
import FormalConjectures.Wikipedia.BatemanHornConjecture

/-! A fixed two-form instance of Bateman–Horn supplies the dyadic primitive-root input. -/

namespace CunninghamChain.DyadicSpacing

open Polynomial Finset Filter Real Asymptotics BatemanHornConjecture ArtinPrimitiveRootsConjecture
open scoped Topology

private noncomputable def line (a b : ℤ) : ℤ[X] := C a * X + C b
private noncomputable def forms : Finset ℤ[X] := {line 4 1,line 8 3}

private noncomputable def parameters (x : ℝ) : Finset ℕ :=
  (range (⌊x⌋₊+1)).filter (fun n => (4*n+1).Prime ∧ (8*n+3).Prime)

private theorem scaled_count (hBH : type_of% @bateman_horn_conjecture) :
    ∃ c : ℝ, 0 < c ∧ (fun x : ℝ => ((parameters x).card : ℝ)) ~[atTop]
      (fun x => c*x/(log x)^2) := by
  classical
  have hne : line 4 1 ≠ line 8 3 := by
    intro he
    have hh := congrArg (eval (0 : ℤ)) he
    norm_num [line] at hh
  have hb {a b : ℤ} (ha : 0<a) (hc : IsCoprime a b) : BunyakovskyCondition (line a b) := by
    exact ⟨(degree_linear ha.ne').ge,irreducible_C_mul_X_add_C ha.ne' hc.isRelPrime,
      (leadingCoeff_linear ha.ne').symm ▸ ha⟩
  have hb' (f : ℤ[X]) (hf : f∈forms) : BunyakovskyCondition f := by
    rcases mem_insert.mp hf with rfl | h
    · exact hb (by decide) ⟨0,1,by norm_num⟩
    · obtain rfl := mem_singleton.mp h
      exact hb (by decide) ⟨-1,3,by norm_num⟩
  have hc : SchinzelCondition forms := by
    intro p hp
    by_cases h : p=3
    · subst p
      refine ⟨1,?_⟩
      intro f hf
      rcases mem_insert.mp hf with rfl | h
      · norm_num [line]
      · obtain rfl := mem_singleton.mp h; norm_num [line]
    · refine ⟨0,?_⟩
      intro f hf
      rcases mem_insert.mp hf with rfl | hs
      · simpa [line] using (show ¬(p:ℤ) ∣ 1 by exact_mod_cast hp.not_dvd_one)
      · obtain rfl := mem_singleton.mp hs
        have hn : ¬p ∣ 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).not.mpr h
        simpa [line] using (show ¬(p:ℤ) ∣ 3 by exact_mod_cast hn)
  obtain ⟨c,hc,_,he⟩ := hBH forms (by simp [forms]) hb' hc
  have hcard : forms.card=2 := by simp [forms,hne]
  have hdeg : DegreesProduct forms=1 := by
    apply Finset.prod_eq_one
    intro f hf
    rcases mem_insert.mp hf with rfl | h
    · exact natDegree_linear (by decide : (4:ℤ) ≠ 0)
    · obtain rfl := mem_singleton.mp h
      exact natDegree_linear (by decide : (8:ℤ) ≠ 0)
  have hp (x : ℝ) : CountSimultaneousPrimes forms x = (parameters x).card := by
    unfold CountSimultaneousPrimes parameters
    congr 1
    apply filter_congr
    intro n _
    simp [forms,line]
    norm_cast
  simpa only [hdeg,Nat.cast_one,div_one,hcard,hp] using (show ∃ c : ℝ, 0<c ∧
    (fun x : ℝ => (CountSimultaneousPrimes forms x : ℝ)) ~[atTop]
    (fun x => c/DegreesProduct forms*x/(log x)^forms.card) from ⟨c,hc,he⟩)

private theorem window_limit {F : ℝ → ℝ} {c a : ℝ} (ha : 0<a)
    (H : F ~[atTop] (fun x : ℝ => c*x/(log x)^2)) :
    Tendsto (fun x : ℝ => F (a*x)*(log x)^2/x) atTop (𝓝 (c*a)) := by
  obtain ⟨u,hu,he⟩ := H.exists_eq_mul
  have ht : Tendsto (fun x : ℝ => a*x) atTop atTop := tendsto_id.const_mul_atTop ha
  have hsmall : Tendsto (fun x : ℝ => log a / log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hratio : Tendsto (fun x : ℝ => (1+log a/log x)⁻¹) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x:=1)).add hsmall).inv₀ (by norm_num)
  have hh := ((hu.comp ht).mul (tendsto_const_nhds (x:=c*a))).mul (hratio.pow 2)
  simp only [one_mul,one_pow,mul_one] at hh
  apply hh.congr'
  filter_upwards [ht.eventually he,eventually_gt_atTop (1:ℝ),ht.eventually_gt_atTop 1] with x he hx hax
  change F (a*x)=u (a*x)*(c*(a*x)/(log (a*x))^2) at he
  change u (a*x)*(c*a)*((1+log a/log x)⁻¹)^2 = _
  rw [he,log_mul ha.ne' (by linarith : x≠0)]
  have hl := log_pos hx
  have hl' := log_pos hax
  rw [log_mul ha.ne' (by linarith : x≠0)] at hl'
  have hsum : 1+log a/log x = (log a+log x)/log x := by field_simp [hl.ne']; ring
  rw [hsum,inv_div]
  have hx0 : x ≠ 0 := by linarith
  field_simp [hx0,hl'.ne']

private theorem window_count {x : ℝ} (hx : 10 ≤ x) :
    ((parameters ((1/5)*x)).card : ℝ) - (parameters ((1/8)*x)).card ≤
    (({p : ℕ | x < p ∧ (p : ℝ) < 2*x ∧ p ∈ S 2} : Set ℕ).ncard : ℝ) := by
  classical
  let U := parameters ((1/5)*x)
  let L := parameters ((1/8)*x)
  let A := {p : ℕ | x < p ∧ (p : ℝ) < 2*x ∧ p ∈ S 2}
  have hx0 : 0 ≤ x := by linarith
  have ha : (1/8:ℝ)*x ≤ (1/5)*x := by linarith
  have hs : L ⊆ U := by
    intro n hn
    obtain ⟨hn,hp⟩ := mem_filter.mp (show n ∈ parameters ((1/8)*x) from hn)
    have hfloor := Nat.floor_mono ha
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hn; omega),hp⟩
  let E := (U \ L).image (fun n => 8*n+3)
  have hinj : Function.Injective (fun n : ℕ => 8*n+3) := by
    intro a b he
    change 8*a+3=8*b+3 at he
    omega
  have hsub : (E : Set ℕ) ⊆ A := by
    intro q hq
    obtain ⟨n,hn,rfl⟩ := mem_image.mp (show q∈E from hq)
    obtain ⟨hu,hl⟩ := mem_sdiff.mp hn
    obtain ⟨hr,hp,hq⟩ := mem_filter.mp (show n ∈ parameters ((1/5)*x) from hu)
    have hhi : (n:ℝ) ≤ (1/5)*x := (Nat.le_floor_iff (by positivity)).mp (by have := mem_range.mp hr; omega)
    have hlo : (1/8)*x < (n:ℝ) := by
      by_contra! h
      apply hl
      exact mem_filter.mpr ⟨mem_range.mpr (by have := Nat.le_floor h; omega),hp,hq⟩
    have hh : 0 < n := by
      exact_mod_cast (show 0 < (n:ℝ) by linarith)
    refine ⟨?_,?_,PairedGaps.safe_prime_generator hp hq (by omega) (by omega) (by omega)⟩ <;>
      push_cast <;> linarith
  have hfin : A.Finite := (Set.finite_Iic ⌈2*x⌉₊).subset (by
    intro p hp
    show p ≤ ⌈2*x⌉₊
    exact_mod_cast hp.2.1.le.trans (Nat.le_ceil (2*x)))
  have hcnt := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset,show E.card=(U \ L).card from card_image_of_injective _ hinj] at hcnt
  change (U.card:ℝ)-L.card ≤ A.ncard
  rw [← Finset.cast_card_sdiff hs]
  exact_mod_cast hcnt

/-- Bateman–Horn for the two safe-prime forms gives the base-two dyadic lower
bound at every sufficiently large real x. Positive-density Artin is unnecessary. -/
theorem dyadic_bound_of_bateman_horn (hBH : type_of% @bateman_horn_conjecture) :
    DyadicPrimitiveRootBound := by
  obtain ⟨c,hc,H⟩ := scaled_count hBH
  have hhi := window_limit (a:=1/5) (by norm_num) H
  have hlo := window_limit (a:=1/8) (by norm_num) H
  have hh := (hhi.sub hlo).eventually (eventually_gt_nhds (show c/30 < c*(1/5)-c*(1/8) by linarith))
  refine ⟨c/30,by positivity,?_⟩
  filter_upwards [hh,eventually_ge_atTop (10:ℝ)] with x h hx
  have hx0 : 0<x := by linarith
  have hl := log_pos (show 1<x by linarith)
  apply le_trans _ (window_count hx)
  apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
  change c/30 < ((parameters ((1/5)*x)).card:ℝ)*(log x)^2/x -
    ((parameters ((1/8)*x)).card:ℝ)*(log x)^2/x at h
  rw [← sub_div,←sub_mul] at h
  exact ((lt_div_iff₀ hx0).mp h).le

#print axioms dyadic_bound_of_bateman_horn

/-- A Bateman–Horn bound uniform in the seeds, orientations and requested length. -/
theorem spacing_of_bateman_horn (hBH : type_of% @bateman_horn_conjecture) :
    ∃ C : ℝ, 0 < C ∧ ∀ k z : ℕ, IsPrefixCenter z k →
      (k : ℝ) ≤ C*lengthScale z ∧ ∀ w, IsPrefixCenter w k → z ≠ w →
        (k : ℝ) ≤ C*lengthScale (Nat.dist z w) :=
  prefix_length_and_spacing (dyadic_bound_of_bateman_horn hBH)

#print axioms spacing_of_bateman_horn

end CunninghamChain.DyadicSpacing
