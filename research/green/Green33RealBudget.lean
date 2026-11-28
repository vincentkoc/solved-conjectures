import Green33RealQuadrature
import Green33PrimeFlatness
import Mathlib.Analysis.Fourier.ZMod

/-! Exactly uniform sums on a common cyclic seed with unrestricted real marginals. -/

open Finset Filter Green33WeightedStability Green33RealQuadrature
open scoped Topology Pointwise

namespace Green33RealBudget

/-- Two independent probability laws on the same available labels give the
uniform law on their cyclic group. Each law may assign zero to some labels. -/
def ExactSeed (p : ℕ+) (A : Finset (ZMod p)) : Prop :=
  ∃ P Q : PMF A, ∀ z, ((law P Q (cyclicSum A)) z).toReal = (p:ℝ)⁻¹

private lemma normalize {S : Type*} [Fintype S] (w : S → ℝ) (nonneg : ∀ i, 0 ≤ w i)
    (pos : 0 < ∑ i, w i) : ∃ u : PMF S, ∀ i, (u i).toReal = w i/(∑ j, w j) := by
  classical
  have h (i) : 0 ≤ w i/(∑ j, w j) := div_nonneg (nonneg _) pos.le
  have total : ∑ i, ENNReal.ofReal (w i/(∑ j, w j)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => h i),← sum_div,div_self pos.ne',ENNReal.ofReal_one]
  exact ⟨PMF.ofFintype _ total,fun i => by simp [h]⟩

private lemma realize {p : ℕ+} (A : Finset (ZMod p)) {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → A) (W : ι → ℝ) (g : ZMod p → ℝ)
    (hw : ∀ i, 0<W i) (hg : ∀ x, 0 ≤ g x) (onA : ∀ x ∈ A, 0<g x)
    (offA : ∀ x ∉ A, g x=0)
    (constant : ∀ z, ∑ i, W i*g (z-(b i:ZMod p)) = ∑ i, W i*g (0-(b i:ZMod p))) :
    ExactSeed p A := by
  classical
  let B (s : A) := ∑ i, if b i=s then W i else 0
  have wp (s : A) : 0 ≤ B s := sum_nonneg fun i _ => by split_ifs <;> first | exact (hw i).le | exact le_rfl
  have push (f : A → ℝ) : ∑ s, B s * f s = ∑ i, W i*f (b i) := by
    simp only [B,sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simp
  have massB : ∑ s, B s = ∑ i, W i := by simpa only [mul_one] using push (fun _ => 1)
  have wpos : 0 < ∑ i, W i := sum_pos (fun i _ => hw i) univ_nonempty
  let i₀ := Classical.choice (inferInstance : Nonempty ι)
  have gpos : 0 < ∑ j : A, g j :=
    (onA _ (b i₀).property).trans_le (single_le_sum (f:=fun j : A => g j) (fun _ _ => hg _) (mem_univ (b i₀)))
  obtain ⟨P,hP⟩ := normalize B wp (massB ▸ wpos)
  obtain ⟨Q,hQ⟩ := normalize (fun s : A => g s) (fun s => hg _) gpos
  let R := law P Q (cyclicSum A)
  have fiber (z : ZMod p) (s : A) :
      ∑ t : A, (if (s:ZMod p)+t=z then g t else 0) = g (z-s) := by
    by_cases mem : z-(s:ZMod p) ∈ A
    · let t : A := ⟨_,mem⟩
      rw [sum_eq_single t]
      · simp [t]
      · intro u _ ne
        rw [if_neg]
        intro e
        apply ne
        apply Subtype.ext
        change (u:ZMod p) = z-s
        rw [← e,add_sub_cancel_left]
      · simp
    · rw [offA _ mem]
      apply sum_eq_zero
      intro t _
      rw [if_neg]
      intro e
      exact mem (show z-(s:ZMod p) ∈ A by rw [← e,add_sub_cancel_left]; exact t.property)
  have atom (z : ZMod p) : (R z).toReal = (∑ i,W i*g (z-(b i:ZMod p)))/((∑ s,B s)*(∑ t : A,g t)) := by
    have hm := (observed_eq_mass P Q (cyclicSum A) {z}).symm
    simp only [mass,sum_singleton] at hm
    rw [hm]
    change (∑ s : A, ∑ t : A, if (s:ZMod p)+t ∈ ({z}:Finset _) then (P s).toReal * (Q t).toReal else 0) = _
    have split (c : Prop) [Decidable c] (a b d : ℝ) :
        (if c then a*b/d else 0) = a*(if c then b else 0)/d := by split_ifs <;> simp
    simp only [mem_singleton,hP,hQ,div_mul_div_comm,split,← sum_div,← mul_sum]
    rw [← push (fun s => g (z-s))]
    simp only [fiber]
  have eq (z : ZMod p) : (R z).toReal = (R 0).toReal := by rw [atom,atom,constant]
  have total := congrArg ENNReal.toReal R.tsum_coe
  rw [tsum_fintype,ENNReal.toReal_sum fun i _ => R.apply_ne_top i,ENNReal.toReal_one] at total
  have c : (p:ℝ)*(R 0).toReal=1 := by
    calc
      _ = ∑ _i : ZMod p, (R 0).toReal := by simp
      _ = ∑ i, (R i).toReal := sum_congr rfl fun i _ => (eq i).symm
      _ = _ := total
  refine ⟨P,Q,fun z => (eq z).trans ?_⟩
  rw [← one_div,eq_div_iff (by exact_mod_cast p.ne_zero : (p:ℝ) ≠ 0),mul_comm]
  exact c

/-- Two independent real probability laws on the complement of `2*n` sites
have exactly uniform sum at both odd orders adjoining `4*(n+1)`. -/
theorem common_seed (p : ℕ+) (n : ℕ)
    (order : p.val+1=4*(n+1) ∨ p.val=4*(n+1)+1) :
    ∃ A : Finset (ZMod p), A.card+2*n=p.val ∧ ExactSeed p A := by
  obtain ⟨A,b,W,g,card,hw,hg,onA,offA,constant⟩ := positive_constant_convolution n order
  exact ⟨A,card,realize A b W g hw hg onA offA constant⟩

/-- At an odd prime the construction and the uncertainty lower bound put the
minimum common budget within two labels. -/
theorem prime_window (p : ℕ+) [Fact p.val.Prime] (odd : Odd p.val) :
    ∃ A : Finset (ZMod p), ExactSeed p A ∧ 2*A.card ≤ p.val+5 ∧
      ∀ B : Finset (ZMod p), ExactSeed p B → p.val+1 ≤ 2*B.card := by
  have hp := (Fact.out : p.val.Prime).two_le
  obtain ⟨k,hk⟩ := odd
  let n := (p.val+1)/4-1
  have order : p.val+1=4*(n+1) ∨ p.val=4*(n+1)+1 := by dsimp [n]; omega
  obtain ⟨A,card,exactSeed⟩ := common_seed p n order
  refine ⟨A,exactSeed,by omega,?_⟩
  rintro B ⟨u,v,flat⟩
  exact Green33PrimeFlatness.prime_divisor_budget (dvd_refl p.val) B u v flat

/-- Least number of available common labels admitting an exactly uniform cyclic sum. -/
noncomputable def minimumBudget (p : ℕ+) : ℕ := by
  classical
  exact sInf {k : ℕ | ∃ A : Finset (ZMod p), A.card=k ∧ ExactSeed p A}

/-- As the prime order grows, the minimum fraction of occupied common labels
tends to one half. -/
theorem prime_limit {ι : Type*} {l : Filter ι} (p : ι → ℕ+) (prime : ∀ i, (p i).val.Prime)
    (big : Tendsto (fun i => (p i).val) l atTop) :
    Tendsto (fun i => (minimumBudget (p i):ℝ)/(p i:ℝ)) l (𝓝 (1/2:ℝ)) := by
  have small : Tendsto (fun i => (5:ℝ)/(p i:ℝ)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp big)
  have upper := (tendsto_const_nhds (x:=(1/2:ℝ))).add small
  rw [add_zero] at upper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  all_goals filter_upwards [big.eventually_ge_atTop 3] with i hi
  all_goals
    have : Fact (p i).val.Prime := ⟨prime i⟩
    obtain ⟨A,w,hb,lb⟩ := prime_window (p i) ((prime i).odd_of_ne_two (by omega))
    let S := {k : ℕ | ∃ B : Finset (ZMod (p i)), B.card=k ∧ ExactSeed (p i) B}
    have mem : A.card ∈ S := ⟨A,rfl,w⟩
    have minim : minimumBudget (p i) ∈ S := Nat.sInf_mem ⟨_,mem⟩
    obtain ⟨B,e,we⟩ := minim
    have lo := lb B we
    have up : minimumBudget (p i) ≤ A.card := Nat.sInf_le mem
    have hp : (0:ℝ) < p i := by exact_mod_cast (p i).pos
  · change 1/2 ≤ _/_
    rw [le_div_iff₀ hp]
    have q : (p i:ℝ) ≤ 2*(minimumBudget (p i):ℝ) := by exact_mod_cast (show (p i).val ≤ 2*(minimumBudget (p i)) by omega)
    linarith
  · change _/_ ≤ 1/2+5/_
    rw [div_le_iff₀ hp]
    have q : (minimumBudget (p i):ℝ)*2 ≤ (p i:ℝ)+5 := by exact_mod_cast (by omega : minimumBudget (p i)*2 ≤ (p i).val+5)
    rw [add_mul,div_mul_cancel₀ _ hp.ne']
    linarith

section Fourier
open Polynomial Green33PrimeFlatness
open scoped ZMod
variable {p : ℕ} [Fact p.Prime]

private lemma dft_conv (f g : ZMod p → ℂ) (t : ZMod p) :
    ZMod.dft (conv f g) t = ZMod.dft f t * ZMod.dft g t := by
  simp only [ZMod.dft_apply,smul_eq_mul,conv]
  rw [sum_mul]
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply Fintype.sum_equiv (Equiv.subRight i)
  intro z
  simp only [Equiv.subRight_apply]
  have e : -(z*t) = -(i*t)+ -((z-i)*t) := by ring
  rw [e,AddChar.map_add_eq_mul]
  ring

private lemma dft_poly (P : ℂ[X]) (d : ℕ) (degree : P.natDegree ≤ d) (t : ZMod p) :
    ZMod.dft (fun z : ZMod p => ∑ j ∈ range (d+1), if (j:ZMod p)=z then P.coeff j else 0) t =
      P.eval (ZMod.stdAddChar (-t)) := by
  rw [ZMod.dft_apply,eval_eq_sum_range' (Nat.lt_succ_of_le degree)]
  simp only [smul_eq_mul,mul_sum,mul_ite,mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [sum_ite_eq,mem_univ,if_true]
  have pow : ZMod.stdAddChar (-((j:ZMod p)*t)) = ZMod.stdAddChar (-t)^j := by
    rw [← AddChar.map_nsmul_eq_pow,nsmul_eq_mul,mul_neg]
  rw [pow,mul_comm]

/-- The Biró–Tao prime Fourier uncertainty inequality, obtained by applying
the zero-convolution support bound to a polynomial vanishing on the spectrum. -/
theorem prime_uncertainty (f : ZMod p → ℂ) (hf : ∃ i, f i ≠ 0) :
    p+1 ≤ (sites f).card+(sites (ZMod.dft f)).card := by
  classical
  let S := sites (ZMod.dft f)
  have sf (i) : i ∈ S ↔ ZMod.dft f i ≠ 0 := by simp [S,sites]
  let d := S.card
  have hpos : 0 < (sites f).card := by
    obtain ⟨i,hi⟩ := hf
    apply card_pos.mpr; exact ⟨i,by simpa [sites] using hi⟩
  by_cases h : d<p
  · let P : ℂ[X] := ∏ t ∈ S, (X-C (ZMod.stdAddChar (-t)))
    have degree : P.natDegree=d := by simp [P,d,natDegree_prod_of_monic,monic_X_sub_C]
    have monic : P.Monic := monic_prod_of_monic _ _ (fun t _ => monic_X_sub_C _)
    let g (z : ZMod p) := ∑ j ∈ range (d+1), if (j:ZMod p)=z then P.coeff j else 0
    have top : g d = 1 := by
      dsimp only [g]
      rw [sum_eq_single d]
      · simpa only [if_true] using degree ▸ monic.coeff_natDegree
      · intro j hj ne
        rw [if_neg]
        intro eq
        have c := congrArg ZMod.val eq
        rw [ZMod.val_natCast_of_lt (by have := mem_range.mp hj;omega),ZMod.val_natCast_of_lt h] at c
        exact ne c
      · simp
    have sizeg : (sites g).card ≤ d+1 := by
      have sub : sites g ⊆ (range (d+1)).image (fun j : ℕ => (j:ZMod p)) := by
        intro z hz
        by_contra out
        have all (j) (hj : j ∈ range (d+1)) : (j:ZMod p) ≠ z := fun e => out (mem_image.mpr ⟨j,hj,e⟩)
        have gz : g z=0 := sum_eq_zero fun j hj => if_neg (all j hj)
        simp [sites,gz] at hz
      exact (card_le_card sub).trans (card_image_le.trans_eq (card_range _))
    have killed : conv f g = 0 := by
      apply ZMod.dft.injective
      ext t
      rw [map_zero,Pi.zero_apply,dft_conv,dft_poly P d degree.le]
      by_cases ht : t ∈ S
      · have ev : P.eval (ZMod.stdAddChar (-t))=0 := by
          rw [show P = _ from rfl,eval_prod]
          exact prod_eq_zero ht (by simp)
        rw [ev,mul_zero]
      · rw [not_not.mp (mt (sf t).mpr ht),zero_mul]
    have bound := constant_support f g hf ⟨_,top.trans_ne one_ne_zero⟩ 0 (fun z => congrFun killed z)
    simp at bound
    change p+1 ≤ (sites f).card+d
    omega
  · change p+1 ≤ (sites f).card+d; omega


private lemma spectrum_odd (f : ZMod p → ℝ) (mass : ∑ x, f x ≠ 0) (hp : p ≠ 2) :
    Odd (sites (ZMod.dft (fun x => (f x:ℂ)))).card := by
  classical
  let F := ZMod.dft (fun x => (f x:ℂ))
  let S := sites F
  have nonzero : 0 ∈ S := by
    simpa [S,sites,F,ZMod.dft_apply_zero,← Complex.ofReal_sum] using mass
  have conj (x : ZMod p) : (starRingEnd ℂ) (F x) = F (-x) := by
    simp only [F,ZMod.dft_apply,smul_eq_mul,map_sum,map_mul,Complex.conj_ofReal]
    apply sum_congr rfl; intro j _
    congr 1
    rw [mul_neg,neg_neg]
    have ch (z : ZMod p) : (starRingEnd ℂ) (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
      change (starRingEnd ℂ) (ZMod.toCircle z:ℂ) = (ZMod.toCircle (-z):ℂ)
      rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    rw [ch,neg_neg]
  have sym (x : ZMod p) : -x ∈ S ↔ x ∈ S := by simp [S,sites,← conj]
  let E := S.erase 0
  have split (x : ZMod p) (hz : x ≠ 0) : (-x).val ≠ x.val := by
    intro eq
    have ex := ZMod.val_injective p eq
    have zz : (2:ZMod p)*x=0 := by linear_combination -ex
    have ne : (2:ZMod p) ≠ 0 := by
      have two : 2<p := by have := (Fact.out : p.Prime).two_le; omega
      have val := ZMod.val_natCast_of_lt two
      change (2:ZMod p).val=2 at val
      intro h; rw [h,ZMod.val_zero] at val; omega
    exact hz ((mul_eq_zero.mp zz).resolve_left ne)
  have eqcard : (E.filter (fun x => x.val<(-x).val)).card =
      (E.filter (fun x => ¬ x.val<(-x).val)).card := by
    apply card_equiv (Equiv.neg _)
    intro x
    simp only [E,mem_filter,mem_erase,Equiv.neg_apply,neg_ne_zero,neg_neg,sym]
    apply and_congr_right
    intro h
    have ne := split x h.1
    omega
  have both := card_filter_add_card_filter_not (s:=E) (fun x => x.val<(-x).val)
  have card := card_erase_add_one nonzero
  change E.card+1=S.card at card
  change Odd S.card
  exact ⟨(E.filter (fun x => x.val<(-x).val)).card,by omega⟩

private lemma cover_spectra (f g : ZMod p → ℂ) (c : ℂ) (flat : ∀ z, conv f g z=c) :
    (sites (ZMod.dft f)).card + (sites (ZMod.dft g)).card ≤ p+1 := by
  classical
  let S := sites (ZMod.dft f)
  let T := sites (ZMod.dft g)
  have included : S ∩ T ⊆ {0} := by
    intro t ht
    by_contra away
    have neq : t ≠ 0 := by simpa using away
    have vanish : ∑ j : ZMod p, ZMod.stdAddChar (-(j*t))=0 := by
      have e (j : ZMod p) : -(j*t)=(-t)*j := by ring
      simp only [e]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p (neg_ne_zero.mpr neq))
    have df := dft_conv f g t
    rw [ZMod.dft_apply] at df
    simp only [flat,smul_eq_mul,← sum_mul,vanish,zero_mul] at df
    have mem := mem_inter.mp ht
    simp only [S,T,sites,mem_filter,mem_univ,true_and] at mem
    exact (mul_ne_zero mem.1 mem.2) df.symm
  have ih := card_le_card included
  have uh := card_le_univ (S ∪ T)
  rw [card_singleton] at ih
  rw [ZMod.card] at uh
  have ident := card_union_add_card_inter S T
  change S.card+T.card ≤ p+1
  omega


private lemma push_weights (A : Finset (ZMod p)) (u : PMF A) :
    let U := u.map (fun i : A => (i:ZMod p))
    let f (z : ZMod p) := (U z).toReal
    (∑ z, f z) = 1 ∧ (sites (fun z => (f z:ℂ))).card ≤ A.card := by
  classical
  dsimp only
  constructor
  · have h := congrArg ENNReal.toReal (u.map (fun i : A => (i:ZMod p))).tsum_coe
    simpa only [tsum_fintype,ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _),ENNReal.toReal_one] using h
  · apply card_le_card
    intro z hz
    by_contra out
    have ne (i : A) : z ≠ (i:ZMod p) := fun e => out (e ▸ i.property)
    have zero : (u.map (fun i : A => (i:ZMod p))) z=0 := by
      simp [PMF.map_apply,tsum_fintype,ne]
    simp only [sites,mem_filter,mem_univ,true_and] at hz
    exact hz (by rw [zero]; simp)

private lemma conv_law (u v : PMF (ZMod p)) (z : ZMod p) :
    conv (fun i => (u i).toReal) (fun i => (v i).toReal) z = ((law u v (·+·)) z).toReal := by
  classical
  have fiber (i : ZMod p) : (v.map (i+·)) z = v (z-i) := by
    rw [PMF.map_apply,tsum_fintype,sum_eq_single (z-i)]
    · simp
    · intro j _ ne; exact if_neg (fun e => ne (by rw [e]; abel))
    · simp
  simp only [conv,law,PMF.bind_apply,tsum_fintype,fiber,ENNReal.toReal_sum
    (fun i _ => ENNReal.mul_ne_top (u.apply_ne_top _) (v.apply_ne_top _)),ENNReal.toReal_mul]

end Fourier

private lemma minimum_at_three (p : ℕ+) [Fact p.val.Prime] (n : ℕ) (order : p.val+1=4*(n+1)) :
    minimumBudget p=2*n+3 := by
  classical
  obtain ⟨A,card,u⟩ := common_seed p n (Or.inl order)
  let S := {k : ℕ | ∃ B : Finset (ZMod p), B.card=k ∧ ExactSeed p B}
  have mem : A.card ∈ S := ⟨A,rfl,u⟩
  have up : minimumBudget p ≤ A.card := Nat.sInf_le mem
  have minim : minimumBudget p ∈ S := Nat.sInf_mem ⟨_,mem⟩
  obtain ⟨B,e,P,Q,flat⟩ := minim
  let U := P.map (fun i : B => (i:ZMod p))
  let V := Q.map (fun i : B => (i:ZMod p))
  let f (z : ZMod p) := (U z).toReal
  let g (z : ZMod p) := (V z).toReal
  let F (z : ZMod p) := (f z:ℂ)
  let G (z : ZMod p) := (g z:ℂ)
  have hf : (∑ z, f z) = 1 ∧ (Green33PrimeFlatness.sites F).card ≤ B.card := push_weights _ _
  have hg : (∑ z, g z) = 1 ∧ (Green33PrimeFlatness.sites G).card ≤ B.card := push_weights _ _
  have exists_ne (w : ZMod p → ℝ) (h : ∑ z, w z=1) : ∃ z, (w z:ℂ) ≠ 0 := by
    by_contra! all
    simp only [Complex.ofReal_eq_zero] at all
    simp [all] at h
  have ua := prime_uncertainty F (exists_ne f hf.1)
  have ub := prime_uncertainty G (exists_ne g hg.1)
  have oa := spectrum_odd f (hf.1.trans_ne one_ne_zero) (by omega)
  have ob := spectrum_odd g (hg.1.trans_ne one_ne_zero) (by omega)
  have law_eq : law U V (·+·) = law P Q (cyclicSum B) := by
    simp [law,U,V,PMF.bind_map,PMF.map_comp,Function.comp_def]
    rfl
  have prod (z : ZMod p) : Green33PrimeFlatness.conv F G z = (((p:ℝ)⁻¹:ℝ):ℂ) := by
    have h := conv_law U V z
    rw [law_eq,flat] at h
    exact (by simpa only [Green33PrimeFlatness.conv,Complex.ofReal_sum,Complex.ofReal_mul,F,G,f,g] using congrArg Complex.ofReal h)
  have cap := cover_spectra F G _ prod
  obtain ⟨a,oa⟩ := oa
  obtain ⟨b,ob⟩ := ob
  change (Green33PrimeFlatness.sites (ZMod.dft F)).card=_ at oa
  change (Green33PrimeFlatness.sites (ZMod.dft G)).card=_ at ob
  omega

/-- Exact minimum number of common labels at every prime congruent to three
modulo four, for unrestricted real probability laws. -/
theorem three_mod_four (p : ℕ+) [Fact p.val.Prime] (hp : p.val%4=3) :
    minimumBudget p = (p.val+3)/2 := by
  have h := minimum_at_three p (p.val/4) (by omega)
  omega

#print axioms common_seed
#print axioms prime_window
#print axioms prime_limit
#print axioms prime_uncertainty
#print axioms three_mod_four
end Green33RealBudget
