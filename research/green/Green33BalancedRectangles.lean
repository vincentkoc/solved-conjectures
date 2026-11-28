import Green33WeightedPeaks

/-! Balanced disjoint rectangles from mean-square uniformity of an independent sum. -/

open Finset Green33WeightedStability Green33WeightedPeaks
open Filter
open scoped Topology

namespace Green33BalancedRectangles

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- If the two side lengths are nearly balanced and the rectangle almost
exhausts the output, few labels on its first side have small mass. -/
theorem trim_bound (U V : Finset ι) (p q : ι → ℝ)
    (nonneg : ∀ i, 0 ≤ p i) (qupper : ∑ j ∈ V,q j≤1)
    (pupper : ∑ i ∈ U,p i≤1) (r e δ : ℝ) (hr : 0<r) (he : 0<e)
    (rect : ∀ X ⊆ U, (∑ i ∈ X,p i)*(∑ j ∈ V,q j) ≤ (X.card:ℝ)/r*((V.card:ℝ)/r)+δ)
    (balanced : 1-e≤(V.card:ℝ)/r)
    (slack : (U.card:ℝ)/r*((V.card:ℝ)/r)-1+
      (1-∑ i ∈ U,p i)+(1-∑ j ∈ V,q j)+δ ≤ e^2) :
    ((U.filter (fun i => r*p i < 1-2*e)).card:ℝ)/r ≤ e := by
  classical
  let B := U.filter fun i => r*p i < 1-2*e
  have sub : B ⊆ U := filter_subset _ _
  let u := ∑ i ∈ U,p i
  let v := ∑ j ∈ V,q j
  let w := ∑ i ∈ B,p i
  let c := (B.card:ℝ)/r
  have cap : w≤c*(1-2*e) := by
    have e' := sum_le_sum (fun i (hi : i∈B) =>
      (le_div_iff₀ hr).mpr (by simpa [mul_comm] using (mem_filter.mp hi).2.le) : ∀ i ∈ B, p i≤(1-2*e)/r)
    calc w ≤ _ := e'
         _ = _ := by simp [c];ring
  have wnon : 0≤w := sum_nonneg fun i _ => nonneg i
  have rem : (∑ i ∈ U\B,p i)=u-w := by
    have := sum_sdiff (f:=p) sub
    dsimp [u,w];linarith
  have rc := rect (U\B) sdiff_subset
  rw [rem,card_sdiff_of_subset sub,Nat.cast_sub (card_le_card sub)] at rc
  change (u-w)*v ≤ _ at rc
  have loss : 1-(1-u)-(1-v)-c*(1-2*e) ≤ (u-w)*v := by
    have a := mul_nonneg (sub_nonneg.mpr pupper) (sub_nonneg.mpr qupper)
    have b := mul_nonneg wnon (sub_nonneg.mpr qupper)
    change 0≤(1-u)*(1-v) at a
    change 0≤w*(1-v) at b
    nlinarith
  have norm : (B.card:ℝ)/r = c := rfl
  have ineq : c*((V.card:ℝ)/r-(1-2*e))≤e^2 := by
    rw [sub_div,norm] at rc
    change _-1+(1-u)+(1-v)+δ≤e^2 at slack
    linarith only [rc,loss,slack]
  have cnon : 0≤c := div_nonneg (Nat.cast_nonneg _) hr.le
  change c≤e
  exact (le_of_mul_le_mul_right (show c*e≤e*e by
    nlinarith [mul_nonneg cnon (sub_nonneg.mpr balanced)]) he)


section Energy
variable {G : Type*} [Fintype G] [DecidableEq G]

/-- Number of ordered pairs from two specified sides with a given output. -/
def pairCount (obs : ι → ι → G) (U V : Finset ι) (z : G) : ℕ :=
  ((U×ˢV).filter fun x => obs x.1 x.2=z).card

omit [DecidableEq ι] [Fintype G] in
private lemma atom (P Q : PMF ι) (obs : ι → ι → G) (z : G) :
    ((law P Q obs) z).toReal =
      ∑ x : ι×ι, if obs x.1 x.2=z then (P x.1).toReal*(Q x.2).toReal else 0 := by
  classical
  have h := (observed_eq_mass P Q obs {z}).symm
  simp only [mass,sum_singleton] at h
  rw [h]
  change (∑ i, ∑ j, if obs i j∈({z}:Finset G) then _ else _) = _
  simp only [mem_singleton,Fintype.sum_prod_type]

omit [DecidableEq ι] [DecidableEq G] in
private lemma collision_mass (u : PMF G) :
    (Fintype.card G:ℝ)*∑ z, (u z).toReal^2=
      1+(Fintype.card G:ℝ)*squaredError u := by
  have tot := congrArg ENNReal.toReal u.tsum_coe
  rw [tsum_fintype,ENNReal.toReal_sum (fun i _ => u.apply_ne_top i),ENNReal.toReal_one] at tot
  let : Nonempty G := u.support_nonempty.to_type
  have mpos : (0:ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α:=G)
  simp only [squaredError,sub_sq,sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,
    tot,mul_one,sum_const,card_univ,nsmul_eq_mul]
  field_simp
  ring

omit [DecidableEq ι] in
/-- Atomwise lower bounds on both retained sides control the unweighted
collision energy by the Pearson divergence of the original sum law. -/
theorem retained_energy (P Q : PMF ι) (obs : ι → ι → G) (U V : Finset ι)
    (r θ : ℝ) (hr : 0<r) (hθ : 0≤θ) (order : r^2=Fintype.card G)
    (first : ∀ i∈U, θ≤r*(P i).toReal) (second : ∀ j∈V, θ≤r*(Q j).toReal) :
    θ^4*((∑ z, (pairCount obs U V z:ℝ)^2)/(Fintype.card G:ℝ)) ≤
      1+(Fintype.card G:ℝ)*squaredError (law P Q obs) := by
  classical
  let M := (Fintype.card G:ℝ)
  let R := law P Q obs
  let : Nonempty G := R.support_nonempty.to_type
  have hm : 0<M := by dsimp [M];exact_mod_cast Fintype.card_pos (α:=G)
  have cells (z : G) : θ^2*(pairCount obs U V z:ℝ)≤M*(R z).toReal := by
    let W (x : ι×ι) : ℝ := if obs x.1 x.2=z then (P x.1).toReal*(Q x.2).toReal else 0
    let F := (U×ˢV).filter fun x => obs x.1 x.2=z
    have each (x : ι×ι) (hx : x∈F) : θ^2≤M*W x := by
      obtain ⟨mem,eq⟩ := mem_filter.mp hx
      obtain ⟨i,j⟩ := mem_product.mp mem
      have h := mul_le_mul (first x.1 i) (second x.2 j) hθ (by positivity)
      rw [show W x=_ from if_pos eq,show M=r^2 from order.symm]
      nlinarith only [h]
    have allW : (∑ x ∈ F,W x) ≤ (R z).toReal := by
      rw [show (R z).toReal=_ from atom P Q obs z]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ F) fun i _ _ => by dsimp [W];split <;> positivity
    have e := sum_le_sum each
    simp only [sum_const,nsmul_eq_mul,← mul_sum] at e
    change _≤M*(R z).toReal
    calc _ = (F.card:ℝ)*θ^2 := mul_comm _ _
         _ ≤ _ := e.trans (mul_le_mul_of_nonneg_left allW hm.le)
  have e := sum_le_sum (s:=(univ:Finset G)) (fun z _ =>
    (sq_le_sq₀ (by positivity) (by positivity)).mpr (cells z))
  simp only [mul_pow,← mul_sum,← pow_mul] at e
  rw [← collision_mass,← mul_div_assoc,div_le_iff₀ hm]
  change _ ≤ (M*∑ z, (R z).toReal^2)*M
  have bound : θ^4*(∑ z, (pairCount obs U V z:ℝ)^2) ≤ M^2*∑ z, (R z).toReal^2 := e
  exact bound.trans_eq (by ring)
end Energy

omit [Fintype ι] [DecidableEq ι] in
private lemma count_total {G : Type*} [Fintype G] [DecidableEq G]
    (obs : ι → ι → G) (U V : Finset ι) :
    ∑ z, pairCount obs U V z=U.card*V.card := by
  classical
  simp only [pairCount,card_filter]
  rw [sum_comm]
  simp

/-- Normalized mean-square error of the ordinary, ordered representation
counts from a pair of sides. -/
noncomputable def countError {G : Type*} [Fintype G] [DecidableEq G]
    (obs : ι → ι → G) (U V : Finset ι) : ℝ :=
  (∑ z, ((pairCount obs U V z:ℝ)-1)^2)/(Fintype.card G:ℝ)

omit [Fintype ι] [DecidableEq ι] in
private lemma counts_expand {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (obs : ι → ι → G) (U V : Finset ι) :
    countError obs U V = (∑ z, (pairCount obs U V z:ℝ)^2)/(Fintype.card G:ℝ)-
      2*((U.card:ℝ)*V.card/(Fintype.card G:ℝ))+1 := by
  have tot : ∑ z, (pairCount obs U V z:ℝ)=(U.card:ℝ)*V.card := by exact_mod_cast count_total obs U V
  have mp : (0:ℝ)<Fintype.card G := by exact_mod_cast Fintype.card_pos (α:=G)
  simp only [countError,sub_sq,mul_one,one_pow,sum_add_distrib,sum_sub_distrib,
    ← mul_sum,sum_const,card_univ,nsmul_eq_mul,tot]
  field_simp

private lemma chi_diffuse {M : ℕ+} (A : Finset (ZMod M)) (p q : PMF A) :
    Diffuse p q (cyclicSum A) M (Real.sqrt (chiSquare A p q)) := by
  intro E
  let R := law p q (cyclicSum A)
  let d (z : ZMod M) := (R z).toReal-(M:ℝ)⁻¹
  have cs := sq_sum_le_card_mul_sum_sq (s:=E) (f:=d)
  have sub : ∑ z ∈ E, d z^2 ≤ squaredError R := by
    unfold squaredError;rw [ZMod.card]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ E) fun z _ _ => sq_nonneg _
  have card : (E.card:ℝ)≤M := by exact_mod_cast (show E.card≤M.val by simpa using card_le_univ E)
  have h : ∑ z ∈ E, d z ≤ Real.sqrt (chiSquare A p q) := by
    apply Real.le_sqrt_of_sq_le
    exact cs.trans (mul_le_mul card sub (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))
  rw [observed_eq_mass]
  change mass R E≤_
  simpa only [d,sum_sub_distrib,sum_const,nsmul_eq_mul,← div_eq_mul_inv,mass,sub_le_iff_le_add,add_comm] using h

omit [DecidableEq ι] in
private lemma prob_le_one (p : PMF ι) (S : Finset ι) : mass p S≤1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype,ENNReal.toReal_sum (fun i _ => p.apply_ne_top i),ENNReal.toReal_one] at h
  exact (sum_le_sum_of_subset_of_nonneg (f:=fun i => (p i).toReal) (subset_univ S)
    (fun i _ _ => ENNReal.toReal_nonneg)).trans_eq h

private lemma balance_scalar (u v B w : ℕ → ℝ)
    (bu : ∀ i, 0≤u i) (bv : ∀ i, 0≤v i) (cap : ∀ i, u i+v i ≤ B i)
    (prod : ∀ i, 1-w i≤u i*v i) (budget : Tendsto B atTop (𝓝 2))
    (loss : Tendsto w atTop (𝓝 0)) : Tendsto u atTop (𝓝 1) ∧ Tendsto v atTop (𝓝 1) := by
  let d i := B i*|B i-2|+w i
  have lim : Tendsto d atTop (𝓝 0) := by
    have gap := (budget.sub_const 2).abs
    simpa [d] using (budget.mul gap).add loss
  have one (x y : ℕ → ℝ) (hx : ∀ i, 0≤x i) (hy : ∀ i, 0≤y i)
      (sum : ∀ i, x i+y i≤B i) (xy : ∀ i, 1-w i≤x i*y i) : Tendsto x atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (by simpa using lim.sqrt)
    rw [Real.norm_eq_abs,← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have bx : x i≤B i := by linarith [sum i,hy i]
    have s := mul_le_mul_of_nonneg_left (sum i) (hx i)
    have t := mul_le_mul_of_nonneg_left (le_abs_self (B i-2)) (hx i)
    have z := mul_le_mul_of_nonneg_right bx (abs_nonneg (B i-2))
    dsimp [d]; nlinarith only [s,t,z,xy i]
  exact ⟨one u v bu bv cap prod,one v u bv bu (fun i => by simpa [add_comm] using cap i)
    (fun i => by simpa [mul_comm] using prod i)⟩

/-- Distance in total absolute mass to the constant density 1/r on S. -/
noncomputable def fairError (p : PMF ι) (S : Finset ι) (r : ℝ) : ℝ :=
  ∑ i, |(p i).toReal-(if i∈S then r⁻¹ else 0)|

private lemma fair_error_le (p : PMF ι) (S : Finset ι) (r θ : ℝ) (hr : 0<r) (cap : θ≤1)
    (large : ∀ i∈S, θ≤r*(p i).toReal) : fairError p S r≤1+(S.card:ℝ)/r-2*((S.card:ℝ)/r)*θ := by
  have each (i : ι) : |(p i).toReal-(if i∈S then r⁻¹ else 0)| ≤
      (p i).toReal+(if i∈S then (1-2*θ)/r else 0) := by
    by_cases h : i∈S
    · rw [if_pos h,if_pos h,abs_le]
      have m := large i h
      constructor <;> field_simp <;> nlinarith
    · simp [h,abs_of_nonneg ENNReal.toReal_nonneg]
  have sum := sum_le_sum (s:=univ) (fun i _ => each i)
  have total := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype,ENNReal.toReal_sum (fun i _ => p.apply_ne_top i),ENNReal.toReal_one] at total
  rw [sum_add_distrib,total] at sum
  simp only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul] at sum
  exact sum.trans_eq (by ring)

noncomputable def retain (S : Finset ι) (p : PMF ι) (r e : ℝ) : Finset ι :=
  S.filter fun i => 1-2*e ≤ r*(p i).toReal

private lemma retain_card (U V : Finset ι) (p q : PMF ι) (r e δ : ℝ) (hr : 0<r) (he : 0<e)
    (rect : ∀ X ⊆ U, mass p X*mass q V ≤ (X.card:ℝ)/r*((V.card:ℝ)/r)+δ)
    (balanced : 1-e≤(V.card:ℝ)/r)
    (slack : (U.card:ℝ)/r*((V.card:ℝ)/r)-1+(1-mass p U)+(1-mass q V)+δ ≤ e^2) :
    (U.card:ℝ)/r-e≤((retain U p r e).card:ℝ)/r ∧ ((retain U p r e).card:ℝ)/r≤(U.card:ℝ)/r := by
  classical
  have b := trim_bound U V (fun i => (p i).toReal) (fun i => (q i).toReal)
    (fun i => ENNReal.toReal_nonneg) (prob_le_one q V) (prob_le_one p U) r e δ hr he rect balanced slack
  have c := card_filter_add_card_filter_not (s:=U) (p:=fun i => 1-2*e ≤ r*(p i).toReal)
  simp only [not_le] at c
  have c' : ((retain U p r e).card:ℝ)+((U.filter fun i => r*(p i).toReal<1-2*e).card:ℝ)=U.card := by
    exact_mod_cast c
  refine ⟨?_,div_le_div_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ _)) hr.le⟩
  rw [← c',add_div];linarith

private lemma fair_normalize (p : PMF ι) (S : Finset ι) (r : ℝ) (hs : S.Nonempty) :
    fairError p S S.card ≤ fairError p S r+|(S.card:ℝ)/r-1| := by
  have pos : 0<(S.card:ℝ) := by exact_mod_cast card_pos.mpr hs
  have bound (i : ι) :
      |(p i).toReal-(if i∈S then (S.card:ℝ)⁻¹ else 0)| ≤
      |(p i).toReal-(if i∈S then r⁻¹ else 0)|+(if i∈S then |r⁻¹-(S.card:ℝ)⁻¹| else 0) := by
    by_cases mem : i∈S
    · simp only [if_pos mem];exact abs_sub_le _ _ _
    · simp [mem]
  have sum := sum_le_sum (s:=univ) (fun i _ => bound i)
  rw [sum_add_distrib] at sum
  simp only [sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul] at sum
  have eq : (S.card:ℝ)*|r⁻¹-(S.card:ℝ)⁻¹|=|(S.card:ℝ)/r-1| := by
    calc _ = |(S.card:ℝ)*(r⁻¹-(S.card:ℝ)⁻¹)| := by rw [abs_mul,abs_of_pos pos]
         _ = _ := by rw [mul_sub,mul_inv_cancel₀ pos.ne',div_eq_mul_inv]
  rwa [eq] at sum

section Limits
variable {N : ℕ → ℕ+} (A : (i : ℕ) → Finset (ZMod (N i)))
local notation "r" => (fun i : ℕ => Real.sqrt (N i:ℝ))

private lemma root_pos (M : ℕ+) : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast M.pos)
private lemma root_sq (M : ℕ+) : Real.sqrt (M:ℝ)^2=(M:ℝ) := Real.sq_sqrt (by positivity)

private lemma normal_rectangle {M : ℕ+} (S : Finset (ZMod M)) (p q : PMF S) (U V : Finset S) :
    mass p U*mass q V≤ ((U.card:ℝ)/Real.sqrt (M:ℝ))*((V.card:ℝ)/Real.sqrt (M:ℝ))+
        Real.sqrt (chiSquare S p q) := by
  have h := rectangle_budget p q (cyclicSum S) (by exact_mod_cast M.pos : (0:ℝ)<M)
    (chi_diffuse S p q) U V
  rwa [div_mul_div_comm,← pow_two,root_sq]

private lemma partition_limit (big : Tendsto (fun i => (N i).val) atTop atTop)
    (p q : (i : ℕ) → PMF (A i)) (B : ℕ → ℝ) (budget : Tendsto B atTop (𝓝 2))
    (size : ∀ i, ((A i).card:ℝ)/r i≤B i) (uniform : Tendsto (fun i => chiSquare (A i) (p i) (q i)) atTop (𝓝 0)) :
    ∃ U : (i : ℕ) → Finset (A i),
      Tendsto (fun i => ((U i).card:ℝ)/r i) atTop (𝓝 1) ∧
      Tendsto (fun i => ((U i)ᶜ.card:ℝ)/r i) atTop (𝓝 1) ∧
      Tendsto (fun i => (1-mass (p i) (U i))+(1-mass (q i) (U i)ᶜ)) atTop (𝓝 0) := by
  classical
  choose U bound using fun i => exists_partition_of_error (p i) (q i) (fun a : A i => (a:ZMod (N i)))
  let u i := ((U i).card:ℝ)/r i
  let v i := ((U i)ᶜ.card:ℝ)/r i
  let w i := (1-mass (p i) (U i))+(1-mass (q i) (U i)ᶜ)
  let δ i := Real.sqrt (chiSquare (A i) (p i) (q i))
  have wrong_pos i : 0≤w i := add_nonneg (sub_nonneg.mpr (prob_le_one _ _)) (sub_nonneg.mpr (prob_le_one _ _))
  have u0 i : 0≤u i := by dsimp [u];positivity
  have v0 i : 0≤v i := by dsimp [v];positivity
  have dlim : Tendsto δ atTop (𝓝 0) := by simpa [δ] using uniform.sqrt
  have rlim := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
  have ilim : Tendsto (fun i => (r i)⁻¹) atTop (𝓝 0) := rlim.inv_tendsto_atTop
  have wlim : Tendsto w atTop (𝓝 0) := by
    have lim : Tendsto (fun i => Real.sqrt (B i*((r i)⁻¹+δ i))) atTop (𝓝 0) := by
      simpa using (budget.mul (ilim.add dlim)).sqrt
    apply squeeze_zero wrong_pos _ lim
    intro i
    apply Real.le_sqrt_of_sq_le
    let E := squaredError (law (p i) (q i) (cyclicSum (A i)))
    have eq : δ i=r i*Real.sqrt E := by
      dsimp [δ,chiSquare,E];rw [Real.sqrt_mul (by positivity)]
    have rr := root_sq (N i)
    have rp := root_pos (N i)
    have b := bound i
    rw [Fintype.card_coe,ZMod.card] at b
    change (w i)^2 ≤ ((A i).card:ℝ)*((N i:ℝ)⁻¹+Real.sqrt E) at b
    calc
      _ ≤ _ := b
      _ = (((A i).card:ℝ)/r i)*((r i)⁻¹+δ i) := by rw [eq,← rr];field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (size i) (by dsimp [δ];positivity)
  have sum i : u i+v i≤B i := by
    have card := card_add_card_compl (U i)
    rw [Fintype.card_coe] at card
    have cast : ((U i).card:ℝ)+((U i)ᶜ.card:ℝ)=(A i).card := by exact_mod_cast card
    simpa only [u,v,← add_div,cast] using size i
  have prod i : 1-(w i+δ i) ≤ u i*v i := by
    have h := normal_rectangle (A i) (p i) (q i) (U i) (U i)ᶜ
    change mass _ _*mass _ _≤u i*v i+δ i at h
    have b := mul_nonneg (sub_nonneg.mpr (prob_le_one (p i) (U i))) (sub_nonneg.mpr (prob_le_one (q i) (U i)ᶜ))
    dsimp [w]; nlinarith only [h,b]
  have both := balance_scalar u v B (fun i => w i+δ i) u0 v0 sum prod budget (by simpa using wlim.add dlim)
  exact ⟨U,both.1,both.2,wlim⟩

set_option maxHeartbeats 600000 in
/-- At the coefficient-two budget, vanishing Pearson divergence yields
disjoint balanced sides whose unweighted representation counts tend to one
in mean square. Both original marginals approach the respective fair masses. -/
theorem extract_rectangles (big : Tendsto (fun i => (N i).val) atTop atTop)
    (p q : (i : ℕ) → PMF (A i)) (B : ℕ → ℝ) (budget : Tendsto B atTop (𝓝 2))
    (size : ∀ i, ((A i).card:ℝ)/r i≤B i) (uniform : Tendsto (fun i => chiSquare (A i) (p i) (q i)) atTop (𝓝 0)) :
    ∃ S T : (i : ℕ) → Finset (A i), (∀ i, Disjoint (S i) (T i)) ∧
      Tendsto (fun i => ((S i).card:ℝ)/r i) atTop (𝓝 1) ∧
      Tendsto (fun i => ((T i).card:ℝ)/r i) atTop (𝓝 1) ∧
      Tendsto (fun i => countError (cyclicSum (A i)) (S i) (T i)) atTop (𝓝 0) ∧
      Tendsto (fun i => fairError (p i) (S i) (S i).card) atTop (𝓝 0) ∧
      Tendsto (fun i => fairError (q i) (T i) (T i).card) atTop (𝓝 0) := by
  classical
  obtain ⟨U,ul,vl,wl⟩ := partition_limit A big p q B budget size uniform
  let V i := (U i)ᶜ
  let u i := ((U i).card:ℝ)/r i
  let v i := ((V i).card:ℝ)/r i
  let w i := (1-mass (p i) (U i))+(1-mass (q i) (V i))
  let δ i := Real.sqrt (chiSquare (A i) (p i) (q i))
  let slack i := u i*v i-1+w i+δ i
  let e i := |u i-1|+|v i-1|+Real.sqrt |slack i|+(r i)⁻¹
  change Tendsto u _ _ at ul
  change Tendsto v _ _ at vl
  change Tendsto w _ _ at wl
  have dl : Tendsto δ atTop (𝓝 0) := by simpa [δ] using uniform.sqrt
  have il : Tendsto (fun i => (r i)⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)).inv_tendsto_atTop
  have sl : Tendsto slack atTop (𝓝 0) := by simpa [slack] using ((((ul.mul vl).sub_const 1).add wl).add dl)
  have el : Tendsto e atTop (𝓝 0) := by simpa [e] using ((((ul.sub_const 1).abs.add (vl.sub_const 1).abs).add sl.abs.sqrt).add il)
  let S i := retain (U i) (p i) (r i) (e i)
  let T i := retain (V i) (q i) (r i) (e i)
  let a i := ((S i).card:ℝ)/r i
  let b i := ((T i).card:ℝ)/r i
  have good (i) : 0<e i ∧ 1-e i≤u i ∧ 1-e i≤v i ∧ slack i≤e i^2 := by
    have rr := inv_pos.mpr (root_pos (N i))
    have ru := abs_nonneg (u i-1)
    have rv := abs_nonneg (v i-1)
    have rs := Real.sqrt_nonneg |slack i|
    have se : Real.sqrt |slack i| ≤ e i := by dsimp [e];linarith
    refine ⟨by dsimp [e];positivity,?_,?_,?_⟩
    · dsimp [e];linarith [neg_le_abs (u i-1)]
    · dsimp [e];linarith [neg_le_abs (v i-1)]
    · exact (le_abs_self _).trans ((Real.sq_sqrt (abs_nonneg _)) ▸ (sq_le_sq₀ rs (rs.trans se)).mpr se)
  have ranges (i) : (u i-e i≤a i ∧ a i≤u i) ∧ (v i-e i≤b i ∧ b i≤v i) := by
    obtain ⟨ep,gu,gv,sc⟩ := good i
    have rect := normal_rectangle (A i) (p i) (q i)
    refine ⟨retain_card (U i) (V i) (p i) (q i) (r i) (e i) (δ i) (root_pos _) ep
      (fun X _ => rect X _) gv ?_,retain_card (V i) (U i) (q i) (p i) (r i) (e i) (δ i) (root_pos _) ep
      (fun X _ => by simpa only [mul_comm] using rect (U i) X) gu ?_⟩
    · dsimp only [slack,u,v,w] at sc;linarith only [sc]
    · dsimp only [slack,u,v,w] at sc;nlinarith only [sc]
  have al : Tendsto a atTop (𝓝 1) := tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using ul.sub el) ul (fun i => (ranges i).1.1) (fun i => (ranges i).1.2)
  have bl : Tendsto b atTop (𝓝 1) := tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using vl.sub el) vl (fun i => (ranges i).2.1) (fun i => (ranges i).2.2)
  let θ i := 1-2*e i
  have tl : Tendsto θ atTop (𝓝 1) := by simpa [θ] using (tendsto_const_nhds (x:=(1:ℝ))).sub (el.const_mul 2)
  have first i j (h : j∈S i) : θ i≤r i*((p i) j).toReal := (mem_filter.mp h).2
  have second i j (h : j∈T i) : θ i≤r i*((q i) j).toReal := (mem_filter.mp h).2
  have disj i : Disjoint (S i) (T i) := Disjoint.mono (filter_subset _ _) (filter_subset _ _) disjoint_compl_right
  have fair (R : (i : ℕ) → PMF (A i)) (W : (i : ℕ) → Finset (A i))
      (sz : Tendsto (fun i => ((W i).card:ℝ)/r i) atTop (𝓝 1)) (atom : ∀ i, ∀ j ∈ W i, θ i ≤ r i*((R i) j).toReal) :
      Tendsto (fun i => fairError (R i) (W i) (W i).card) atTop (𝓝 0) := by
    have base : Tendsto (fun i => fairError (R i) (W i) (r i)) atTop (𝓝 0) := by
      apply squeeze_zero (fun i => sum_nonneg fun _ _ => abs_nonneg _) (fun i => fair_error_le _ _ _ _
        (root_pos _) (by dsimp [θ];linarith [(good i).1]) (atom i))
      convert ((sz.const_add 1).sub ((sz.const_mul 2).mul tl)) using 1; norm_num
    apply squeeze_zero' (Eventually.of_forall fun i => sum_nonneg fun _ _ => abs_nonneg _) _ (by simpa using base.add (sz.sub_const 1).abs)
    filter_upwards [sz.eventually_const_lt (by norm_num : (0:ℝ)<1)] with i hi
    apply fair_normalize
    apply card_pos.mp
    exact_mod_cast (pos_of_mul_pos_left (b:= (r i)⁻¹) (by simpa only [← div_eq_mul_inv] using hi) (by positivity) : 0<((W i).card:ℝ))
  refine ⟨S,T,disj,al,bl,?_,fair p S al first,fair q T bl second⟩
  let D i := chiSquare (A i) (p i) (q i)
  have ub : Tendsto (fun i => (1+D i)/(θ i)^4 - 2*(a i*b i)+1) atTop (𝓝 0) := by
    have h := ((((uniform.const_add 1).div (tl.pow 4) (by norm_num)).sub ((al.mul bl).const_mul 2)).add_const 1)
    norm_num at h
    exact h
  apply squeeze_zero' (Eventually.of_forall (fun i => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _))) _ ub
  filter_upwards [tl.eventually_const_lt (by norm_num : (0:ℝ)<1)] with i pos
  have z := retained_energy (p i) (q i) (cyclicSum (A i)) (S i) (T i) (r i) (θ i)
    (root_pos _) pos.le (by rw [ZMod.card,root_sq]) (first i) (second i)
  change countError (cyclicSum (A i)) (S i) (T i)≤_
  rw [counts_expand,ZMod.card]
  rw [ZMod.card] at z
  have h : (∑ z, (pairCount (cyclicSum (A i)) (S i) (T i) z:ℝ)^2)/(N i:ℝ)≤(1+D i)/θ i^4 := by
    apply (le_div_iff₀ (pow_pos pos 4)).mpr
    rwa [mul_comm] at z
  have ab : a i*b i=(S i).card*(T i).card/(N i:ℝ) := by dsimp [a,b];rw [div_mul_div_comm,←pow_two,root_sq]
  rw [ab]
  linarith only [h]
end Limits

section Converse
variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] in
private lemma fair_atom (S T : Finset ι) (s : S.Nonempty) (t : T.Nonempty) (obs : ι → ι → G) (z : G) :
    ((law (PMF.uniformOfFinset S s) (PMF.uniformOfFinset T t) obs) z).toReal =
      (pairCount obs S T z:ℝ)/((S.card:ℝ)*T.card) := by
  classical
  let F := (S×ˢT).filter fun x => obs x.1 x.2=z
  have term (x : ι×ι) : (if obs x.1 x.2=z then
      ((PMF.uniformOfFinset S s) x.1).toReal*((PMF.uniformOfFinset T t) x.2).toReal else 0)
      = if x∈F then ((S.card:ℝ)*T.card)⁻¹ else 0 := by
    by_cases a : x.1∈S <;> by_cases b : x.2∈T <;> by_cases eq : obs x.1 x.2=z <;>
      simp [F,a,b,eq,PMF.uniformOfFinset_apply,mul_comm]
  rw [atom]; simp only [term,sum_ite_mem,univ_inter,sum_const,nsmul_eq_mul,div_eq_mul_inv]
  rfl

/-- Replacing both laws by fair laws gives an exact identity between the
two squared errors, including the correction for a rectangle of the wrong size. -/
theorem fair_energy_identity {M : ℕ+} (A : Finset (ZMod M)) (S T : Finset A)
    (s : S.Nonempty) (t : T.Nonempty) :
    let y := (S.card:ℝ)*T.card/M
    chiSquare A (PMF.uniformOfFinset S s) (PMF.uniformOfFinset T t)*y^2+(1-y)^2 =
      countError (cyclicSum A) S T := by
  let R := law (PMF.uniformOfFinset S s) (PMF.uniformOfFinset T t) (cyclicSum A)
  let n := (S.card:ℝ)*T.card
  have hn : 0<n := mul_pos (by exact_mod_cast card_pos.mpr s) (by exact_mod_cast card_pos.mpr t)
  have hm : (0:ℝ)<M := by exact_mod_cast M.pos
  have col := collision_mass R
  rw [ZMod.card] at col
  have e : ∑ z, (R z).toReal^2=(∑ z, (pairCount (cyclicSum A) S T z:ℝ)^2)/n^2 := by
    rw [sum_div]
    apply sum_congr rfl; intro z _
    change ((law _ _ _) z).toReal^2=_
    rw [fair_atom,div_pow]
  dsimp only
  rw [counts_expand,ZMod.card]
  change (M:ℝ)*squaredError R*(n/M)^2+(1-n/M)^2=_-2*(n/M)+1
  rw [e] at col
  have d : (M:ℝ)*squaredError R = (M:ℝ)*((∑ z, (pairCount (cyclicSum A) S T z:ℝ)^2)/n^2)-1 := by linarith only [col]
  rw [d]; field_simp;ring
end Converse

section
variable {N : ℕ → ℕ+} (A : (i : ℕ) → Finset (ZMod (N i)))
local notation "r" => (fun i : ℕ => Real.sqrt (N i:ℝ))

/-- At budget coefficient two, a prescribed sequence of nonempty seeds
admits sums with vanishing Pearson divergence exactly when it contains
disjoint balanced rectangles with unweighted mean squared count error tending to zero. -/
theorem pearson_iff_rectangles (big : Tendsto (fun i => (N i).val) atTop atTop)
    [∀ i, Nonempty (A i)] (B : ℕ → ℝ) (budget : Tendsto B atTop (𝓝 2))
    (size : ∀ i, ((A i).card:ℝ)/r i≤B i) :
    (∃ p q : (i : ℕ) → PMF (A i), Tendsto (fun i => chiSquare (A i) (p i) (q i)) atTop (𝓝 0)) ↔
    ∃ S T : (i : ℕ) → Finset (A i), (∀ i, Disjoint (S i) (T i)) ∧
      Tendsto (fun i => ((S i).card:ℝ)/r i) atTop (𝓝 1) ∧
      Tendsto (fun i => ((T i).card:ℝ)/r i) atTop (𝓝 1) ∧
      Tendsto (fun i => countError (cyclicSum (A i)) (S i) (T i)) atTop (𝓝 0) := by
  classical
  constructor
  · rintro ⟨p,q,h⟩
    obtain ⟨S,T,d,s,t,m,_⟩ := extract_rectangles A big p q B budget size h
    exact ⟨S,T,d,s,t,m⟩
  rintro ⟨S,T,_,sl,tl,err⟩
  let lawOn (i : ℕ) (U : Finset (A i)) := if h : U.Nonempty then PMF.uniformOfFinset U h else
    PMF.pure (Classical.arbitrary (A i))
  refine ⟨fun i => lawOn i (S i),fun i => lawOn i (T i),?_⟩
  let y i := ((S i).card:ℝ)*(T i).card/(N i:ℝ)
  have yl : Tendsto y atTop (𝓝 1) := by
    simpa only [y,div_mul_div_comm,← pow_two,root_sq,one_pow] using sl.mul tl
  have lim : Tendsto (fun i => (countError (cyclicSum (A i)) (S i) (T i)-(1-y i)^2)/y i^2) atTop (𝓝 0) := by
    simpa [Pi.div_def] using (err.sub (((tendsto_const_nhds (x:=(1:ℝ))).sub yl).pow 2)).div (yl.pow 2) (by norm_num)
  refine lim.congr' ?_
  filter_upwards [sl.eventually_const_lt (by norm_num : (0:ℝ)<1),tl.eventually_const_lt (by norm_num : (0:ℝ)<1)]
    with i hs ht
  have spos : 0<((S i).card:ℝ) := pos_of_mul_pos_left (b:= (r i)⁻¹) (by simpa only [← div_eq_mul_inv] using hs) (by positivity)
  have tpos : 0<((T i).card:ℝ) := pos_of_mul_pos_left (b:= (r i)⁻¹) (by simpa only [← div_eq_mul_inv] using ht) (by positivity)
  have sp : (S i).Nonempty := card_pos.mp (by exact_mod_cast spos)
  have tp : (T i).Nonempty := card_pos.mp (by exact_mod_cast tpos)
  have yp : 0<y i := by dsimp [y];positivity
  simp only [lawOn,dif_pos sp,dif_pos tp]
  apply (div_eq_iff (pow_ne_zero 2 yp.ne')).mpr
  have h := fair_energy_identity (A i) (S i) (T i) sp tp
  change _*(y i)^2+(1-y i)^2=countError _ _ _ at h
  linarith
end

#print axioms trim_bound
#print axioms retained_energy
#print axioms extract_rectangles
#print axioms fair_energy_identity
#print axioms pearson_iff_rectangles
end Green33BalancedRectangles
