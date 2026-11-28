import Green33SumsetFactors
import Green33TailEnergy
/-! Sparse intersections with additive factorizations of critical cyclic bases. -/
open Finset Filter Green33SumsetFactors
open scoped Pointwise Topology Filter
namespace Green33FactorDensity

/-- Unordered pairs beyond one ordinary representation per occupied sum. -/
abbrev excess {G : Type*} [AddCommMonoid G] [DecidableEq G] (T : Finset G) : ℕ :=
  (T.card+1).choose 2-(T+T).card

private theorem scale {w a b h k C : ℝ} (wa : 0≤a) (wb : 0≤b) (wh : 0≤h) (kp : 0<k)
    (cost : a*b≤C*k) (bound : w^2≤a*b*(min a b+2*Real.sqrt h)) :
    (w/k)^2≤C*(Real.sqrt (C/k)+2*Real.sqrt (h/k^2)) := by
  have K : 0≤C := nonneg_of_mul_nonneg_left ((mul_nonneg wa wb).trans cost) kp
  have prod : a*b/k≤C := (div_le_iff₀ kp).mpr cost
  have small : (min a b)^2≤a*b := by
    rcases le_total a b with ab|ba
    · rw [min_eq_left ab,sq];exact mul_le_mul_of_nonneg_left ab wa
    · rw [min_eq_right ba,sq];exact mul_le_mul_of_nonneg_right ba wb
  have x : (min a b/k)^2≤C/k := by
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos kp) kp]
    nlinarith only [mul_le_mul_of_nonneg_right (small.trans cost) kp.le]
  have rt:=Real.sqrt_le_sqrt x
  rw [Real.sqrt_sq (div_nonneg (le_min wa wb) kp.le)] at rt
  rw [Real.sqrt_div wh,Real.sqrt_sq kp.le]
  calc
    _ ≤ a*b*(min a b+2*Real.sqrt h)/k^2 := by rw [div_pow];exact div_le_div_of_nonneg_right bound (sq_nonneg k)
    _ = (a*b/k)*(min a b/k+2*(Real.sqrt h/k)) := by ring
    _ ≤ _ := mul_le_mul prod (by linarith only [rt]) (by positivity) K

section Families
variable {ι : Type*} {l : Filter ι} {G : ι→Type*} [∀ i,AddCommMonoid (G i)] [∀ i,DecidableEq (G i)]
    (T X Y : ∀ i,Finset (G i))

/-- Uniform over arbitrary relative factor sizes. Only a vanishing fraction
of a quasi-Sidon set can lie above the capacity of the larger factor. -/
theorem uniform_surplus (large : Tendsto (fun i => (T i).card) l atTop)
    (few : Tendsto (fun i => (excess (T i):ℝ)/((T i).card:ℝ)^2) l (𝓝 0))
    {C : ℝ} (cost : ∀ᶠ i in l,((X i).card:ℝ)*(Y i).card≤C*(T i).card) :
    Tendsto (fun i => (((T i∩(X i+Y i)).card-max (X i).card (Y i).card : ℕ) : ℝ) / (T i).card) l (𝓝 0) := by
  let w i:=(T i∩(X i+Y i)).card-max (X i).card (Y i).card
  have tiny:=(tendsto_const_nhds (x:=C)).div_atTop ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp large)
  have limit:=(tiny.sqrt.add (few.sqrt.const_mul 2)).const_mul C
  simp only [Real.sqrt_zero,mul_zero,add_zero] at limit
  have sqs : Tendsto (fun i => ((w i:ℝ)/(T i).card)^2) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => sq_nonneg _) _ limit
    filter_upwards [cost,large.eventually_gt_atTop 0] with i ci ki
    exact scale (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast ki)
      ci (surplus_bound (T i) (X i) (Y i))
  have nn (i) : 0≤(w i:ℝ)/(T i).card := by positivity
  simpa only [Real.sqrt_sq (nn _),Real.sqrt_zero] using sqs.sqrt

/-- If both factors grow, their sumset contains a vanishing fraction of the
set. Repeated representations by the factors are allowed. -/
theorem growing_escape (large : Tendsto (fun i => (T i).card) l atTop)
    (few : Tendsto (fun i => (excess (T i):ℝ)/((T i).card:ℝ)^2) l (𝓝 0))
    {C : ℝ} (cost : ∀ᶠ i in l,((X i).card:ℝ)*(Y i).card≤C*(T i).card)
    (ax : Tendsto (fun i => (X i).card) l atTop) (by' : Tendsto (fun i => (Y i).card) l atTop) :
    Tendsto (fun i => ((T i∩(X i+Y i)).card:ℝ)/(T i).card) l (𝓝 0) := by
  have h:=uniform_surplus T X Y large few cost
  have amin : Tendsto (fun i => min (X i).card (Y i).card) l atTop := tendsto_inf_atTop l ax by'
  have small := (tendsto_const_nhds (x:=C)).div_atTop ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp amin)
  have lim:=h.add small
  rw [add_zero] at lim
  apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ lim
  filter_upwards [cost,large.eventually_gt_atTop 0,amin.eventually_gt_atTop 0] with i ci tk tm
  let e:=(T i∩(X i+Y i)).card
  let a:=(X i).card
  let b:=(Y i).card
  let k:=(T i).card
  have eq : max a b*min a b=a*b := by
    rcases le_total a b with ab|ba
    · simp [ab,mul_comm]
    · simp [ba]
  have pk : (0:ℝ)<k := by exact_mod_cast tk
  have pm : (0:ℝ)<((min a b : ℕ):ℝ) := by exact_mod_cast tm
  have cap : ((max a b:ℕ):ℝ)/(k:ℝ)≤C/(min a b:ℕ) := by
    rw [div_le_div_iff₀ pk pm]
    calc
      _ = ((a*b:ℕ):ℝ) := by exact_mod_cast eq
      _ ≤ _ := by simpa [a,b,k] using ci
  have ext : (e:ℝ)≤((e-max a b:ℕ):ℝ)+(max a b:ℕ) := by exact_mod_cast (show e≤e-max a b+max a b by omega)
  exact (div_le_div_of_nonneg_right ext pk.le).trans (by rw [add_div];exact add_le_add le_rfl cap)


/-- A covering factorization costing at most C times the label count has
smaller factor eventually below every positive integer r>C. -/
theorem cover_threshold (large : Tendsto (fun i => (T i).card) l atTop)
    (few : Tendsto (fun i => (excess (T i):ℝ)/((T i).card:ℝ)^2) l (𝓝 0))
    {C : ℝ} (cost : ∀ᶠ i in l,((X i).card:ℝ)*(Y i).card≤C*(T i).card)
    (covered : ∀ᶠ i in l,T i⊆X i+Y i) (r : ℕ) (pos : 0<r) (gap : C<(r:ℝ)) :
    ∀ᶠ i in l,min (X i).card (Y i).card<r := by
  have h:=uniform_surplus T X Y large few cost
  have rp : (0:ℝ)<r := by exact_mod_cast pos
  have δ : 0<1-C/(r:ℝ) := sub_pos.mpr ((div_lt_one rp).mpr gap)
  filter_upwards [cost,covered,large.eventually_gt_atTop 0,h.eventually_lt_const δ] with i ci inc big small
  rw [inter_eq_left.mpr inc] at small
  let k:=(T i).card
  let a:=(X i).card
  let b:=(Y i).card
  let M:=max a b
  have kp : (0:ℝ)<k := by exact_mod_cast big
  by_contra! many
  have prod : r*M≤a*b := by
    have bound:=Nat.mul_le_mul_right M many
    rcases le_total a b with ab|ba
    · simpa [M,a,b,min_eq_left ab,max_eq_right ab] using bound
    · simpa [M,a,b,min_eq_right ba,max_eq_left ba,Nat.mul_comm] using bound
  have p : (r:ℝ)*M≤C*k := (show (r:ℝ)*M≤(a:ℝ)*b by exact_mod_cast prod).trans ci
  have maxle : (M:ℝ)/(k:ℝ)≤C/r := (div_le_div_iff₀ kp rp).mpr (by linarith only [p])
  have dk : (k:ℝ)≤((k-M:ℕ):ℝ)+M := by exact_mod_cast (show k≤k-M+M by omega)
  have one:=(div_le_div_of_nonneg_right dk kp.le)
  rw [div_self kp.ne',add_div] at one
  change (((k-M:ℕ):ℝ)/(k:ℝ)) <1-C/(r:ℝ) at small
  linarith only [one,maxle,small]



/-- Even positive-density occupancy forces the factor product divided by the
set size to tend to infinity when both factors grow. -/
theorem product_diverges (large : Tendsto (fun i => (T i).card) l atTop)
    (few : Tendsto (fun i => (excess (T i):ℝ)/((T i).card:ℝ)^2) l (𝓝 0))
    (ax : Tendsto (fun i => (X i).card) l atTop) (by' : Tendsto (fun i => (Y i).card) l atTop)
    {η : ℝ} (pos : 0<η) (occupied : ∀ᶠ i in l,η≤((T i∩(X i+Y i)).card:ℝ)/(T i).card) :
    Tendsto (fun i => ((X i).card:ℝ)*(Y i).card/(T i).card) l atTop := by
  apply tendsto_atTop.mpr
  intro C
  let S : Set ι:={i | ((X i).card:ℝ)*(Y i).card≤C*(T i).card}
  have onS : ∀ᶠ i in l⊓𝓟 S,((X i).card:ℝ)*(Y i).card≤C*(T i).card :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h => h)
  have h:=growing_escape T X Y (large.mono_left inf_le_left) (few.mono_left inf_le_left) onS
    (ax.mono_left inf_le_left) (by'.mono_left inf_le_left)
  have cut:=eventually_inf_principal.mp (h.eventually_lt_const pos)
  filter_upwards [cut,occupied,large.eventually_gt_atTop 0] with i less lower ki
  have hn : i∉S := fun s => (not_lt_of_ge lower) (less s)
  have strict : C*(T i).card<((X i).card:ℝ)*(Y i).card := lt_of_not_ge hn
  exact ((lt_div_iff₀ (by exact_mod_cast ki : (0:ℝ)<(T i).card)).mpr strict).le

end Families
#print axioms product_diverges
#print axioms cover_threshold
#print axioms uniform_surplus
#print axioms growing_escape

section Cyclic
variable {ι : Type*} {l : Filter ι} (M : ι→ℕ+) (T X Y : ∀ i,Finset (ZMod (M i)))
    (big : Tendsto (fun i => (M i).val) l atTop)
    (critical : Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (M i)) l (𝓝 (Real.sqrt 2)))

include big critical

private theorem cyclic_parameters
    (dense : Tendsto (fun i => ((T i+T i).card:ℝ)/(M i:ℝ)) l (𝓝 1)) :
    Tendsto (fun i => (T i).card) l atTop ∧
    Tendsto (fun i => (excess (T i):ℝ)/((T i).card:ℝ)^2) l (𝓝 0) := by
  obtain ⟨lin,quad⟩:=Green33TailEnergy.card_limits M (fun i => (T i).card) big critical
  have grow:=Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp big)
  refine ⟨(tendsto_natCast_atTop_iff (R:=ℝ)).mp ?_,?_⟩
  · have h:=critical.pos_mul_atTop (by positivity) grow
    exact h.congr (fun i => by dsimp; field_simp [Real.sqrt_ne_zero'.mpr (by exact_mod_cast (M i).pos : (0:ℝ)<(M i).val)])
  · have h:=(((quad.add lin).div_const 2).sub dense)
    norm_num at h
    have lim : Tendsto (fun i => (excess (T i):ℝ)/(M i:ℝ)) l (𝓝 0) := by
      apply h.congr
      intro i
      let f : Sym2 (ZMod (M i))→ZMod (M i) := Sym2.lift ⟨(·+·),add_comm⟩
      have sub : T i+T i⊆(T i).sym2.image f := by
        intro z hz;obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hz
        exact mem_image.mpr ⟨Sym2.mk a b,mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩
      have cap:= (card_le_card sub).trans card_image_le
      rw [card_sym2] at cap
      rw [excess,Nat.cast_sub cap,Nat.cast_choose_two,Nat.cast_add_one]
      ring
    have ratio:=lim.div quad (by norm_num)
    rw [zero_div] at ratio
    apply ratio.congr
    intro i
    change ((excess (T i):ℝ)/(M i).val)/(((T i).card:ℝ)^2/(M i).val)=_
    rw [div_div_div_cancel_right₀ (by exact_mod_cast (M i).ne_zero : ((M i).val:ℝ)≠0)]

/-- The same obstruction already holds for doubled sums covering 1-o(1) of
the modulus, at the ordinary Green 33 size coefficient. -/
theorem almost_basis_stability (dense : Tendsto (fun i => ((T i+T i).card:ℝ)/(M i:ℝ)) l (𝓝 1))
    {C : ℝ} (cost : ∀ᶠ i in l,((X i).card:ℝ)*(Y i).card≤C*(T i).card) :
    Tendsto (fun i => (((T i∩(X i+Y i)).card-max (X i).card (Y i).card:ℕ):ℝ)/(T i).card) l (𝓝 0) := by
  obtain ⟨large,few⟩:=cyclic_parameters M T big critical dense
  exact uniform_surplus T X Y large few cost

omit big critical in
private theorem full_density (full : ∀ i,T i+T i=univ) :
    Tendsto (fun i => ((T i+T i).card:ℝ)/(M i:ℝ)) l (𝓝 1) := by
  apply tendsto_const_nhds.congr
  intro i
  rw [full,card_univ,ZMod.card,div_self (by exact_mod_cast (M i).ne_zero)]

/-- Any full Green 33 witness family escapes every product-budget sumset of
two growing factors, allowing arbitrary collisions and additional labels. -/
theorem green33_escape (full : ∀ i,T i+T i=univ)
    {C : ℝ} (cost : ∀ᶠ i in l,((X i).card:ℝ)*(Y i).card≤C*(T i).card)
    (ax : Tendsto (fun i => (X i).card) l atTop) (by' : Tendsto (fun i => (Y i).card) l atTop) :
    Tendsto (fun i => ((T i∩(X i+Y i)).card:ℝ)/(T i).card) l (𝓝 0) := by
  obtain ⟨large,few⟩:=cyclic_parameters M T big critical (full_density M T full)
  exact growing_escape T X Y large few cost ax by'

/-- A full basis covered by X+Y with |X||Y|≤C|T| eventually needs a smaller
factor of size at most floor(C). -/
theorem green33_cover (full : ∀ i,T i+T i=univ)
    {C : ℝ} (cost : ∀ᶠ i in l,((X i).card:ℝ)*(Y i).card≤C*(T i).card)
    (covered : ∀ᶠ i in l,T i⊆X i+Y i) (r : ℕ) (pos : 0<r) (gap : C<(r:ℝ)) :
    ∀ᶠ i in l,min (X i).card (Y i).card<r := by
  obtain ⟨large,few⟩:=cyclic_parameters M T big critical (full_density M T full)
  exact cover_threshold T X Y large few cost covered r pos gap

/-- Any sumset of two growing factors capturing a fixed positive fraction of
the Green witnesses has superlinear product of factor cardinalities. -/
theorem green33_factor_cost (full : ∀ i,T i+T i=univ)
    (ax : Tendsto (fun i => (X i).card) l atTop) (by' : Tendsto (fun i => (Y i).card) l atTop)
    {η : ℝ} (pos : 0<η) (occupied : ∀ᶠ i in l,η≤((T i∩(X i+Y i)).card:ℝ)/(T i).card) :
    Tendsto (fun i => ((X i).card:ℝ)*(Y i).card/(T i).card) l atTop := by
  obtain ⟨large,few⟩:=cyclic_parameters M T big critical (full_density M T full)
  exact product_diverges T X Y large few ax by' pos occupied

end Cyclic
#print axioms green33_factor_cost
#print axioms almost_basis_stability
#print axioms green33_escape
#print axioms green33_cover

end Green33FactorDensity
