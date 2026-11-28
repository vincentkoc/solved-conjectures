import Green33QuasiSidon

/-! Integer pair sums seen from rotated interval copies of a cyclic set. -/

open Finset Filter Green33ApproximateCovers
open scoped Pointwise Topology

namespace Green33RotatedIntervals

variable {M : ℕ+}

/-- Integer representative of a point in the interval starting at the cut. -/
def atCut (u x : ZMod M) : ℕ := (x-u).val

/-- Sum of the two ordinary integer representatives, including diagonal pairs. -/
def liftSum (u : ZMod M) : Sym2 (ZMod M) → ℕ :=
  Sym2.lift ⟨fun x y => atCut u x+atCut u y,fun _ _ => Nat.add_comm ..⟩

/-- The number of unordered pairs beyond the first per occupied integer sum. -/
def cutExcess (A : Finset (ZMod M)) (u : ZMod M) : ℕ := excess A.sym2 (liftSum u)

private theorem residue_eq (u : ZMod M) (t : Sym2 (ZMod M)) :
    ((liftSum u t:ℕ):ZMod M)+u+u=ordinarySum t := by
  obtain ⟨x,y⟩ := t
  change (((x-u).val+(y-u).val:ℕ):ZMod M)+u+u=x+y
  rw [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val]
  abel

private theorem lift_lt (u : ZMod M) (t : Sym2 (ZMod M)) : liftSum u t<2*M.val := by
  obtain ⟨x,y⟩ := t
  change (x-u).val+(y-u).val<2*M.val
  have hx := (x-u).val_lt
  have hy := (y-u).val_lt
  omega

private theorem two_lifts (x : ZMod M) (n : ℕ) (en : (n:ZMod M)=x) (small : n<2*M.val) :
    n=x.val ∨ n=x.val+M.val := by
  have e := congrArg ZMod.val en
  rw [ZMod.val_natCast] at e
  by_cases h : n<M.val
  · exact Or.inl ((Nat.mod_eq_of_lt h).symm.trans e)
  · have lo : n-M.val<M.val := by omega
    rw [Nat.mod_eq_sub_mod (by omega : M.val≤n),Nat.mod_eq_of_lt lo] at e
    omega

/-- Every integer cut can only separate modular pairs with the same sum. -/
theorem cut_le_modular (A : Finset (ZMod M)) (u) : cutExcess A u≤pairExcess false A := by
  let f (n : ℕ) : ZMod M := n+u+u
  have eq : (A.sym2.image (liftSum u)).image f = A.sym2.image ordinarySum := by
    rw [image_image]
    apply image_congr
    exact fun t _ => residue_eq u t
  have bound := card_image_le (s:=A.sym2.image (liftSum u)) (f:=f)
  rw [eq] at bound
  have e := excess_add_occupied A.sym2 (liftSum u)
  have m := excess_add_occupied A.sym2 ordinarySum
  change excess A.sym2 (liftSum u)≤excess A.sym2 ordinarySum
  omega

private theorem excess_mono {P G : Type*} [DecidableEq G] {S T : Finset P} (f : P → G) (sub : S⊆T) :
    excess S f≤excess T f := by
  unfold excess
  calc
    _ ≤ ∑ z ∈ S.image f, ((T.filter fun a => f a=z).card-1) := by
      apply sum_le_sum
      intro z _
      exact Nat.sub_le_sub_right (card_le_card (filter_subset_filter _ sub)) _
    _ ≤ _ := sum_le_sum_of_subset (image_subset_image sub)

/-- Labels lying within `h` places after a cut. -/
def window (A : Finset (ZMod M)) (u : ZMod M) (h : ℕ) : Finset (ZMod M) :=
  A.filter fun x => atCut u x<h

private theorem window_lift_card (A : Finset (ZMod M)) (u v : ZMod M) (h : ℕ) :
    ((window A u h).sym2.image (liftSum v)).card ≤ 4*h := by
  let code (t : ℕ×ℕ) := ((t.1:ZMod M)+u+u-v-v).val+t.2*M.val
  let pool := (range (2*h))×ˢ(range 2)
  have sub : (window A u h).sym2.image (liftSum v)⊆pool.image code := by
    intro n hn
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hn
    obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hab
    let t := s(a,b)
    have low : liftSum u t<2*h := by
      change atCut u a+atCut u b<2*h
      have a' := (mem_filter.mp ha).2
      have b' := (mem_filter.mp hb).2
      omega
    have phase : ((liftSum v t:ℕ):ZMod M)=((liftSum u t:ℕ):ZMod M)+u+u-v-v := by
      rw [residue_eq]
      have ev := residue_eq v t
      rw [← ev]
      abel
    rcases two_lifts _ _ phase (lift_lt v t) with e|e
    · refine mem_image.mpr ⟨(liftSum u t,0),mk_mem_product (mem_range.mpr low) (by decide),?_⟩
      simpa only [code,zero_mul,add_zero] using e.symm
    · refine mem_image.mpr ⟨(liftSum u t,1),mk_mem_product (mem_range.mpr low) (by decide),?_⟩
      simpa only [code,one_mul] using e.symm
  have e := (card_le_card sub).trans card_image_le
  simp only [pool,card_product,card_range] at e
  omega

/-- Concentration of labels in any short arc is controlled by the excess at
any chosen integer cut, including one minimizing that excess. -/
theorem window_choose (A : Finset (ZMod M)) (u v : ZMod M) (h : ℕ) :
    ((window A u h).card+1).choose 2 ≤ 4*h+cutExcess A v := by
  let W := window A u h
  have lose := excess_mono (liftSum v) (sym2_mono (filter_subset _ A) : W.sym2⊆A.sym2)
  have cnt := excess_add_occupied W.sym2 (liftSum v)
  rw [card_sym2] at cnt
  have bound := window_lift_card A u v h
  change (W.sym2.image (liftSum v)).card≤4*h at bound
  change (W.card+1).choose 2≤4*h+excess A.sym2 (liftSum v)
  omega


private def fibreCost {P G : Type*} [DecidableEq G] (S : Finset P) (f : P → G) (z : G) : ℕ :=
  (S.filter fun a => f a=z).card-1

private theorem sum_cost_le {P G : Type*} [DecidableEq G] (S : Finset P) (f : P → G) (T : Finset G) :
    ∑ z ∈ T, fibreCost S f z≤excess S f := by
  classical
  have zero (z : G) (miss : z∉S.image f) : fibreCost S f z=0 := by
    have off : S.filter (fun a => f a=z)=∅ := filter_eq_empty_iff.mpr (fun a ha e => miss (e ▸ mem_image_of_mem _ ha))
    simp [fibreCost,off]
  calc
    _ = ∑ z ∈ T∩S.image f, fibreCost S f z := by
      symm
      exact sum_subset inter_subset_left fun z hz off => zero z (fun ha => off (mem_inter.mpr ⟨hz,ha⟩))
    _ ≤ _ := sum_le_sum_of_subset inter_subset_right

private def phase (u z : ZMod M) : ℕ := (z-u-u).val

private theorem phase_inj (u : ZMod M) : Function.Injective (phase u) := by
  intro a b eq
  have v : a-u-u=b-u-u := ZMod.val_injective _ eq
  exact sub_left_inj.mp (sub_left_inj.mp v)

private theorem band_incidence (z : ZMod M) (d : ℕ) (fit : 2*d≤M.val) :
    d≤(univ.filter fun u : ZMod M => phase u z<2*d).card := by
  let middle : ZMod M := (z.val/2:ℕ)
  let cut (i : Fin d) : ZMod M := middle-(i.val:ZMod M)
  have small (i : Fin d) : i.val<M.val := by have := i.isLt; omega
  have inj : Function.Injective cut := by
    intro i j e
    have h : (i.val:ZMod M)=(j.val:ZMod M) := sub_right_inj.mp e
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (small _)] at this
    exact Fin.ext this
  have center : (z.val%2:ℕ)+2*middle=z := by
    change ((z.val%2:ℕ):ZMod M)+2*(↑(z.val/2):ZMod M)=z
    rw [← Nat.cast_ofNat (R:=ZMod M) (n:=2),← Nat.cast_mul,← Nat.cast_add,Nat.mod_add_div,ZMod.natCast_zmod_val]
  have sub : univ.image cut⊆univ.filter (fun u : ZMod M => phase u z<2*d) := by
    intro u hu
    obtain ⟨i,_,rfl⟩ := mem_image.mp hu
    have half : z.val%2+2*i.val<2*d := by have := i.isLt; omega
    have e : z-cut i-cut i=((z.val%2+2*i.val:ℕ):ZMod M) := by
      simp only [cut,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
      linear_combination -center
    exact mem_filter.mpr ⟨mem_univ _,by
      rw [phase,e,ZMod.val_natCast,Nat.mod_eq_of_lt (half.trans_le fit)]; exact half⟩
  simpa [card_image_of_injective _ inj] using card_le_card sub


private theorem cost_fold (A : Finset (ZMod M)) (u z : ZMod M) :
    fibreCost A.sym2 ordinarySum z ≤
      (A.sym2.filter fun t => liftSum u t=phase u z).card+
        fibreCost A.sym2 (liftSum u) (phase u z+M.val) := by
  let f := liftSum u
  let P := A.sym2
  let n := phase u z
  have sub : (P.filter fun t => ordinarySum t=z)⊆
      (P.filter fun t => f t=n)∪(P.filter fun t => f t=n+M.val) := by
    intro t ht
    obtain ⟨mem,eq⟩ := mem_filter.mp ht
    have cast : ((f t:ℕ):ZMod M)=z-u-u := by rw [← eq,← residue_eq u t]; abel
    rcases two_lifts _ _ cast (lift_lt u t) with lo|hi
    · exact mem_union_left _ (mem_filter.mpr ⟨mem,lo⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem,hi⟩)
  have e := (card_le_card sub).trans (card_union_le _ _)
  change (P.filter fun t => ordinarySum t=z).card-1 ≤
    (P.filter fun t => f t=n).card + ((P.filter fun t => f t=n+M.val).card-1)
  omega

private theorem band_cost (A : Finset (ZMod M)) (u : ZMod M) (h : ℕ) :
    ∑ z ∈ univ.filter (fun z => phase u z<h), fibreCost A.sym2 ordinarySum z ≤
    cutExcess A u+((window A u h).card+1).choose 2 := by
  let B := univ.filter (fun z => phase u z<h)
  let P := A.sym2
  let f := liftSum u
  let g (z) := phase u z+M.val
  have gi : Function.Injective g := fun x y e => phase_inj u (Nat.add_right_cancel e)
  have high : ∑ z ∈ B, fibreCost P f (g z)≤cutExcess A u := by
    rw [← sum_image gi.injOn]
    exact sum_cost_le P f _
  have low : ∑ z ∈ B, (P.filter fun t => f t=phase u z).card≤((window A u h).card+1).choose 2 := by
    let count (n : ℕ) := (P.filter fun t => f t=n).card
    change ∑ z ∈ B, count (phase u z)≤_
    rw [← sum_image (phase_inj u).injOn]
    dsimp [count]
    rw [sum_card_fiberwise_eq_card_filter,← card_sym2]
    apply card_le_card
    rintro ⟨a,b⟩ ht
    obtain ⟨mem,hz⟩ := mem_filter.mp ht
    obtain ⟨z,mz,eq⟩ := mem_image.mp hz
    have lt := (mem_filter.mp mz).2
    change phase u z=atCut u a+atCut u b at eq
    obtain ⟨ma,mb⟩ := mk_mem_sym2_iff.mp mem
    exact mk_mem_sym2_iff.mpr ⟨mem_filter.mpr ⟨ma,by omega⟩,mem_filter.mpr ⟨mb,by omega⟩⟩
  calc
    _ ≤ ∑ z ∈ B, ((P.filter fun t => f t=phase u z).card+fibreCost P f (g z)) :=
      sum_le_sum fun z _ => cost_fold A u z
    _ ≤ _ := by rw [sum_add_distrib]; omega

/-- Averaging the integer cuts captures modular collisions, up to pairs
lying together in a short arc after the cut. -/
theorem averaged_fold (A : Finset (ZMod M)) (d : ℕ) (fit : 2*d≤M.val) :
    d*pairExcess false A ≤ (∑ u, cutExcess A u) + ∑ u, ((window A u (2*d)).card+1).choose 2 := by
  let c (z : ZMod M) := fibreCost A.sym2 ordinarySum z
  have all : pairExcess false A=∑ z, c z := by
    apply le_antisymm
    · exact sum_le_sum_of_subset (subset_univ _)
    · exact sum_cost_le A.sym2 ordinarySum univ
  rw [all,mul_sum]
  calc
    _ ≤ ∑ z, ∑ u ∈ univ.filter (fun u => phase u z<2*d), c z := by
      apply sum_le_sum
      intro z _
      simpa [nsmul_eq_mul] using Nat.mul_le_mul_right (c z) (band_incidence z d fit)
    _ = ∑ u, ∑ z ∈ univ.filter (fun z => phase u z<2*d), c z := by
      simp only [sum_filter]
      rw [sum_comm]
    _ ≤ _ := by
      rw [← sum_add_distrib]
      exact sum_le_sum fun u _ => band_cost A u (2*d)


private theorem cut_count (x : ZMod M) (h : ℕ) (fit : h≤M.val) :
    (univ.filter fun u => atCut u x<h).card=h := by
  let cut (i : Fin h) : ZMod M := x-(i.val:ZMod M)
  have small (i : Fin h) : i.val<M.val := i.isLt.trans_le fit
  have inj : Function.Injective cut := by
    intro i j e
    have a : (i.val:ZMod M)=(j.val:ZMod M) := sub_right_inj.mp e
    have b := congrArg ZMod.val a
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (small _)] at b
    exact Fin.ext b
  have eq : univ.filter (fun u => atCut u x<h)=univ.image cut := by
    ext u
    constructor
    · intro hu
      refine mem_image.mpr ⟨⟨atCut u x,(mem_filter.mp hu).2⟩,mem_univ _,?_⟩
      simp [cut,atCut]
    · intro hu
      obtain ⟨i,_,rfl⟩ := mem_image.mp hu
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      simpa only [atCut,cut,sub_sub_cancel,ZMod.val_natCast,Nat.mod_eq_of_lt (small i)] using i.isLt
  rw [eq,card_image_of_injective _ inj,card_univ,Fintype.card_fin]

private theorem windows_total (A : Finset (ZMod M)) (h : ℕ) (fit : h≤M.val) :
    ∑ u, (window A u h).card=h*A.card := by
  calc
    _ = ∑ u : ZMod M, ∑ x ∈ A, if atCut u x<h then 1 else 0 := by
      apply sum_congr rfl
      intro u _
      rw [window,card_eq_sum_ones,sum_filter]
    _ = ∑ x ∈ A, (univ.filter fun u => atCut u x<h).card := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [card_eq_sum_ones,sum_filter]
    _ = _ := by simp [cut_count _ _ fit,mul_comm]

/-- Finite reverse bound. The width can be optimized for a given mean
integer excess. The reference cut controlling local concentration is arbitrary. -/
theorem finite_reverse (A : Finset (ZMod M)) (v : ZMod M) (d : ℕ) (fit : 2*d≤M.val) :
    d*pairExcess false A ≤ (∑ u, cutExcess A u)+
      d*A.card*(1+Nat.sqrt (16*d+2*cutExcess A v)) := by
  let W (u) := (window A u (2*d)).card
  let L := Nat.sqrt (16*d+2*cutExcess A v)
  have small (u) : W u≤L := by
    have w := window_choose A u v (2*d)
    change ((W u)+1).choose 2 ≤ _ at w
    rw [Nat.choose_two_right] at w
    apply Nat.le_sqrt.mpr
    simp only [Nat.add_sub_cancel] at w
    nlinarith [Nat.div_add_mod ((W u+1)*W u) 2, Nat.mod_lt ((W u+1)*W u) (by decide : 0<2)]
  have each (u) : 2*((W u+1).choose 2)≤W u*(1+L) := by
    rw [Nat.choose_two_right,Nat.add_sub_cancel]
    have half := Nat.div_mul_le_self ((W u+1)*W u) 2
    nlinarith [Nat.mul_le_mul_left (W u) (small u)]
  have total : 2*(∑ u, (W u+1).choose 2)≤(2*d*A.card)*(1+L) := by
    rw [mul_sum,← windows_total A _ fit,sum_mul]
    exact sum_le_sum fun u _ => each u
  have b := averaged_fold A d fit
  change d*pairExcess false A≤_+∑ u, (W u+1).choose 2 at b
  have eq : 2*d*A.card*(1+L)=2*(d*A.card*(1+L)) := by ring
  rw [eq] at total
  change d*pairExcess false A≤_+d*A.card*(1+L)
  omega


/-- Total integer excess over all cuts, before division by the number of cuts. -/
def totalCutExcess (A : Finset (ZMod M)) := ∑ u, cutExcess A u

private theorem total_upper (A : Finset (ZMod M)) :
    totalCutExcess A≤M.val*pairExcess false A := by
  simpa [totalCutExcess,nsmul_eq_mul] using sum_le_sum (s:=univ) (fun u _ => cut_le_modular A u)

/-- A convenient width makes the reverse estimate depend only on the
size of the seed, the order, and the total ordinary integer excess. -/
theorem size_reverse (A : Finset (ZMod M)) (d : ℕ) (pos : 0<d) (fit : 2*d≤M.val)
    (err : totalCutExcess A≤d^2) :
    pairExcess false A≤d+A.card*(1+Nat.sqrt (18*d)) := by
  have avg : (∑ u, cutExcess A u)≤∑ _u : ZMod M, d := by
    simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul]
    change totalCutExcess A≤M.val*d
    exact err.trans (by rw [pow_two]; exact Nat.mul_le_mul_right _ (by omega))
  obtain ⟨v,_,good⟩ := exists_le_of_sum_le univ_nonempty avg
  have b := finite_reverse A v d fit
  have cap : Nat.sqrt (16*d+2*cutExcess A v)≤Nat.sqrt (18*d) := Nat.sqrt_le_sqrt (by omega)
  have e : d*pairExcess false A ≤ d*(d+A.card*(1+Nat.sqrt (18*d))) := by
    calc
      _ ≤ (∑ u, cutExcess A u)+d*A.card*(1+Nat.sqrt (16*d+2*cutExcess A v)) := b
      _ ≤ d^2+d*A.card*(1+Nat.sqrt (18*d)) := Nat.add_le_add err (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left e pos

open Filter

/-- The expected fraction of lost integer pairs, normalized by the
cyclic order. Each diagonal is counted once. -/
noncomputable def meanDefect (A : Finset (ZMod M)) : ℝ := (totalCutExcess A:ℝ)/(M:ℝ)^2

/-- For any prescribed sequence with bounded normalized size, vanishing
mean integer excess is equivalent to vanishing cyclic excess. -/
theorem mean_iff_modular {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop) {C : ℝ}
    (size : ∀ᶠ i in atTop, ((A i).card:ℝ)/Real.sqrt (N i)≤C) :
    Tendsto (fun i => meanDefect (A i)) atTop (𝓝 0) ↔
    Tendsto (fun i => (pairExcess false (A i):ℝ)/(N i:ℝ)) atTop (𝓝 0) := by
  let m (i : ℕ) : ℝ := N i
  let d (i : ℕ) := Nat.sqrt (totalCutExcess (A i))+1
  have mp (i) : 0 < m i := by dsimp [m]; exact_mod_cast (N i).pos
  have mt : Tendsto m atTop atTop := tendsto_natCast_atTop_atTop.comp big
  have inv : Tendsto (fun i => 1/m i) atTop (𝓝 0) := tendsto_const_nhds.div_atTop mt
  have ri : Tendsto (fun i => 1/Real.sqrt (m i)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp mt)
  constructor
  · intro h
    have root := Real.continuous_sqrt.continuousAt.tendsto.comp h
    have bound : Tendsto (fun i => Real.sqrt (meanDefect (A i))+1/m i) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Real.sqrt_zero,zero_add] using root.add inv
    have width : Tendsto (fun i => (d i:ℝ)/m i) atTop (𝓝 0) := by
      apply squeeze_zero (fun i => div_nonneg (by positivity) (mp i).le) _ bound
      intro i
      change ((Nat.sqrt (totalCutExcess (A i))+1:ℕ):ℝ)/m i≤
        Real.sqrt ((totalCutExcess (A i):ℝ)/(m i)^2)+1/m i
      rw [Real.sqrt_div (by positivity),Real.sqrt_sq (mp i).le,Nat.cast_add,Nat.cast_one,add_div]
      exact add_le_add (div_le_div_of_nonneg_right Real.nat_sqrt_le_real_sqrt (mp i).le) le_rfl
    have fit : ∀ᶠ i in atTop, 2*d i≤(N i).val := by
      filter_upwards [width.eventually_lt_const (show (0:ℝ)<1/2 by norm_num)] with i hi
      have ineq := (div_lt_iff₀ (mp i)).mp hi
      have e : (2:ℝ)*d i ≤ m i := by linarith
      change (2:ℝ)*d i≤((N i).val:ℝ) at e
      exact_mod_cast e
    have rlim : Tendsto (fun i => Real.sqrt (18*((d i:ℝ)/m i))) atTop (𝓝 0) := by
      have h' := Real.continuous_sqrt.continuousAt.tendsto.comp (width.const_mul 18)
      simpa only [Function.comp_def,mul_zero,Real.sqrt_zero] using h'
    have last : Tendsto (fun i => (d i:ℝ)/m i+C*(1/Real.sqrt (m i)+Real.sqrt (18*((d i:ℝ)/m i)))) atTop (𝓝 0) := by
      simpa only [add_zero,mul_zero] using width.add ((ri.add rlim).const_mul C)
    apply squeeze_zero' (Eventually.of_forall (fun i => div_nonneg (by positivity) (mp i).le)) _ last
    filter_upwards [size,fit] with i si fi
    have finite := size_reverse (A i) (d i) (Nat.succ_pos _) fi (Nat.lt_succ_sqrt' _).le
    have b : (pairExcess false (A i):ℝ)≤(d i:ℝ)+(A i).card*(1+(Nat.sqrt (18*d i):ℝ)) := by exact_mod_cast finite
    have hs := div_le_div_of_nonneg_right b (mp i).le
    have sq := Real.sq_sqrt (mp i).le
    have sp := Real.sqrt_pos.mpr (mp i)
    have factor : (((A i).card:ℝ)*(1+(Nat.sqrt (18*d i):ℝ)))/m i=
        (((A i).card:ℝ)/Real.sqrt (m i))*(1/Real.sqrt (m i)+(Nat.sqrt (18*d i):ℝ)/Real.sqrt (m i)) := by
      field_simp [sp.ne',(mp i).ne']
      nlinarith
    rw [add_div,factor] at hs
    have cr : 0≤C := (div_nonneg (Nat.cast_nonneg _) sp.le).trans si
    apply hs.trans (add_le_add le_rfl (mul_le_mul si _ (by positivity) cr))
    apply add_le_add le_rfl
    rw [show 18*((d i:ℝ)/m i)=(18*d i)/m i by ring,Real.sqrt_div (by positivity)]
    apply div_le_div_of_nonneg_right _ sp.le
    exact_mod_cast (Real.nat_sqrt_le_real_sqrt (a:=18*d i))
  · intro h
    apply squeeze_zero (fun i => div_nonneg (by positivity) (sq_nonneg (m i))) _ h
    intro i
    have e : (totalCutExcess (A i):ℝ) ≤ m i*pairExcess false (A i) := by dsimp [m]; exact_mod_cast total_upper (A i)
    change (totalCutExcess (A i):ℝ)/(m i)^2≤_/m i
    rw [sq,← div_div]
    apply div_le_div_of_nonneg_right _ (mp i).le
    rw [div_le_iff₀ (mp i)]
    linarith


/-- Rotate and cut the cyclic seed to obtain ordinary positive integer
representatives, as in the interval convention of Erdős 840. -/
def interval (A : Finset (ZMod M)) (u : ZMod M) : Finset ℕ := A.image fun x => atCut u x+1

theorem interval_spec (A : Finset (ZMod M)) (u) :
    interval A u⊆Icc 1 M.val ∧ (interval A u).card=A.card ∧
    cutExcess A u+(interval A u+interval A u).card=(A.card+1).choose 2 := by
  have inj : Function.Injective (fun x => atCut u x+1) := fun x y h =>
    sub_left_inj.mp (ZMod.val_injective _ (Nat.add_right_cancel h))
  refine ⟨?_,card_image_of_injective _ inj,?_⟩
  · intro n hn
    obtain ⟨x,_,rfl⟩ := mem_image.mp hn
    exact mem_Icc.mpr ⟨by omega,(x-u).val_lt⟩
  have eq : (A.sym2.image (liftSum u)).image (fun n => n+2)=interval A u+interval A u := by
    ext n
    constructor
    · intro hn
      obtain ⟨_,hw,rfl⟩ := mem_image.mp hn
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_image.mp hw
      obtain ⟨ha,hb⟩ := mk_mem_sym2_iff.mp hab
      refine mem_add.mpr ⟨_,mem_image_of_mem _ ha,_,mem_image_of_mem _ hb,?_⟩
      change atCut u a+1+(atCut u b+1)=atCut u a+atCut u b+2
      omega
    · intro hn
      obtain ⟨_,hx,_,hy,rfl⟩ := mem_add.mp hn
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
      refine mem_image.mpr ⟨_,mem_image_of_mem _ (mk_mem_sym2_iff.mpr ⟨ha,hb⟩),?_⟩
      change atCut u a+atCut u b+2=atCut u a+1+(atCut u b+1)
      omega
  rw [← eq,card_image_of_injective _ (fun _ _ => Nat.add_right_cancel)]
  simpa only [cutExcess,card_sym2] using excess_add_occupied A.sym2 (liftSum u)

/-- Mean number of distinct integer sums divided by the number of unordered
distinct pairs, using the interval normalization in Erdős 840. -/
noncomputable def meanRatio (A : Finset (ZMod M)) : ℝ :=
  (∑ u, ((interval A u+interval A u).card:ℝ))/((M:ℝ)*A.card.choose 2)

private theorem counts (A : Finset (ZMod M)) :
    (∑ u, ((interval A u+interval A u).card:ℝ))=
      (M:ℝ)*((A.card+1).choose 2:ℕ)-totalCutExcess A := by
  have h (u) := (interval_spec A u).2.2
  have total := sum_congr (s₁:=univ) rfl (fun u _ => h u)
  rw [sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul] at total
  have e : (totalCutExcess A:ℝ)+(∑ u, ((interval A u+interval A u).card:ℝ))=
      (M:ℝ)*((A.card+1).choose 2:ℕ) := by exact_mod_cast total
  linarith

private theorem ratio_identity (A : Finset (ZMod M)) :
    meanRatio A=((((A.card+1).choose 2:ℕ):ℝ)/(M:ℝ)-meanDefect A)/
      ((A.card.choose 2:ℝ)/(M:ℝ)) := by
  have hp : (M:ℝ)≠0 := by exact_mod_cast M.pos.ne'
  rw [meanRatio,counts,meanDefect]
  by_cases h : (A.card.choose 2:ℝ)=0
  · simp [h]
  · field_simp [hp,h]

/-- On each prescribed sequence of critical-size cyclic seeds, having
almost all possible sums on average in their rotated interval copies is
equivalent to vanishing cyclic unordered-pair excess. -/
theorem interval_iff_modular {N : ℕ → ℕ+} (A : ∀ i, Finset (ZMod (N i)))
    (big : Tendsto (fun i => (N i).val) atTop atTop)
    (size : Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => meanRatio (A i)) atTop (𝓝 1) ↔
    Tendsto (fun i => (pairExcess false (A i):ℝ)/(N i:ℝ)) atTop (𝓝 0) := by
  have bound := (size.eventually_lt_const (lt_add_one (Real.sqrt 2))).mono fun i h => h.le
  rw [← mean_iff_modular A big bound]
  obtain ⟨distinct,ordinary⟩ := Green33QuasiSidon.pair_scales_along (N:=fun i => (N i).val) (fun i => (A i).card) big size
  constructor
  · intro ratio
    have h := ordinary.sub (ratio.mul distinct)
    norm_num at h
    apply h.congr'
    filter_upwards [distinct.eventually_ne (by norm_num : (1:ℝ)≠0)] with i ne
    rw [ratio_identity,div_mul_cancel₀ _ ne]
    ring
  · intro defect
    have h := (ordinary.sub defect).div distinct (by norm_num)
    norm_num at h
    exact h.congr (fun i => (ratio_identity (A i)).symm)

/-- The Green 33 statement with a condition solely on integer sumset sizes
of rotated copies at unbounded orders. -/
theorem green_iff_rotated_intervals : Green33StrictReduction.OrdinaryLimit ↔
    ∃ N : ℕ → ℕ+, Tendsto (fun i => (N i).val) atTop atTop ∧
      ∃ A : (i : ℕ) → Finset (ZMod (N i)),
      Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun i => meanRatio (A i)) atTop (𝓝 1) := by
  rw [green_iff_pairExcess false]
  constructor
  · rintro ⟨N,big,A,size,h⟩
    exact ⟨N,big,A,size,(interval_iff_modular A big size).mpr h⟩
  · rintro ⟨N,big,A,size,h⟩
    exact ⟨N,big,A,size,(interval_iff_modular A big size).mp h⟩


/-- Cut a positive integer interval at offset `t<N` and rotate its labels
back into `[1,N]`. -/
def rotate (N t : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.image fun b => (b-1+N-t)%N+1

/-- The normalized mean number of sums, computed entirely with integer sets. -/
noncomputable def integerRatio (N : ℕ) (B : Finset ℕ) : ℝ :=
  (∑ t ∈ range N, ((rotate N t B+rotate N t B).card:ℝ))/((N:ℝ)*B.card.choose 2)

private def reduce (M : ℕ+) (B : Finset ℕ) : Finset (ZMod M) :=
  B.image fun x => ((x-1:ℕ):ZMod M)

private theorem reduce_interval (A : Finset (ZMod M)) : reduce M (interval A 0)=A := by
  ext x
  simp [reduce,interval,image_image,atCut]

private theorem unreduced (B : Finset ℕ) (fit : B⊆Icc 1 M.val) :
    interval (reduce M B) 0=B := by
  rw [interval,reduce,image_image]
  calc
    _ = B.image id := by
      apply image_congr
      intro x hx
      obtain ⟨lo,hi⟩ := mem_Icc.mp (fit hx)
      have h : x-1<M.val := by omega
      simp [atCut,ZMod.val_natCast,Nat.mod_eq_of_lt h,Nat.sub_add_cancel lo]
    _ = B := image_id

private theorem rotate_eq (B : Finset ℕ) (t : ℕ) (small : t<M.val) :
    rotate M.val t B=interval (reduce M B) (t:ZMod M) := by
  rw [rotate,interval,reduce,image_image]
  apply image_congr
  intro b _
  have fit : t≤b-1+M.val := by omega
  have eq : ((b-1+M.val-t:ℕ):ZMod M)=((b-1:ℕ):ZMod M)-(t:ZMod M) := by
    rw [Nat.cast_sub fit,Nat.cast_add,ZMod.natCast_self,add_zero]
  exact congrArg (·+1) (by rw [atCut,← eq,ZMod.val_natCast])

private theorem integer_eq (B : Finset ℕ) (fit : B⊆Icc 1 M.val) :
    integerRatio M.val B=meanRatio (reduce M B) := by
  let A := reduce M B
  have card : A.card=B.card := by
    rw [← (interval_spec A 0).2.1]
    exact congrArg card (unreduced B fit)
  rw [integerRatio,meanRatio,show (reduce M B).card=B.card from card]
  congr 1
  let e : Fin M.val ≃ ZMod M := ⟨fun t => (t.val:ZMod M),fun z => ⟨z.val,z.val_lt⟩,
    fun t => Fin.ext (by simp [ZMod.val_natCast,Nat.mod_eq_of_lt t.isLt]),fun z => z.natCast_zmod_val⟩
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv e
  intro t
  rw [rotate_eq B _ t.isLt]
  rfl

/-- Green 33 in ordinary integer intervals. Both the sets and their
sumsets on the right hand side use natural-number addition. -/
theorem green_iff_integer_rotations : Green33StrictReduction.OrdinaryLimit ↔
    ∃ N : ℕ → ℕ+, Tendsto (fun i => (N i).val) atTop atTop ∧
      ∃ B : ℕ → Finset ℕ, (∀ i, B i⊆Icc 1 (N i).val) ∧
      Tendsto (fun i => ((B i).card:ℝ)/Real.sqrt (N i)) atTop (𝓝 (Real.sqrt 2)) ∧
      Tendsto (fun i => integerRatio (N i).val (B i)) atTop (𝓝 1) := by
  rw [green_iff_rotated_intervals]
  constructor
  · rintro ⟨N,big,A,size,h⟩
    let B i := interval (A i) 0
    have spec (i) := interval_spec (A i) 0
    refine ⟨N,big,B,fun i => (spec i).1,size.congr (fun i => ?_),h.congr (fun i => ?_)⟩
    · simp only [B,(spec i).2.1]
    · rw [integer_eq (B i) (spec i).1,show reduce (N i) (B i)=A i from reduce_interval _]
  · rintro ⟨N,big,B,fit,size,h⟩
    let A i := reduce (N i) (B i)
    have card (i) : (A i).card=(B i).card := by
      rw [← (interval_spec (A i) 0).2.1]
      exact congrArg Finset.card (unreduced _ (fit i))
    exact ⟨N,big,A,size.congr (fun i => by rw [card]),h.congr (fun i => integer_eq (B i) (fit i))⟩

#print axioms cut_le_modular
#print axioms window_choose
#print axioms averaged_fold
#print axioms finite_reverse
#print axioms size_reverse
#print axioms mean_iff_modular
#print axioms interval_spec
#print axioms interval_iff_modular
#print axioms green_iff_rotated_intervals
#print axioms green_iff_integer_rotations
end Green33RotatedIntervals
