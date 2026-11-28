import Green33WeightedStability

/-! Weighted sum peaks and exact flatness barriers for cyclic two-bases. -/

namespace Green33WeightedPeaks
open Finset Green33WeightedStability
open scoped Pointwise

variable {G ι Ω : Type*} [Fintype G] [Fintype ι] [Fintype Ω] [DecidableEq G]

/-- Total weight in one fibre of an observation. -/
private noncomputable def fiberWeight (w : Ω → ℝ) (f : Ω → G) (z : G) : ℝ :=
  ∑ i, if f i = z then w i else 0

private theorem fiber_energy (w : Ω → ℝ) (f : Ω → G) :
    (∑ z, (fiberWeight w f z)^2) =
      ∑ u : Ω×Ω, if f u.1=f u.2 then w u.1*w u.2 else 0 := by
  classical
  let term (z : G) (i : Ω) := if f i=z then w i else 0
  calc _ = ∑ z, ∑ u : Ω×Ω, term z u.1*term z u.2 := by
         simp only [fiberWeight,term,pow_two,Fintype.sum_prod_type,sum_mul,mul_sum]
         exact sum_congr rfl (fun _ _ => sum_comm)
       _ = ∑ u : Ω×Ω, ∑ z, term z u.1*term z u.2 := sum_comm
       _ = _ := by
         apply sum_congr rfl
         intro u _
         rw [sum_eq_single (f u.1)]
         · by_cases eq : f u.1=f u.2
           · simp [term,eq]
           · simp [term,eq,Ne.symm eq]
         · intro z _ ne;simp [term,Ne.symm ne]
         · simp

omit [Fintype G] in
private theorem atom_fiber (p q : PMF ι) (f : ι → ι → G) (z : G) :
    ((law p q f) z).toReal = fiberWeight (fun u : ι×ι => (p u.1).toReal*(q u.2).toReal)
      (fun u => f u.1 u.2) z := by
  have h := (observed_eq_mass p q f {z}).symm
  simp only [mass,sum_singleton] at h
  rw [h]
  change (∑ i, ∑ j, if f i j∈({z}:Finset G) then _ else _) = _
  simp only [fiberWeight,Fintype.sum_prod_type,mem_singleton]

/-- The weighted sum and difference of independent labels have the same collision probability. -/
theorem sum_difference_energy [AddCommGroup G] (p q : PMF ι) (label : ι → G) :
    (∑ z, (((law p q (fun i j => label i+label j)) z).toReal)^2) =
      ∑ z, (((law p q (fun i j => label i-label j)) z).toReal)^2 := by
  classical
  simp_rw [atom_fiber]
  rw [fiber_energy,fiber_energy]
  let swap : ((ι×ι)×(ι×ι)) ≃ ((ι×ι)×(ι×ι)) :=
    { toFun := fun u => ((u.1.1,u.2.2),(u.2.1,u.1.2))
      invFun := fun u => ((u.1.1,u.2.2),(u.2.1,u.1.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply Fintype.sum_equiv swap
  rintro ⟨⟨i,j⟩,⟨k,l⟩⟩
  change (if label i+label j=label k+label l then _ else _) =
    (if label i-label l=label k-label j then _ else _)
  have eq : label i+label j=label k+label l ↔ label i-label l=label k-label j := by rw [sub_eq_sub_iff_add_eq_add]
  by_cases h : label i+label j=label k+label l
  · rw [if_pos h,if_pos (eq.mp h)];dsimp [swap];ring
  · rw [if_neg h,if_neg (fun a => h (eq.mpr a))]

/-- A diffuse law cannot have large collision excess unless its largest atom is large. -/
private theorem variance_bound (r : PMF G) {δ L : ℝ}
    (diffuse : ∀ E : Finset G, mass r E ≤ (E.card:ℝ)/Fintype.card G+δ)
    (peak : ∀ z, (r z).toReal ≤ L) :
    (∑ z, ((r z).toReal-(Fintype.card G:ℝ)⁻¹)^2) ≤ δ*L := by
  classical
  let u := (Fintype.card G:ℝ)⁻¹
  let R := fun z => (r z).toReal
  let E := univ.filter (fun z => u ≤ R z)
  have tot : ∑ z, R z = 1 := by
    have h := congrArg ENNReal.toReal r.tsum_coe
    rwa [tsum_fintype,ENNReal.toReal_sum (fun i _ => r.apply_ne_top i),ENNReal.toReal_one] at h
  let _ : Nonempty G := r.support_nonempty.to_type
  have hcard : (Fintype.card G:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have center : ∑ z, (R z-u) = 0 := by simp [sum_sub_distrib,tot,u,hcard]
  have variance : (∑ z, (R z-u)^2) = ∑ z, R z*(R z-u) := by
    calc _ = ∑ z, (R z*(R z-u)-u*(R z-u)) := sum_congr rfl (fun _ _ => by ring)
         _ = _ := by rw [sum_sub_distrib,←mul_sum,center,mul_zero,sub_zero]
  have exc := diffuse E
  change (∑ z ∈ E, R z) ≤ _ at exc
  have plus : (∑ z ∈ E, (R z-u)) ≤ δ := by rw [sum_sub_distrib];simp only [sum_const,nsmul_eq_mul];dsimp [u];rw [div_eq_mul_inv] at exc;linarith
  have atom (z : G) : R z*(R z-u) ≤ if z∈E then L*(R z-u) else 0 := by
    by_cases mem : z∈E
    · rw [if_pos mem]
      exact mul_le_mul_of_nonneg_right (peak z) (sub_nonneg.mpr (mem_filter.mp mem).2)
    · rw [if_neg mem]
      have lt : R z < u := by simpa [E] using mem
      exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg (sub_nonpos.mpr lt.le)
  have L0 : 0 ≤ L := ENNReal.toReal_nonneg.trans (peak (Classical.arbitrary G))
  change (∑ z, (R z-u)^2) ≤ _
  rw [variance]
  calc _ ≤ ∑ z, if z∈E then L*(R z-u) else 0 := sum_le_sum (fun z _ => atom z)
       _ = L*(∑ z ∈ E, (R z-u)) := by rw [mul_sum,←sum_filter];congr 1;ext z;simp
       _ ≤ δ*L := (mul_le_mul_of_nonneg_left plus L0).trans_eq (mul_comm _ _)

/-- Squared Euclidean distance to the uniform probability vector. -/
noncomputable def squaredError (r : PMF G) : ℝ := ∑ z, ((r z).toReal-(Fintype.card G:ℝ)⁻¹)^2

omit [DecidableEq G] in
private theorem error_ge_zero (r : PMF G) : 0 ≤ squaredError r := sum_nonneg (fun _ _ => sq_nonneg _)

private theorem atom_le_error [AddCommGroup G] (p q : PMF ι) (label : ι → G) (y : G) :
    (((law p q (fun i j => label i-label j)) y).toReal-(Fintype.card G:ℝ)⁻¹)^2 ≤
      squaredError (law p q (fun i j => label i+label j)) := by
  let u := (Fintype.card G:ℝ)⁻¹
  let D := law p q (fun i j => label i-label j)
  let R := law p q (fun i j => label i+label j)
  have shift (d : PMF G) : (∑ z, ((d z).toReal-u)^2) =
      (∑ z, (d z).toReal^2)-2*u+(Fintype.card G:ℝ)*u^2 := by
    have tot : ∑ z, (d z).toReal=1 := by
      have hd := congrArg ENNReal.toReal d.tsum_coe
      rwa [tsum_fintype,ENNReal.toReal_sum (fun i _ => d.apply_ne_top i),ENNReal.toReal_one] at hd
    simp_rw [sub_sq,sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ,
      show ∀ x : ℝ, 2*x*u=x*(2*u) by intro x;ring,←sum_mul,tot,one_mul]
  calc _ ≤ ∑ z, ((D z).toReal-u)^2 :=
           single_le_sum (f:=fun z => ((D z).toReal-u)^2) (fun _ _ => sq_nonneg _) (mem_univ y)
       _ = ∑ z, ((R z).toReal-u)^2 := by rw [shift,shift];rw [←sum_difference_energy p q label]

/-- Total variation and the sum-law peak bound every atom of the difference law. -/
theorem difference_atom_bound [AddCommGroup G] (p q : PMF ι) (label : ι → G) {δ L : ℝ}
    (h : Diffuse p q (fun i j => label i+label j) (Fintype.card G) δ)
    (peak : ∀ z, ((law p q (fun i j => label i+label j)) z).toReal ≤ L) (y : G) :
    (((law p q (fun i j => label i-label j)) y).toReal-(Fintype.card G:ℝ)⁻¹)^2 ≤ δ*L :=
  (atom_le_error p q label y).trans (variance_bound _ (fun E => (observed_eq_mass p q _ E) ▸ h E) peak)

/-- Common probability mass of the two laws on the label set. -/
noncomputable def overlap (p q : PMF ι) : ℝ := ∑ i, min (p i).toReal (q i).toReal

private noncomputable def heavy (p q : PMF ι) : Finset ι := univ.filter (fun i => (q i).toReal ≤ (p i).toReal)

private theorem total (p : PMF ι) : ∑ i, (p i).toReal = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rwa [tsum_fintype,ENNReal.toReal_sum (fun i _ => p.apply_ne_top i),ENNReal.toReal_one] at h

private theorem overlap_split (p q : PMF ι) :
    overlap p q = 1-mass p (heavy p q)+mass q (heavy p q) := by
  classical
  let H := heavy p q
  have pt := sum_add_sum_compl H (fun i => (p i).toReal)
  rw [total] at pt
  unfold overlap
  rw [←sum_add_sum_compl H]
  have pos : ∀ i ∈ H, min (p i).toReal (q i).toReal = (q i).toReal :=
    fun _ hi => min_eq_right (mem_filter.mp hi).2
  have neg : ∀ i ∈ Hᶜ, min (p i).toReal (q i).toReal = (p i).toReal := by
    intro i hi
    have := mem_compl.mp hi
    exact min_eq_left (le_of_lt (by simpa [H,heavy] using this))
  rw [sum_congr rfl pos,sum_congr rfl neg]
  change _ = 1-(∑ i ∈ H, (p i).toReal)+(∑ i ∈ H, (q i).toReal)
  linarith

private theorem overlap_sq (p q : PMF ι) :
    overlap p q ^ 2 ≤ (Fintype.card ι:ℝ)*(∑ i, (p i).toReal*(q i).toReal) := by
  have h := sum_sq_le_sum_mul_sum_of_sq_le_mul (R:=ℝ) (s:=(univ:Finset ι))
    (f:=fun _ => (1:ℝ)) (g:=fun i => (p i).toReal*(q i).toReal)
    (r:=fun i => min (p i).toReal (q i).toReal)
    (fun _ _ => zero_le_one) (fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (fun i _ => by
      rw [one_mul,pow_two]
      exact mul_le_mul (min_le_left _ _) (min_le_right _ _) (le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
  simpa [overlap] using h

omit [Fintype G] in
private theorem rect_lower (p q : PMF ι) (f : ι → ι → G) (U V : Finset ι) :
    mass p U * mass q V ≤ observed p q f (image₂ f U V) := by
  classical
  let w (i j : ι) := if f i j∈image₂ f U V then (p i).toReal*(q j).toReal else 0
  have hn (i j) : 0 ≤ w i j := by dsimp [w];positivity
  have sub (i : ι) : (∑ j ∈ V, w i j) ≤ ∑ j, w i j :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => hn i j)
  change _ ≤ ∑ i, ∑ j, w i j
  calc _ = ∑ i ∈ U, ∑ j ∈ V, w i j := by
         unfold mass
         rw [sum_mul]
         apply sum_congr rfl
         intro i hi
         rw [mul_sum]
         exact sum_congr rfl (fun j hj => (if_pos (mem_image₂_of_mem hi hj)).symm)
       _ ≤ ∑ i ∈ U, ∑ j, w i j := sum_le_sum (fun i _ => sub i)
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => sum_nonneg (fun j _ => hn i j))

omit [Fintype G] in
/-- Dividing labels between their heavier input laws leaves at most a quarter of the
square budget for mixed sums. The missing mass must be supplied by their overlap. -/
theorem overlap_lower (p q : PMF ι) (f : ι → ι → G) {m δ : ℝ} (hm : 0 < m)
    (h : Diffuse p q f m δ) :
    1-δ-(Fintype.card ι:ℝ)^2/(4*m) ≤ overlap p q := by
  classical
  let H := heavy p q
  have count := card_image₂_le f H Hᶜ
  have n : (H.card:ℝ)+(Hᶜ.card:ℝ) = Fintype.card ι := by exact_mod_cast card_add_card_compl H
  have cap : ((image₂ f H Hᶜ).card:ℝ) ≤ (Fintype.card ι:ℝ)^2/4 := by
    have c : ((image₂ f H Hᶜ).card:ℝ) ≤ (H.card:ℝ)*Hᶜ.card := by exact_mod_cast count
    rw [←n];nlinarith [sq_nonneg ((H.card:ℝ)-Hᶜ.card)]
  have mixed := (rect_lower p q f H Hᶜ).trans (h _)
  have cmp (r : PMF ι) : mass r H+mass r Hᶜ = 1 := (sum_add_sum_compl H _).trans (total r)
  have nonneg (r : PMF ι) (T : Finset ι) : 0 ≤ mass r T := sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have mcap := div_le_div_of_nonneg_right cap hm.le
  rw [div_div] at mcap
  rw [overlap_split]
  change _ ≤ 1-mass p H+mass q H
  have pC : mass p Hᶜ=1-mass p H := by linarith [cmp p]
  have qC : mass q Hᶜ=1-mass q H := by linarith [cmp q]
  rw [qC] at mixed
  have z := mul_nonneg (nonneg p Hᶜ) (nonneg q H)
  rw [pC] at z
  nlinarith

omit [Fintype G] in
private theorem diagonal_le [AddCommGroup G] (p q : PMF ι) (label : ι → G) :
    (∑ i, (p i).toReal*(q i).toReal) ≤ ((law p q (fun i j => label i-label j)) 0).toReal := by
  classical
  rw [atom_fiber,fiberWeight,Fintype.sum_prod_type]
  apply sum_le_sum
  intro i _
  have h := single_le_sum (f:=fun j => if label i-label j=0 then (p i).toReal*(q j).toReal else 0)
    (fun _ _ => by positivity) (mem_univ i)
  simpa only [sub_self,if_true] using h

private theorem overlap_energy [AddCommGroup G] (p q : PMF ι) (label : ι → G) :
    overlap p q^2 ≤ (Fintype.card ι:ℝ)*((Fintype.card G:ℝ)⁻¹+
      Real.sqrt (squaredError (law p q (fun i j => label i+label j)))) := by
  have bound := Real.le_sqrt_of_sq_le (atom_le_error p q label 0)
  have diagonal := diagonal_le p q label
  exact (overlap_sq p q).trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))

/-- Finite peak trade-off. In a near-uniform group sum, a large common mass of the
input distributions forces a large point mass in the sum law. -/
theorem overlap_peak_bound [AddCommGroup G] (p q : PMF ι) (label : ι → G) {δ L : ℝ}
    (h : Diffuse p q (fun i j => label i+label j) (Fintype.card G) δ)
    (peak : ∀ z, ((law p q (fun i j => label i+label j)) z).toReal ≤ L) :
    overlap p q^2 ≤ (Fintype.card ι:ℝ)*((Fintype.card G:ℝ)⁻¹+Real.sqrt (δ*L)) := by
  have bound := Real.le_sqrt_of_sq_le (difference_atom_bound p q label h peak 0)
  have diagonal := diagonal_le p q label
  exact (overlap_sq p q).trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))

omit [Fintype G] in
private theorem pair_le (p q : PMF ι) (f : ι → ι → G) (i j : ι) :
    (p i).toReal*(q j).toReal ≤ ((law p q f) (f i j)).toReal := by
  classical
  rw [atom_fiber,fiberWeight]
  have h := single_le_sum
    (f:=fun u : ι×ι => if f u.1 u.2=f i j then (p u.1).toReal*(q u.2).toReal else 0)
    (fun _ _ => by positivity) (mem_univ (i,j))
  simpa using h

/-- An exactly uniform independent sum requires at least `2√|G|−1` labels in the common
budget, allowing different input laws and zero mass on any chosen labels. -/
theorem exact_uniform_budget [AddCommGroup G] (p q : PMF ι) (label : ι → G)
    (flat : ∀ z, ((law p q (fun i j => label i+label j)) z).toReal = (Fintype.card G:ℝ)⁻¹) :
    2*Real.sqrt (Fintype.card G)-1 ≤ (Fintype.card ι:ℝ) := by
  classical
  let m := (Fintype.card G:ℝ)
  have hm : 0 < m := by dsimp [m];exact_mod_cast Fintype.card_pos (α:=G)
  let f (i j : ι) := label i+label j
  have diffuse : Diffuse p q f (Fintype.card G) 0 := by
    intro E
    rw [observed_eq_mass,mass]
    simp only [f,flat,sum_const,nsmul_eq_mul,add_zero,div_eq_mul_inv]
    rfl
  have atom := difference_atom_bound p q label diffuse (fun z => (flat z).le) 0
  have diagonal := diagonal_le p q label
  have small : (∑ i, (p i).toReal*(q i).toReal) ≤ m⁻¹ := by
    change (_-m⁻¹)^2 ≤ 0*m⁻¹ at atom
    nlinarith [sq_nonneg (((law p q (fun i j => label i-label j)) 0).toReal-m⁻¹)]
  let _ : Nonempty ι := p.support_nonempty.to_type
  obtain ⟨i,_,maximal⟩ := exists_max_image univ (fun i => (p i).toReal) univ_nonempty
  let a := (p i).toReal
  have maxp (j) : (p j).toReal ≤ a := maximal j (mem_univ _)
  have apos : 0 < a := by
    by_contra! hn
    have zero (j) : (p j).toReal=0 := le_antisymm ((maxp j).trans hn) ENNReal.toReal_nonneg
    have htot := total p
    simp [zero] at htot
  let b := m⁻¹/a
  have ab : a*b=m⁻¹ := by dsimp [b];field_simp
  have maxq (j) : (q j).toReal ≤ b := by
    apply (le_div_iff₀ apos).mpr
    rw [mul_comm]
    exact (pair_le p q f i j).trans (flat _).le
  have count := sum_nonneg (s:=(univ:Finset ι)) (fun j _ =>
    mul_nonneg (sub_nonneg.mpr (maxp j)) (sub_nonneg.mpr (maxq j)))
  have expr (j : ι) : (a-(p j).toReal)*(b-(q j).toReal) =
      a*b-b*(p j).toReal-a*(q j).toReal+(p j).toReal*(q j).toReal := by ring
  simp only [expr,sum_add_distrib,sum_sub_distrib,←mul_sum,total,mul_one,sum_const,card_univ,nsmul_eq_mul,ab] at count
  have upper : a+b ≤ ((Fintype.card ι:ℝ)+1)/m := by rw [div_eq_mul_inv];nlinarith
  have root := Real.sq_sqrt hm.le
  have identity : (a*b)*Real.sqrt m^2=1 := by rw [ab,root,inv_mul_cancel₀ hm.ne']
  have amgm : 2 ≤ (a+b)*Real.sqrt m := by
    have h2 : 4 ≤ ((a+b)*Real.sqrt m)^2 := by
      nlinarith [mul_nonneg (sq_nonneg (a-b)) (sq_nonneg (Real.sqrt m))]
    have nonneg := mul_nonneg (add_nonneg apos.le (div_nonneg (inv_nonneg.mpr hm.le) apos.le)) (Real.sqrt_nonneg m)
    exact (sq_le_sq₀ (by norm_num : (0:ℝ)≤2) nonneg).mp (by nlinarith)
  have bound := (le_div_iff₀ hm).mp upper
  change 2*Real.sqrt m-1 ≤ _
  nlinarith [mul_le_mul_of_nonneg_right amgm (Real.sqrt_nonneg m),
    show (a+b)*Real.sqrt m*Real.sqrt m=(a+b)*m by rw [mul_assoc,←sq,root]]

/-- A radix block in every cyclic order containing at least `k²` residues. Independent
fair low and high digits occupy at most `2k−1` labels together and give equal probability
to exactly `k²` consecutive sums. -/
theorem radix_block {M : ℕ+} (k : ℕ) (hk : 0 < k) (fits : k*k ≤ M.val) :
    ∃ A : Finset (ZMod M), A.card+1 ≤ 2*k ∧ ∃ p q : PMF A,
      ∀ z, ((law p q (cyclicSum A)) z).toReal =
        if z.val < k*k then ((k:ℝ)*k)⁻¹ else 0 := by
  classical
  let _ : NeZero k := ⟨hk.ne'⟩
  let lo (j : Fin k) := (j.val:ZMod M)
  let hi (i : Fin k) := ((k*i.val:ℕ):ZMod M)
  let e (v : Fin k×Fin k) := ((finProdFinEquiv v).val:ZMod M)
  have eval (v : Fin k×Fin k) : (e v).val=(finProdFinEquiv v).val :=
    ZMod.val_natCast_of_lt ((finProdFinEquiv v).isLt.trans_le fits)
  have inj : Function.Injective e := by
    intro i j he
    exact finProdFinEquiv.injective (Fin.ext (by simpa only [eval] using congrArg ZMod.val he))
  have digits (i j : Fin k) : hi i+lo j=e (i,j) := by
    change ((k*i.val:ℕ):ZMod M)+(j.val:ZMod M)=((j.val+k*i.val:ℕ):ZMod M)
    push_cast
    rw [add_comm]
  let H := univ.image hi
  let K := univ.image lo
  let A := H∪K
  let h (i : Fin k) : A := ⟨hi i,mem_union_left _ (mem_image_of_mem _ (mem_univ _))⟩
  let l (i : Fin k) : A := ⟨lo i,mem_union_right _ (mem_image_of_mem _ (mem_univ _))⟩
  let U := PMF.uniformOfFintype (Fin k)
  let p := U.map h
  let q := U.map l
  have transport : law p q (cyclicSum A) = law U U (fun i j => e (i,j)) := by
    simp only [p,q,law,PMF.bind_map,PMF.map_comp,Function.comp_def]
    change U.bind (fun i => U.map (fun j => hi i+lo j)) = _
    simp_rw [digits]
  have flat (z : ZMod M) : ((law p q (cyclicSum A)) z).toReal =
      if z.val < k*k then ((k:ℝ)*k)⁻¹ else 0 := by
    rw [transport,atom_fiber,fiberWeight]
    by_cases hz : z.val < k*k
    · let v := finProdFinEquiv.symm (⟨z.val,hz⟩ : Fin (k*k))
      have ev : e v = z := by
        change ((finProdFinEquiv (finProdFinEquiv.symm _)).val:ZMod M) = z
        rw [Equiv.apply_symm_apply,ZMod.natCast_zmod_val]
      rw [if_pos hz,sum_eq_single v]
      · simp [ev,U,PMF.uniformOfFintype_apply,ENNReal.toReal_inv,mul_inv_rev]
      · intro w _ ne
        have neq : e w ≠ z := fun eq => ne (inj (eq.trans ev.symm))
        simp [neq]
      · simp
    · rw [if_neg hz]
      apply sum_eq_zero
      intro w _
      have neq : e w ≠ z := by
        intro eq
        apply hz
        rw [←eq,eval]
        exact (finProdFinEquiv w).isLt
      simp [neq]
  have hH : H.card ≤ k := by simpa [H] using (card_image_le (f:=hi) (s:=univ))
  have hK : K.card ≤ k := by simpa [K] using (card_image_le (f:=lo) (s:=univ))
  have both : (H∩K).Nonempty := by
    refine ⟨0,mem_inter.mpr ⟨mem_image.mpr ⟨0,mem_univ _,?_⟩,mem_image.mpr ⟨0,mem_univ _,?_⟩⟩⟩
    · simp [hi]
    · simp [lo]
  have balance := card_union_add_card_inter H K
  have nonzero := card_pos.mpr both
  exact ⟨A,by change (H∪K).card+1 ≤ _;omega,p,q,flat⟩

/-- The exact bound is attained for every square cyclic order. -/
theorem square_order_attains (k : ℕ) (hk : 0 < k) :
    ∃ A : Finset (ZMod (k*k)), A.card+1=2*k ∧ ∃ p q : PMF A,
      ∀ z, ((law p q (fun i j : A => (i:ZMod (k*k))+j)) z).toReal = ((k:ℝ)*k)⁻¹ := by
  classical
  let M : ℕ+ := ⟨k*k,Nat.mul_pos hk hk⟩
  obtain ⟨A,card,p,q,inside⟩ := radix_block (M:=M) k hk le_rfl
  have flat (z : ZMod M) : ((law p q (cyclicSum A)) z).toReal = ((k:ℝ)*k)⁻¹ := by
    rw [inside,if_pos (show z.val < k*k from ZMod.val_lt z)]
  have bound := exact_uniform_budget p q (fun i : A => (i:ZMod M)) (fun z => by
    change ((law p q (cyclicSum A)) z).toReal = _
    rw [flat,ZMod.card];change _ = ((k*k:ℕ):ℝ)⁻¹;rw [Nat.cast_mul])
  rw [ZMod.card,Fintype.card_coe] at bound
  change 2*Real.sqrt ((k*k:ℕ):ℝ)-1 ≤ _ at bound
  rw [Nat.cast_mul,←sq,Real.sqrt_sq (Nat.cast_nonneg k)] at bound
  exact ⟨A,le_antisymm card (by exact_mod_cast (by linarith : 2*(k:ℝ) ≤ A.card+1)),p,q,flat⟩

open Filter
open scoped Topology

/-- Largest point mass of a probability law on a finite space. -/
noncomputable def largest (r : PMF G) : ℝ := by
  classical
  let _ : Nonempty G := r.support_nonempty.to_type
  exact univ.sup' univ_nonempty (fun z => (r z).toReal)

omit [DecidableEq G] in
private theorem le_largest (r : PMF G) (z : G) : (r z).toReal ≤ largest r :=
  le_sup' (f:=fun z => (r z).toReal) (mem_univ z)

omit [DecidableEq G] in
private theorem largest_nonneg (r : PMF G) : 0 ≤ largest r :=
  ENNReal.toReal_nonneg.trans (le_largest r r.support_nonempty.choose)

/-- Peak probability relative to the uniform mass of one residue. -/
noncomputable def normalizedPeak {M : ℕ+} (A : Finset (ZMod M)) (p q : PMF A) : ℝ :=
  (M:ℝ)*largest (law p q (cyclicSum A))

/-- Pearson chi-squared divergence of the sum law from the uniform cyclic law. -/
noncomputable def chiSquare {M : ℕ+} (A : Finset (ZMod M)) (p q : PMF A) : ℝ :=
  (M:ℝ)*squaredError (law p q (cyclicSum A))

theorem chiSquare_le_peak {M : ℕ+} (A : Finset (ZMod M)) (p q : PMF A) {δ : ℝ}
    (h : Diffuse p q (cyclicSum A) M δ) : chiSquare A p q ≤ δ*normalizedPeak A p q := by
  have z := variance_bound (law p q (cyclicSum A)) (δ:=δ)
    (by intro E;rw [ZMod.card,←observed_eq_mass];exact h E) (fun z => le_largest _ z)
  calc _ ≤ (M:ℝ)*(δ*largest (law p q (cyclicSum A))) := mul_le_mul_of_nonneg_left z (by positivity)
       _ = _ := by unfold normalizedPeak;ring

omit [Fintype G] in
private theorem error_nonneg (p q : PMF ι) (f : ι → ι → G) {m δ : ℝ} (h : Diffuse p q f m δ) :
    0 ≤ δ := by
  have bound := h ∅
  rw [observed_eq_mass] at bound
  simpa [mass] using bound

private theorem rate_from_overlap {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i))
    {c v : ℝ} (hc : 0 < c) (hv : 0 < v)
    {r : ℕ → ℝ} (size : Tendsto r atTop (𝓝 c))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ r i)
    {w : ℕ → ℝ}
    (win : Tendsto w atTop (𝓝 v)) (w0 : ∀ i, 0 ≤ w i) (sub : ∀ i, w i ≤ overlap (p i) (q i)) :
    ∀ B : ℝ, B < (v^2/c)^2 → ∀ᶠ i in atTop, B < chiSquare (A i) (p i) (q i) := by
  let m (i : ℕ) := (N i:ℝ)
  have mp (i) : 0 < m i := by dsimp [m];exact_mod_cast (N i).pos
  have rp (i) : 0 < r i := by
    have ne : (A i).Nonempty := by
      obtain ⟨x,_⟩ := (p i).support_nonempty
      exact ⟨x,x.property⟩
    exact (div_pos (by exact_mod_cast card_pos.mpr ne : 0<((A i).card:ℝ)) (Real.sqrt_pos.mpr (mp i))).trans_le (budget i)
  have bound (i) : w i^2/r i-1/Real.sqrt (m i) ≤ Real.sqrt (chiSquare (A i) (p i) (q i)) := by
    let V := squaredError (law (p i) (q i) (cyclicSum (A i)))
    have v0 : 0 ≤ V := error_ge_zero _
    have z := overlap_energy (p i) (q i) (fun x : A i => (x:ZMod (N i)))
    rw [ZMod.card,Fintype.card_coe] at z
    change _ ≤ ((A i).card:ℝ)*((m i)⁻¹+Real.sqrt V) at z
    have sqle := (sq_le_sq₀ (w0 i) ((w0 i).trans (sub i))).mpr (sub i)
    have root := Real.sq_sqrt (mp i).le
    have pos := Real.sqrt_pos.mpr (mp i)
    have divbound : w i^2/r i ≤ ((m i)⁻¹+Real.sqrt V)*Real.sqrt (m i) := by
      apply (div_le_iff₀ (rp i)).mpr
      calc _ ≤ ((A i).card:ℝ)*((m i)⁻¹+Real.sqrt V) := sqle.trans z
           _ = (((m i)⁻¹+Real.sqrt V)*Real.sqrt (m i))*(((A i).card:ℝ)/Real.sqrt (m i)) := by field_simp
           _ ≤ _ := mul_le_mul_of_nonneg_left (budget i) (by positivity)
    have unit : (m i)⁻¹*Real.sqrt (m i) = 1/Real.sqrt (m i) := by
      apply (eq_div_iff pos.ne').mpr
      rw [mul_assoc,←sq,root,inv_mul_cancel₀ (mp i).ne']
    change _ ≤ Real.sqrt (m i*V)
    rw [mul_comm (m i) V,Real.sqrt_mul v0]
    rw [add_mul,unit] at divbound
    linarith
  have hr := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp big)
  have lim : Tendsto (fun i => w i^2/r i-1/Real.sqrt (m i)) atTop (𝓝 (v^2/c)) := by
    have ht := ((win.pow 2).div size hc.ne').sub ((tendsto_const_nhds (x:=(1:ℝ))).div_atTop hr)
    simpa [m] using ht
  intro B hB
  by_cases neg : B < 0
  · exact Eventually.of_forall (fun i => neg.trans_le (mul_nonneg (mp i).le (error_ge_zero _)))
  have pos : 0 < v^2/c := by positivity
  have lt : Real.sqrt B < v^2/c := (Real.sqrt_lt' pos).mpr hB
  filter_upwards [lim.eventually_const_lt lt] with i hi
  have hsq := (sq_lt_sq₀ (Real.sqrt_nonneg B) (Real.sqrt_nonneg _)).mpr (hi.trans_le (bound i))
  have nn : 0 ≤ chiSquare (A i) (p i) (q i) := mul_nonneg (mp i).le (error_ge_zero _)
  rwa [Real.sq_sqrt (le_of_not_gt neg),Real.sq_sqrt nn] at hsq

/-- Below coefficient two, a sum approaching uniform in total variation has a positive
lower limit for its chi-squared divergence from uniform. -/
theorem sub_two_energy {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i))
    {c : ℝ} (hc : 0 < c) (c2 : c < 2)
    {r : ℕ → ℝ} (size : Tendsto r atTop (𝓝 c))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ r i)
    {δ : ℕ → ℝ} (hd : Tendsto δ atTop (𝓝 0))
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    ∀ B : ℝ, B < (1-c^2/4)^4/c^2 →
      ∀ᶠ i in atTop, B < chiSquare (A i) (p i) (q i) := by
  let w (i : ℕ) := max 0 (1-δ i-(r i)^2/4)
  have pos : 0 < 1-c^2/4 := by nlinarith [mul_pos (sub_pos.mpr c2) (show 0<2+c by linarith)]
  have win : Tendsto w atTop (𝓝 (1-c^2/4)) := by
    have lim := (tendsto_const_nhds (x:=(0:ℝ))).max
      (((tendsto_const_nhds (x:=(1:ℝ))).sub hd).sub ((size.pow 2).div_const 4))
    simpa [w,max_eq_right pos.le] using lim
  have sub (i) : w i ≤ overlap (p i) (q i) := by
    apply max_le_iff.mpr
    refine ⟨sum_nonneg (fun _ _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg),?_⟩
    have bound := overlap_lower _ _ _ (show 0 < (N i:ℝ) by positivity) (h i)
    rw [Fintype.card_coe] at bound
    have s0 : 0 ≤ ((A i).card:ℝ)/Real.sqrt (N i) := by positivity
    have sqle := (sq_le_sq₀ s0 (s0.trans (budget i))).mpr (budget i)
    rw [div_pow,Real.sq_sqrt (by positivity)] at sqle
    have div := div_le_div_of_nonneg_right sqle (by norm_num : (0:ℝ)≤4)
    rw [div_div,mul_comm _ (4:ℝ)] at div
    linarith
  have rate := rate_from_overlap big A p q hc pos size budget win (fun i => le_max_left _ _) sub
  intro B hB
  exact rate B (by rwa [div_pow,←pow_mul])

/-- For every limiting coefficient strictly below two, vanishing total variation requires
spikes. The error times the normalized peak has an explicit positive lower limit. -/
theorem sub_two_rate {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i))
    {c : ℝ} (hc : 0 < c) (c2 : c < 2)
    {r : ℕ → ℝ} (size : Tendsto r atTop (𝓝 c))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ r i)
    {δ : ℕ → ℝ} (hd : Tendsto δ atTop (𝓝 0))
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    ∀ B : ℝ, B < (1-c^2/4)^4/c^2 →
      ∀ᶠ i in atTop, B < δ i*normalizedPeak (A i) (p i) (q i) := by
  intro B hB
  filter_upwards [sub_two_energy big A p q hc c2 size budget hd h B hB] with i hi
  exact hi.trans_le (chiSquare_le_peak (A i) (p i) (q i) (h i))

/-- Actual divergence of the largest normalized output probability, allowing two arbitrary
weightings on the common seed. -/
theorem sub_two_peaks {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i))
    {c : ℝ} (hc : 0 < c) (c2 : c < 2)
    {r : ℕ → ℝ} (size : Tendsto r atTop (𝓝 c))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ r i)
    {δ : ℕ → ℝ} (hd : Tendsto δ atTop (𝓝 0))
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    Tendsto (fun i => normalizedPeak (A i) (p i) (q i)) atTop atTop := by
  let B := (1-c^2/4)^4/c^2/2
  have pos : 0 < 1-c^2/4 := by nlinarith [mul_pos (sub_pos.mpr c2) (show 0<2+c by linarith)]
  have bpos : 0 < B := by dsimp [B];positivity
  have rate := sub_two_rate big A p q hc c2 size budget hd h B (by dsimp [B] at bpos ⊢;linarith)
  apply tendsto_atTop.mpr
  intro K
  have small := (hd.mul_const K).eventually_lt_const (show 0*K<B by simpa using bpos)
  filter_upwards [rate,small] with i large tiny
  by_contra! low
  exact (not_lt_of_ge (mul_le_mul_of_nonneg_left low.le (error_nonneg _ _ _ (h i)))) (tiny.trans large)

/-- At the critical Green budget the chi-squared divergence has lower limit at least one half. -/
theorem green_energy {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i))
    {σ δ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) (hd : Tendsto δ atTop (𝓝 0))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ Real.sqrt 2+σ i)
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    ∀ B : ℝ, B < 1/2 → ∀ᶠ i in atTop, B < chiSquare (A i) (p i) (q i) := by
  have size := size_of_weighted_budget big A p q hσ hd budget h
  have stable := uniform_weights_of_critical_budget big A p q hσ hd budget h
  have lim : Tendsto (fun i => overlap (p i) (q i)) atTop (𝓝 1) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [stable (ε/2) (by linarith)] with i close
    obtain ⟨left,right⟩ := close (heavy (p i) (q i))
    rw [abs_lt] at left right
    rw [Real.dist_eq,overlap_split,abs_lt]
    constructor <;> linarith
  have rate := rate_from_overlap big A p q (by positivity) zero_lt_one size (fun _ => le_rfl) lim
    (fun _ => sum_nonneg (fun _ _ => le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) (fun _ => le_rfl)
  intro B hB
  apply rate B
  simpa [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] using hB

/-- At Green's critical upper budget the two weights converge together, improving the
lower limit for error times normalized peak to one half. -/
theorem green_peak_rate {N : ℕ → ℕ+} (big : Tendsto (fun i => (N i).val) atTop atTop)
    (A : (i : ℕ) → Finset (ZMod (N i))) (p q : (i : ℕ) → PMF (A i))
    {σ δ : ℕ → ℝ} (hσ : Tendsto σ atTop (𝓝 0)) (hd : Tendsto δ atTop (𝓝 0))
    (budget : ∀ i, ((A i).card:ℝ)/Real.sqrt (N i) ≤ Real.sqrt 2+σ i)
    (h : ∀ i, Diffuse (p i) (q i) (cyclicSum (A i)) (N i) (δ i)) :
    ∀ B : ℝ, B < 1/2 → ∀ᶠ i in atTop, B < δ i*normalizedPeak (A i) (p i) (q i) := by
  intro B hB
  filter_upwards [green_energy big A p q hσ hd budget h B hB] with i hi
  exact hi.trans_le (chiSquare_le_peak (A i) (p i) (q i) (h i))


/-- At every positive modulus, a budget of twice the integer square root minus one
suffices for output error at most `1−k²/M` and normalized peak at most `M/k²`. -/
theorem every_order (M : ℕ+) :
    let k := M.val.sqrt
    ∃ A : Finset (ZMod M), A.card+1 ≤ 2*k ∧ ∃ p q : PMF A,
      Diffuse p q (cyclicSum A) M (1-(k:ℝ)^2/M) ∧ normalizedPeak A p q ≤ (M:ℝ)/(k:ℝ)^2 := by
  classical
  let k := M.val.sqrt
  have hk : 0 < k := Nat.sqrt_pos.mpr M.pos
  have fit := Nat.sqrt_le M.val
  obtain ⟨A,card,p,q,flat⟩ := radix_block (M:=M) k hk fit
  let R := law p q (cyclicSum A)
  let n := (k:ℝ)^2
  have np : 0 < n := by dsimp [n];positivity
  have mp : 0 < (M:ℝ) := by exact_mod_cast M.pos
  have nm : n ≤ M := by dsimp [n];rw [sq];exact_mod_cast fit
  have cap (z : ZMod M) : (R z).toReal ≤ 1/n := by
    dsimp [R]
    rw [flat]
    split
    · simp [n,sq,one_div]
    · exact div_nonneg zero_le_one np.le
  refine ⟨A,card,p,q,?_,?_⟩
  · intro E
    rw [observed_eq_mass]
    have prob : mass R E ≤ 1 := (sum_le_sum_of_subset_of_nonneg (f:=fun z => (R z).toReal)
      (subset_univ E) (fun _ _ _ => ENNReal.toReal_nonneg)).trans_eq (total R)
    have cnt : mass R E ≤ (E.card:ℝ)/n := by
      calc _ ≤ ∑ _z ∈ E, 1/n := sum_le_sum (fun z _ => cap z)
           _ = _ := by simp [div_eq_mul_inv]
    have b := (le_div_iff₀ np).mp cnt
    change mass R E ≤ (E.card:ℝ)/M+(1-n/M)
    rw [show (E.card:ℝ)/M+(1-n/M) = (E.card+(M:ℝ)-n)/M by field_simp;ring]
    apply (le_div_iff₀ mp).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr nm) (sub_nonneg.mpr prob)]
  · have hi : largest R ≤ 1/n := Finset.sup'_le univ_nonempty _ (fun z _ => cap z)
    change (M:ℝ)*largest R ≤ (M:ℝ)/n
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hi mp.le

#print axioms sum_difference_energy
#print axioms difference_atom_bound
#print axioms overlap_lower
#print axioms overlap_peak_bound
#print axioms exact_uniform_budget
#print axioms square_order_attains
#print axioms sub_two_rate
#print axioms sub_two_peaks
#print axioms green_peak_rate
#print axioms chiSquare_le_peak
#print axioms sub_two_energy
#print axioms green_energy
#print axioms radix_block
#print axioms every_order
end Green33WeightedPeaks
