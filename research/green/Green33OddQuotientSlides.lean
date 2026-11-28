import Green33QuotientLayerBalance
open Finset Filter
open scoped Pointwise Topology
namespace Green33LayerSlides
variable {H:Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- Mean fraction of the ambient group covered by an independently translated basis. -/
noncomputable def meanCoverage {m:ℕ+} (π:H→+ZMod m) (A:Finset H) : ℝ :=
  (∑ h:ZMod m→π.ker,((displaced π A h+displaced π A h).card:ℝ)) /
    ((Fintype.card H:ℝ)*(Fintype.card π.ker:ℝ)^m.val)

theorem meanCoverage_rows {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (s:ZMod m→H) (right:Function.RightInverse s π) :
    meanCoverage π A=1-(∑ c:ZMod m,rowMiss π A (s (c+c)))/(m:ℝ) := by
  classical
  let K:=π.ker
  let M (h:ZMod m→K):=displaced π A h+displaced π A h
  let e:=((doubleEquiv odd).prodCongr (Equiv.refl K)).trans (sectionCoordinates π s right)
  let misses (c:ZMod m) := (univ.filter fun p:K×(ZMod m→K) => s (c+c)+(p.1:H)∉M p.2).card
  have row (c:ZMod m) : misses c=∑ h:ZMod m→K,∑ x:K,if s (c+c)+(x:H)∉M h then 1 else 0 := by
    dsimp only [misses]
    rw [card_filter,Fintype.sum_prod_type,sum_comm]
  have col (h:ZMod m→K) : ∑ c:ZMod m,∑ x:K,(if s (c+c)+(x:H)∉M h then 1 else 0:ℕ)=(M h)ᶜ.card := by
    let f (a:H):ℕ:=if a∉M h then 1 else 0
    have eq:=e.sum_comp f
    rw [Fintype.sum_prod_type] at eq
    change (∑ c:ZMod m,∑ x:K,f (e (c,x)))=_
    rw [eq]
    dsimp only [f]
    rw [←card_filter]
    congr 1
    ext a
    simp
  have total:(∑ h:ZMod m→K,(M h).card)+(∑ c:ZMod m,misses c)=Fintype.card H*(Fintype.card K)^m.val := by
    simp_rw [row]
    rw [sum_comm (f:=fun c (h:ZMod m→K) => ∑ x:K,(if s (c+c)+(x:H)∉M h then 1 else 0:ℕ))]
    simp_rw [col]
    rw [←sum_add_distrib]
    simp [ZMod.card,mul_comm]
  have size:(m:ℝ)*(Fintype.card K:ℝ)=(Fintype.card H:ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_prod,ZMod.card] using Fintype.card_congr e :
      m.val*Fintype.card K=Fintype.card H)
  have k:(0:ℝ)<Fintype.card K:=by positivity
  have d:(0:ℝ) < (m:ℝ) :=by exact_mod_cast m.pos
  have tot:(∑ h:ZMod m→K,((M h).card:ℝ))+(∑ c:ZMod m,(misses c:ℝ))=
      (Fintype.card H:ℝ)*(Fintype.card K:ℝ)^m.val:=by exact_mod_cast total
  unfold meanCoverage rowMiss
  change (∑ h:ZMod m→K,((M h).card:ℝ)) / _ = 1-(∑ c:ZMod m,(misses c:ℝ)/_)/(m:ℝ)
  rw [←sum_div,←size]
  rw [←size] at tot
  change (∑ h:ZMod m→K,((M h).card:ℝ)) / ((m:ℝ)*(Fintype.card K:ℝ)*(Fintype.card K:ℝ)^m.val) =
    1 - (∑ c:ZMod m,(misses c:ℝ))/((Fintype.card K:ℝ)*(Fintype.card K:ℝ)^m.val)/(m:ℝ)
  rw [div_div,sub_div' (by positivity : ((Fintype.card K:ℝ)*(Fintype.card K:ℝ)^m.val*(m:ℝ))≠0)]
  rw [show (Fintype.card K:ℝ)*(Fintype.card K:ℝ)^m.val*(m:ℝ)=(m:ℝ)*Fintype.card K*(Fintype.card K:ℝ)^m.val by ring]
  congr 1
  linarith
#print axioms meanCoverage_rows
variable {ι:Type*} {l:Filter ι}
theorem critical_row_misses {m:ℕ+} (odd:Odd m.val) (n:ι→ℕ+) (T:∀ i,Finset (ZMod (n i)))
    (π:∀ i,ZMod (n i)→+ZMod m) (onto:∀ i,Function.Surjective (π i)) (c:ZMod m)
    (t:∀ i,ZMod (n i)) (row:∀ i,π i (t i)=c+c)
    (grow:Tendsto (fun i => (n i).val) l atTop) (full:∀ i,T i+T i=univ)
    (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => rowMiss (π i) (T i) (t i)) l
      (𝓝 ((1-1/(m:ℝ))*(1-2/(m:ℝ))^(positiveHalf m).card)) := by
  classical
  let d:ℝ:=m
  let L (c:ZMod m) (i:ι):=layer (π i) (T i) c
  let K (i:ι):ℝ:=Fintype.card (π i).ker
  have dp:0<d:=by dsimp [d];exact_mod_cast m.pos
  have kp (i:ι):0<K i:=by dsimp [K];positivity
  have size (i:ι):d*K i=(n i:ℝ) := by
    let s:=Function.surjInv (onto i)
    have e:=sectionCoordinates (π i) s (Function.rightInverse_surjInv (onto i))
    dsimp only [d,K]
    exact_mod_cast (by simpa only [Fintype.card_prod,ZMod.card] using Fintype.card_congr e :
      m.val*Fintype.card (π i).ker=(n i).val)
  have scale (i:ι) (a:ℝ):a/K i=(a/(n i:ℝ))*d := by
    rw [←size];field_simp [dp.ne',(kp i).ne']
  have inside (a:ZMod m) (i:ι):L a i⊆T i:=filter_subset _ _
  have balance (a:ZMod m):Tendsto (fun i => ((L a i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2/d)) := by
    simpa only [ZMod.card,L,d] using quotient_balance n T π onto (fun _ => a) grow full crit
  have empty:Tendsto (fun i => ((∅:Finset (ZMod (n i))).card:ℝ)/Real.sqrt (n i)) l (𝓝 0) := by simpa using (tendsto_const_nhds (f:=l) (x:=(0:ℝ)))
  have diag:=(support_limits n T (L c) (fun _ => ∅) grow full crit (inside c) (fun _ => empty_subset _) (fun _ => by simp) (balance c) empty).1
  have diag':Tendsto (fun i => ((L c i+L c i).card:ℝ)/K i) l (𝓝 (1/d)) := by
    simp_rw [scale]
    convert diag.mul_const d using 1
    rw [div_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    field_simp [dp.ne']
  have cross (j:positiveHalf m) :
      Tendsto (fun i => ((L (c+j.val) i+L (c-j.val) i).card:ℝ)/K i) l (𝓝 (2/d)) := by
    have ne:c+j.val≠c-j.val:=by
      intro eq
      rw [sub_eq_add_neg] at eq
      have opp:=add_left_cancel eq
      have lt:= (mem_filter.mp j.property).2
      rw [←opp] at lt
      exact (lt_irrefl _ lt)
    have sep (i:ι):Disjoint (L (c+j.val) i) (L (c-j.val) i) :=
      Finset.disjoint_left.mpr fun _ h k => ne ((mem_filter.mp h).2.symm.trans (mem_filter.mp k).2)
    have hh:=(support_limits n T _ _ grow full crit (inside _) (inside _) sep (balance _) (balance _)).2
    simp_rw [scale]
    convert hh.mul_const d using 1
    rw [div_mul_div_comm,Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)]
    field_simp [dp.ne']
  simp_rw [rowMiss_product odd _ _ c _ (row _)]
  have prod:=tendsto_finsetProd (univ:Finset (positiveHalf m)) fun j _ => (cross j).const_sub 1
  simpa only [prod_const,card_univ,Fintype.card_coe] using (diag'.const_sub 1).mul prod

#print axioms critical_row_misses

/-- Limiting coverage for an odd quotient of order 2r+1. -/
noncomputable def oddCoverage (r:ℕ):ℝ := 1-(1-1/(2*(r:ℝ)+1))*(1-2/(2*(r:ℝ)+1))^r

/-- For every fixed odd divisor, the arithmetic mean over physical layer
translations converges, for every full cyclic family at Green's density. -/
theorem critical_mean_coverage {m:ℕ+} (odd:Odd m.val) (n:ι→ℕ+) (T:∀ i,Finset (ZMod (n i)))
    (π:∀ i,ZMod (n i)→+ZMod m) (onto:∀ i,Function.Surjective (π i))
    (grow:Tendsto (fun i => (n i).val) l atTop) (full:∀ i,T i+T i=univ)
    (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2))) :
    Tendsto (fun i => meanCoverage (π i) (T i)) l (𝓝 (oddCoverage ((m.val-1)/2))) := by
  classical
  let s (i:ι) :=Function.surjInv (onto i)
  have right (i:ι):Function.RightInverse (s i) (π i):=Function.rightInverse_surjInv (onto i)
  have row (c:ZMod m):=critical_row_misses odd n T π onto c (fun i => s i (c+c))
    (fun i => right i _) grow full crit
  have sum:=tendsto_finsetSum (univ:Finset (ZMod m)) fun c _ => row c
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul] at sum
  have avg:=(sum.div_const (m:ℝ)).const_sub 1
  have nz:(m:ℝ)≠0:=by exact_mod_cast m.pos.ne'
  simp only [mul_div_cancel_left₀ _ nz] at avg
  simp_rw [meanCoverage_rows odd _ _ _ (right _)]
  have half:=half_count odd
  have r:(m.val-1)/2=(positiveHalf m).card:=by omega
  have sz:(2:ℝ)*((positiveHalf m).card:ℝ)+1=(m:ℝ):=by exact_mod_cast (show 2*(positiveHalf m).card+1=m.val by omega)
  simpa only [oddCoverage,r,sz] using avg

theorem thirds_value : oddCoverage 1=7/9 := by norm_num [oddCoverage]

/-- Iterating the limit through odd quotient orders yields 1−exp(−1). -/
theorem oddCoverage_limit : Tendsto oddCoverage atTop (𝓝 (1-Real.exp (-1))) := by
  have pos:=Real.tendsto_one_add_div_pow_exp (1/2)
  have neg:=Real.tendsto_one_add_div_pow_exp (-(1/2))
  have ratio:=neg.div pos (Real.exp_ne_zero _)
  have powlim:Tendsto (fun r:ℕ => (1-2/(2*(r:ℝ)+1))^r) atTop (𝓝 (Real.exp (-1))) := by
    rw [←Real.exp_sub,show -(1/2:ℝ)-1/2= -1 by norm_num] at ratio
    apply ratio.congr'
    filter_upwards [eventually_gt_atTop 0] with r hr
    dsimp only [Pi.div_apply]
    rw [←div_pow]
    congr 1
    have h:(0:ℝ)<r:=by exact_mod_cast hr
    field_simp
    ring
  have inf:Tendsto (fun r:ℕ => 2*(r:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (f:=fun r:ℕ => (r:ℝ)) (fun r => by linarith [Nat.cast_nonneg (α:=ℝ) r]) tendsto_natCast_atTop_atTop
  have one:= (inf.const_div_atTop 1).const_sub 1
  change Tendsto (fun r:ℕ => 1-(1-1/(2*(r:ℝ)+1))*(1-2/(2*(r:ℝ)+1))^r) _ _
  simpa using (one.mul powlim).const_sub 1
#print axioms critical_mean_coverage
#print axioms thirds_value
#print axioms oddCoverage_limit

end Green33LayerSlides
