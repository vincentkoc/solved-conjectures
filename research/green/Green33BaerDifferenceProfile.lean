import Green33BaerQuadraticRetention
open Finset Green33TailEnergy Green33Multiplicity
open scoped Pointwise BigOperators
namespace Green33BaerDifferenceProfile
variable {G:Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

private def diag (A:Finset G) (s:G) := (A.filter fun a => a+a=s).card

omit [Fintype G] in
private theorem supported (A:Finset G) {s:G} (hit:s∈A+A) : 2≤reps A s+diag A s := by
  obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hit
  let P:=(A×ˢA).filter fun p => p.1+p.2=a+b
  have p:(a,b)∈P:=by simp [P,ha,hb]
  change 2≤P.card+_
  by_cases eq:a=b
  · subst b
    have d:0<diag A (a+a):=card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,rfl⟩⟩
    have h:=card_pos.mpr ⟨_,p⟩
    omega
  · have q:(b,a)∈P:=by simp [P,ha,hb,add_comm b a]
    have h:1<P.card := one_lt_card.mpr ⟨_,p,_,q,fun h => eq (congrArg Prod.fst h)⟩
    omega

/-- Quantitative near-perfect difference bound for a bounded-representation
set. The sum excludes the compulsory diagonal difference at zero. -/
theorem difference_variance (A:Finset G) (C:ℕ) (cap:∀ s,reps A s≤C) :
    (∑ s∈(univ.erase 0),((diffReps A s:ℝ)-1)^2) ≤
      C*((A.card:ℝ)^2+A.card-2*(A+A).card)+Fintype.card G-((A.card:ℝ)-1)^2 := by
  classical
  let u (s:G):ℝ:=if s∈A+A then 1 else 0
  have ub (s:G) : ((reps A s:ℝ)-1)^2≤
      C*((reps A s:ℝ)+diag A s-2*u s)+1 := by
    have non : 0≤(C:ℝ) := Nat.cast_nonneg _
    have cr : (reps A s:ℝ)≤C := by exact_mod_cast cap s
    by_cases h:s∈A+A
    · have d : (2:ℝ)≤reps A s+diag A s := by exact_mod_cast supported A h
      simp only [u,if_pos h,mul_one]
      have p:=mul_nonneg (sub_nonneg.mpr cr) (sub_nonneg.mpr d)
      have z:=mul_nonneg (Nat.cast_nonneg (α:=ℝ) (reps A s)) (Nat.cast_nonneg (α:=ℝ) (diag A s))
      nlinarith only [p,z]
    · have z:reps A s=0 := by
        apply card_eq_zero.mpr
        apply eq_empty_of_forall_notMem
        intro p hp
        obtain ⟨a,b⟩:=p
        have k:=mem_filter.mp hp
        exact h (k.2 ▸ Finset.add_mem_add (mem_product.mp k.1).1 (mem_product.mp k.1).2)
      simp only [u,if_neg h,z,Nat.cast_zero,zero_sub,neg_sq,one_pow,mul_zero,sub_zero,zero_add]
      linarith only [mul_nonneg non (Nat.cast_nonneg (α:=ℝ) (diag A s))]
  have sums : ∑ s:G,(reps A s:ℝ)=(A.card:ℝ)^2 := by
    exact_mod_cast (show ∑ s:G,reps A s=A.card^2 by simpa [reps,pow_two] using sum_card_fiberwise_eq_card_filter (A×ˢA) univ (fun p:G×G => p.1+p.2))
  have ds : ∑ s:G,(diag A s:ℝ)=A.card := by
    exact_mod_cast (show ∑ s:G,diag A s=A.card by simpa [diag] using sum_card_fiberwise_eq_card_filter A univ (fun a:G => a+a))
  have us : ∑ s:G,u s=(A+A).card := by simp [u]
  have at0 : diffReps A 0=A.card := by simp only [diffReps,sub_eq_zero,←diag_eq_filter,diag_card]
  have b:=sum_le_sum (s:=univ) fun s _ => ub s
  rw [centered_energy_eq,←sum_erase_add _ _ (mem_univ (0:G)),at0] at b
  simp only [sum_add_distrib,←mul_sum,sum_sub_distrib,sums,ds,us,sum_const,card_univ,nsmul_eq_mul,mul_one] at b
  linarith only [b]
#print axioms difference_variance

variable {H:Type*} [AddCommGroup H] [DecidableEq H] [Fintype H]

/-- Translate a subgroup embedding before intersecting with the full basis. -/
def placed (f:G→+H) (z:H) (B:Finset G) := B.image fun b => z+f b

/-- Squared error of all nonzero difference multiplicities from one. -/
noncomputable def variance (B:Finset G) : ℝ :=
  ∑ s∈(univ.erase 0),((diffReps B s:ℝ)-1)^2

/-- Exact finite budget, charging missing points in the placed copy of B. -/
theorem retained_variance (B:Finset G) (T:Finset H) (f:G→+H) (inj:Function.Injective f)
    (z:H) (C:ℕ) (cap:∀ s,reps B s≤C) (full:T+T=univ) :
    let d:ℝ:=((placed f z B)\T).card
    variance B≤ C*(((T.card:ℝ)^2+T.card-2*Fintype.card H)+d*(2*B.card+1-d))+
      Fintype.card G-((B.card:ℝ)-1)^2 := by
  classical
  let L:=placed f z B
  let R:=L∩T
  have k:L.card=B.card:=card_image_of_injective _ (fun _ _ eq => inj (add_left_cancel eq))
  have small:(R+R).card≤(B+B).card := by
    have im : R+R ⊆ (B+B).image (fun x => (z+z)+f x) := by
      intro x hx
      obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hx
      obtain ⟨u,hu,rfl⟩:=mem_image.mp (show a∈L from (mem_inter.mp ha).1)
      obtain ⟨v,hv,rfl⟩:=mem_image.mp (show b∈L from (mem_inter.mp hb).1)
      exact mem_image.mpr ⟨u+v,add_mem_add hu hv,by rw [f.map_add];abel⟩
    exact (card_le_card im).trans card_image_le
  have h:=Green33BaerQuadratic.retained_pair_budget T R inter_subset_right
  rw [full,card_univ] at h
  have hh:(Fintype.card H:ℝ)+((R.card+1).choose 2:ℕ)≤((T.card+1).choose 2:ℕ)+((B+B).card:ℝ) := by
    exact_mod_cast h.trans (Nat.add_le_add_left small _)
  rw [Nat.cast_choose_two,Nat.cast_choose_two,Nat.cast_add_one,Nat.cast_add_one] at hh
  have cnt:(L\T).card+R.card=B.card := (card_sdiff_add_card_inter L T).trans k
  have cc:((L\T).card:ℝ)+R.card=B.card := by exact_mod_cast cnt
  have rr:(R.card:ℝ)=(B.card:ℝ)-(L\T).card := by linarith
  rw [rr] at hh
  have bound:(B.card:ℝ)^2+B.card-2*(B+B).card ≤ (T.card:ℝ)^2+T.card-2*Fintype.card H+
      ((L\T).card:ℝ)*(2*B.card+1-(L\T).card) := by linarith only [hh]
  exact (difference_variance B C cap).trans (by gcongr)
#print axioms retained_variance


open Filter
open scoped Topology
variable {ι:Type*} {l:Filter ι}

/-- A bounded-representation seed of size asymptotic to √v, placed in a
critical full basis of bounded index, must have vanishing relative variance
if only o(√v) seed points are omitted. No condition is imposed on other points. -/
theorem critical_profile (v n:ι→ℕ+) (B:∀ i,Finset (ZMod (v i))) (T:∀ i,Finset (ZMod (n i)))
    (f:∀ i,ZMod (v i)→+ZMod (n i)) (inj:∀ i,Function.Injective (f i)) (z:∀ i,ZMod (n i))
    (C J:ℕ) (idx:∀ i,(n i).val≤J*(v i).val) (cap:∀ i s,reps (B i) s≤C) (full:∀ i,T i+T i=univ)
    (grow:Tendsto (fun i => (v i).val) l atTop)
    (seed:Tendsto (fun i => ((B i).card:ℝ)/Real.sqrt (v i)) l (𝓝 1))
    (crit:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2)))
    (omitted:Tendsto (fun i => (((placed (f i) (z i) (B i))\(T i)).card:ℝ)/Real.sqrt (v i)) l (𝓝 0)) :
    Tendsto (fun i => variance (B i)/(v i:ℝ)) l (𝓝 0) := by
  let k (i:ι):ℝ:=(B i).card
  let t (i:ι):ℝ:=(T i).card
  let d (i:ι):ℝ:=((placed (f i) (z i) (B i))\(T i)).card
  let a (i:ι):ℝ:=Real.sqrt (v i)
  have vp i : (0:ℝ)<(v i).val := by exact_mod_cast (v i).pos
  have np i : (0:ℝ)<(n i).val := by exact_mod_cast (n i).pos
  have ap i : 0<a i:=Real.sqrt_pos.mpr (vp i)
  have sq i : a i^2=(v i:ℝ):=Real.sq_sqrt (vp i).le
  have big:Tendsto (fun i => (n i).val) l atTop := by
    apply tendsto_atTop_mono _ grow
    intro i
    simpa only [ZMod.card] using Fintype.card_le_of_injective _ (inj i)
  obtain ⟨lin,quad⟩:=card_limits n (fun i => (T i).card) big crit
  let exc (i:ι):=t i^2/(n i:ℝ)+t i/(n i:ℝ)-2
  have ex:Tendsto exc l (𝓝 0) := by
    simpa only [exc,t,add_zero,sub_self] using (quad.add lin).sub_const 2
  have tiny:Tendsto (fun i => 1/a i) l (𝓝 0) := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop
    (Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow))
  change Tendsto (fun i => k i/a i) l (𝓝 1) at seed
  change Tendsto (fun i => d i/a i) l (𝓝 0) at omitted
  let U (i:ι):=(C:ℝ)*((J:ℝ)*|exc i|+(d i/a i)*(2*(k i/a i)+1/a i))+1-(k i/a i-1/a i)^2
  have lim:Tendsto U l (𝓝 0) := by
    have hh:=((((ex.abs.const_mul (J:ℝ)).add (omitted.mul ((seed.const_mul 2).add tiny))).const_mul (C:ℝ)).add_const 1).sub ((seed.sub tiny).pow 2)
    simpa only [U,abs_zero,mul_zero,zero_mul,zero_add,sub_zero,one_pow,sub_self] using hh
  apply squeeze_zero' (Eventually.of_forall fun i => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (vp i).le) _ lim
  apply Eventually.of_forall
  intro i
  have h:=retained_variance (B i) (T i) (f i) (inj i) (z i) C (cap i) (full i)
  simp only [ZMod.card] at h
  have idxr:((n i).val:ℝ)≤J*((v i).val:ℝ) := by exact_mod_cast idx i
  have he:t i^2+t i-2*(n i).val≤(J:ℝ)*|exc i| *(v i).val := by
    calc
      _ = exc i*(n i).val := by dsimp [exc];field_simp [(np i).ne']
      _ ≤ |exc i| *(n i).val := mul_le_mul_of_nonneg_right (le_abs_self _) (np i).le
      _ ≤ |exc i| *(J*(v i).val) := mul_le_mul_of_nonneg_left idxr (abs_nonneg _)
      _ = _ := by ring
  have miss:d i*(2*k i+1-d i)≤d i*(2*k i+1) := by nlinarith only [sq_nonneg (d i)]
  apply (div_le_iff₀ (vp i)).mpr
  apply h.trans
  change (C:ℝ)*(t i^2+t i-2*(n i).val+d i*(2*k i+1-d i))+(v i).val-(k i-1)^2 ≤ U i*(v i).val
  calc
    _ ≤ (C:ℝ)*((J:ℝ)*|exc i| *(v i).val+d i*(2*k i+1))+(v i).val-(k i-1)^2 := by gcongr
    _ = _ := by dsimp only [U];rw [←sq];field_simp [(ap i).ne']
#print axioms critical_profile

end Green33BaerDifferenceProfile
