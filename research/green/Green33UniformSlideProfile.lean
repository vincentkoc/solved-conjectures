import Green33SidonLayerRepairs
import Green33BaerDifferenceProfile
import Green33ShiftVariation

/-! Translate intersections of the self-sum support of an approximate difference set. -/
open Finset Green33Multiplicity Green33TailEnergy Green33BaerDifferenceProfile
open scoped Pointwise BigOperators
namespace Green33UniformSlides
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def sumIndicator (A : Finset G) (x:G) : ℝ := if x∈A+A then 1 else 0

omit [Fintype G] in
private theorem zero_diff (A : Finset G) : diffReps A 0 = A.card := by
  simp only [diffReps,sub_eq_zero,←diag_eq_filter,diag_card]

private theorem total_reps (A : Finset G) : ∑ z:G,(reps A z:ℝ)=(A.card:ℝ)^2 := by
  exact_mod_cast (show ∑ s:G,reps A s=A.card^2 by
    simpa [reps,pow_two] using sum_card_fiberwise_eq_card_filter (A×ˢA) univ (fun p:G×G => p.1+p.2))

private theorem centered (A : Finset G) :
    (∑ z:G, ((reps A z:ℝ)-1)^2) = variance A + ((A.card:ℝ)-1)^2 := by
  rw [centered_energy_eq,←sum_erase_add _ _ (mem_univ (0:G)),zero_diff]
  rfl

/-- The squared error made by replacing ordered sum counts by twice the
indicator of the self-sum support is controlled by off-zero differences. -/
theorem support_error (A : Finset G) :
    (∑ z:G, ((reps A z:ℝ)-2*sumIndicator A z)^2) ≤
      variance A + (A.card:ℝ)^2 + 1 - Fintype.card G := by
  have identity (z:G) :
      ((reps A z:ℝ)-2*sumIndicator A z)^2 = ((reps A z:ℝ)-1)^2-2*(reps A z:ℝ)+4*sumIndicator A z-1 := by
    by_cases h:z∈A+A
    · simp only [sumIndicator,if_pos h];ring
    · have r:reps A z=0 := addConvolution_eq_zero.mpr h
      simp [sumIndicator,h,r]
  have mass : (∑ z:G,sumIndicator A z)=((A+A).card:ℝ) := by simp [sumIndicator]
  have u:2*((A+A).card:ℝ)≤(A.card:ℝ)^2+A.card := by exact_mod_cast Green33SidonLayerRepairs.sum_upper A
  simp only [identity,sum_sub_distrib,sum_add_distrib,←mul_sum,total_reps,centered,mass,sum_const,card_univ,nsmul_eq_mul,mul_one]
  linarith only [u]
#print axioms support_error

private noncomputable def correlation (f : G→ℝ) (h:G) := ∑ z:G,f z*f (z+h)
private noncomputable def squareMass (f : G→ℝ) := ∑ z:G,(f z)^2

omit [DecidableEq G] in
private theorem cs (f g : G→ℝ) (h:G) : |∑ z:G,f z*g (z+h)| ≤
    Real.sqrt (squareMass f) * Real.sqrt (squareMass g) := by
  have b:=Real.sum_mul_le_sqrt_mul_sqrt univ (fun z:G => |f z|) (fun z:G => |g (z+h)|)
  have eq : ∑ z:G,(g (z+h))^2 = ∑ z:G,(g z)^2 := Equiv.sum_comp (Equiv.addRight h) (fun z:G => (g z)^2)
  simp only [sq_abs,eq] at b
  unfold squareMass
  calc
    _ ≤ ∑ z:G,|f z*g (z+h)| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul]
    _ ≤ _ := b

omit [DecidableEq G] in
private theorem correlation_error (f g : G→ℝ) (h:G) :
    |correlation f h-correlation g h| ≤
      Real.sqrt (squareMass fun z => f z-g z) * (Real.sqrt (squareMass f)+Real.sqrt (squareMass g)) := by
  have eq : correlation f h-correlation g h =
      (∑ z:G,(f z-g z)*f (z+h))+(∑ z:G,g z*(f (z+h)-g (z+h))) := by
    simp only [correlation,←sum_sub_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro z _
    ring
  rw [eq]
  have b₁:=cs (fun z => f z-g z) f h
  have b₂:=cs g (fun z => f z-g z) h
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := (add_le_add b₁ b₂).trans_eq (by ring)

private noncomputable def model (k:ℝ) (z:G) : ℝ := if z=0 then k else 1

private theorem model_correlation (k : ℝ) {h:G} (hh : h≠0) :
    correlation (model k) h=Fintype.card G+2*(k-1) := by
  have pt (z:G) : model k z*model k (z+h)=1+(if z=0 then k-1 else 0)+(if z=-h then k-1 else 0) := by
    have shift : z+h=0 ↔ z=-h := eq_neg_iff_add_eq_zero.symm
    by_cases zero:z=0
    · subst z;simp [model,hh]
    · by_cases minus:z=-h
      · simp [model,minus,hh]
      · simp [model,zero,minus,shift]
  simp only [correlation,pt,sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,nsmul_eq_mul,mul_one]
  ring

private theorem model_square (k:ℝ) :
    squareMass (model (G:=G) k)=Fintype.card G-1+k^2 := by
  have pt (z:G) : model k z ^ 2 = 1+(if z=0 then k^2-1 else 0) := by
    by_cases h:z=0 <;> simp [model,h]
  simp only [squareMass,pt,sum_add_distrib,sum_ite_eq',mem_univ,if_true,sum_const,card_univ,nsmul_eq_mul,mul_one]
  ring

private theorem diff_error (A:Finset G) :
    squareMass (fun z:G => (diffReps A z:ℝ)-model (A.card:ℝ) z)=variance A := by
  unfold squareMass variance
  rw [←sum_erase_add _ _ (mem_univ (0:G))]
  simp only [zero_diff,model,ite_true,sub_self,zero_pow (by decide : 2≠0),add_zero]
  apply sum_congr rfl
  intro z hz
  rw [if_neg (mem_erase.mp hz).1]

private theorem rep_square (A:Finset G) :
    squareMass (fun z:G => (reps A z:ℝ)) =
      variance A + 3*(A.card:ℝ)^2-2*A.card-Fintype.card G+1 := by
  have eq (t:ℝ) : (t-1)^2=t^2-2*t+1 := by ring
  have h:=centered A
  simp only [eq,sum_add_distrib,sum_sub_distrib,←mul_sum,total_reps,sum_const,card_univ,nsmul_eq_mul,mul_one] at h
  unfold squareMass
  linarith only [h]

private theorem diff_square (A:Finset G) :
    squareMass (fun z:G => (diffReps A z:ℝ))=squareMass (fun z:G => (reps A z:ℝ)) := by
  simpa [squareMass] using (centered_energy_eq A 0).symm

private theorem mark_square (A : Finset G) :
    squareMass (fun z:G => 2*sumIndicator A z) = 4*((A+A).card:ℝ) := by
  have eq (z:G) : (2*sumIndicator A z)^2=4*(if z∈A+A then (1:ℝ) else 0) := by
    by_cases h:z∈A+A <;> norm_num [sumIndicator,h]
  simp only [squareMass,eq,←mul_sum]
  congr 1;simp

private theorem mark_corr (A:Finset G) (h:G) :
    correlation (fun z:G => 2*sumIndicator A z) h = 4*(diffReps (A+A) h:ℝ) := by
  let U:=A+A
  have pt (z:G) : (2*sumIndicator A z)*(2*sumIndicator A (z+h))=
      4*(if z∈U∩((-h) +ᵥ U) then (1:ℝ) else 0) := by
    have shift : z ∈ (-h) +ᵥ U ↔ z+h∈U := by
      rw [mem_vadd_finset]
      constructor
      · rintro ⟨w,hw,eq⟩;convert hw using 1;rw [←eq];change -h+w+h=w;abel
      · intro hw;exact ⟨z+h,hw,by change -h+(z+h)=z;abel⟩
    by_cases hz:z∈U <;> by_cases ht:z+h∈U <;> norm_num [sumIndicator,←show U=A+A from rfl,shift,hz,ht]
  simp only [correlation,pt,←mul_sum]
  have trans : (({h}:Finset G)+(U∩((-h) +ᵥ U)))=(h +ᵥ U)∩U := by
    rw [singleton_add_inter,singleton_add,singleton_add,vadd_vadd,add_neg_cancel,zero_vadd]
  have same:=congrArg card trans
  rw [card_singleton_add,inter_comm (h +ᵥ U) U,card_inter_vadd U U h,←card_sub_eq U U h] at same
  have mass : ∑ z:G,(if z∈U∩(-h +ᵥ U) then (1:ℝ) else 0)=((U∩(-h +ᵥ U)).card:ℝ) := by
    rw [sum_boole,filter_mem_eq_inter,univ_inter]
  rw [mass,same]
  rfl


/-- An explicit error for the intersection of A+A with each of its nonzero
translates. Only the variance of nonzero differences and the size of A enter. -/
noncomputable def slideError (V k n : ℝ) : ℝ :=
  let J := V+3*k^2-2*k-n+1
  Real.sqrt (V+k^2+1-n)*(Real.sqrt (4*n)+Real.sqrt J) +
    Real.sqrt V*(Real.sqrt J+Real.sqrt (n-1+k^2))

theorem uniform_intersection (A:Finset G) {h:G} (hh:h≠0) :
    |4*(diffReps (A+A) h:ℝ)-(Fintype.card G+2*((A.card:ℝ)-1))| ≤
      slideError (variance A) A.card (Fintype.card G) := by
  let r (z:G):ℝ:=reps A z
  let d (z:G):ℝ:=diffReps A z
  let w (z:G):ℝ:=2*sumIndicator A z
  let p := model (G:=G) (A.card:ℝ)
  have bridge : correlation r h=correlation d h := by
    unfold correlation
    dsimp only [r,d]
    exact_mod_cast Green33ShiftVariation.shifted_correlation A h
  have x:=correlation_error w r h
  have y:=correlation_error d p h
  have equal : squareMass (fun z => w z-r z)=squareMass (fun z => r z-w z) := by
    unfold squareMass;apply sum_congr rfl;intro z _;ring
  have lw : squareMass (fun z => r z-w z) ≤ variance A+(A.card:ℝ)^2+1-Fintype.card G := support_error A
  have ws : squareMass w≤4*(Fintype.card G:ℝ) := by
    rw [show squareMass w=_ from mark_square A]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_univ _)) (by norm_num)
  rw [equal] at x
  have x' := x.trans (mul_le_mul (Real.sqrt_le_sqrt lw)
    (add_le_add (Real.sqrt_le_sqrt ws) le_rfl) (by positivity) (by positivity))
  have xy:=abs_add_le (correlation w h-correlation r h) (correlation d h-correlation p h)
  rw [bridge] at x'
  rw [bridge,sub_add_sub_cancel] at xy
  have pair := xy.trans (add_le_add x' y)
  dsimp only [w,r,d,p] at pair
  rw [mark_corr,model_correlation _ hh,diff_error,diff_square,rep_square,model_square] at pair
  exact pair
#print axioms uniform_intersection


private noncomputable def relativeError (V K k τ : ℝ) :=
  let J := V+3*K-2*k-1+τ
  Real.sqrt (V+K+τ-1)*(2+Real.sqrt J) + Real.sqrt V*(Real.sqrt J+Real.sqrt (1-τ+K))

private theorem scale_error (V k n:ℝ) (hn:0<n) : slideError V k n/n =
    relativeError (V/n) (k^2/n) (k/n) (1/n) := by
  have ne: n≠0 := hn.ne'
  let H:=V+k^2+1-n
  let J:=V+3*k^2-2*k-n+1
  let F:=n-1+k^2
  have Hq : V/n+k^2/n+1/n-1=H/n := by dsimp [H];field_simp
  have Jq : V/n+3*(k^2/n)-2*(k/n)-1+1/n=J/n := by dsimp [J];field_simp
  have Fq : 1-1/n+k^2/n=F/n := by dsimp [F];field_simp
  unfold relativeError
  rw [Hq,Jq,Fq]
  simp only [Real.sqrt_div' _ hn.le]
  have four : Real.sqrt (4*n)=2*Real.sqrt n := by rw [Real.sqrt_mul (by norm_num)];norm_num
  change (Real.sqrt H*(Real.sqrt (4*n)+Real.sqrt J)+Real.sqrt V*(Real.sqrt J+Real.sqrt F))/n=_
  rw [four]
  field_simp [(Real.sqrt_pos.mpr hn).ne']
  rw [Real.sq_sqrt hn.le,mul_comm]

open Filter
open scoped Topology

/-- If the nonzero differences have mean-square error o(1) from one and the
size is asymptotic to √v, every nonzero translate of the sum support has
quarter-density intersection. The shift can depend on the set. -/
theorem quarter_translates {ι : Type*} {l : Filter ι} (v:ι→ℕ+) (A:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) l atTop)
    (size:Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (v i).val) l (𝓝 1))
    (profile:Tendsto (fun i => variance (A i)/(v i).val) l (𝓝 0)) :
    ∀ ε:ℝ, 0<ε → ∀ᶠ i in l, ∀ h:ZMod (v i),h≠0 →
      |(diffReps (A i+A i) h:ℝ)/(v i).val-1/4| < ε := by
  let n (i:ι) : ℝ := (v i).val
  let k (i:ι) : ℝ := (A i).card
  let V (i:ι) := variance (A i)
  have hn (i) : 0<n i := by dsimp [n];exact_mod_cast (v i).property
  have top:Tendsto n l atTop := tendsto_natCast_atTop_atTop.comp grow
  change Tendsto (fun i => k i/Real.sqrt (n i)) _ _ at size
  change Tendsto (fun i => V i/n i) _ _ at profile
  have ks:Tendsto (fun i => k i^2/n i) l (𝓝 1) := by
    simpa only [div_pow,Real.sq_sqrt (hn _).le,one_pow] using size.pow 2
  have kt:Tendsto (fun i => k i/n i) l (𝓝 0) := by
    simpa only [Function.comp_apply,div_div,Real.mul_self_sqrt (hn _).le] using
      size.div_atTop (Real.tendsto_sqrt_atTop.comp top)
  have tiny:Tendsto (fun i => 1/n i) l (𝓝 0) := tendsto_const_nhds.div_atTop top
  have err:Tendsto (fun i => slideError (V i) (k i) (n i)/n i) l (𝓝 0) := by
    simp_rw [scale_error _ _ _ (hn _)]
    have c:Continuous (fun p:ℝ×ℝ×ℝ×ℝ => relativeError p.1 p.2.1 p.2.2.1 p.2.2.2) := by
      unfold relativeError;fun_prop
    have q:=c.continuousAt.tendsto.comp (profile.prodMk_nhds (ks.prodMk_nhds (kt.prodMk_nhds tiny)))
    norm_num only [Prod.fst,Prod.snd,show relativeError 0 1 0 0=0 by norm_num [relativeError]] at q
    exact q
  intro ε ep
  have small:=err.add ((kt.sub tiny).abs.const_mul 2)
  norm_num only [sub_zero,abs_zero,mul_zero,add_zero] at small
  filter_upwards [small.eventually_lt_const (show (0:ℝ)<4*ε by positivity)] with i hi
  intro h hh
  have b:=uniform_intersection (A i) hh
  rw [ZMod.card] at b
  let d:ℝ:=diffReps (A i+A i) h
  change |4*d-(n i+2*(k i-1))| ≤ slideError (V i) (k i) (n i) at b
  have b' : |(4*d-(n i+2*(k i-1)))/n i| ≤ slideError (V i) (k i) (n i)/n i := by
    rw [abs_div,abs_of_pos (hn i)]
    exact div_le_div_of_nonneg_right b (hn i).le
  have q: (4*d-(n i+2*(k i-1)))/n i=4*(d/n i-1/4)-2*(k i/n i-1/n i) := by field_simp [(hn i).ne'];ring
  rw [q] at b'
  have triangle:=abs_sub_le (4*(d/n i-1/4)) (2*(k i/n i-1/n i)) 0
  simp only [sub_zero,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4),abs_of_pos (by norm_num : (0:ℝ)<2)] at triangle
  change _+2*|k i/n i-1/n i|<4*ε at hi
  change |d/n i-1/4|<ε
  linarith only [hi,b',triangle]
#print axioms quarter_translates


/-- For a Sidon seed the variance is exactly the number of missing nonzero
differences. This also covers the empty seed. -/
theorem sidon_variance (A:Finset G) (sid:IsSidon (A:Set G)) :
    variance A = Fintype.card G-1-(A.card:ℝ)*((A.card:ℝ)-1) := by
  have cap (z:G) (hz:z≠0) : diffReps A z ≤ 1 := by
    apply card_le_one.mpr
    rintro ⟨a,b⟩ hab ⟨u,v⟩ huv
    obtain ⟨⟨ha,hb⟩,hs⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp hab
    obtain ⟨⟨hu,hv⟩,ht⟩ := (mem_filter.trans (and_congr_left fun _ => mem_product)).mp huv
    have eq : a+v=u+b := sub_eq_sub_iff_add_eq_add.mp (hs.trans ht.symm)
    rcases sid a ha u hu v hv b hb eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · simp_all
  have total : ∑ z:G,(diffReps A z:ℝ)=(A.card:ℝ)^2 := by
    exact_mod_cast (show ∑ z:G,diffReps A z=A.card^2 by
      simpa [diffReps,pow_two] using sum_card_fiberwise_eq_card_filter (A×ˢA) univ (fun p:G×G => p.1-p.2))
  have nonzero : variance A=∑ z∈univ.erase 0,(1-(diffReps A z:ℝ)) := by
    apply sum_congr rfl
    intro z hz
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (cap z (mem_erase.mp hz).1) with h|h <;> norm_num [h]
  have h:=sum_erase_add univ (fun z:G => 1-(diffReps A z:ℝ)) (mem_univ 0)
  rw [←nonzero,zero_diff,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,total] at h
  linarith only [h]

/-- Unconditionally, the self-sum support of every asymptotically
square-root-size Sidon seed meets *every* nonzero translate in quarter density. -/
theorem sidon_quarter_translates {ι:Type*} {l:Filter ι} (v:ι→ℕ+) (A:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) l atTop)
    (size:Tendsto (fun i => ((A i).card:ℝ)/Real.sqrt (v i).val) l (𝓝 1))
    (sid:∀ i,IsSidon (A i:Set (ZMod (v i)))) :
    ∀ ε:ℝ, 0<ε → ∀ᶠ i in l, ∀ h:ZMod (v i),h≠0 →
      |(diffReps (A i+A i) h:ℝ)/(v i).val-1/4| < ε := by
  apply quarter_translates v A grow size
  let n (i:ι):ℝ:=(v i).val
  let k (i:ι):ℝ:=(A i).card
  have hn (i):0<n i:=by dsimp [n];exact_mod_cast (v i).property
  have top:Tendsto n l atTop := tendsto_natCast_atTop_atTop.comp grow
  change Tendsto (fun i => k i/Real.sqrt (n i)) _ _ at size
  have ks:Tendsto (fun i => k i^2/n i) l (𝓝 1) := by
    simpa only [div_pow,Real.sq_sqrt (hn _).le,one_pow] using size.pow 2
  have kt:Tendsto (fun i => k i/n i) l (𝓝 0) := by
    simpa only [Function.comp_apply,div_div,Real.mul_self_sqrt (hn _).le] using
      size.div_atTop (Real.tendsto_sqrt_atTop.comp top)
  have tiny:Tendsto (fun i => 1/n i) l (𝓝 0) := tendsto_const_nhds.div_atTop top
  have c:=((tiny.const_sub 1).sub ks).add kt
  norm_num only [sub_zero,sub_self,add_zero] at c
  apply c.congr
  intro i
  rw [sidon_variance _ (sid i),ZMod.card]
  change 1-1/n i-k i^2/n i+k i/n i=(n i-1-k i*(k i-1))/n i
  field_simp [(hn i).ne']
  ring
#print axioms sidon_variance
#print axioms sidon_quarter_translates

end Green33UniformSlides
