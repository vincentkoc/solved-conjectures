import Green33ParityDifferences
import Green33BaerCyclicCertificate

/-! Opposite blocking sets and the size of a full cyclic basis. -/
open Finset Green33PerfectDifferenceCenters Green33SingerBlockingLayers Green33ParityDifferences
open scoped Pointwise
namespace Green33BlockingDifferenceBudget
variable {v:ℕ+}

/-- Keeping both a bounded-sum set and a mixed difference cover in opposite
parities costs even-sum capacity, including when points of either are missing. -/
theorem blocking_budget (D L E B:Finset (ZMod v)) (C:ℕ) (cap:∀ s,Green33Multiplicity.reps D s≤C)
    (cover:D-L=univ) :
    v.val≤2*C*(((split E B).card+1).choose 2-(split E B+split E B).card)+
      2*(D\E).card*B.card+2*D.card*(L\B).card := by
  have sub:D-L⊆(D-B)∪(D-(L\B)) := by
    intro x h
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_sub.mp h
    by_cases ok:b∈B
    · exact mem_union_left _ (sub_mem_sub ha ok)
    · exact mem_union_right _ (sub_mem_sub ha (mem_sdiff.mpr ⟨hb,ok⟩))
  have h:=((card_le_card sub).trans (card_union_le _ _)).trans (Nat.add_le_add_left card_sub_le _)
  rw [cover,card_univ,ZMod.card] at h
  have k:=support_budget D E B C cap
  rw [mul_assoc 2 D.card];omega
#print axioms blocking_budget

open Green33BaerSubline Green33BaerForms Green33SingerAllCharacteristics Green33PrimeSingerIncidence
variable {F E K:Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]

/-- In matching Singer coordinates every rational subplane meets every
translated line. There is no rank assumption on the products of its points. -/
theorem baer_blocks (square:Fintype.card E=(Fintype.card F)^2) (frame:K≃ₗ[E](Fin 3→E))
    {D:Finset (ZMod (order E))} (S:SingerMap E K D) (shift:ZMod (order E)) :
    D-layer S.tag (rationalForm F frame) shift=univ := by
  classical
  apply eq_univ_of_forall
  intro x
  obtain ⟨u,hu⟩:=S.surj (x+shift)
  let W:=rationalForm F frame
  let L:W→ₗ[F]E:=(S.form.restrictScalars F).comp ((LinearMap.mulLeft F (u:K)).comp W.subtype)
  have tw:Module.finrank F E=2:=(Nat.pow_right_inj Fintype.one_lt_card).mp
    ((Module.card_eq_pow_finrank (K:=F) (V:=E)).symm.trans square)
  have ker:L.ker≠⊥ := by
    intro zero
    have dim:=L.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp zero)
    rw [tw,show Module.finrank F W=3 from form_rank frame] at dim
    omega
  obtain ⟨w,hw,wn⟩:=Submodule.exists_mem_ne_zero_of_ne_bot ker
  let b:=Units.mk0 (w.val:K) (fun z => wn (Subtype.ext z))
  have dm:S.tag (u*b)∈D := (S.mem _).mpr (show L w=0 from hw)
  have bm:shift+S.tag b∈layer S.tag (rationalForm F frame) shift := by
    simp only [layer,mem_filter,mem_univ,true_and]
    exact ⟨b,w.property,rfl⟩
  exact mem_sub.mpr ⟨_,dm,_,bm,by rw [S.mul,hu];abel⟩
#print axioms baer_blocks

open Filter
open scoped Topology

/-- Almost-full retention of both a two-representation seed and a blocking
opposite layer raises the critical size coefficient to at least 3/2. -/
theorem blocking_floor {ι:Type*} {l:Filter ι} (v:ι→ℕ+) (D L E B:∀ i,Finset (ZMod (v i)))
    (grow:Tendsto (fun i => (v i).val) l atTop)
    (cap:∀ i s,Green33Multiplicity.reps (D i) s≤2) (cover:∀ i,D i-L i=univ)
    (full:∀ i,split (E i) (B i)+split (E i) (B i)=univ)
    (deletions:Tendsto (fun i => (((D i)\(E i)).card:ℝ)/Real.sqrt (v i)) l (𝓝 0))
    (missing:Tendsto (fun i => ((D i).card:ℝ)*((L i)\(B i)).card/(v i:ℝ)) l (𝓝 0))
    {c:ℝ} (below:c<3/2) :
    ∀ᶠ i in l,c<((split (E i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ) := by
  let T i:=split (E i) (B i)
  let d (i:ι):ℝ:=((D i)\(E i)).card
  let e (i:ι):ℝ:=(D i).card*((L i)\(B i)).card
  let n (i:ι):ℝ:=2*((v i).val:ℝ)
  have vp i:(0:ℝ)<(v i).val:=by exact_mod_cast (v i).pos
  have np i:0<n i:=by dsimp [n];positivity
  have finite (i):9*((v i).val:ℝ)/2-e i≤(((T i).card:ℝ)+1+d i)^2 := by
    have hb:=blocking_budget (D i) (L i) (E i) (B i) 2 (cap i) (cover i)
    have charge:=Green33BaerQuadratic.retained_pair_budget (T i) ∅ (empty_subset _)
    have enough:((T i)+(T i)).card≤((T i).card+1).choose 2:=by simpa using charge
    have h:=Nat.cast_le (α:=ℝ).mpr hb
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h
    rw [Nat.cast_sub enough,Nat.cast_choose_two,Nat.cast_add_one,full,card_univ,ZMod.card,Nat.cast_mul,Nat.cast_ofNat] at h
    have b:(B i).card≤(T i).card:=by simp [T,split_card]
    have dd:0≤d i:=Nat.cast_nonneg _
    have kd:=mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr b) dd
    dsimp only [T,d,e] at kd dd ⊢
    nlinarith only [h,kd,mul_nonneg dd (Nat.cast_nonneg (α:=ℝ) (T i).card),dd,sq_nonneg (d i),Nat.cast_nonneg (α:=ℝ) (T i).card]
  have rt:=Real.tendsto_sqrt_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have tiny:=(tendsto_const_nhds (x:=(1:ℝ))).div_atTop rt
  have lower:Tendsto (fun i => Real.sqrt (9/4-e i/(2*(v i).val))-(1+d i)/Real.sqrt (n i)) l (𝓝 (3/2)) := by
    have a:=((tendsto_const_nhds (f:=l) (x:=(9/4:ℝ))).sub (missing.div_const 2)).sqrt
    have b:=(tiny.add deletions).div_const (Real.sqrt 2)
    have lim:=a.sub b
    norm_num [Real.sqrt_div (by norm_num : (0:ℝ)≤9)] at lim
    apply lim.congr
    intro i
    dsimp only [e,d,n,Function.comp_apply]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    apply congrArg₂ (·-·)
    · congr 1
      field_simp
    · field_simp [Real.sqrt_ne_zero'.mpr (vp i),Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<2)]
  filter_upwards [lower.eventually_const_lt below] with i hi
  have bound:9/4-e i/(2*(v i).val)≤((((T i).card:ℝ)+1+d i)/Real.sqrt (n i))^2 := by
    rw [div_pow,Real.sq_sqrt (np i).le,le_div_iff₀ (np i)]
    calc
      _ = 9*((v i).val:ℝ)/2-e i := by dsimp [n];field_simp [(vp i).ne'];ring
      _ ≤ _ := finite i
  have rb:=Real.sqrt_le_sqrt bound
  rw [Real.sqrt_sq (by dsimp [d];positivity)] at rb
  change c<((T i).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ)
  rw [Nat.cast_mul,Nat.cast_ofNat]
  change c<((T i).card:ℝ)/Real.sqrt (n i)
  rw [add_div,add_div] at rb
  rw [add_div] at hi
  linarith only [hi,rb]
#print axioms blocking_floor

/-- A matching Singer line and translated rational subplane in opposite
parities force the 3/2 lower coefficient after o(√v) deletions from each. -/
theorem baer_blocking_floor {ι:Type*} {l:Filter ι} (F E K:ι→Type*)
    [∀ i,Field (F i)] [∀ i,Fintype (F i)] [∀ i,Field (E i)] [∀ i,Fintype (E i)]
    [∀ i,Field (K i)] [∀ i,Algebra (F i) (E i)] [∀ i,Algebra (E i) (K i)]
    [∀ i,Algebra (F i) (K i)] [∀ i,IsScalarTower (F i) (E i) (K i)]
    (square:∀ i,Fintype.card (E i)=(Fintype.card (F i))^2)
    (frame:∀ i,K i≃ₗ[E i](Fin 3→E i)) (D A B:∀ i,Finset (ZMod (order (E i))))
    (chart:∀ i,SingerMap (E i) (K i) (D i)) (perf:∀ i,Perfect (D i))
    (shift:∀ i,ZMod (order (E i))) (grow:Tendsto (fun i => order (E i)) l atTop)
    (full:∀ i,split (v:=positiveOrder (E i)) (A i) (B i)+split (v:=positiveOrder (E i)) (A i) (B i)=univ)
    (line:Tendsto (fun i => (((D i)\(A i)).card:ℝ)/Real.sqrt (order (E i))) l (𝓝 0))
    (plane:Tendsto (fun i => (((layer (chart i).tag (rationalForm (F i) (frame i)) (shift i))\(B i)).card:ℝ)/
      Real.sqrt (order (E i))) l (𝓝 0)) {c:ℝ} (below:c<3/2) :
    ∀ᶠ i in l,c<((split (v:=positiveOrder (E i)) (A i) (B i)).card:ℝ)/Real.sqrt ((2*order (E i):ℕ):ℝ) := by
  let L i:=layer (chart i).tag (rationalForm (F i) (frame i)) (shift i)
  refine blocking_floor (fun i => positiveOrder (E i)) D L A B grow (fun i => perfect_sum_cap _ (perf i))
    (fun i => baer_blocks (square i) (frame i) (chart i) (shift i)) full line ?_ below
  let r (i:ι):=Real.sqrt (order (E i))
  have vp i:(0:ℝ)<order (E i):=by exact_mod_cast (positiveOrder (E i)).pos
  have sq i:r i^2=(order (E i):ℝ):=Real.sq_sqrt (vp i).le
  have rp i:0<r i:=Real.sqrt_pos.mpr (vp i)
  have bound (i):((D i).card:ℝ)≤2*r i := by
    have k:=parameters _ (perf i)
    rw [ZMod.card] at k
    have b:(D i).card≤order (E i):=by simpa only [ZMod.card] using card_le_univ (D i)
    nlinarith only [k,Nat.cast_le (α:=ℝ).mpr b,sq i,(rp i).le,Nat.cast_nonneg (α:=ℝ) (D i).card]
  have lim:=plane.const_mul 2
  rw [mul_zero] at lim
  apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ lim
  apply Eventually.of_forall
  intro i
  change (D i).card*(((L i)\(B i)).card:ℝ)/(order (E i):ℝ)≤2*(((L i)\(B i)).card/r i)
  rw [←sq i,div_le_iff₀ (sq_pos_of_pos (rp i))]
  calc
    _ ≤ (2*r i)*(((L i)\(B i)).card:ℝ) := mul_le_mul_of_nonneg_right (bound i) (Nat.cast_nonneg _)
    _ = _ := by field_simp [(rp i).ne']
#print axioms baer_blocking_floor

end Green33BlockingDifferenceBudget
