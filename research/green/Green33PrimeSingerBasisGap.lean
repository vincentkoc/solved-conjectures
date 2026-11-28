import Green33PrimeSingerIncidence

/-! A cardinality gap for ordinary cyclic bases containing an even prime Singer line. -/

open Finset Green33SingerBlockingLayers
open Green33ReflectedLayers (doubleHom)
open Green33PrimeSingerIncidence Green33SingerAllCharacteristics
open Green33SingerProjectiveOverlap (Plane scalars)
open Green33SingerKloosterman (proj hyperplane cubic_parameters)
open scoped Pointwise

namespace Green33PrimeSingerBasisGap

section Geometry

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Fintype F] [Fintype K]
variable [DecidableEq F] [DecidableEq K]
noncomputable local instance : Fintype (Plane F K) := Fintype.ofFinite _

private theorem singer_map (h : Fintype.card K=(Fintype.card F)^3) (L : K→ₗ[F] F)
    (onto : Function.Surjective L) : Nonempty (SingerMap F K (labels h L)) := by
  classical
  have coords : ∃ e : ZMod (order F) ≃+ Additive (Plane F K),
      labels h L=(hyperplane L).map (e.toEquiv.trans Additive.toMul).symm.toEmbedding := ⟨_,rfl⟩
  obtain ⟨e,coords⟩ := coords
  let tag (u : Kˣ) := e.symm (Additive.ofMul (proj (F:=F) u))
  have same (u v : Kˣ) : proj (F:=F) u=proj (F:=F) v ↔ ∃ a : F, (u:K)=a • (v:K) := by
    constructor
    · intro eq
      obtain ⟨a,ha⟩ := QuotientGroup.eq_iff_div_mem.mp eq
      have t := congrArg (fun z : Kˣ => (z:K)) ha
      rw [Units.val_div_eq_div_val] at t
      refine ⟨a,?_⟩
      rw [Algebra.smul_def]
      exact ((eq_div_iff v.ne_zero).mp t).symm
    · rintro ⟨a,ha⟩
      have nz : a≠0 := by rintro rfl; simp [u.ne_zero] at ha
      apply QuotientGroup.eq_iff_div_mem.mpr
      refine ⟨Units.mk0 a nz,Units.ext ?_⟩
      rw [Units.val_div_eq_div_val]
      change algebraMap F K a=(u:K)/(v:K)
      rw [Algebra.smul_def] at ha
      exact (eq_div_iff v.ne_zero).mpr ha.symm
  refine ⟨⟨L,onto,tag,?_,?_,?_,?_⟩⟩
  · intro u v
    exact (congrArg (fun z => e.symm (Additive.ofMul z)) (map_mul (proj (F:=F)) u v)).trans
      (e.symm.map_add _ _)
  · intro x
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (scalars F K) (e x).toMul
    exact ⟨u, (congrArg (fun z => e.symm (Additive.ofMul z)) hu).trans (e.symm_apply_apply x)⟩
  · intro u v
    exact e.symm.injective.eq_iff.trans (same u v)
  · intro u
    rw [coords,mem_map_equiv,Equiv.symm_symm]
    change (e (e.symm _)).toMul∈hyperplane L ↔ _
    rw [e.apply_symm_apply]
    constructor
    · intro hm
      obtain ⟨v,hv,zero⟩ := (mem_filter.mp hm).2
      obtain ⟨a,ha⟩ := (same u v).mp hv.symm
      rw [ha,map_smul,zero,smul_zero]
    · intro zero
      exact mem_filter.mpr ⟨mem_univ _,u,rfl,zero⟩

end Geometry

private theorem thresholds {p h : ℕ} (big : 4096≤p) (low : 20*h<p^2) :
    let d := (p-4)/3
    2*h<(d+1)*(d+2) ∧ 3*(d+1)<p ∧ 2*(p+h)<(p+1)*(p-d) := by
  let d := (p-4)/3
  change 2*h<(d+1)*(d+2) ∧ 3*(d+1)<p ∧ 2*(p+h)<(p+1)*(p-d)
  have lower : p≤3*(d+2) := by dsimp [d];omega
  have bigD : 9≤d := by dsimp [d];omega
  have small : 3*(d+1)<p := by dsimp [d];omega
  have diff : 2*p≤3*(p-d) := by omega
  refine ⟨?_,small,?_⟩
  · nlinarith only [low,Nat.mul_le_mul lower lower,Nat.mul_le_mul_right (d+2) bigD]
  · nlinarith only [low,Nat.mul_le_mul_left (p+1) diff,Nat.mul_le_mul_right p big]

private theorem reflected_holes {p : ℕ} [Fact p.Prime] {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K]
    (h : Fintype.card K=(Fintype.card (ZMod p))^3) (L : K→ₗ[ZMod p] ZMod p)
    (onto : Function.Surjective L) (ψ : AddChar (ZMod p) ℂ) (nt : ψ≠0)
    (bound : RankFourBound L ψ) (big : 4096≤p) (c : ZMod (order (ZMod p))) :
    7*p^2 ≤ 32*(reflected h L c+reflected h L c)ᶜ.card := by
  let R := reflected h L c
  have cover := (abs_le.mp (doubled_bound h L onto ψ nt bound c)).2
  have mass := card_add_card_compl (R+R)
  rw [ZMod.card] at mass
  change (R+R).card+(R+R)ᶜ.card=2*(order (ZMod p)) at mass
  have order_eq : order (ZMod p)=p^2+p+1 := by simp [order]
  rw [order_eq] at mass cover
  rw [ZMod.card] at cover
  change 4*((R+R).card:ℝ)-7*((p^2+p+1:ℕ):ℝ)≤_ at cover
  have pr : (4096:ℝ)≤p := by exact_mod_cast big
  have root : 64*Real.sqrt p≤p := by
    have ss := Real.sq_sqrt (show 0≤(p:ℝ) by positivity)
    have lo : 64≤Real.sqrt p := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact big)
    nlinarith only [mul_le_mul_of_nonneg_right lo (Real.sqrt_nonneg (p:ℝ)),ss]
  have err : (p:ℝ)*(4*Real.sqrt p+20) ≤ p^2/8 := by
    nlinarith only [mul_le_mul_of_nonneg_left root (show 0≤(p:ℝ) by positivity),
      mul_le_mul_of_nonneg_left pr (show 0≤(p:ℝ) by positivity)]
  have total := congrArg (Nat.cast (R:=ℝ)) mass
  push_cast at total cover
  change 7*p^2 ≤ 32*(R+R)ᶜ.card
  exact_mod_cast (show 7*(p:ℝ)^2≤32*((R+R)ᶜ.card:ℝ) by linarith [show (0:ℝ)≤p by positivity])

/-- Every balanced opposite layer leaves a quadratic number of holes in the doubled cycle. -/
theorem prime_holes {p : ℕ} [Fact p.Prime] {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K]
    (h : Fintype.card K=(Fintype.card (ZMod p))^3) (L : K→ₗ[ZMod p] ZMod p)
    (onto : Function.Surjective L) (ψ : AddChar (ZMod p) ℂ) (nt : ψ≠0)
    (bound : RankFourBound L ψ) (big : 4096≤p) (B : Finset (ZMod (order (ZMod p))))
    (sizeB : B.card=p+1) :
    let S := split (v:=positiveOrder (ZMod p)) (labels h L) B
    p^2 ≤ 20*(S+S)ᶜ.card := by
  classical
  let D := labels h L
  let S := split (v:=positiveOrder (ZMod p)) D B
  change p^2≤20*(S+S)ᶜ.card
  have hodd := odd_holes (v:=positiveOrder (ZMod p)) D B
  by_cases low : 20*(D+B)ᶜ.card<p^2
  · let d := (p-4)/3
    obtain ⟨few,small,extra⟩ := thresholds big low
    have sizeD : D.card=p+1 := by
      rw [show D.card=(hyperplane L).card by simp [D,labels],(cubic_parameters L onto h).1,ZMod.card]
    have order_eq : Fintype.card (ZMod (order (ZMod p)))=p^2+p+1 := by simp [order]
    obtain ⟨geom⟩ := singer_map h L onto
    obtain ⟨c,heavy⟩ := large_line (d:=d) D B geom order_eq sizeD sizeB few small extra
    let m := occupancy D B c
    have strong : 2*p+3≤3*m := by change p+1≤m+d at heavy;dsimp [d] at heavy;omega
    have hit := (occupancy_pos D B c).mp (show 0<m by omega)
    have sec := secant_bound D B (perfect_labels h L onto) sizeD hit
    rw [sizeD,sizeB] at sec
    let t := p+1-m
    change t*(m+p)≤t*(p+1)+(D+B)ᶜ.card at sec
    have cost : 40*t≤3*p := by
      have mul : 40*t*p<3*p*p := by nlinarith only [sec,low,Nat.mul_le_mul_left t strong]
      exact (Nat.lt_of_mul_lt_mul_right mul).le
    have sizes : S.card=2*(p+1) := by rw [show S.card=D.card+B.card from split_card ..,sizeD,sizeB];omega
    have outside := outside_reflection (v:=positiveOrder (ZMod p)) D B c
    let R := reflected h L c
    have bill : (S\R).card≤t := outside.trans (Nat.sub_le_sub_right sizeB.le m)
    have change_bound := changed_sums S R
    have vacant := reflected_holes h L onto ψ nt bound big c
    change 7*p^2≤32*(R+R)ᶜ.card at vacant
    rw [sizes] at change_bound
    nlinarith only [vacant,change_bound,Nat.mul_le_mul_right (2*(p+1)) bill,
      Nat.mul_le_mul_right (p+1) cost,Nat.mul_le_mul_right p big]
  · change (D+B)ᶜ.card≤(S+S)ᶜ.card at hodd
    omega

#print axioms prime_holes

private theorem budget_gap {p x y w : ℝ} (pos : 0<p) (hx : 0≤x) (hy : 0≤y) (hw : 0≤w)
    (product : p^2≤x*y) (charge : p^2≤20*w*(x+y))
    (cost : w≤x+y-2*p ∨ w≤x-p) : 40001*p≤20000*(x+y) := by
  by_contra! small
  have short : x+y≤3*p := by linarith
  have unpaid : p≤60*w := by
    by_contra! less
    nlinarith only [charge,mul_nonneg hw (sub_nonneg.mpr short),mul_pos pos (sub_pos.mpr less)]
  rcases cost with sum|even
  · linarith
  · have lo : 0≤60*x-61*p := by linarith
    have hi : 0≤60*x-59*p := by linarith
    nlinarith only [mul_nonneg lo hi,product,mul_nonneg hx (sub_nonneg.mpr small.le),
      mul_nonneg (show 0≤3*p-x by linarith) pos.le,sq_pos_of_pos pos]

private theorem split_mono {v : ℕ+} {D A B U : Finset (ZMod v)} (da : D⊆A) (bu : B⊆U) :
    split D B ⊆ split A U :=
  union_subset_union (image_mono _ da) (image_mono _ bu)

private theorem trim {v : ℕ+} {p : ℕ} (sizeV : v.val=p^2+p+1)
    {D A U : Finset (ZMod v)} (sizeD : D.card=p+1) (da : D⊆A) :
    ∃ B : Finset (ZMod v), B.card=p+1 ∧
      (((split A U)\(split D B)).card+2*p≤(split A U).card ∨
       ((split A U)\(split D B)).card+p≤A.card) := by
  by_cases enough : p+1≤U.card
  · obtain ⟨B,bu,len⟩ := exists_subset_card_eq enough
    refine ⟨B,len,Or.inl ?_⟩
    rw [card_sdiff_of_subset (split_mono da bu),split_card,split_card,sizeD,len]
    have sizeA := card_le_card da
    omega
  · have room : p+1≤(univ : Finset (ZMod v)).card := by rw [card_univ,ZMod.card,sizeV];omega
    obtain ⟨B,ub,_,len⟩ := exists_subsuperset_card_eq (subset_univ U) (by omega : U.card≤p+1) room
    refine ⟨B,len,Or.inr ?_⟩
    have incl : (split A U)\(split D B) ⊆ (split A B)\(split D B) := by
      intro x hx
      exact mem_sdiff.mpr ⟨split_mono (Subset.rfl) ub (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
    have cap := card_le_card incl
    rw [card_sdiff_of_subset (split_mono da Subset.rfl),split_card,split_card,sizeD,len] at cap
    have sizeA := card_le_card da
    omega

/-- A full cyclic basis containing the whole prescribed even layer pays a linear
cardinality excess whenever every balanced opposite layer has quadratic defect. -/
theorem anchored_gap {v : ℕ+} {p : ℕ} (pos : 0<p) (sizeV : v.val=p^2+p+1)
    (D : Finset (ZMod v)) (sizeD : D.card=p+1)
    (defect : ∀ B : Finset (ZMod v), B.card=p+1 →
      p^2≤20*(split D B+split D B)ᶜ.card)
    (T : Finset (ZMod (2*v.val))) (anchor : D.image (doubleHom v)⊆T) (full : T+T=univ) :
    40001*p≤20000*T.card := by
  obtain ⟨E,U,decomp,_⟩ := decompose T
  let A := E∪D
  have eqn : split A U=T := by
    calc split A U=split E U∪D.image (doubleHom v) := by unfold split A;rw [image_union];ac_rfl
         _ = T := by rw [← decomp,union_eq_left.mpr anchor]
  have sizeT : T.card=A.card+U.card := eqn ▸ split_card A U
  have odd := odd_holes A U
  rw [eqn,full,compl_univ,card_empty] at odd
  have all := card_add_card_compl (A+U)
  rw [ZMod.card] at all
  have cap : (A+U).card≤A.card*U.card := card_add_le
  have product : p^2≤A.card*U.card := by omega
  obtain ⟨B,len,cost⟩ := trim sizeV sizeD (show D⊆A from subset_union_right) (U:=U)
  let S := split D B
  let w := (T\S).card
  have holes := defect B len
  have change_bound := changed_sums T S
  rw [full,compl_univ,card_empty,zero_add] at change_bound
  have charge : p^2≤20*w*T.card := (holes.trans (Nat.mul_le_mul_left 20 change_bound)).trans_eq (by ring)
  rw [eqn] at cost
  change w+2*p≤T.card ∨ w+p≤A.card at cost
  rw [sizeT] at charge cost ⊢
  have bill : (w:ℝ)≤A.card+U.card-2*p ∨ (w:ℝ)≤A.card-p := by
    rcases cost with a|b
    · left; have h : (w:ℝ)+2*p≤A.card+U.card := by exact_mod_cast a
      linarith
    · right; have h : (w:ℝ)+p≤A.card := by exact_mod_cast b
      linarith
  exact_mod_cast budget_gap (p:=(p:ℝ)) (x:=(A.card:ℝ)) (y:=(U.card:ℝ)) (w:=(w:ℝ))
    (by exact_mod_cast pos) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast product) (by exact_mod_cast charge) bill

#print axioms anchored_gap

/-- For every cubic Singer line over a sufficiently large prime field, the normalized
size of every full basis containing its even image stays away from Green's endpoint.
The rank-four estimate is the only analytic hypothesis. -/
theorem prime_gap {p : ℕ} [Fact p.Prime] {K : Type*}
    [Field K] [Fintype K] [DecidableEq K] [Algebra (ZMod p) K]
    (h : Fintype.card K=(Fintype.card (ZMod p))^3) (L : K→ₗ[ZMod p] ZMod p)
    (onto : Function.Surjective L) (ψ : AddChar (ZMod p) ℂ) (nt : ψ≠0)
    (bound : RankFourBound L ψ) (big : 100000≤p)
    (T : Finset (ZMod (2*(positiveOrder (ZMod p)).val)))
    (anchor : (labels h L).image (doubleHom (positiveOrder (ZMod p)))⊆T)
    (full : T+T=univ) :
    40001*p≤20000*T.card ∧ Real.sqrt 2+1/100000≤
      (T.card:ℝ)/Real.sqrt ((2*(positiveOrder (ZMod p)).val:ℕ):ℝ) := by
  classical
  let v := positiveOrder (ZMod p)
  have sizeV : v.val=p^2+p+1 := by simp [v,positiveOrder,order]
  have sizeD : (labels h L).card=p+1 := by
    rw [labels,card_map,(cubic_parameters L onto h).1,ZMod.card]
  have finite := anchored_gap (by omega : 0<p) sizeV (labels h L) sizeD
    (prime_holes h L onto ψ nt bound (by omega)) T anchor full
  refine ⟨finite,?_⟩
  have pos : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have large : (100000:ℝ)≤p := by exact_mod_cast big
  have card : 40001*(p:ℝ)≤20000*T.card := by exact_mod_cast finite
  have root : Real.sqrt (v.val:ℝ)≤p+1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [sizeV];push_cast;nlinarith
  have two : Real.sqrt 2≤2 := by norm_num [Real.sqrt_le_iff]
  have sq := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  change Real.sqrt 2+1/100000≤(T.card:ℝ)/Real.sqrt ((2*v.val:ℕ):ℝ)
  push_cast
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  apply (le_div_iff₀ (mul_pos (Real.sqrt_pos_of_pos (by norm_num)) (Real.sqrt_pos_of_pos (by exact_mod_cast v.property)))).mpr
  calc (Real.sqrt 2+1/100000)*(Real.sqrt 2*Real.sqrt (v.val:ℝ)) =
      (2+Real.sqrt 2/100000)*Real.sqrt (v.val:ℝ) := by linear_combination Real.sqrt (v.val:ℝ)*sq
    _ ≤ (2+2/100000)*((p:ℝ)+1) := mul_le_mul (by linarith) root (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ (T.card:ℝ) := by linarith

#print axioms prime_gap

end Green33PrimeSingerBasisGap
