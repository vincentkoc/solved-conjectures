import Green33SingerBlockingLayers
/-! Concentration of an arbitrary opposite Singer layer on curves and lines. -/
open Finset Green33PerfectDifferenceCenters Green33SingerBlockingLayers Green33ReflectedLayers
open scoped Pointwise
namespace Green33SingerCurveEscape

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Bounded line intersections inside a subset spend collisions of the entire layer. -/
theorem arc_budget (D B C : Finset G) (perfect : Perfect D) {q d : ℕ}
    (size : D.card=q+1) (budget : B.card≤q+1) (sub : C⊆B) (cap : ∀ x,occupancy D C x≤d) :
    (C.card:ℝ)*(C.card-1)≤d*((q:ℝ)+((D+B)ᶜ.card:ℝ)) := by
  have add : D+B⊆(D+C)∪(D+(B\C)) := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hx
    by_cases h:b∈C
    · exact mem_union_left _ (add_mem_add ha h)
    · exact mem_union_right _ (add_mem_add ha (mem_sdiff.mpr ⟨hb,h⟩))
  have step:=((card_le_card add).trans (card_union_le _ _)).trans
    (Nat.add_le_add_left (card_add_le : (D+(B\C)).card≤_) _)
  have num:=card_sdiff_add_card_eq_card sub
  have loss : ((D+B).card:ℝ)≤(D+C).card+D.card*((B\C).card:ℝ) := by exact_mod_cast step
  have count : ((B\C).card:ℝ)+C.card=B.card := by exact_mod_cast num
  have lim : (B.card:ℝ)≤q+1 := by exact_mod_cast budget
  have k : (D.card:ℝ)=q+1 := by exact_mod_cast size
  have group:=parameters D perfect
  have total : ((D+B).card:ℝ)+((D+B)ᶜ.card:ℝ)=Fintype.card G := by exact_mod_cast card_add_card_compl (D+B)
  have bd : (D.card:ℝ)*C.card-(D+C).card≤(q:ℝ)+((D+B)ᶜ.card:ℝ) := by
    have u:=mul_le_mul_of_nonneg_left lim (show 0≤(D.card:ℝ) from Nat.cast_nonneg _)
    rw [←count] at u
    rw [k] at group u loss ⊢
    nlinarith only [group,u,loss,total]
  exact (collision_bound D C perfect size cap).trans (mul_le_mul_of_nonneg_left bd (Nat.cast_nonneg _))

#print axioms arc_budget

/-- The deficit of a reflected seed pays for the maximum number of collinear
points in an arbitrary opposite layer, once the mixed layer is almost full. -/
theorem line_budget {v : ℕ+} (D B : Finset (ZMod v)) (perfect : Perfect D) {q : ℕ}
    (size : D.card=q+1) (budget : B.card≤q+1) (c : ZMod v) :
    let m:=(occupancy D B c:ℝ)
    let k:=(q:ℝ)+1
    let R:=split D B
    let H:=((R+R)ᶜ.card:ℝ)
    let S:=doubled D c
    let E:=((S+S)ᶜ.card:ℝ)
    (E-H)*(m-1)≤2*k*H ∨ m≤1 := by
  let m:=occupancy D B c
  let R:=split D B
  let S:=doubled D c
  let H:ℝ:=(R+R)ᶜ.card
  let E:ℝ:=(S+S)ᶜ.card
  change (E-H)*((m:ℝ)-1)≤2*((q:ℝ)+1)*H ∨ (m:ℝ)≤1
  by_cases tiny:m≤1
  · exact Or.inr (by exact_mod_cast tiny)
  left
  have nz : 0<m := by omega
  have sec:=secant_bound D B perfect size ((occupancy_pos D B c).mp nz)
  have md : m≤D.card := card_filter_le _ _
  have mb : m≤B.card := by
    have inj : Set.InjOn (c-·) (↑(D.filter fun x => c-x∈B) : Set (ZMod v)) :=
      fun _ _ _ _ eq => sub_right_inj.mp eq
    have sub : (D.filter fun x => c-x∈B).image (c-·)⊆B := by
      intro z hz;obtain ⟨a,ha,rfl⟩:=mem_image.mp hz;exact (mem_filter.mp ha).2
    have s:=card_le_card sub
    rwa [card_image_of_injOn inj] at s
  change (D.card-m)*(m+q)≤(D.card-m)*B.card+(D+B)ᶜ.card at sec
  have real_sec : ((D.card:ℝ)-m)*(m+q)≤((D.card:ℝ)-m)*B.card+((D+B)ᶜ.card:ℝ) := by
    exact_mod_cast sec
  have u : (D.card:ℝ)=q+1 := by exact_mod_cast size
  have b : (B.card:ℝ)≤q+1 := by exact_mod_cast budget
  have mn : (m:ℝ)≤D.card := by exact_mod_cast md
  have m1 : (1:ℝ)≤m := by exact_mod_cast nz
  have om : ((D+B)ᶜ.card:ℝ)≤H := by dsimp only [H,R]; exact_mod_cast odd_holes D B
  have s1 : ((q:ℝ)+1-m)*(m-1)≤H := by
    have s2:=mul_le_mul_of_nonneg_left b (sub_nonneg.mpr mn)
    rw [u] at real_sec s2
    nlinarith only [s2,real_sec,om]
  have changes:=changed_sums R S
  have outside:=outside_reflection D B c
  have out : ((R\S).card:ℝ)≤(B.card:ℝ)-m := by exact_mod_cast outside
  have sc : (R.card:ℝ)≤2*((q:ℝ)+1) := by
    change ((split D B).card:ℝ)≤_
    rw [split_card,Nat.cast_add,u];linarith
  have total : E≤H+(R\S).card*(R.card:ℝ) := by dsimp only [E,H];exact_mod_cast changes
  have bound:=mul_le_mul (out.trans (sub_le_sub_right b _)) sc (Nat.cast_nonneg _) (by linarith only [mn,u])
  have step : E-H≤2*((q:ℝ)+1)*((q:ℝ)+1-m) := by linarith only [total,bound]
  have left:=mul_le_mul_of_nonneg_right step (sub_nonneg.mpr m1)
  have right:=mul_le_mul_of_nonneg_left s1 (show 0≤2*((q:ℝ)+1) by positivity)
  nlinarith only [left,right]

#print axioms line_budget

/-- A certificate for a subset of the odd layer: all but the residual subset
lie on the listed reflected Singer lines. -/
structure LineCover (D V : Finset G) (d : ℕ) where
  residual : Finset G
  inside : residual⊆V
  lines : Finset G
  caps : ∀ x,occupancy D residual x≤d
  cover : ∀ b∈V,b∈residual ∨ ∃ c∈lines,c-b∈D

omit [Fintype G] in
theorem occ_flip (D B : Finset G) (c : G) :
    (B.filter (fun b => c-b∈D)).card=occupancy D B c := by
  apply card_nbij' (c-·) (c-·)
  · intro b hb
    obtain ⟨hB,hD⟩:=mem_filter.mp hb
    exact mem_filter.mpr ⟨hD,by simpa using hB⟩
  · intro d hd
    obtain ⟨hD,hB⟩:=mem_filter.mp hd
    exact mem_filter.mpr ⟨hB,by simpa using hD⟩
  · intro x _;simp
  · intro x _;simp

#print axioms occ_flip

/-- Simultaneous finite escape bound. Each exceptional line is charged by its
actual occupancy, and all remaining curve points share a single collision budget. -/
theorem cover_bound {v : ℕ+} (D B V : Finset (ZMod v)) (perf : Perfect D) {q d : ℕ}
    (size : D.card=q+1) (budget : B.card≤q+1) (sub : V⊆B) (C : LineCover D V d)
    (E : ℝ) (few : ∀ c∈C.lines,E≤(((doubled D c+doubled D c)ᶜ.card):ℝ))
    (sep : ((split D B+split D B)ᶜ.card:ℝ)<E) :
    let H:ℝ:=(split D B+split D B)ᶜ.card
    (V.card:ℝ)≤1+Real.sqrt (d*((q:ℝ)+H))+C.lines.card*(1+2*(q+1)*H/(E-H)) := by
  classical
  let H:ℝ:=(split D B+split D B)ᶜ.card
  change (V.card:ℝ)≤1+Real.sqrt (d*((q:ℝ)+H))+C.lines.card*(1+2*(q+1)*H/(E-H))
  have hpos : 0≤H := Nat.cast_nonneg _
  have den : 0<E-H := sub_pos.mpr sep
  have arc:=arc_budget D B C.residual perf size budget (C.inside.trans sub) C.caps
  have odd : (((D+B)ᶜ.card):ℝ)≤H := by dsimp only [H];exact_mod_cast odd_holes D B
  have arc' :=arc.trans (mul_le_mul_of_nonneg_left (add_le_add_right odd q) (Nat.cast_nonneg d))
  have rv : (C.residual.card:ℝ)≤1+Real.sqrt (d*((q:ℝ)+H)) := by
    let u:ℝ:=C.residual.card
    have root:=Real.sq_sqrt (show 0≤(d:ℝ)*(q+H) by positivity)
    have rn:=Real.sqrt_nonneg ((d:ℝ)*(q+H))
    change u*(u-1)≤_ at arc'
    change u≤_
    by_contra! lo
    have m:=mul_pos (show 0<u-1-Real.sqrt (d*((q:ℝ)+H)) by linarith)
      (show 0<u-1+Real.sqrt (d*((q:ℝ)+H)) by linarith)
    nlinarith only [root,m,arc',lo,rn]
  let peak:=1+2*((q:ℝ)+1)*H/(E-H)
  have ge : 1≤peak := by dsimp [peak]; exact le_add_of_nonneg_right (by positivity)
  have cap (c) (hc:c∈C.lines) : (occupancy D B c:ℝ)≤peak := by
    rcases line_budget D B perf size budget c with bound|one
    · by_cases one:(occupancy D B c:ℝ)≤1
      · exact one.trans ge
      · have mpos:0≤(occupancy D B c:ℝ)-1 := by linarith
        have cost:=(mul_le_mul_of_nonneg_right (sub_le_sub_right (few c hc) H) mpos).trans bound
        have ratio:=(le_div_iff₀ den).mpr ((mul_comm ..).trans_le cost)
        dsimp only [peak];linarith
    · exact one.trans ge
  let pts (c : ZMod v) := B.filter fun b => c-b∈D
  have inc : V⊆C.residual∪C.lines.biUnion pts := by
    intro b hb;rcases C.cover b hb with r|⟨c,hc,hit⟩
    · exact mem_union_left _ r
    · exact mem_union_right _ (mem_biUnion.mpr ⟨c,hc,mem_filter.mpr ⟨sub hb,hit⟩⟩)
  have total:=((card_le_card inc).trans (card_union_le _ _)).trans
    (Nat.add_le_add_left (card_biUnion_le (s:=C.lines) (t:=pts)) _)
  have total' : (V.card:ℝ)≤C.residual.card+∑ c∈C.lines,((pts c).card:ℝ) := by exact_mod_cast total
  have peakSum : (∑ c∈C.lines,((pts c).card:ℝ))≤(C.lines.card:ℝ)*peak := by
    calc _ ≤ ∑ _c∈C.lines,peak := sum_le_sum (fun c hc => by simpa only [pts,occ_flip] using cap c hc)
         _ = _ := by simp
  exact total'.trans (add_le_add rv peakSum)

#print axioms cover_bound

private theorem scale_bound (v q h r n d : ℝ) (one : 1≤q) (hh : 0≤h)
    (cut : h≤q^2/16) (cn : 0≤n) (dr : r≤d) (dn : n≤d)
    (bound : v≤1+Real.sqrt (r*(q+h))+n*(1+2*(q+1)*h/(q^2/8-h))) :
    v/q≤1/q+Real.sqrt (d/q+d*h/q^2)+d/q+64*d*h/q^2 := by
  have qp:0<q:=by linarith
  have sq:=sq_pos_of_pos qp
  have num : 0≤2*(q+1)*h := by positivity
  have den : 0<q^2/8-h := by linarith only [cut,sq]
  have half : q^2/16≤q^2/8-h := by linarith
  have frac : 2*(q+1)*h/(q^2/8-h)≤64*h/q := by
    calc _ ≤ 2*(q+1)*h/(q^2/16) := div_le_div_of_nonneg_left num (by positivity) half
         _ ≤ 64*h/q := by
           rw [div_le_div_iff₀ (by positivity) qp]
           have pr:=mul_nonneg (sub_nonneg.mpr one) (mul_nonneg hh qp.le)
           nlinarith only [pr]
  have term:=mul_le_mul dn (add_le_add_right frac 1) (by positivity) (cn.trans dn)
  have root:=Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right dr (by positivity : 0≤q+h))
  have total:=bound.trans (add_le_add (add_le_add_right root 1) term)
  have d0:=cn.trans dn
  have amt : 0≤d*(q+h) := by positivity
  have rad : Real.sqrt (d*(q+h))/q=Real.sqrt (d/q+d*h/q^2) := by
    rw [show d/q+d*h/q^2=(d*(q+h))/q^2 by field_simp,Real.sqrt_div amt,Real.sqrt_sq qp.le]
  calc v/q ≤ (1+Real.sqrt (d*(q+h))+d*(1+64*h/q))/q :=
         (div_le_div_iff_of_pos_right qp).mpr total
       _ = 1/q+Real.sqrt (d*(q+h))/q+d/q+64*d*h/q^2 := by field_simp;ring
       _ = _ := by rw [rad]

/-- The occupied proportion of a curve is controlled by its line and residual
budgets, the doubled holes, and the deficit on every reflected axis. -/
theorem relative_bound {v : ℕ+} (D B V : Finset (ZMod v)) (perf : Perfect D) {q d w : ℕ}
    (pos : 0<q) (size : D.card=q+1) (budget : B.card≤q+1) (sub : V⊆B) (C : LineCover D V d)
    (deg : d≤w) (lines : C.lines.card≤w)
    (few : ∀ c∈C.lines,(q:ℝ)^2/8≤(((doubled D c+doubled D c)ᶜ.card):ℝ))
    (cut : ((split D B+split D B)ᶜ.card:ℝ)≤(q:ℝ)^2/16) :
    let H:=((split D B+split D B)ᶜ.card:ℝ)
    (V.card:ℝ)/q≤1/q+Real.sqrt (w/q+w*H/q^2)+w/q+64*w*H/q^2 := by
  have qp : (0:ℝ)<q := by exact_mod_cast pos
  have small : ((split D B+split D B)ᶜ.card:ℝ)<(q:ℝ)^2/8 := by nlinarith only [sq_pos_of_pos qp,cut]
  have main:=cover_bound D B V perf size budget sub C _ few small
  exact scale_bound _ _ _ _ _ _ (by exact_mod_cast pos) (Nat.cast_nonneg _) cut
    (Nat.cast_nonneg _) (by exact_mod_cast deg) (by exact_mod_cast lines) main

#print axioms relative_bound

open Filter
open scoped Topology

theorem reflected_floor {v : ℕ→ℕ+} (D : ∀ i,Finset (ZMod (v i))) (perfect : ∀ i,Perfect (D i))
    (q : ℕ→ℕ) (size : ∀ i,(D i).card=q i+1)
    (reflects : ∀ a : ∀ i,ZMod (v i),Tendsto (fun i =>
      ((doubled (D i) (a i)+doubled (D i) (a i)).card:ℝ)/(2*(v i).val)) atTop (𝓝 (7/8))) :
    ∀ᶠ i in atTop,∀ c:ZMod (v i),(q i:ℝ)^2/8≤((doubled (D i) c+doubled (D i) c)ᶜ.card:ℝ) := by
  classical
  let count (i : ℕ) (c : ZMod (v i)) := (doubled (D i) c+doubled (D i) c)ᶜ.card
  choose a ha low using fun i => exists_min_image (univ : Finset (ZMod (v i))) (count i) univ_nonempty
  have small:=(reflects a).eventually_lt_const (show (7/8:ℝ)<15/16 by norm_num)
  filter_upwards [small] with i hi c
  have den : 0<2*((v i).val:ℝ) := by positivity
  have num:=(div_lt_iff₀ den).mp hi
  have par:=parameters (D i) (perfect i)
  rw [size i,Nat.cast_add,Nat.cast_one,ZMod.card] at par
  let S:=doubled (D i) (a i)+doubled (D i) (a i)
  have total : (S.card:ℝ)+(count i (a i):ℝ)=2*(v i).val := by
    have h:=card_add_card_compl S
    rw [ZMod.card] at h
    exact_mod_cast h
  change (S.card:ℝ)<_ at num
  have m : (count i (a i):ℝ)≤count i c := by exact_mod_cast low i c (mem_univ c)
  change (q i:ℝ)^2/8≤(count i c:ℝ)
  nlinarith only [par,num,total,m,Nat.cast_nonneg (α:=ℝ) (q i)]

#print axioms reflected_floor

theorem cover_escape {v : ℕ→ℕ+} (D B V : ∀ i,Finset (ZMod (v i))) (q d w : ℕ→ℕ)
    (perf : ∀ i,Perfect (D i)) (pos : ∀ i,0<q i) (size : ∀ i,(D i).card=q i+1)
    (budget : ∀ i,(B i).card≤q i+1) (sub : ∀ i,V i⊆B i)
    (C : ∀ i,LineCover (D i) (V i) (d i)) (deg : ∀ i,d i≤w i) (lines : ∀ i,(C i).lines.card≤w i)
    (wpos : ∀ i,0<w i) (grow : Tendsto q atTop atTop)
    (low : Tendsto (fun i => (w i:ℝ)/(q i:ℝ)) atTop (𝓝 0))
    (loss : Tendsto (fun i => (w i:ℝ)*((split (D i) (B i)+split (D i) (B i))ᶜ.card:ℝ)/(q i:ℝ)^2) atTop (𝓝 0))
    (reflects : ∀ a : ∀ i,ZMod (v i),Tendsto (fun i =>
      ((doubled (D i) (a i)+doubled (D i) (a i)).card:ℝ)/(2*(v i).val)) atTop (𝓝 (7/8))) :
    Tendsto (fun i => ((V i).card:ℝ)/(q i:ℝ)) atTop (𝓝 0) := by
  let H (i : ℕ) : ℝ := (split (D i) (B i)+split (D i) (B i))ᶜ.card
  have rt:=((tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_natCast_atTop_atTop.comp grow))
  have ub:=((rt.add (low.add loss).sqrt).add low).add (loss.const_mul 64)
  simp only [add_zero,Real.sqrt_zero,mul_zero] at ub
  apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ ub
  filter_upwards [loss.eventually_lt_const (show (0:ℝ)<1/16 by norm_num),reflected_floor D perf q size reflects] with i tiny all
  have qp : (0:ℝ)<q i := by exact_mod_cast pos i
  have up : (1:ℝ)≤w i := by exact_mod_cast wpos i
  have hn : 0≤H i := Nat.cast_nonneg _
  change (w i:ℝ)*H i/(q i:ℝ)^2<1/16 at tiny
  have t:=(div_lt_iff₀ (sq_pos_of_pos qp)).mp tiny
  have h0:=mul_le_mul_of_nonneg_right up hn
  have cut : H i≤(q i:ℝ)^2/16 := by linarith
  have h:=relative_bound (D i) (B i) (V i) (perf i) (pos i) (size i) (budget i) (sub i) (C i)
    (deg i) (lines i) (fun c _ => all c) cut
  change _≤1/(q i:ℝ)+Real.sqrt ((w i:ℝ)/q i+(w i:ℝ)*H i/(q i)^2)+(w i:ℝ)/q i+64*((w i:ℝ)*H i/(q i)^2)
  convert h using 1; ring

#print axioms cover_escape

/-- Translate doubled sumset density into holes per square plane order. -/
theorem small_deficit {v : ℕ→ℕ+} (D B : ∀ i,Finset (ZMod (v i))) (q : ℕ→ℕ)
    (perf : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=q i+1) (pos : ∀ i,0<q i)
    (grow : Tendsto q atTop atTop)
    (dense : Tendsto (fun i => ((split (D i) (B i)+split (D i) (B i)).card:ℝ)/(2*(v i).val))
      atTop (𝓝 1)) :
    Tendsto (fun i => ((split (D i) (B i)+split (D i) (B i))ᶜ.card:ℝ)/(q i:ℝ)^2)
      atTop (𝓝 0) := by
  have top : Tendsto (fun i => (q i:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp grow
  have small : Tendsto (fun i => 1/(q i:ℝ)) atTop (𝓝 0):=tendsto_const_nhds.div_atTop top
  have qpos (i) : (0:ℝ)<q i := by exact_mod_cast pos i
  have ord (i) : ((v i).val:ℝ)=(q i:ℝ)^2+q i+1 := by
    have e:=parameters (D i) (perf i);rw [size i,Nat.cast_add,Nat.cast_one,ZMod.card] at e;nlinarith only [e]
  have scale : Tendsto (fun i => 2*((v i).val:ℝ)/(q i:ℝ)^2) atTop (𝓝 2) := by
    have one:=tendsto_const_nhds (f:=atTop (α:=ℕ)) (x:=(1:ℝ))
    have h:=((one.add small).add (small.pow 2)).const_mul 2
    simp only [add_zero,zero_pow (by decide : 2≠0),mul_one] at h
    apply h.congr;intro i
    rw [ord];field_simp [(qpos i).ne']
  have miss:=((tendsto_const_nhds (x:=(1:ℝ))).sub dense).mul scale
  rw [sub_self,zero_mul] at miss
  apply miss.congr
  intro i
  let R:=split (D i) (B i)+split (D i) (B i)
  have eq:=(card_add_card_compl R)
  rw [ZMod.card] at eq
  have total : (R.card:ℝ)+(Rᶜ.card:ℝ)=2*(v i).val := by exact_mod_cast eq
  have vp : (((v i).val):ℝ)≠0 := by exact_mod_cast (v i).property.ne'
  change (1-(R.card:ℝ)/(2*(v i).val))*(2*(v i).val/(q i:ℝ)^2)=(Rᶜ.card:ℝ)/(q i:ℝ)^2
  field_simp [vp,(qpos i).ne']
  linarith

#print axioms small_deficit
end Green33SingerCurveEscape
