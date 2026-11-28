import Green33SingerBasisCurves
import Green33OrientedDifferences
/-! Mixed differences across the parity classes of a cyclic two-basis. -/
open Finset Green33ReflectedLayers Green33SingerBlockingLayers Green33Multiplicity
open scoped Pointwise
namespace Green33ParityDifferences
variable {v:ℕ+}

/-- Ordered sum ceilings survive an injective additive map. -/
private theorem image_cap {G H:Type*} [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (D:Finset G) (f:G→+H) (inj:Function.Injective f) (C:ℕ) (cap:∀ s,reps D s≤C) (s:H) :
    reps (D.image f) s≤C := by
  classical
  let R:=((D.image f)×ˢ(D.image f)).filter fun p => p.1+p.2=s
  change R.card≤C
  by_cases empty:R=∅
  · simp [empty]
  obtain ⟨⟨x,y⟩,hit⟩:=nonempty_iff_ne_empty.mpr empty
  obtain ⟨⟨hx,hy⟩,eq⟩:=(mem_filter.trans (and_congr_left fun _ => mem_product)).mp hit
  obtain ⟨a,_,rfl⟩:=mem_image.mp hx
  obtain ⟨b,_,rfl⟩:=mem_image.mp hy
  have inc:R⊆((D×ˢD).filter fun p => p.1+p.2=a+b).image (Prod.map f f) := by
    rintro ⟨u,w⟩ h
    obtain ⟨⟨hu,hw⟩,e⟩:=(mem_filter.trans (and_congr_left fun _ => mem_product)).mp h
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hu
    obtain ⟨y,hy,rfl⟩:=mem_image.mp hw
    exact mem_image.mpr ⟨(x,y),mem_filter.mpr ⟨mem_product.mpr ⟨hx,hy⟩,
      inj (by rw [map_add,map_add];exact e.trans eq.symm)⟩,rfl⟩
  exact ((card_le_card inc).trans card_image_le).trans (cap _)

/-- The coordinates of reflected mixed differences are x and 1−x. -/
theorem parity_budget (D E B:Finset (ZMod v)) (sub:D⊆E) (C:ℕ) (cap:∀ s,reps D s≤C) :
    ((D-B).filter fun x => 1-x∈D-B).card ≤
      2*C*(((split E B).card+1).choose 2-(split E B+split E B).card) := by
  classical
  let f:=doubleHom v
  let A:=D.image f
  let L:=B.image fun b => 1+f b
  have inj:Function.Injective f:=(double_coordinates v 0).1
  have axis:f 1=1+1 := by simpa [f] using (double_coordinates v 0).2.2
  have sep:Disjoint A L := by
    apply Finset.disjoint_left.mpr
    intro x hx hl
    obtain ⟨d,_,rfl⟩:=mem_image.mp hx
    obtain ⟨b,_,e⟩:=mem_image.mp hl
    exact (double_coordinates v b).2.1 d e.symm
  have ae:A⊆split E B := fun _ hx => mem_union_left _ (image_subset_image sub hx)
  have gb:=Green33OrientedDifferences.mixed_difference_budget (split E B) A L ae
    (show L⊆split E B from subset_union_right) sep C (image_cap D f inj C cap)
  let Y:=(D-B).filter fun x => 1-x∈D-B
  have im:Y.image (fun x => f x-1) ⊆ (A-L)∩(L-A) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩:=mem_image.mp hx
    obtain ⟨h1,h2⟩:=mem_filter.mp hy
    obtain ⟨d,hd,b,hb,eq⟩:=mem_sub.mp h1
    obtain ⟨e,he,c,hc,eq'⟩:=mem_sub.mp h2
    apply mem_inter.mpr
    constructor
    · exact mem_sub.mpr ⟨f d,mem_image_of_mem _ hd,1+f b,mem_image_of_mem _ hb,by rw [←eq,map_sub];abel⟩
    · have g:=congrArg f eq'
      rw [map_sub,map_sub,axis] at g
      refine mem_sub.mpr ⟨1+f c,mem_image_of_mem _ hc,f e,mem_image_of_mem _ he,?_⟩
      apply (eq_sub_iff_add_eq).mpr
      calc
        1+f c-f e+1 = (1+1)-(f e-f c) := by abel
        _ = f y := by rw [g];abel
  have cnt:=card_le_card im
  rw [card_image_of_injective _ (fun _ _ h => inj (sub_left_injective h))] at cnt
  exact cnt.trans gb
#print axioms parity_budget

private theorem reflected_card (X:Finset (ZMod v)) :
    2*X.card≤v.val+(X.filter fun x => 1-x∈X).card := by
  let Y:=X.image (fun x => 1-x)
  have memY (x:ZMod v) : x∈Y ↔ 1-x∈X := by
    constructor
    · rintro h
      obtain ⟨y,hy,rfl⟩:=mem_image.mp h
      simpa using hy
    · intro h
      exact mem_image.mpr ⟨_,h,by simp⟩
  have I:X∩Y=X.filter (fun x => 1-x∈X) := by ext x;simp [memY]
  have h:=card_inter_add_card_union X Y
  rw [I,show Y.card=X.card from card_image_of_injective _ (fun _ _ h => sub_right_injective h)] at h
  have n: (X∪Y).card≤v.val := by simpa only [ZMod.card] using card_le_univ (X∪Y)
  omega

/-- Losing d points of a first layer costs at most d|B| mixed differences. -/
private theorem omitted_differences (D E B:Finset (ZMod v)) :
    (D-B).card≤((D∩E)-B).card+(D\E).card*B.card := by
  have h:D-B ⊆ ((D∩E)-B)∪((D\E)-B) := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_sub.mp hx
    by_cases e:a∈E
    · exact mem_union_left _ (sub_mem_sub (mem_inter.mpr ⟨ha,e⟩) hb)
    · exact mem_union_right _ (sub_mem_sub (mem_sdiff.mpr ⟨ha,e⟩) hb)
  exact ((card_le_card h).trans (card_union_le _ _)).trans (Nat.add_le_add_left card_sub_le _)

/-- A first layer with bounded sum multiplicity cannot have dense mixed
differences with the opposite layer without paying unordered-pair excess. -/
theorem support_budget (D E B:Finset (ZMod v)) (C:ℕ) (cap:∀ s,reps D s≤C) :
    2*(D-B).card≤v.val+2*C*(((split E B).card+1).choose 2-(split E B+split E B).card)+2*(D\E).card*B.card := by
  have cap' (s) : reps (D∩E) s≤C := by
    apply le_trans _ (cap s)
    apply card_le_card
    apply filter_subset_filter
    exact product_subset_product inter_subset_left inter_subset_left
  have h:=parity_budget (D∩E) E B inter_subset_right C cap'
  have k:=reflected_card ((D∩E)-B)
  have m:=omitted_differences D E B
  rw [mul_assoc 2 (D\E).card B.card]
  omega
#print axioms support_budget

open Green33PerfectDifferenceCenters

/-- The line indexed by x consists of the labels d−x with d in D. -/
def lines (D B:Finset (ZMod v)) (x:ZMod v) := occupancy D (-B) x

private theorem line_pos (D B:Finset (ZMod v)) (x:ZMod v) : 0<lines D B x ↔ x∈D-B := by
  simpa only [lines,sub_eq_add_neg] using occupancy_pos D (-B) x

private theorem moments (D B:Finset (ZMod v)) (perf:Perfect D) :
    (∑ x,(lines D B x:ℝ))=D.card*(B.card:ℝ) ∧
    (∑ x,(lines D B x:ℝ)^2)=((D.card:ℝ)-1)*B.card+(B.card:ℝ)^2 := by
  classical
  let w (y:ZMod v):ℝ:=if y∈-B then 1 else 0
  have sm : ∑ x,w x=(B.card:ℝ) := by
    have ind (U:Finset (ZMod v)) : (∑ x,if x∈U then (1:ℝ) else 0)=U.card := by simp
    exact (ind (-B)).trans (by simp only [card_neg])
  have idm x : w x*w x=w x := by dsimp only [w];split <;> norm_num
  have sum (x:ZMod v) : ∑ d∈D,w (x-d)=(lines D B x:ℝ) := by simp [lines,occupancy,w]
  constructor
  · simp_rw [←sum, sum_comm (s:=univ) (t:=D)]
    have tr (d:ZMod v) : ∑ x,w (x-d)=B.card := (Equiv.sum_comp (Equiv.subRight d) w).trans sm
    simp only [tr,sum_const,nsmul_eq_mul]
  · have h:=translate_inner D perf w w
    simpa only [sum,idm,sm,←pow_two] using h

/-- The error from two at represented differences; zero differences counts
outside the support incur no error. -/
noncomputable def lineError (D B:Finset (ZMod v)) : ℝ :=
  ∑ x∈D-B,((lines D B x:ℝ)-2)^2

private theorem error_exact (D B:Finset (ZMod v)) (perf:Perfect D) :
    lineError D B=((D.card:ℝ)-1)*B.card+(B.card:ℝ)^2-4*(D.card*B.card)+4*((D-B).card:ℝ) := by
  classical
  let X:=D-B
  have outside x (hx:x∉X) : lines D B x=0 := Nat.eq_zero_of_not_pos fun h => hx ((line_pos D B x).mp h)
  obtain ⟨h1,h2⟩:=moments D B perf
  have lin:(∑ x∈X,(lines D B x:ℝ))=D.card*(B.card:ℝ) := by
    rw [←h1]
    exact sum_subset (subset_univ _) (fun x _ hx => by rw [outside x hx,Nat.cast_zero])
  have sq:(∑ x∈X,(lines D B x:ℝ)^2)=((D.card:ℝ)-1)*B.card+(B.card:ℝ)^2 := by
    rw [←h2]
    exact sum_subset (subset_univ _) (fun x _ hx => by rw [outside x hx];norm_num)
  change (∑ x∈X,_) = _
  simp_rw [show ∀ y:ℝ,(y-2)^2=y^2-4*y+4 by intro y;ring]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum,sq,lin,sum_const]
  simp only [X,nsmul_eq_mul]
  ring

/-- An actual perfect difference set has at most two ordered pairs at a sum. -/
theorem perfect_sum_cap (D:Finset (ZMod v)) (perf:Perfect D) (s:ZMod v) : reps D s≤2 := by
  classical
  let R:=(D×ˢD).filter fun p => p.1+p.2=s
  change R.card≤2
  by_cases empty:R=∅
  · simp [empty]
  obtain ⟨⟨a,b⟩,h⟩:=nonempty_iff_ne_empty.mpr empty
  obtain ⟨⟨ha,hb⟩,eq⟩:=(mem_filter.trans (and_congr_left fun _ => mem_product)).mp h
  apply (card_le_card (t:={(a,b),(b,a)}) ?_).trans card_le_two
  rintro ⟨x,y⟩ h
  obtain ⟨⟨hx,hy⟩,e⟩:=(mem_filter.trans (and_congr_left fun _ => mem_product)).mp h
  rcases perf.sidon x hx a ha y hy b hb (e.trans eq.symm) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

#print axioms perfect_sum_cap

/-- Finite mean-square cost of exceptions to the zero-or-two line law
opposite a retained perfect difference set. -/
theorem line_budget (D E B:Finset (ZMod v)) (perf:Perfect D) (q:ℕ) (size:D.card=q+1) :
    let T:=split E B
    lineError D B≤(B.card:ℝ)^2-(3*q+4)*B.card+2*v.val+
      8*(((T.card+1).choose 2:ℕ)-(T+T).card:ℕ)+4*((D\E).card:ℝ)*B.card := by
  let T:=split E B
  have h:=support_budget D E B 2 (perfect_sum_cap D perf)
  have h':(2:ℝ)*(D-B).card≤v.val+2*2*((((T.card+1).choose 2-(T+T).card:ℕ):ℝ))+2*((D\E).card:ℝ)*B.card := by exact_mod_cast h
  rw [error_exact D B perf,size,Nat.cast_add_one]
  dsimp only
  nlinarith only [h']
#print axioms line_budget

open Filter
open scoped Topology

/-- If a critical full cyclic two-basis retains a perfect difference set
up to o(q) even labels, the opposite support meets almost every translated
line in zero or two points, with vanishing mean squared error on hit lines. -/
theorem perfect_line_profile (v:ℕ→ℕ+) (D E B:∀ i,Finset (ZMod (v i))) (q:ℕ→ℕ)
    (perf:∀ i,Perfect (D i)) (size:∀ i,(D i).card=q i+1) (pos:∀ i,0<q i)
    (grow:Tendsto q atTop atTop) (full:∀ i,split (E i) (B i)+split (E i) (B i)=univ)
    (crit:Tendsto (fun i => ((split (E i) (B i)).card:ℝ)/Real.sqrt ((2*(v i).val:ℕ):ℝ)) atTop (𝓝 (Real.sqrt 2)))
    (missing:Tendsto (fun i => (((D i)\(E i)).card:ℝ)/(q i:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun i => lineError (D i) (B i)/(v i:ℝ)) atTop (𝓝 0) := by
  let T i:=split (E i) (B i)
  let P i:=((T i).card+1).choose 2-((T i)+(T i)).card
  have qp i : (0:ℝ)<q i:=by exact_mod_cast pos i
  have vp i : (0:ℝ)<(v i).val:=by exact_mod_cast (v i).pos
  obtain ⟨evenL,oddL⟩:=Green33SingerBasisCurves.parity_balance D E B q perf size pos grow full crit
  have total:Tendsto (fun i => ((T i).card:ℝ)/(q i:ℝ)) atTop (𝓝 2) := by
    have h:=evenL.add oddL
    norm_num at h
    simpa only [T,split_card,Nat.cast_add,add_div] using h
  have ratio i : ((v i).val:ℝ)=(q i:ℝ)^2+q i+1 := by
    have h:=parameters _ (perf i)
    rw [size,ZMod.card,Nat.cast_add_one] at h
    linarith only [h]
  have tiny:= (tendsto_const_nhds (x:=(1:ℝ))).div_atTop ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have ord:Tendsto (fun i => ((v i).val:ℝ)/(q i:ℝ)^2) atTop (𝓝 1) := by
    have h:=((tendsto_const_nhds (f:=atTop) (x:=(1:ℝ))).add tiny).add (tiny.pow 2)
    norm_num at h
    apply h.congr
    intro i
    rw [ratio];field_simp [(qp i).ne']
  have pl:Tendsto (fun i => (P i:ℝ)/(q i:ℝ)^2) atTop (𝓝 0) := by
    have h:=(((total.pow 2).add (total.mul tiny)).div_const 2).sub (ord.const_mul 2)
    norm_num at h
    apply h.congr
    intro i
    have side:((T i)+(T i)).card≤((T i).card+1).choose 2 := by
      have h:=Green33SidonLayerRepairs.sum_upper (T i)
      rw [Nat.choose_two_right,Nat.add_sub_cancel]
      nlinarith only [h,Nat.mod_lt (((T i).card+1)*(T i).card) (by decide : 0<2),Nat.mod_add_div (((T i).card+1)*(T i).card) 2]
    rw [show (P i:ℝ)=((((T i).card+1).choose 2:ℕ):ℝ)-(((T i)+(T i)).card:ℝ) from Nat.cast_sub side,
      Nat.cast_choose_two,Nat.cast_add_one,full,card_univ,ZMod.card,Nat.cast_mul,Nat.cast_ofNat]
    field_simp [(qp i).ne']
    ring
  let U i:=(((B i).card:ℝ)/(q i:ℝ))^2-(3+4*(1/(q i:ℝ)))*((B i).card/(q i:ℝ))+
    2*((v i).val/(q i:ℝ)^2)+8*((P i:ℝ)/(q i:ℝ)^2)+4*((((D i)\(E i)).card:ℝ)/(q i:ℝ))*((B i).card/(q i:ℝ))
  have ulim:Tendsto U atTop (𝓝 0) := by
    have h:=((((oddL.pow 2).sub (((tiny.const_mul 4).const_add 3).mul oddL)).add
      (ord.const_mul 2)).add (pl.const_mul 8)).add ((missing.const_mul 4).mul oddL)
    norm_num at h
    simpa only [U,one_div] using h
  have z:Tendsto (fun i => lineError (D i) (B i)/(q i:ℝ)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)) _ ulim
    apply Eventually.of_forall
    intro i
    apply (div_le_iff₀ (sq_pos_of_pos (qp i))).mpr
    apply (line_budget (D i) (E i) (B i) (perf i) (q i) (size i)).trans
    change _≤U i*(q i:ℝ)^2
    dsimp only [U,P,T]
    field_simp [(qp i).ne']
    ring_nf
    exact le_rfl
  have h:=z.div ord (by norm_num)
  rw [zero_div] at h
  exact h.congr fun i => div_div_div_cancel_right₀ (pow_ne_zero 2 (qp i).ne') _ _
#print axioms perfect_line_profile

end Green33ParityDifferences
