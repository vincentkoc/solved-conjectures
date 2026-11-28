import Mathlib
import Green33FactorDensity
/-! Four-root counting for the square of a projective subline. -/
open Finset
open scoped Pointwise BigOperators
namespace Green33BaerQuadratic
variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- Every ordinary sum of four roots is indexed by a multiset of size four,
including all repeated roots. -/
theorem four_root_budget (X : Finset G) :
    ((X+X)+(X+X)).card≤(X.card+3).choose 4 := by
  classical
  let ev (p : Sym (↥X) 4):=((p:Multiset (↥X)).map (fun x => x.val)).sum
  have sub : (X+X)+(X+X)⊆univ.image ev := by
    intro x hx
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hx
    obtain ⟨i,hi,j,hj,rfl⟩:=mem_add.mp ha
    obtain ⟨k,hk,l,hl,rfl⟩:=mem_add.mp hb
    let p : Sym (↥X) 4 := ⟨([⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩,⟨l,hl⟩] : List (↥X)),by simp⟩
    refine mem_image.mpr ⟨p,mem_univ _,?_⟩
    simp [ev,p,add_assoc]
  have h:=(card_le_card sub).trans card_image_le
  rw [card_univ,Sym.card_sym_eq_multichoose,Fintype.card_coe,Nat.multichoose_eq] at h
  simpa only [show X.card+4-1=X.card+3 by omega] using h
#print axioms four_root_budget

private def valPair : Sym2 G→G := Sym2.lift ⟨(·+·),add_comm⟩

/-- Repeated unordered pairs in retained labels are also charged to the ambient set. -/
theorem retained_pair_budget (T H : Finset G) (sub : H⊆T) :
    (T+T).card+(H.card+1).choose 2≤(T.card+1).choose 2+(H+H).card := by
  classical
  let R:=T.sym2\H.sym2
  have inc : T+T⊆(R.image valPair)∪(H+H) := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩:=mem_add.mp hz
    by_cases h:Sym2.mk x y∈H.sym2
    · exact mem_union_right _ (add_mem_add (mk_mem_sym2_iff.mp h).1 (mk_mem_sym2_iff.mp h).2)
    · exact mem_union_left _ (mem_image.mpr ⟨Sym2.mk x y,mem_sdiff.mpr ⟨mk_mem_sym2_iff.mpr ⟨hx,hy⟩,h⟩,rfl⟩)
  have pairs : H.sym2⊆T.sym2 := by rintro ⟨x,y⟩ h;exact mk_mem_sym2_iff.mpr ⟨sub (mk_mem_sym2_iff.mp h).1,sub (mk_mem_sym2_iff.mp h).2⟩
  have sz : R.card+H.sym2.card=T.sym2.card := card_sdiff_add_card_eq_card pairs
  rw [card_sym2,card_sym2] at sz
  have count:=((card_le_card inc).trans (card_union_le _ _)).trans (Nat.add_le_add_right card_image_le _)
  omega

/-- Finite cyclic completion bound, also valid with missing old labels.
H can be any retained collection of pairwise root products on one translate. -/
theorem quadratic_seed_budget (T H X : Finset G) (s : G) (inc : H⊆T)
    (root : H⊆(X+X).image (s+·)) :
    (T+T).card+(H.card+1).choose 2≤(T.card+1).choose 2+(X.card+3).choose 4 := by
  have sub : H+H⊆((X+X)+(X+X)).image (s+s+·) := by
    intro z hz
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hz
    obtain ⟨u,hu,rfl⟩:=mem_image.mp (root ha)
    obtain ⟨v,hv,rfl⟩:=mem_image.mp (root hb)
    exact mem_image.mpr ⟨u+v,add_mem_add hu hv,by ac_rfl⟩
  have b:=((card_le_card sub).trans card_image_le).trans (four_root_budget X)
  exact (retained_pair_budget T H inc).trans (Nat.add_le_add_left b _)

#print axioms retained_pair_budget
#print axioms quadratic_seed_budget

end Green33BaerQuadratic

/-! A normalized four-root obstruction in the cyclic double of a square-order plane. -/
open Filter
open scoped Topology
namespace Green33BaerQuadraticLimit

private theorem finite_bound (n k h t:ℕ)
    (cap:n+(h+1).choose 2≤(k+1).choose 2+(t+3).choose 4) :
    2*(n:ℝ)+(h:ℝ)^2-(t+3:ℝ)^4/12≤((k:ℝ)+1)^2 := by
  have four:=Nat.descFactorial_le_pow (t+3) 4
  rw [Nat.descFactorial_eq_factorial_mul_choose] at four
  norm_num [Nat.factorial] at four
  have hh : (n:ℝ)+((h+1).choose 2:ℕ)≤((k+1).choose 2:ℕ)+(((t+3).choose 4:ℕ):ℝ) := by exact_mod_cast cap
  have ff : (24:ℝ)*(((t+3).choose 4:ℕ):ℝ)≤((t:ℝ)+3)^4 := by exact_mod_cast four
  rw [Nat.cast_choose_two,Nat.cast_choose_two,Nat.cast_add_one,Nat.cast_add_one] at hh
  nlinarith only [hh,ff,Nat.cast_nonneg (α:=ℝ) k,Nat.cast_nonneg (α:=ℝ) h]

/-- Retaining asymptotically half of t² split root products yields the
normalized lower size coefficient sqrt(25/12). -/
theorem floor_limit {ι : Type*} {l : Filter ι} (t k h:ι→ℕ) (n:ι→ℕ+) (pos:∀ i,0<t i)
    (order:∀ i,(n i).val=2*((t i)^4+(t i)^2+1))
    (grow:Tendsto t l atTop) (kept:Tendsto (fun i => ((h i):ℝ)/(t i:ℝ)^2) l (𝓝 (1/2)))
    (cap:∀ i,(n i).val+(h i+1).choose 2≤(k i+1).choose 2+(t i+3).choose 4)
    {v:ℝ} (below:v<Real.sqrt (25/12)) :
    ∀ᶠ i in l,v<(k i:ℝ)/Real.sqrt (n i) := by
  have tp i : (0:ℝ)<t i := by exact_mod_cast pos i
  have np i : (0:ℝ)<(n i).val := by exact_mod_cast (n i).pos
  have tr:=((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow)
  have tiny:=(tendsto_const_nhds (x:=(1:ℝ))).div_atTop tr
  have one:=tendsto_const_nhds (f:=l) (x:=(1:ℝ))
  have ord : Tendsto (fun i => ((n i).val:ℝ)/(t i:ℝ)^4) l (𝓝 2) := by
    have g:=(((one.add (tiny.pow 2)).add (tiny.pow 4)).const_mul 2)
    norm_num at g
    apply g.congr
    intro i
    simp only [order,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    field_simp [(tp i).ne']
  have off : Tendsto (fun i => ((t i:ℝ)+3)/(t i:ℝ)) l (𝓝 1) := by
    have g:=one.add (tiny.const_mul 3)
    norm_num at g
    apply g.congr
    intro i
    field_simp [(tp i).ne']
  let A (i:ι):=2+(((h i:ℝ)/(t i:ℝ)^2)^2)/((n i).val/(t i:ℝ)^4)-
    (((t i:ℝ)+3)/(t i:ℝ))^4/(12*((n i).val/(t i:ℝ)^4))
  have value : Tendsto A l (𝓝 (25/12)) := by
    have g:=((tendsto_const_nhds (f:=l) (x:=(2:ℝ))).add ((kept.pow 2).div ord (by norm_num))).sub
      ((off.pow 4).div (ord.const_mul 12) (by norm_num))
    norm_num at g ⊢
    exact g
  have nlarge : Tendsto (fun i => ((n i).val:ℝ)) l atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact tendsto_atTop_mono (fun i => by rw [order];nlinarith only [Nat.le_self_pow (by decide : 2≠0) (t i)]) grow
  have lose:=(tendsto_const_nhds (x:=(1:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp nlarge)
  have root:=value.sqrt.sub lose
  rw [sub_zero] at root
  filter_upwards [root.eventually_const_lt below] with i hi
  have finite:=finite_bound _ _ _ _ (cap i)
  have aa : A i≤(((k i:ℝ)+1)/Real.sqrt (n i))^2 := by
    dsimp only [A]
    rw [div_pow ((k i:ℝ)+1) (Real.sqrt (n i)) 2,Real.sq_sqrt (np i).le]
    have y : (((h i:ℝ)/(t i:ℝ)^2)^2)/((n i).val/(t i:ℝ)^4)=(h i:ℝ)^2/(n i).val := by field_simp [(tp i).ne',(np i).ne']
    have z : (((t i:ℝ)+3)/(t i:ℝ))^4/(12*((n i).val/(t i:ℝ)^4))=((t i:ℝ)+3)^4/(12*(n i).val) := by field_simp [(tp i).ne',(np i).ne']
    rw [y,z]
    calc
      _ = (2*((n i).val:ℝ)+(h i:ℝ)^2-((t i:ℝ)+3)^4/12)/(n i).val := by field_simp [(np i).ne']
      _ ≤ _ := div_le_div_of_nonneg_right finite (np i).le
  have rr:=Real.sqrt_le_sqrt aa
  rw [Real.sqrt_sq (by positivity)] at rr
  change v<Real.sqrt (A i)-1/Real.sqrt (n i) at hi
  rw [add_div] at rr
  linarith only [hi,rr]
#print axioms floor_limit
end Green33BaerQuadraticLimit

namespace Green33BaerRetention
open Filter Finset Green33BaerQuadratic Green33BaerQuadraticLimit
open scoped Topology Pointwise
variable {ι : Type*} {l : Filter ι} (t:ι→ℕ) (n:ι→ℕ+) (B T:∀ i,Finset (ZMod (n i)))

private theorem pair_limit (pos:∀ i,0<t i) (grow:Tendsto t l atTop) :
    Tendsto (fun i => (((t i+1).choose 2:ℕ):ℝ)/(t i:ℝ)^2) l (𝓝 (1/2)) := by
  have g:=((tendsto_const_nhds (f:=l) (x:=(1:ℝ))).div_atTop
    ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow))
  have h:=((tendsto_const_nhds (f:=l) (x:=(1:ℝ))).add g).div_const 2
  norm_num at h
  apply h.congr
  intro i
  rw [Nat.cast_choose_two,Nat.cast_add_one]
  have p : (t i:ℝ)≠0 := by exact_mod_cast (pos i).ne'
  field_simp [p]
  ring

/-- A full basis retaining all but o(t²) points of the layer has normalized
size eventually above every real coefficient less than sqrt(25/12). -/
theorem retained_floor (pos:∀ i,0<t i) (grow:Tendsto t l atTop)
    (order:∀ i,(n i).val=2*((t i)^4+(t i)^2+1))
    (full:∀ i,T i+T i=univ)
    (roots:∀ i,∃ X:Finset (ZMod (n i)),∃ c:ZMod (n i),X.card=t i ∧
      (X+X).card=(t i+1).choose 2 ∧ (X+X).image (c+·)⊆B i)
    (missing:Tendsto (fun i => (((B i)\(T i)).card:ℝ)/(t i:ℝ)^2) l (𝓝 0))
    {v:ℝ} (below:v<Real.sqrt (25/12)) :
    ∀ᶠ i in l,v<((T i).card:ℝ)/Real.sqrt (n i) := by
  classical
  choose X c size pairs inc using roots
  let Q (i:ι):=(X i+X i).image (c i+·)
  let H (i:ι):=Q i∩T i
  have qcard i : (Q i).card=(t i+1).choose 2 :=
    (card_image_of_injective _ (fun _ _ eq => add_left_cancel eq)).trans (pairs i)
  have loss : Tendsto (fun i => (((Q i)\(T i)).card:ℝ)/(t i:ℝ)^2) l (𝓝 0) := by
    apply squeeze_zero (fun _ => by positivity) _ missing
    intro i
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast card_le_card (sdiff_subset_sdiff (inc i) (Subset.rfl : T i⊆T i))
  have kept:= (pair_limit t pos grow).sub loss
  rw [sub_zero] at kept
  have retain : Tendsto (fun i => ((H i).card:ℝ)/(t i:ℝ)^2) l (𝓝 (1/2)) := by
    apply kept.congr
    intro i
    have eq:=card_sdiff_add_card_inter (Q i) (T i)
    rw [qcard] at eq
    have realEq:=congrArg (Nat.cast (R:=ℝ)) eq
    push_cast only [Nat.cast_add] at realEq
    rw [←sub_div]
    exact congrArg (fun x:ℝ => x/(t i:ℝ)^2) (by dsimp only [H];linarith only [realEq])
  apply floor_limit t _ _ n pos order grow retain _ below
  intro i
  have cap:=quadratic_seed_budget (T i) (H i) (X i) (c i) inter_subset_right inter_subset_left
  rwa [full,card_univ,ZMod.card,size] at cap
#print axioms retained_floor
/-- A critical full basis captures at most (1/2+o(1))t² points from any
layer of order t²+t+1 containing the full split quadratic family. -/
theorem critical_half (pos:∀ i,0<t i) (grow:Tendsto t l atTop)
    (order:∀ i,(n i).val=2*((t i)^4+(t i)^2+1)) (full:∀ i,T i+T i=univ)
    (critical:Tendsto (fun i => ((T i).card:ℝ)/Real.sqrt (n i)) l (𝓝 (Real.sqrt 2)))
    (sizeB:∀ i,(B i).card=(t i)^2+t i+1)
    (roots:∀ i,∃ X:Finset (ZMod (n i)),∃ c:ZMod (n i),X.card=t i ∧
      (X+X).card=(t i+1).choose 2 ∧ (X+X).image (c+·)⊆B i)
    {v:ℝ} (above:1/2<v) :
    ∀ᶠ i in l,((T i∩B i).card:ℝ)/(t i:ℝ)^2<v := by
  classical
  choose X c cardX pairs inc using roots
  let Y (i:ι):=(X i).image (c i+·)
  let Q (i:ι):=X i+Y i
  have cy i : (Y i).card=t i := (card_image_of_injective _ (fun _ _ eq => add_left_cancel eq)).trans (cardX i)
  have eq i : Q i=(X i+X i).image (c i+·) := by
    ext a
    constructor
    · intro ha
      obtain ⟨u,hu,w,hw,rfl⟩:=mem_add.mp ha
      obtain ⟨d,hd,rfl⟩:=mem_image.mp hw
      exact mem_image.mpr ⟨u+d,Finset.add_mem_add hu hd,by abel⟩
    · intro ha
      obtain ⟨b,hb,rfl⟩:=mem_image.mp ha
      obtain ⟨u,hu,w,hw,rfl⟩:=mem_add.mp hb
      exact mem_add.mpr ⟨u,hu,c i+w,mem_image_of_mem _ hw,by abel⟩
  have qc i : (Q i).card=(t i+1).choose 2 := by rw [eq,card_image_of_injective _ (fun _ _ h => add_left_cancel h),pairs]
  have big:Tendsto (fun i => (n i).val) l atTop := tendsto_atTop_mono (fun i => by rw [order];nlinarith only [Nat.le_self_pow (by decide : 2≠0) (t i)]) grow
  have cost (i:ι) : ((X i).card:ℝ)*(Y i).card≤1*(T i).card := by
    have cap : (n i).val≤(T i).card^2 := by simpa [full,ZMod.card,pow_two] using (card_add_le : (T i+T i).card≤_)
    have cap' := (order i).ge.trans cap
    have kk : (t i)^2≤(T i).card := by
      by_contra! h
      have bad:=Nat.pow_lt_pow_left h (by decide : 2≠0)
      nlinarith only [cap',bad]
    rw [cardX,cy,one_mul,←pow_two]
    exact_mod_cast kk
  have sparse:=Green33FactorDensity.green33_escape n T X Y big critical full (Eventually.of_forall cost)
    (by simpa only [cardX] using grow) (by simpa only [cy] using grow)
  have tp i : (0:ℝ)<t i := by exact_mod_cast pos i
  have np i : (0:ℝ)<(n i).val := by exact_mod_cast (n i).pos
  have tr:=(tendsto_natCast_atTop_atTop (R:=ℝ)).comp grow
  have tiny:=(tendsto_const_nhds (x:=(1:ℝ))).div_atTop tr
  have one:=tendsto_const_nhds (f:=l) (x:=(1:ℝ))
  have ratios : Tendsto (fun i => Real.sqrt (n i)/(t i:ℝ)^2) l (𝓝 (Real.sqrt 2)) := by
    have g:=(((one.add (tiny.pow 2)).add (tiny.pow 4)).const_mul 2)
    norm_num at g
    apply g.sqrt.congr
    intro i
    conv_rhs => rw [←Real.sqrt_sq (sq_nonneg (t i:ℝ)),←Real.sqrt_div (np i).le]
    apply congrArg Real.sqrt
    change 2*(1+((t i:ℝ)^2)⁻¹+((t i:ℝ)^4)⁻¹)=_
    simp only [order,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_pow,Nat.cast_one]
    field_simp [(tp i).ne']
  have kq:=critical.mul ratios
  have small:=sparse.mul kq
  rw [zero_mul] at small
  have tail : Tendsto (fun i => ((T i∩Q i).card:ℝ)/(t i:ℝ)^2) l (𝓝 0) := by
    apply small.congr
    intro i
    have kp : (T i).card≠0 := by have h:=cost i;rw [cardX,cy,one_mul] at h;exact fun e => by rw [e,Nat.cast_zero] at h;exact (not_le_of_gt (mul_pos (tp i) (tp i))) h
    change _/((T i).card:ℝ)*(((T i).card/Real.sqrt (n i))*(Real.sqrt (n i)/(t i:ℝ)^2))=_
    dsimp only [Q]
    field_simp [(Nat.cast_ne_zero.mpr kp : ((T i).card:ℝ)≠0),Real.sqrt_ne_zero'.mpr (np i)]
  have base:Tendsto (fun i => ((B i).card:ℝ)/(t i:ℝ)^2) l (𝓝 1) := by
    have g:=(one.add tiny).add (tiny.pow 2)
    norm_num at g
    apply g.congr
    intro i
    simp only [sizeB,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
    field_simp [(tp i).ne']
  have lim:=(base.sub (pair_limit t pos grow)).add tail
  norm_num at lim
  filter_upwards [lim.eventually_lt_const above] with i hi
  change ((B i).card:ℝ)/(t i:ℝ)^2-(((t i+1).choose 2:ℕ):ℝ)/(t i:ℝ)^2+((T i∩Q i).card:ℝ)/(t i:ℝ)^2<v at hi
  have qb : Q i⊆B i := eq i ▸ inc i
  have sub : T i∩B i⊆(B i\Q i)∪(T i∩Q i) := by
    intro a ha
    by_cases h:a∈Q i
    · exact mem_union_right _ (mem_inter.mpr ⟨(mem_inter.mp ha).1,h⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨(mem_inter.mp ha).2,h⟩)
  have b:= (card_le_card sub).trans (card_union_le ..)
  have r:=card_sdiff_add_card_eq_card qb
  have bound : (T i∩B i).card+(t i+1).choose 2≤(B i).card+(T i∩Q i).card := by rw [←qc];omega
  have bb : ((T i∩B i).card:ℝ)+(((t i+1).choose 2:ℕ):ℝ)≤(B i).card+(T i∩Q i).card := by exact_mod_cast bound
  apply lt_of_le_of_lt _ hi
  rw [←sub_div,←add_div]
  exact div_le_div_of_nonneg_right (by linarith only [bb]) (sq_nonneg _)
#print axioms critical_half

end Green33BaerRetention
