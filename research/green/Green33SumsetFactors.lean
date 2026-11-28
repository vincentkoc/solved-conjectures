import Mathlib
/-! Four-cycle bounds for the intersection of a set with an arbitrary sumset. -/
open Finset
open scoped BigOperators Pointwise
namespace Green33SumsetFactors
variable {I J : Type*}

/-- Two applications of Cauchy--Schwarz, including repeated vertices. -/
theorem four_cycle_count (X : Finset I) (Y : Finset J) (w : I→J→ℕ) :
    (∑ j∈Y, ∑ i∈X, w i j)^4 ≤ X.card^2*Y.card^2*
      ∑ p∈X×ˢX, (∑ j∈Y,w p.1 j*w p.2 j)^2 := by
  let c (p:I×I):=∑ j∈Y,w p.1 j*w p.2 j
  have first : (∑ j∈Y, ∑ i∈X,w i j)^2≤Y.card*∑ j∈Y,(∑ i∈X,w i j)^2 :=
    sq_sum_le_card_mul_sum_sq
  have mid : (∑ j∈Y,(∑ i∈X,w i j)^2)=∑ p∈X×ˢX,c p := by
    dsimp only [c]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [sum_product,sq,sum_mul_sum]
  rw [mid] at first
  have last : (∑ p∈X×ˢX,c p)^2≤(X×ˢX).card*∑ p∈X×ˢX,(c p)^2 := sq_sum_le_card_mul_sum_sq
  rw [card_product,←sq] at last
  calc
    _ = ((∑ j∈Y,∑ i∈X,w i j)^2)^2 := by ring
    _ ≤ (Y.card*(∑ p∈X×ˢX,c p))^2 := Nat.pow_le_pow_left first 2
    _ = Y.card^2*(∑ p∈X×ˢX,c p)^2 := mul_pow ..
    _ ≤ Y.card^2*(X.card^2*∑ p∈X×ˢX,(c p)^2) := Nat.mul_le_mul_left _ last
    _ = _ := by ring
#print axioms four_cycle_count

variable [DecidableEq I] [DecidableEq J]
abbrev Quad (I J : Type*) := (I×I)×(J×J)
abbrev cornerCondition (E : Finset (I×J)) (r : Quad I J) : Prop :=
  (r.1.1,r.2.1)∈E ∧ (r.1.2,r.2.1)∈E ∧ (r.1.1,r.2.2)∈E ∧ (r.1.2,r.2.2)∈E

def rectangles (X : Finset I) (Y : Finset J) (E : Finset (I×J)) : Finset (Quad I J) :=
  (X.offDiag×ˢY.offDiag).filter (cornerCondition E)

/-- Nondegenerate rectangles control the fourth power of the number of occupied cells. -/
theorem occupied_bound (X : Finset I) (Y : Finset J) (E : Finset (I×J)) (sub : E⊆X×ˢY) :
    E.card^4≤X.card^2*Y.card^2*(X.card*Y.card*(X.card+Y.card)+(rectangles X Y E).card) := by
  classical
  let w (i:I) (j:J) : ℕ := if (i,j)∈E then 1 else 0
  let all := ((X×ˢX)×ˢ(Y×ˢY)).filter (cornerCondition E)
  have edges : E.card=∑ j∈Y,∑ i∈X,w i j := by
    have eq : (X×ˢY).filter (·∈E)=E := by ext a;simp only [mem_filter];exact and_iff_right_of_imp fun h => sub h
    rw [←eq,card_filter,sum_product,sum_comm]
  have count : all.card=∑ p∈X×ˢX,(∑ j∈Y,w p.1 j*w p.2 j)^2 := by
    dsimp only [all]
    rw [card_filter,sum_product]
    apply sum_congr rfl
    intro p _
    rw [sum_product,sq,sum_mul_sum]
    apply sum_congr rfl
    intro y _
    apply sum_congr rfl
    intro z _
    by_cases h₁:(p.1,y)∈E <;> by_cases h₂:(p.2,y)∈E <;>
      by_cases h₃:(p.1,z)∈E <;> by_cases h₄:(p.2,z)∈E <;> simp [cornerCondition,w,h₁,h₂,h₃,h₄]
  have inc : all⊆(rectangles X Y E ∪ (X.diag×ˢ(Y×ˢY))) ∪ ((X×ˢX)×ˢY.diag) := by
    rintro ⟨⟨i,i'⟩,⟨j,j'⟩⟩ hr
    obtain ⟨p,yes⟩:=mem_filter.mp hr
    obtain ⟨⟨hi,hi'⟩,hj,hj'⟩ := (show (i∈X ∧ i'∈X) ∧ j∈Y ∧ j'∈Y by simpa only [mem_product] using p)
    by_cases ri:i=i'
    · exact mem_union_left _ (mem_union_right _ (mem_product.mpr ⟨mem_diag.mpr ⟨hi,ri⟩,mem_product.mpr ⟨hj,hj'⟩⟩))
    by_cases cj:j=j'
    · exact mem_union_right _ (mem_product.mpr ⟨mem_product.mpr ⟨hi,hi'⟩,mem_diag.mpr ⟨hj,cj⟩⟩)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_offDiag.mpr ⟨hi,hi',ri⟩,mem_offDiag.mpr ⟨hj,hj',cj⟩⟩,yes⟩))
  have cap:=((card_le_card inc).trans (card_union_le _ _)).trans (Nat.add_le_add_right (card_union_le _ _) _)
  simp only [card_product,diag_card] at cap
  have lo:=four_cycle_count X Y w
  rw [←edges,←count] at lo
  exact lo.trans (Nat.mul_le_mul_left _ (cap.trans_eq (by ring)))
#print axioms occupied_bound



section DegreeCounts
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

private def commonCols (Y : Finset J) (E : Finset (I×J)) (p : I×I) : Finset J :=
  Y.filter fun j => (p.1,j)∈E ∧ (p.2,j)∈E

/-- The second moment of column degrees, with the equal-row terms removed. -/
private theorem column_moment (X : Finset I) (Y : Finset J) (E : Finset (I×J)) (sub : E⊆X×ˢY) :
    E.card^2≤Y.card*(E.card+∑ p∈X.offDiag,(commonCols Y E p).card) := by
  classical
  let d (j:J):=X.filter fun i => (i,j)∈E
  have edges : E.card=∑ j∈Y,(d j).card := by
    have eq : (X×ˢY).filter (·∈E)=E := by ext a;simp only [mem_filter];exact and_iff_right_of_imp fun h => sub h
    rw [←eq,card_filter,sum_product,sum_comm]
    simp only [d,card_filter]
  have pair (j) : (d j).offDiag=X.offDiag.filter (fun p => (p.1,j)∈E ∧ (p.2,j)∈E) := by
    ext p
    simp only [mem_offDiag,d,mem_filter]
    tauto
  have wedge : (∑ j∈Y,(d j).offDiag.card)=∑ p∈X.offDiag,(commonCols Y E p).card := by
    simp only [pair,card_filter,commonCols]
    rw [sum_comm]
  have sqs : (∑ j∈Y,(d j).card^2)=E.card+∑ p∈X.offDiag,(commonCols Y E p).card := by
    rw [edges,←wedge,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [offDiag_card,sq]
    exact (Nat.add_sub_of_le (by exact Nat.le_mul_self _)).symm
  have h : (∑ j∈Y,(d j).card)^2≤Y.card*∑ j∈Y,(d j).card^2 := sq_sum_le_card_mul_sum_sq
  rwa [←edges,sqs] at h

private theorem common_rectangles (X : Finset I) (Y : Finset J) (E : Finset (I×J)) :
    (rectangles X Y E).card=∑ p∈X.offDiag,(commonCols Y E p).offDiag.card := by
  classical
  rw [rectangles,card_filter,sum_product]
  apply sum_congr rfl
  intro p _
  have eq : (commonCols Y E p).offDiag=Y.offDiag.filter (fun u => cornerCondition E (p,u)) := by
    ext j
    rw [Finset.mem_filter]
    simp only [commonCols,mem_offDiag,mem_filter,cornerCondition]
    tauto
  rw [eq,card_filter]

/-- A four-cycle estimate retaining the exact contribution of repeated rows.
This gives the usual order m^(3/2) for a square m-by-m rectangle-free grid. -/
theorem column_bound (X : Finset I) (Y : Finset J) (E : Finset (I×J)) (sub : E⊆X×ˢY) :
    (E.card:ℝ)^2≤Y.card*(E.card+(X.card:ℝ)^2+X.card*Real.sqrt (rectangles X Y E).card) := by
  classical
  let U:=X.offDiag
  let d (p:I×I):=(commonCols Y E p).card
  let f (p:I×I):=((d p-1:ℕ):ℝ)
  have each (p) : f p^2≤((commonCols Y E p).offDiag.card:ℝ) := by
    rw [offDiag_card,←Nat.mul_sub_one]
    dsimp only [f,d]
    rw [sq]
    exact_mod_cast Nat.mul_le_mul_right ((commonCols Y E p).card-1) (Nat.sub_le (commonCols Y E p).card 1)
  have total : ∑ p∈U,f p^2≤((rectangles X Y E).card:ℝ) := by
    rw [common_rectangles,Nat.cast_sum]
    exact sum_le_sum fun p _ => each p
  have usize : (U.card:ℝ)≤(X.card:ℝ)^2 := by
    dsimp only [U];rw [offDiag_card,sq]
    exact_mod_cast (Nat.sub_le _ _ : X.card*X.card-X.card≤X.card*X.card)
  have cs : (∑ p∈U,f p)^2≤(U.card:ℝ)*∑ p∈U,f p^2 := sq_sum_le_card_mul_sum_sq
  have root : (∑ p∈U,f p)≤(X.card:ℝ)*Real.sqrt (rectangles X Y E).card := by
    have bound:=cs.trans (mul_le_mul usize total (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _))
    have h:=Real.sqrt_le_sqrt bound
    simpa only [Real.sqrt_sq (show 0≤∑ p∈U,f p by positivity),Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)] using h
  have pbound (p) : (d p:ℝ)≤1+f p := by dsimp only [f];exact_mod_cast (show d p≤1+(d p-1) by omega)
  have wedge : (∑ p∈U,(d p:ℝ))≤(X.card:ℝ)^2+X.card*Real.sqrt (rectangles X Y E).card := by
    have h:=sum_le_sum (s:=U) fun p _ => pbound p
    rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at h
    exact h.trans (add_le_add usize root)
  have h:=column_moment X Y E sub
  have val : (E.card:ℝ)^2≤Y.card*(E.card+∑ p∈U,(d p:ℝ)) := by exact_mod_cast h
  exact val.trans (mul_le_mul_of_nonneg_left (by linarith only [wedge]) (Nat.cast_nonneg _))

#print axioms column_bound
end DegreeCounts

section Sums
variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

def label (p : G×G) := p.1+p.2
private def mainPair (r : Quad G G) : Sym2 G := Sym2.mk (label (r.1.1,r.2.1)) (label (r.1.2,r.2.2))
private def flip (r : Quad G G) : Quad G G := (r.1,r.2.swap)
private def reverseBoth (r : Quad G G) : Quad G G := (r.1.swap,r.2.swap)
private def pairValue : Sym2 G→G := Sym2.lift ⟨(·+·),add_comm⟩

/-- Each four ordered versions of a nondegenerate rectangle spend one
unordered-pair excess. Only the chosen cells need distinct additive labels. -/
theorem rectangle_charge (T X Y : Finset G) (E : Finset (G×G))
    (inj : Set.InjOn (label (G:=G)) (E : Set (G×G))) (inside : ∀ p∈E,label p∈T) :
    (rectangles X Y E).card≤4*((T.card+1).choose 2-(T+T).card) := by
  classical
  let R:=rectangles X Y E
  have sur : Set.SurjOn (pairValue (G:=G)) (↑T.sym2) (↑(T+T)) := by
    intro z hz
    obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp hz
    exact ⟨Sym2.mk a b,mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩
  obtain ⟨P,sub,unique,onto⟩:=exists_subset_injOn_image_eq_of_surjOn _ _ sur
  have sizeP:=congrArg card onto
  rw [card_image_of_injOn unique] at sizeP
  have prop (r) (hr:r∈R) : cornerCondition E r := (mem_filter.mp hr).2
  have side (r) (hr:r∈R) : r.2.1≠r.2.2 := (mem_offDiag.mp (mem_product.mp (mem_filter.mp hr).1).2).2.2
  have side' (r) (hr:r∈R) : r.1.1≠r.1.2 := (mem_offDiag.mp (mem_product.mp (mem_filter.mp hr).1).1).2.2
  have swap_mem (r) (hr:r∈R) : flip r∈R := by
    obtain ⟨xy,h⟩:=mem_filter.mp hr
    obtain ⟨x,y⟩:=mem_product.mp xy
    obtain ⟨a,b,n⟩:=mem_offDiag.mp y
    exact mem_filter.mpr ⟨mem_product.mpr ⟨x,mem_offDiag.mpr ⟨b,a,n.symm⟩⟩,h.2.2.1,h.2.2.2,h.1,h.2.1⟩
  have inS (r) (hr:r∈R) : mainPair r∈T.sym2 := by
    have h:=prop r hr
    exact mk_mem_sym2_iff.mpr ⟨inside _ h.1,inside _ h.2.2.2⟩
  have changePair (r) (hr:r∈R) : mainPair r≠mainPair (flip r) := by
    have h:=prop r hr
    intro eq
    rcases Sym2.eq_iff.mp eq with ⟨s,_⟩|⟨s,_⟩
    · exact side r hr (congrArg Prod.snd (inj h.1 h.2.2.1 s))
    · exact side' r hr (congrArg Prod.fst (inj h.1 h.2.1 s))
  let bad:=R.filter fun r => mainPair r∉P
  have inc : R⊆bad∪bad.image flip := by
    intro r hr
    by_cases g:mainPair r∈P
    · have loss : mainPair (flip r)∉P := by
        intro g'
        apply changePair r hr
        apply unique g g'
        change r.1.1+r.2.1+(r.1.2+r.2.2)=r.1.1+r.2.2+(r.1.2+r.2.1)
        ac_rfl
      exact mem_union_right _ (mem_image.mpr ⟨flip r,mem_filter.mpr ⟨swap_mem r hr,loss⟩,rfl⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hr,g⟩)
  have same (r s : Quad G G) (hr:r∈R) (hs:s∈R) (eq:mainPair r=mainPair s) :
      r=s ∨ r=reverseBoth s := by
    have r':=prop r hr
    have s':=prop s hs
    rcases Sym2.eq_iff.mp eq with ⟨a,b⟩|⟨a,b⟩
    · have e:=inj r'.1 s'.1 a
      have f:=inj r'.2.2.2 s'.2.2.2 b
      obtain ⟨ex,ey⟩:=Prod.mk.inj e
      obtain ⟨fx,fy⟩:=Prod.mk.inj f
      exact Or.inl (Prod.ext (Prod.ext ex fx) (Prod.ext ey fy))
    · have e:=inj r'.1 s'.2.2.2 a
      have f:=inj r'.2.2.2 s'.1 b
      obtain ⟨ex,ey⟩:=Prod.mk.inj e
      obtain ⟨fx,fy⟩:=Prod.mk.inj f
      exact Or.inr (Prod.ext (Prod.ext ex fx) (Prod.ext ey fy))
  have maps (r) (hr:r∈bad) : mainPair r∈T.sym2\P :=
    mem_sdiff.mpr ⟨inS r (mem_filter.mp hr).1,(mem_filter.mp hr).2⟩
  have cap (u : Sym2 G) (_ : u∈T.sym2\P) : (bad.filter (fun r => mainPair r=u)).card≤2 := by
    let F:=bad.filter (fun r => mainPair r=u)
    by_cases ne:F.Nonempty
    · obtain ⟨s,hs⟩:=ne
      apply (card_le_card (t:={s,reverseBoth s}) ?_).trans card_le_two
      intro r hr
      obtain ⟨r',eq⟩:=mem_filter.mp hr
      obtain ⟨s',eq'⟩:=mem_filter.mp hs
      simpa only [mem_insert,mem_singleton] using
        same r s (mem_filter.mp r').1 (mem_filter.mp s').1 (eq.trans eq'.symm)
    · change F.card≤2
      simp [not_nonempty_iff_eq_empty.mp ne]
  have n:=card_le_mul_card_image_of_maps_to maps 2 cap
  have cardlost : (T.sym2\P).card=(T.card+1).choose 2-(T+T).card := by
    rw [card_sdiff_of_subset sub,card_sym2,sizeP]
  rw [cardlost] at n
  have total:=((card_le_card inc).trans (card_union_le _ _)).trans (Nat.add_le_add_left card_image_le _)
  change R.card≤4*((T.card+1).choose 2-(T+T).card)
  omega


private theorem selected (T X Y : Finset G) :
    ∃ E : Finset (G×G), E⊆X×ˢY ∧ Set.InjOn (label (G:=G)) (E : Set (G×G)) ∧
      (∀ p∈E,label p∈T) ∧ E.card=(T∩(X+Y)).card := by
  classical
  have sur : Set.SurjOn (label (G:=G)) (↑(X×ˢY)) (↑(T∩(X+Y))) := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩:=mem_add.mp (mem_inter.mp hz).2
    exact ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,rfl⟩
  obtain ⟨E,sub,inj,sums⟩:=exists_subset_injOn_image_eq_of_surjOn _ _ sur
  refine ⟨E,sub,inj,fun p hp => (mem_inter.mp (sums ▸ mem_image_of_mem label hp)).1,?_⟩
  exact (card_image_of_injOn inj).symm.trans (congrArg card sums)

/-- Four-cycle obstruction for arbitrary additive factorizations; the sum map
on the entire product may have repeated labels. -/
theorem factor_bound (T X Y : Finset G) :
    (T∩(X+Y)).card^4≤X.card^2*Y.card^2*(X.card*Y.card*(X.card+Y.card)+
      4*((T.card+1).choose 2-(T+T).card)) := by
  obtain ⟨E,sub,inj,ins,size⟩:=selected T X Y
  have charge:=rectangle_charge T X Y E inj ins
  rw [←size]
  exact (occupied_bound X Y E sub).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left charge _))

#print axioms rectangle_charge
#print axioms factor_bound

/-- The unbalanced rectangle estimate. The correction depends on the smaller
factor and on the square root of the global unordered-pair excess. -/
theorem factor_stability (T X Y : Finset G) :
    let e:=((T∩(X+Y)).card:ℝ)
    let a:=(X.card:ℝ)
    let b:=(Y.card:ℝ)
    let Δ:=(((T.card+1).choose 2-(T+T).card:ℕ):ℝ)
    e^2≤ max a b*e+(a*b)*(min a b+2*Real.sqrt Δ) := by
  let Δ:=(((T.card+1).choose 2-(T+T).card:ℕ):ℝ)
  have oriented (X Y : Finset G) :
      let e:=((T∩(X+Y)).card:ℝ)
      let a:=(X.card:ℝ)
      let b:=(Y.card:ℝ)
      e^2≤b*e+(a*b)*(a+2*Real.sqrt Δ) := by
    obtain ⟨E,sub,inj,ins,size⟩:=selected T X Y
    have h:=column_bound X Y E sub
    have r:=rectangle_charge T X Y E inj ins
    have r' : ((rectangles X Y E).card:ℝ)≤4*Δ := by dsimp only [Δ];exact_mod_cast r
    have root:=Real.sqrt_le_sqrt r'
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num] at root
    rw [size] at h
    dsimp only
    exact h.trans (by nlinarith only [mul_le_mul_of_nonneg_left root (show 0≤(X.card:ℝ)*Y.card by positivity)])
  dsimp only
  rcases le_total (X.card:ℝ) (Y.card:ℝ) with xy|yx
  · rw [max_eq_right xy,min_eq_left xy]
    exact oriented X Y
  · rw [max_eq_left yx,min_eq_right yx,mul_comm (X.card:ℝ) (Y.card:ℝ)]
    simpa only [add_comm Y X] using oriented Y X

/-- A finite bound for the number of occupied labels above the capacity of
the larger factor, uniform in the relative sizes of the two factors. -/
theorem surplus_bound (T X Y : Finset G) :
    let m:=max X.card Y.card
    let e:=(T∩(X+Y)).card
    (((e-m:ℕ):ℝ))^2≤(X.card:ℝ)*Y.card*
      (min (X.card:ℝ) Y.card+2*Real.sqrt (((T.card+1).choose 2-(T+T).card:ℕ):ℝ)) := by
  dsimp only
  by_cases h:max X.card Y.card≤(T∩(X+Y)).card
  · rw [Nat.cast_sub h,Nat.cast_max]
    have hm : (0:ℝ)≤ max (X.card:ℝ) (Y.card:ℝ) := le_max_of_le_left (Nat.cast_nonneg _)
    have non : max (X.card:ℝ) (Y.card:ℝ)≤((T∩(X+Y)).card:ℝ) := by exact_mod_cast h
    have bound:=factor_stability T X Y
    dsimp only at bound
    nlinarith only [bound,mul_nonneg hm (sub_nonneg.mpr non)]
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge h),Nat.cast_zero,zero_pow (by decide : 2≠0)]
    positivity

#print axioms factor_stability
#print axioms surplus_bound

end Sums

/-- The coefficient four in the rectangle charge is attained by an ordinary
full cyclic basis. Its only extra unordered representation is 0+4=1+3. -/
theorem sharp_charge :
    let X : Finset (ZMod 9):={0,1}
    let Y : Finset (ZMod 9):={0,3}
    let T:=X+Y
    T+T=univ ∧ T.card=4 ∧ (rectangles X Y (X×ˢY)).card=4 ∧
      (T.card+1).choose 2-(T+T).card=1 := by decide

#print axioms sharp_charge
end Green33SumsetFactors
