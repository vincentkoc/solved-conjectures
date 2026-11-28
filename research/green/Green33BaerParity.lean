import Green33BaerLayers
/-! Per-coset capacity of the even parity layer in a cyclic Baer construction. -/
open Finset Green33BaerLayers Green33PerfectDifferenceCenters Green33SingerBlockingLayers
open scoped Pointwise
namespace Green33BaerParity
variable {H J : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    [AddCommGroup J] [Fintype J] [DecidableEq J]

omit [AddCommGroup H] [AddCommGroup J] in
private theorem row_compl (S : Finset (H×J)) (j : J) :
    (row Sᶜ j).card+(row S j).card=Fintype.card H := by
  have eq : row Sᶜ j=(row S j)ᶜ := by ext x;simp [row]
  rw [eq,add_comm,card_add_card_compl]

omit [AddCommGroup H] [AddCommGroup J] in
private theorem fresh_rows (S V : Finset (H×J)) (Q : Finset J) {L : ℕ}
    (cap : ∀ j,2*(row Sᶜ j).card≤L) (support : ∀ z∈V,z.2∈Q) :
    2*(V\S).card≤Q.card*L := by
  classical
  let F (j : J) := layer (row Sᶜ j) j
  have sub : V\S⊆Q.biUnion F := by
    intro z hz
    obtain ⟨hv,hs⟩:=mem_sdiff.mp hz
    refine mem_biUnion.mpr ⟨z.2,support z hv,mem_image.mpr ⟨z.1,?_,rfl⟩⟩
    simpa only [row,mem_filter,mem_univ,true_and,mem_compl,Prod.mk.eta] using hs
  have size (j : J) : (F j).card=(row Sᶜ j).card :=
    card_image_of_injective _ (fun _ _ eq => congrArg Prod.fst eq)
  have cost:=(card_le_card sub).trans (card_biUnion_le)
  calc 2*(V\S).card ≤ 2*∑ j∈Q,(F j).card := Nat.mul_le_mul_left _ cost
       _ = ∑ j∈Q,2*(row Sᶜ j).card := by simp only [mul_sum,size]
       _ ≤ ∑ _j∈Q,L := sum_le_sum (fun j _ => cap j)
       _ = Q.card*L := by simp

private theorem planar_cap (A : Finset (H×J)) {t : ℕ}
    (sid : IsSidon (A : Set (H×J))) (size : A.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1) :
    ∀ j, 2*(row (A+A)ᶜ j).card≤t^2+t := by
  intro j
  have c:=row_compl (A+A) j
  have rr:=sumset_rows A sid size left right rows
  by_cases z:j=0
  · subst j;rw [rr.1,card_univ] at c;omega
  · have h:=rr.2 j z
    rw [left] at c h
    omega


variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

private theorem perfect_fresh (D X : Finset G) (perf : Perfect D) (ne : D.Nonempty) :
    2*((X+D)\(D+D)).card≤X.card*D.card := by
  have all : D-D=univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz:z=0
    · obtain ⟨a,ha⟩:=ne
      exact mem_sub.mpr ⟨a,ha,a,ha,(sub_self _).trans hz.symm⟩
    · have pos : 0<Green33TailEnergy.diffReps D z := by rw [perf z hz];decide
      obtain ⟨⟨a,b⟩,hab⟩:=Finset.card_pos.mp pos
      obtain ⟨h,eq⟩:=mem_filter.mp hab
      exact mem_sub.mpr ⟨a,(mem_product.mp h).1,b,(mem_product.mp h).2,eq⟩
  obtain ⟨e,h,c⟩:=Green33SidonLayerRepairs.fresh_mixed_bound X D perf.sidon
  rw [all,compl_univ,card_empty,zero_mul] at c
  have z : e=0 := by nlinarith only [c]
  simpa [z] using h

omit [Fintype H] [Fintype J] in
private theorem shifted_support (d : H×J) (U V : Finset (H×J)) (P Q : Finset J)
    (hu : ∀ z∈U,z.2∈P) (hv : ∀ z∈V,z.2∈Q) :
    ∀ z∈shift d (U+V),z.2∈shift d.2 (P+Q) := by
  intro z hz
  obtain ⟨_,h,rfl⟩:=mem_image.mp hz
  obtain ⟨a,ha,b,hb,rfl⟩:=mem_add.mp h
  exact mem_image_of_mem _ (add_mem_add (hu _ ha) (hv _ hb))

private theorem fresh_cost (A B Y : Finset (H×J)) (P : Finset J) (d : H×J) {L : ℕ}
    (cap : ∀ j,2*(row (A+A)ᶜ j).card≤L) (hb : ∀ z∈B,z.2∈P) :
    2*(shift d (B+Y)\(A+A)).card≤min (2*(B.card*Y.card)) (P.card*Y.card*L) := by
  apply le_min
  · have m:=(card_le_card (sdiff_subset : shift d (B+Y)\(A+A)⊆shift d (B+Y))).trans
      (card_image_le.trans (card_add_le : (B+Y).card≤_))
    omega
  · let Q:=Y.image Prod.snd
    have hr:=fresh_rows (A+A) _ _ cap (shifted_support d B Y P Q hb (fun z hz => mem_image_of_mem _ hz))
    have n : (shift d.2 (P+Q)).card≤P.card*Y.card := by
      exact card_image_le.trans (card_add_le.trans (Nat.mul_le_mul_left _ card_image_le))
    exact hr.trans (Nat.mul_le_mul_right L n)

/-- Even-parity capacity after arbitrary changes to the two layers. The old odd layer
is supported on quotient cosets in `P`. The two alternatives for fresh odd points
charge either the number of old points or the remaining capacity of these cosets. -/
theorem even_budget (A B X Y : Finset (H×J)) (P : Finset J) (d : H×J) {t : ℕ}
    (perfect : Perfect A) (size : A.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1)
    (support : ∀ z∈B,z.2∈P)
    (full : (A∪X)+(A∪X)∪shift d ((B∪Y)+(B∪Y))=univ) :
    2*(Fintype.card H*Fintype.card J)≤
      2*(A+A).card+(P+P).card*(t^2+t)+X.card*A.card+
      min (2*(B.card*Y.card)) (P.card*Y.card*(t^2+t))+
      X.card^2+X.card+Y.card^2+Y.card := by
  let S:=A+A
  let U:=shift d (B+B)
  let V:=X+A
  let W:=shift d (B+Y)
  let O:=shift d (Y+Y)
  have cap:=planar_cap A perfect.sidon size left right rows
  have b:=fresh_rows S U (shift d.2 (P+P)) cap (shifted_support d B B P P support support)
  have u : 2*(U\S).card≤(P+P).card*(t^2+t) := b.trans (Nat.mul_le_mul_right _ card_image_le)
  have x:=perfect_fresh A X perfect (card_pos.mp (by rw [size];omega))
  have y:=fresh_cost A B Y P d cap support
  have v:=Green33SidonLayerRepairs.sum_upper X
  have w : 2*O.card≤Y.card^2+Y.card :=
    (Nat.mul_le_mul_left 2 card_image_le).trans (Green33SidonLayerRepairs.sum_upper Y)
  have shape : S∪U∪V∪W∪(X+X)∪O=univ := by
    rw [←full]
    simp only [S,U,V,W,O,shift,union_add,add_union,image_union]
    rw [add_comm A X,add_comm Y B]
    ext z;simp only [mem_union];tauto
  have cover : (univ : Finset (H×J))⊆S∪(U\S)∪(V\S)∪(W\S)∪(X+X)∪O := by
    rw [←shape];intro z hz
    simp only [mem_union,mem_sdiff] at hz ⊢
    tauto
  have n:=(card_le_card cover).trans (card_union_le _ _)
  rw [card_univ,Fintype.card_prod] at n
  have n1:=card_union_le (S∪(U\S)∪(V\S)∪(W\S)) (X+X)
  have n2:=card_union_le (S∪(U\S)∪(V\S)) (W\S)
  have n3:=card_union_le (S∪(U\S)) (V\S)
  have n4:=card_union_le S (U\S)
  change 2*(V\S).card≤X.card*A.card at x
  change 2*(W\S).card≤_ at y
  change _≤2*S.card+(P+P).card*(t^2+t)+X.card*A.card+
    min (2*(B.card*Y.card)) (P.card*Y.card*(t^2+t))+X.card^2+X.card+Y.card^2+Y.card
  omega

#print axioms even_budget

/-- A sum-free quotient fibre leaves half of its even residues uncovered,
uniformly in the number of points in the old odd layer. -/
theorem support_budget (A B : Finset (H×J)) (P : Finset J) (d : H×J) {t : ℕ}
    (sid : IsSidon (A : Set (H×J))) (size : A.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (rows : ∀ j : J,(row A j).card=(if j=0 then t else 0)+1)
    (support : ∀ z∈B,z.2∈P) :
    2*(A+A∪shift d (B+B)).card≤2*(A+A).card+(P+P).card*(t^2+t) := by
  let S:=A+A
  let V:=shift d (B+B)
  have cap:=planar_cap A sid size left right rows
  have n:=fresh_rows S V (shift d.2 (P+P)) cap (shifted_support d B B P P support support)
  have b : 2*(V\S).card≤(P+P).card*(t^2+t) := n.trans (Nat.mul_le_mul_right _ card_image_le)
  have shape : S∪V⊆S∪(V\S) := by intro x hx;simp only [mem_union,mem_sdiff] at hx ⊢; tauto
  have h:=(card_le_card shape).trans (card_union_le _ _)
  change 2*(S∪V).card≤2*S.card+_
  omega

#print axioms support_budget

open Filter
open scoped Topology

private theorem fresh_floor (q v k p L a w : ℕ→ℝ) (ρ α s : ℝ)
    (positive : ∀ i,0<q i) (nonneg : ∀ i,0≤w i ∧ 0≤a i)
    (scale : Tendsto (fun i => v i/(q i)^2) atTop (𝓝 1))
    (pairs : Tendsto (fun i => k i/(q i)^2) atTop (𝓝 1))
    (rows : Tendsto (fun i => L i/q i) atTop (𝓝 1))
    (projected : Tendsto (fun i => p i/q i) atTop (𝓝 ρ))
    (cost : Tendsto (fun i => a i/q i) atTop (𝓝 α))
    (bound : ∀ i, 2*v i≤k i+p i*L i+a i*w i+(w i)^2)
    (threshold : ρ+α*s+s^2<1) : ∀ᶠ i in atTop,s<w i/q i := by
  by_cases neg:s<0
  · exact Eventually.of_forall fun i => neg.trans_le (div_nonneg (nonneg i).1 (positive i).le)
  have h:=(((pairs.add (projected.mul rows)).add (cost.mul_const s)).add_const (s^2))
  have lim:=(scale.const_mul 2).sub h
  have gap : 0<2*1-(1+ρ*1+α*s+s^2) := by linarith
  filter_upwards [lim.eventually_const_lt gap] with i he
  have qi:=positive i
  have ai:=(nonneg i).2
  have wi:=(nonneg i).1
  change 0<2*(v i/(q i)^2)-(k i/(q i)^2+p i/q i*(L i/q i)+a i/q i*s+s^2) at he
  by_contra! small
  have sw := (div_le_iff₀ qi).mp small
  have sq := mul_self_le_mul_self wi sw
  have prod:=mul_le_mul_of_nonneg_left sw ai
  have base:=bound i
  field_simp [qi.ne'] at he
  nlinarith only [he,sq,prod,base]


private theorem scalings (t : ℕ→ℕ) (pos : ∀ i,0<t i) (big : Tendsto t atTop atTop) :
    let u (i : ℕ) : ℝ := t i
    let q (i : ℕ) := (u i)^2
    Tendsto (fun i => ((q i)^2+q i+1)/(q i)^2) atTop (𝓝 1) ∧
    Tendsto (fun i => ((q i+1)*(q i+2))/(q i)^2) atTop (𝓝 1) ∧
    Tendsto (fun i => (q i+u i)/q i) atTop (𝓝 1) ∧
    Tendsto (fun i => (q i+u i+1)/q i) atTop (𝓝 1) ∧
    Tendsto (fun i => (2*(q i+1)+1)/q i) atTop (𝓝 2) := by
  let u (i : ℕ) : ℝ := t i
  let q (i : ℕ) := (u i)^2
  have up (i) : 0<u i := by dsimp only [u];exact_mod_cast pos i
  have qp (i) : 0<q i := sq_pos_of_pos (up i)
  have top : Tendsto u atTop atTop:=tendsto_natCast_atTop_atTop.comp big
  have inv : Tendsto (fun i => 1/u i) atTop (𝓝 0):=tendsto_const_nhds.div_atTop top
  have iq : Tendsto (fun i => 1/q i) atTop (𝓝 0) := by simpa only [q,div_pow,one_pow,zero_pow (by decide : 2≠0)] using inv.pow 2
  have one : Tendsto (fun _i : ℕ => (1:ℝ)) atTop (𝓝 1):=tendsto_const_nhds
  refine ⟨?_,?_,?_,?_,?_⟩
  · have h:=(one.add iq).add (iq.pow 2)
    simp only [add_zero,zero_pow (by decide : 2≠0)] at h
    apply h.congr
    intro i
    change 1+1/q i+(1/q i)^2=((q i)^2+q i+1)/(q i)^2
    field_simp [(qp i).ne']
  · have h:=(one.add iq).mul (one.add (iq.const_mul 2))
    simp only [mul_zero,add_zero,mul_one] at h
    apply h.congr
    intro i
    change (1+1/q i)*(1+2*(1/q i))=((q i+1)*(q i+2))/(q i)^2
    field_simp [(qp i).ne']
  · have h:=one.add inv
    rw [add_zero] at h
    apply h.congr
    intro i
    change 1+1/u i=((u i)^2+u i)/(u i)^2
    field_simp [(up i).ne']
  · have h:=(one.add inv).add iq
    simp only [add_zero] at h
    apply h.congr
    intro i
    change 1+1/u i+1/(u i)^2=((u i)^2+u i+1)/(u i)^2
    field_simp [(up i).ne']
  · have h:=(one.const_mul 2).add (iq.const_mul 3)
    simp only [mul_one,mul_zero,add_zero] at h
    apply h.congr
    intro i
    change 2+3*(1/q i)=(2*(q i+1)+1)/q i
    field_simp [(qp i).ne']
    ring


private theorem cost_scalar {q t p x y u b : ℕ}
    (budget : 2*(q^2+q+1)≤(q+1)*(q+2)+p*(q+t)+x*(q+1)+
      min (2*(b*y)) (u*y*(q+t))+x^2+x+y^2+y) (size : b≤q+1) (pos : 0<t) :
    2*(q^2+q+1)≤(q+1)*(q+2)+p*(q+t)+(2*(q+1)+1)*(x+y)+(x+y)^2 ∧
    (u≤1 → 2*(q^2+q+1)≤(q+1)*(q+2)+p*(q+t)+(q+t+1)*(x+y)+(x+y)^2) := by
  constructor
  · have first:=min_le_left (2*(b*y)) (u*y*(q+t))
    have k:=Nat.mul_le_mul_right y size
    nlinarith only [budget,first,k,Nat.zero_le x,Nat.zero_le (q*x),Nat.zero_le (x*y)]
  · intro one
    have second:=min_le_right (2*(b*y)) (u*y*(q+t))
    have yc:=Nat.mul_le_mul_right (y*(q+t)) one
    have xc:=Nat.mul_le_mul_right x (by omega : 1≤t)
    nlinarith only [budget,second,yc,xc,Nat.zero_le (x*y)]

/-- The numerical obstruction for a growing family. The quotient sumset density is measured
in units of the plane order, which is asymptotic to the number of Baer cosets. -/
private theorem count_floor (t p w : ℕ→ℕ) (single : Bool) (ρ s : ℝ)
    (pos : ∀ i,0<t i) (big : Tendsto t atTop atTop)
    (projected : Tendsto (fun i => (p i:ℝ)/(t i:ℝ)^2) atTop (𝓝 ρ))
    (count : ∀ i, let q:=(t i)^2
      2*(q^2+q+1)≤(q+1)*(q+2)+p i*(q+t i)+
        (if single then q+t i+1 else 2*(q+1)+1)*w i+(w i)^2)
    (threshold : ρ+(if single then 1 else 2)*s+s^2<1) :
    ∀ᶠ i in atTop,s<(w i:ℝ)/(t i:ℝ)^2 := by
  let u (i : ℕ) : ℝ := t i
  let q (i : ℕ) := (u i)^2
  let a (i : ℕ) := if single then q i+u i+1 else 2*(q i+1)+1
  obtain ⟨v,k,L,one,two⟩:=scalings t pos big
  have a0 (i) : 0≤a i := by dsimp only [a];split <;> positivity
  apply fresh_floor q (fun i => (q i)^2+q i+1) (fun i => (q i+1)*(q i+2)) (fun i => p i)
    (fun i => q i+u i) a (fun i => w i) ρ (if single then 1 else 2) s
    (fun i => sq_pos_of_pos (by dsimp only [u];exact_mod_cast pos i)) (fun i => ⟨by positivity,a0 i⟩)
    v k L projected _ _ threshold
  · cases single <;> first | exact two | exact one
  · intro i
    cases single <;> dsimp only [a,q,u,Bool.false_eq_true,if_false,if_true] <;>
      exact_mod_cast count i


private theorem full_even {v : ℕ+} (E F : Finset (ZMod v))
    (full : split E F+split E F=univ) : E+E∪shift 1 (F+F)=univ := by
  apply eq_univ_of_card
  have count:=split_count E F
  rw [full,card_univ,ZMod.card] at count
  have h:=(E+F).card_le_univ
  have h':=(E+E∪shift 1 (F+F)).card_le_univ
  rw [ZMod.card] at h h' ⊢
  omega

private theorem extract_changes {v : ℕ+} (D B : Finset (ZMod v))
    (T : Finset (ZMod (2*v.val))) (full : T+T=univ) :
    ∃ X Y : Finset (ZMod v), X.card+Y.card=(T\split D B).card ∧
      (D∪X)+(D∪X)∪shift 1 ((B∪Y)+(B∪Y))=univ := by
  let R:=split D B
  obtain ⟨X,Y,eq,h⟩:=decompose (T\R)
  refine ⟨X,Y,h.symm,full_even _ _ ?_⟩
  have includes : T⊆split (D∪X) (B∪Y) := by
    have eqn : R∪(T\R)=split (D∪X) (B∪Y) := by
      rw [eq];simp only [R,split,image_union];ac_rfl
    rw [←eqn]
    intro x hx
    by_cases mem:x∈R
    · exact mem_union_left _ mem
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hx,mem⟩)
  exact eq_univ_of_forall (fun x => (add_subset_add includes includes) (full ▸ mem_univ x))


/-- A full replacement has an explicit split of its fresh points, even and odd.
The hypothesis locates only the quotient support of the old odd layer. -/
theorem cyclic_budget {v : ℕ+} (e : ZMod v≃+H×J) (D B : Finset (ZMod v))
    {t : ℕ} (pos : 0<t) (perf : Perfect D) (size : D.card=t^2+1)
    (left : Fintype.card H=t^2+t+1) (right : Fintype.card J+t=t^2+1)
    (P : Finset J) (support : ∀ b∈B,(e b).2-(-(t^2 • ∑ z∈D.image e,z)).2∈P)
    (T : Finset (ZMod (2*v.val))) (full : T+T=univ) :
    ∃ x y : ℕ, x+y=(T\split D B).card ∧
      2*(Fintype.card H*Fintype.card J)≤(t^2+1)*(t^2+2)+(P+P).card*(t^2+t)+x*(t^2+1)+
        min (2*(B.card*y)) (P.card*y*(t^2+t))+x^2+x+y^2+y := by
  obtain ⟨U,V,number,covers⟩:=extract_changes D B T full
  let c:= -(t^2 • ∑ z∈D.image e,z)
  let F:=frame e c
  have eq (S Z : Finset (ZMod v)) : F (S∪Z)=F S∪F Z := image_union _ _
  have n (S : Finset (ZMod v)) : (F S).card=S.card := frame_card e c S
  obtain ⟨p,rows⟩:=frame_rows e D pos perf size left right
  have same:=(n D).trans size
  have loc : ∀ z∈F B,z.2∈P := by
    intro z hz
    obtain ⟨b,hb,rfl⟩:=mem_image.mp hz
    exact support b hb
  have ev:=frame_even_full e c 1 (D∪U) (B∪V) covers
  change F (D∪U)+F (D∪U)∪shift (e 1) (F (B∪V)+F (B∪V))=univ at ev
  rw [eq,eq] at ev
  have bound:=even_budget (F D) (F B) (F U) (F V) P (e 1) p same left right rows loc ev
  have old:=Green33SidonLayerRepairs.sum_upper (F D)
  rw [same] at old
  simp only [n,size] at bound
  refine ⟨U.card,V.card,number,?_⟩
  nlinarith only [bound,old]

#print axioms cyclic_budget

private lemma mod_product (t : ℕ) (h j : ℕ+) (hl : h.val=t^2+t+1) (jr : j.val+t=t^2+1) :
    h.val*j.val=(t^2)^2+t^2+1 := by
  zify at hl jr ⊢
  rw [hl,show (j.val:ℤ)=(t:ℤ)^2-t+1 by linarith only [jr]]
  ring

open Filter
open scoped Topology

/-- The quotient sumset and new labels jointly constrain full coverage.
For any tested fresh-point ratio satisfying the strict quadratic threshold,
every full replacement eventually exceeds that ratio. -/
theorem fresh_labels (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (budget : ∀ i,(B i).card≤(t i)^2+1) (P : (i : ℕ)→Finset (ZMod (j i)))
    (support : ∀ i, let e:=chart _ _ _ (hl i) (jr i)
      ∀ b∈B i,(e b).2-(-((t i)^2 • ∑ z∈(D i).image e,z)).2∈P i)
    (T : (i : ℕ)→Finset (ZMod (2*(h i*j i).val))) (full : ∀ i,T i+T i=univ)
    (big : Tendsto t atTop atTop) (ρ s : ℝ) (single : Bool)
    (small : single=true → ∀ i,(P i).card≤1)
    (projected : Tendsto (fun i => ((P i+P i).card:ℝ)/(t i:ℝ)^2) atTop (𝓝 ρ))
    (threshold : ρ+(if single then 1 else 2)*s+s^2<1) :
    ∀ᶠ i in atTop,s<((T i\split (D i) (B i)).card:ℝ)/(t i:ℝ)^2 := by
  apply count_floor t (fun i => (P i+P i).card) (fun i => (T i\split (D i) (B i)).card)
    single ρ s pos big projected _ threshold
  intro i
  obtain ⟨x,y,w,c⟩:=cyclic_budget (chart _ _ _ (hl i) (jr i)) (D i) (B i) (pos i) (perfect i)
    (size i) (by simpa only [ZMod.card] using hl i) (by simpa only [ZMod.card] using jr i)
    (P i) (support i) (T i) (full i)
  simp only [ZMod.card,mod_product _ _ _ (hl i) (jr i)] at c
  have hcost:=cost_scalar c (budget i) (pos i)
  rw [←w]
  cases single
  · exact hcost.1
  · exact hcost.2 (small rfl i)

#print axioms fresh_labels

private theorem singleton_limit (t : ℕ→ℕ) (big : Tendsto t atTop atTop) :
    Tendsto (fun i => 1/(t i:ℝ)^2) atTop (𝓝 0) := by
  have top : Tendsto (fun i => (t i:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp big
  have sq:=((tendsto_const_nhds (x:=(1:ℝ))).div_atTop top).pow 2
  simpa only [div_pow,one_pow,zero_pow (by decide : 2≠0)] using sq

/-- Even after deletions, completing a one-coset seed needs at least
`((sqrt 5 - 1)/2 - o(1)) * t²` labels outside it. -/
theorem singleton_repair (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (budget : ∀ i,(B i).card≤(t i)^2+1)
    (support : ∀ i,∃ z,∀ b∈B i,(chart _ _ _ (hl i) (jr i) b).2=z)
    (T : (i : ℕ)→Finset (ZMod (2*(h i*j i).val))) (full : ∀ i,T i+T i=univ)
    (big : Tendsto t atTop atTop) (s : ℝ) (below : s<(Real.sqrt 5-1)/2) :
    ∀ᶠ i in atTop,s<((T i\split (D i) (B i)).card:ℝ)/(t i:ℝ)^2 := by
  classical
  choose z located using support
  let e (i) := chart _ _ _ (hl i) (jr i)
  let c (i) := -((t i)^2 • ∑ a∈(D i).image (e i),a)
  let P (i) : Finset (ZMod (j i)) := {z i-(c i).2}
  by_cases neg:s<0
  · exact Eventually.of_forall fun i => neg.trans_le (by positivity)
  refine fresh_labels t h j pos hl jr D B perfect size budget P ?_ T full big 0 s true ?_ ?_ ?_
  · intro i
    change ∀ b∈B i,(e i b).2-(c i).2∈P i
    intro b hb
    change (e i b).2-(c i).2∈{z i-(c i).2}
    rw [show (e i b).2=z i from located i b hb];exact mem_singleton_self _
  · intro _ i; simp [P]
  · simpa only [P,singleton_add_singleton,card_singleton,Nat.cast_one] using singleton_limit t big
  · have root:=Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
    have h1 : 0<(Real.sqrt 5-1)/2+s+1 := by linarith [Real.sqrt_nonneg 5]
    have h2:=mul_pos (sub_pos.mpr below) h1
    change 0+1*s+s^2<1
    nlinarith only [h2,root]

#print axioms singleton_repair

/-- If the number of occupied Baer cosets is little-o of `t`, every full
replacement needs at least `(sqrt 2 - 1 - o(1)) * t²` fresh labels. -/
theorem sparse_repair (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (budget : ∀ i,(B i).card≤(t i)^2+1) (P : (i : ℕ)→Finset (ZMod (j i)))
    (support : ∀ i, let e:=chart _ _ _ (hl i) (jr i)
      ∀ b∈B i,(e b).2-(-((t i)^2 • ∑ z∈(D i).image e,z)).2∈P i)
    (T : (i : ℕ)→Finset (ZMod (2*(h i*j i).val))) (full : ∀ i,T i+T i=univ)
    (big : Tendsto t atTop atTop)
    (sparse : Tendsto (fun i => ((P i).card:ℝ)/(t i:ℝ)) atTop (𝓝 0))
    (s : ℝ) (below : s<Real.sqrt 2-1) :
    ∀ᶠ i in atTop,s<((T i\split (D i) (B i)).card:ℝ)/(t i:ℝ)^2 := by
  by_cases neg:s<0
  · exact Eventually.of_forall fun i => neg.trans_le (by positivity)
  refine fresh_labels t h j pos hl jr D B perfect size budget P support T full big 0 s false
    (by simp) ?_ ?_
  · have sq:=sparse.pow 2
    rw [zero_pow (by decide : 2≠0)] at sq
    apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall ?_) sq
    intro i
    rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show (P i+P i).card≤(P i).card^2 by rw [pow_two];exact card_add_le)
  · have h1 : 0<Real.sqrt 2+1+s := by linarith [Real.sqrt_nonneg 2]
    have h2:=mul_pos (sub_pos.mpr below) h1
    change 0+2*s+s^2<1
    nlinarith only [h2,Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]

#print axioms sparse_repair

private theorem extension_ratio (t k w : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (big : Tendsto t atTop atTop) (cards : ∀ i,2*(t i)^2+w i≤k i) {γ : ℝ}
    (fresh : ∀ a : ℝ,a<γ → ∀ᶠ i in atTop,a<(w i:ℝ)/(t i:ℝ)^2)
    {c : ℝ} (below : c<(2+γ)/Real.sqrt 2) :
    ∀ᶠ i in atTop,c<(k i:ℝ)/Real.sqrt ((2*(h i*j i).val:ℕ):ℝ) := by
  let q (i : ℕ) : ℝ := (t i:ℝ)^2
  let N (i : ℕ) : ℝ := (2*(h i*j i).val:ℕ)
  have qp (i) : 0<q i := sq_pos_of_pos (by exact_mod_cast pos i)
  have rp : 0<Real.sqrt 2 := by positivity
  obtain ⟨v,_,_,_,_⟩:=scalings t pos big
  have lim : Tendsto (fun i => Real.sqrt (N i)/q i) atTop (𝓝 (Real.sqrt 2)) := by
    have raw:=(v.const_mul 2).sqrt
    rw [mul_one] at raw
    apply raw.congr
    intro i
    have eq : N i=2*((q i)^2+q i+1) := by
      dsimp only [N,q,PNat.mul_coe]
      rw [mod_product _ _ _ (hl i) (jr i)]
      push_cast;ring
    rw [eq]
    change Real.sqrt (2*(((q i)^2+q i+1)/(q i)^2))=_
    rw [←mul_div_assoc,Real.sqrt_div (by positivity),Real.sqrt_sq (qp i).le]
  have start := (lt_div_iff₀ rp).mp below
  let a:=(c*Real.sqrt 2-2+γ)/2
  have a0 : a<γ := by dsimp [a];linarith
  have a1 : c<(2+a)/Real.sqrt 2 := (lt_div_iff₀ rp).mpr (by dsimp [a];linarith)
  have cut:=((tendsto_const_nhds (x:=2+a)).div lim rp.ne').eventually_const_lt a1
  filter_upwards [cut,fresh a a0] with i hi hw
  have hwi:= (lt_div_iff₀ (qp i)).mp hw
  have hki : 2*q i+(w i:ℝ)≤k i := by dsimp only [q];exact_mod_cast cards i
  change c<(2+a)/(Real.sqrt (N i)/q i) at hi
  rw [div_div_eq_mul_div] at hi
  exact hi.trans_le (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

private theorem anchor_size {v : ℕ+} (D B : Finset (ZMod v)) {q : ℕ} (hd : D.card=q+1)
    (hb : B.card=q+1) (T : Finset (ZMod (2*v.val))) (sub : split D B⊆T) :
    2*q+(T\split D B).card≤T.card := by
  have c:=card_sdiff_add_card_eq_card sub
  rw [split_card,hd,hb] at c
  omega

/-- Any full superset of the balanced one-coset seed has normalized size
eventually above every constant below `(3 + sqrt 5)/(2 sqrt 2)`. -/
theorem singleton_completion (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (bal : ∀ i,(B i).card=(t i)^2+1)
    (support : ∀ i,∃ z,∀ b∈B i,(chart _ _ _ (hl i) (jr i) b).2=z)
    (T : (i : ℕ)→Finset (ZMod (2*(h i*j i).val))) (full : ∀ i,T i+T i=univ)
    (sub : ∀ i,split (D i) (B i)⊆T i) (big : Tendsto t atTop atTop)
    (c : ℝ) (below : c<(3+Real.sqrt 5)/(2*Real.sqrt 2)) :
    ∀ᶠ i in atTop,c<((T i).card:ℝ)/Real.sqrt ((2*(h i*j i).val:ℕ):ℝ) := by
  apply extension_ratio t (fun i => (T i).card) (fun i => (T i\split (D i) (B i)).card)
    h j pos hl jr big (fun i => anchor_size _ _ (size i) (bal i) _ (sub i)) (γ:=(Real.sqrt 5-1)/2)
  · exact singleton_repair t h j pos hl jr D B perfect size (fun i => (bal i).le) support T full big
  · have eq : (2+(Real.sqrt 5-1)/2)/Real.sqrt 2=(3+Real.sqrt 5)/(2*Real.sqrt 2) := by ring
    rwa [eq]

#print axioms singleton_completion

/-- On any little-o family of occupied Baer cosets, the corresponding
balanced seed has anchored completion coefficient at least `1 + 1/sqrt 2`. -/
theorem sparse_completion (t : ℕ→ℕ) (h j : ℕ→ℕ+) (pos : ∀ i,0<t i)
    (hl : ∀ i,(h i).val=(t i)^2+t i+1) (jr : ∀ i,(j i).val+t i=(t i)^2+1)
    (D B : (i : ℕ)→Finset (ZMod (h i*j i : ℕ+)))
    (perfect : ∀ i,Perfect (D i)) (size : ∀ i,(D i).card=(t i)^2+1)
    (bal : ∀ i,(B i).card=(t i)^2+1) (P : (i : ℕ)→Finset (ZMod (j i)))
    (support : ∀ i, let e:=chart _ _ _ (hl i) (jr i)
      ∀ b∈B i,(e b).2-(-((t i)^2 • ∑ z∈(D i).image e,z)).2∈P i)
    (T : (i : ℕ)→Finset (ZMod (2*(h i*j i).val))) (full : ∀ i,T i+T i=univ)
    (big : Tendsto t atTop atTop)
    (sparse : Tendsto (fun i => ((P i).card:ℝ)/(t i:ℝ)) atTop (𝓝 0))
    (sub : ∀ i,split (D i) (B i)⊆T i) (c : ℝ) (below : c<1+1/Real.sqrt 2) :
    ∀ᶠ i in atTop,c<((T i).card:ℝ)/Real.sqrt ((2*(h i*j i).val:ℕ):ℝ) := by
  apply extension_ratio t (fun i => (T i).card) (fun i => (T i\split (D i) (B i)).card)
    h j pos hl jr big (fun i => anchor_size _ _ (size i) (bal i) _ (sub i)) (γ:=Real.sqrt 2-1)
  · exact sparse_repair t h j pos hl jr D B perfect size (fun i => (bal i).le) P support T full big sparse
  · have eq : (2+(Real.sqrt 2-1))/Real.sqrt 2=1+1/Real.sqrt 2 := by
      field_simp [show Real.sqrt 2≠0 by positivity];ring
    rwa [eq]

#print axioms sparse_completion
end Green33BaerParity
