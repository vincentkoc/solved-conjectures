import Green33OddSlideCoordinates
/-! Translating entire fibres of an additive quotient. -/
open Finset
open scoped Pointwise
namespace Green33LayerSlides
variable {H C:Type*} [AddCommGroup H] [AddCommGroup C] [DecidableEq H] [DecidableEq C]
def layer (π:H→+C) (A:Finset H) (c:C) := A.filter fun a => π a=c
def displaced (π:H→+C) (A:Finset H) (h:C→π.ker) := A.image fun a => a+(h (π a):H)
theorem displaced_sum (π:H→+C) (A:Finset H) (h:C→π.ker) (t:H) (x:π.ker) :
    t+(x:H)∈displaced π A h + displaced π A h ↔
      ∃ i j:C,i+j=π t ∧ t+((x-(h i+h j):π.ker):H)∈layer π A i + layer π A j := by
  constructor
  · intro hit
    obtain ⟨_,ha,_,hb,eq⟩:=mem_add.mp hit
    obtain ⟨a,ha',rfl⟩:=mem_image.mp ha
    obtain ⟨b,hb',rfl⟩:=mem_image.mp hb
    have e:=congrArg π eq
    simp only [map_add,AddMonoidHom.mem_ker.mp (h _).property,AddMonoidHom.mem_ker.mp x.property,add_zero] at e
    refine ⟨π a,π b,e,mem_add.mpr ⟨a,mem_filter.mpr ⟨ha',rfl⟩,b,mem_filter.mpr ⟨hb',rfl⟩,?_⟩⟩
    simp only [AddSubgroup.coe_sub,AddSubgroup.coe_add]
    calc
      a+b = ((a+(h (π a):H))+(b+(h (π b):H)))-((h (π a):H)+(h (π b):H)) := by abel
      _ = _ := by rw [eq];abel
  · rintro ⟨i,j,_,hit⟩
    obtain ⟨a,ha,b,hb,eq⟩:=mem_add.mp hit
    obtain ⟨ha',ai⟩:=mem_filter.mp ha
    obtain ⟨hb',bj⟩:=mem_filter.mp hb
    refine mem_add.mpr ⟨_,mem_image_of_mem _ ha',_,mem_image_of_mem _ hb',?_⟩
    rw [ai,bj]
    simp only [AddSubgroup.coe_sub,AddSubgroup.coe_add] at eq
    calc
      _ = (a+b)+((h i:H)+(h j:H)) := by abel
      _ = _ := by rw [eq];abel
#print axioms displaced_sum

omit [DecidableEq C] in
theorem displaced_card (π:H→+C) (A:Finset H) (h:C→π.ker) : (displaced π A h).card=A.card := by
  apply card_image_of_injOn
  intro a _ b _ eq
  have label:=congrArg π eq
  simp only [map_add,AddMonoidHom.mem_ker.mp (h _).property,add_zero] at label
  change a+(h (π a):H)=b+(h (π b):H) at eq
  rw [label] at eq
  exact add_right_cancel eq
#print axioms displaced_card

variable [Fintype H]
def rowSupport {m:ℕ+} (π:H→+ZMod m) (A:Finset H) (t:H) (i j:ZMod m) : Finset π.ker :=
  univ.filter fun z => t+(z:H)∈layer π A i+layer π A j

/-- Missing entries in a complete quotient row have the product count
predicted by independent translates, even when the kernel has two-torsion. -/
theorem odd_row_misses {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H) (c:ZMod m) (t:H)
    (row:π t=c+c) :
    (univ.filter fun p : π.ker×(ZMod m→π.ker) =>
      t+(p.1:H)∉displaced π A p.2+displaced π A p.2).card =
      (Fintype.card π.ker)^((positiveHalf m).card+1) * (rowSupport π A t c c)ᶜ.card *
        ∏ j:positiveHalf m,(rowSupport π A t (c+j.val) (c-j.val))ᶜ.card := by
  classical
  let e:=labelEquiv odd c
  let D:Finset π.ker:=(rowSupport π A t c c)ᶜ
  let M (j:positiveHalf m):Finset π.ker:=(rowSupport π A t (c+j.val) (c-j.val))ᶜ
  have law:=quotient_row_count π.ker (positiveHalf m) e D M
  rw [Fintype.card_coe] at law
  apply Eq.trans _ law
  congr 1
  ext p
  simp only [mem_filter,mem_univ,true_and]
  let h:=p.2
  let x:=p.1
  let P (i j:ZMod m) := t+((x-(h i+h j):π.ker):H)∈layer π A i+layer π A j
  have sym (i j:ZMod m): P i j↔P j i := by
    simp only [P];rw [add_comm (h i) (h j),add_comm (layer π A i) (layer π A j)]
  have hit : t+(x:H)∈displaced π A h+displaced π A h ↔ P c c ∨ ∃ j:positiveHalf m,P (c+j.val) (c-j.val) := by
    rw [displaced_sum,row];exact row_cases odd c P sym
  rw [show t+(p.1:H)∉displaced π A p.2+displaced π A p.2 ↔
      ¬(P c c ∨ ∃ j:positiveHalf m,P (c+j.val) (c-j.val)) from not_congr hit]
  simp only [not_or,not_exists,D,M,mem_compl,rowSupport,mem_filter,mem_univ,true_and]
  have base : e (.inl ())=c := by change c+0=c;exact add_zero _
  simp only [base]
  change (¬P c c ∧ _) ↔ (¬P c c ∧ _)
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  have plus : e (.inr (.inl j))=c+j.val := rfl
  have minus : e (.inr (.inr j))=c-j.val := by change c+-j.val=c-j.val;abel
  rw [plus,minus]
#print axioms odd_row_misses


theorem rowSupport_card {m:ℕ+} (π:H→+ZMod m) (A:Finset H) (t:H) (i j:ZMod m)
    (row:π t=i+j) : (rowSupport π A t i j).card=(layer π A i+layer π A j).card := by
  apply card_bij (fun (z:π.ker) _ => t+(z:H))
  · intro z hz;exact (mem_filter.mp hz).2
  · intro z _ w _ eq;exact Subtype.ext (add_left_cancel eq)
  · intro a ha
    have image:π a=i+j := by
      obtain ⟨b,hb,d,hd,rfl⟩:=mem_add.mp ha
      rw [map_add,(mem_filter.mp hb).2,(mem_filter.mp hd).2]
    let z:π.ker:=⟨a-t,by rw [AddMonoidHom.mem_ker,map_sub,image,row,sub_self]⟩
    have eq:t+(z:H)=a := by dsimp [z];abel
    exact ⟨z,mem_filter.mpr ⟨mem_univ _,eq ▸ ha⟩,eq⟩

/-- Every section of the quotient identifies its cosets with copies of the
kernel, with no homomorphism requirement on the section. -/
def sectionCoordinates (π:H→+C) (s:C→H) (right:Function.RightInverse s π) : (C×π.ker) ≃ H where
  toFun p := s p.1+(p.2:H)
  invFun a := (π a,⟨a-s (π a),by simp [right _]⟩)
  left_inv := by
    rintro ⟨c,z⟩
    have eq:π (s c+(z:H))=c := by rw [map_add,right,AddMonoidHom.mem_ker.mp z.property,add_zero]
    apply Prod.ext
    · exact eq
    · apply Subtype.ext
      change s c+z.val-s (π (s c+z.val))=z.val
      rw [eq];abel
  right_inv := by intro a;change s (π a)+(a-s (π a))=a;abel

noncomputable def doubleEquiv {m:ℕ+} (odd:Odd m.val) : ZMod m ≃ ZMod m := by
  let f (x:ZMod m) := x+x
  have inj:Function.Injective f := by
    intro a b eq
    have z:(a-b)+(a-b)=0 := by calc
      _ = f a-f b := by dsimp [f];abel
      _ = 0 := by rw [eq,sub_self]
    exact sub_eq_zero.mp ((ZMod.add_self_eq_zero_iff_eq_zero odd).mp z)
  exact Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
#print axioms rowSupport_card
#print axioms sectionCoordinates


/-- Fraction of unwitnessed targets in the physical row of t, averaged
over all independent choices of shifts for the quotient layers. -/
noncomputable def rowMiss {m:ℕ+} (π:H→+ZMod m) (A:Finset H) (t:H) : ℝ :=
  ((univ.filter fun p : π.ker×(ZMod m→π.ker) =>
    t+(p.1:H)∉displaced π A p.2+displaced π A p.2).card:ℝ) /
    ((Fintype.card π.ker:ℝ)*(Fintype.card π.ker:ℝ)^m.val)

theorem rowMiss_product {m:ℕ+} (odd:Odd m.val) (π:H→+ZMod m) (A:Finset H)
    (c:ZMod m) (t:H) (row:π t=c+c) :
    rowMiss π A t=(1-((layer π A c+layer π A c).card:ℝ)/Fintype.card π.ker)*
      ∏ j:positiveHalf m,(1-((layer π A (c+j.val)+layer π A (c-j.val)).card:ℝ)/Fintype.card π.ker) := by
  classical
  let k:ℝ:=Fintype.card π.ker
  let r:ℕ:=(positiveHalf m).card
  have pos:0<k:=by dsimp [k];positivity
  have comp (i j:ZMod m) (sum:π t=i+j) :
      ((rowSupport π A t i j)ᶜ.card:ℝ)=k-((layer π A i+layer π A j).card:ℝ) := by
    rw [card_compl,Nat.cast_sub (card_le_univ _),rowSupport_card _ _ _ _ _ sum]
  have op (i j:ZMod m) :
      1-((layer π A i+layer π A j).card:ℝ)/k=(k-((layer π A i+layer π A j).card:ℝ))/k := by
    field_simp [pos.ne']
  let b (j:positiveHalf m):ℝ := k-((layer π A (c+j.val)+layer π A (c-j.val)).card:ℝ)
  have pairs:((∏ j:positiveHalf m,(rowSupport π A t (c+j.val) (c-j.val))ᶜ.card:ℕ):ℝ)=∏ j,b j := by
    push_cast
    apply prod_congr rfl
    intro j _
    exact comp _ _ (by rw [row];abel)
  unfold rowMiss
  rw [odd_row_misses odd π A c t row,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,pairs,comp c c row]
  change k^(r+1)*(k-_)*(∏ j,b j)/(k*k^m.val)=(1-_/k)*∏ j:positiveHalf m,(1-_/k)
  simp_rw [op]
  rw [prod_div_distrib]
  simp only [prod_const,card_univ,Fintype.card_coe]
  change _=(_/k)*((∏ j,b j)/k^r)
  have half:m.val=(r+1)+r:=by have h:=half_count odd;dsimp [r];omega
  have power:k^m.val=k^(r+1)*k^r:=by rw [half,pow_add]
  rw [power]
  field_simp [pos.ne']
#print axioms rowMiss_product

end Green33LayerSlides
