import Green51OctadFlats
/-! # Large even relations in eleven dimensions -/
open Finset Green50Downsets Green50Sharp Green51TenDimensions Green51PerfectColumns
open scoped Classical Pointwise
namespace Green51MissingLabel
local notation "F" => ZMod 2
local notation "V" => Cube 11

private theorem relation_code (T:Finset V) (even:2∣T.card)
    (free:∀U⊆T,U.card=4 ∨ U.card=6 → syndrome U≠0) (sum:syndrome T=0) :
    ∃C:Submodule F (Cube T.card),2^(T.card-12)≤Fintype.card C ∧
      (fun _ => (1:F))∈C ∧ (∀x:C,2∣(supp x.val).card) ∧
      (∀x:C,x≠0 → 8≤(supp x.val).card) ∧
      ∀x:C,∃U⊆T,U.card=(supp x.val).card ∧ syndrome U=0 := by
  classical
  obtain ⟨P,eval,parity,kernel,_⟩:=Green51SparseDimensions.even_pair_columns T free
  have rank:=P.finrank_range_add_finrank_ker
  have up:=Submodule.finrank_le P.range
  rw [show Module.finrank F (Cube T.card)=T.card by simp [Cube]] at rank
  rw [show Module.finrank F (F×V)=12 by simp [Module.finrank_prod,Cube]] at up
  refine ⟨P.ker,?_,?_,fun x=>parity x.val x.property,?_,?_⟩
  · rw [Module.card_eq_pow_finrank (K:=F),ZMod.card]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · change P (fun _=>1)=0
    have full : supp (fun _:Fin T.card => (1:F))=univ := by ext i; simp [supp]
    rw [eval,full]
    apply Prod.ext
    · simpa only [Prod.fst_sum,Prod.fst_zero,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
        mul_one,ZMod.natCast_eq_zero_iff] using even
    · simp only [Prod.snd_sum,Prod.snd_zero]
      exact (T.equivFin.symm.sum_comp Subtype.val).trans ((sum_attach T id).trans sum)
  · intro x non
    have e:=parity x.val x.property
    by_contra! low
    exact non (Subtype.ext (kernel x.val (by omega) x.property))
  · intro x
    let index : Fin T.card ↪ V := ⟨fun i=>(T.equivFin.symm i).val,
      Subtype.val_injective.comp T.equivFin.symm.injective⟩
    refine ⟨(supp x.val).map index,?_,card_map _,?_⟩
    · rintro a h
      obtain ⟨i,_,rfl⟩:=mem_map.mp h
      exact (T.equivFin.symm i).property
    · have z:= (eval x.val).symm.trans x.property
      change (∑a∈(supp x.val).map index,a)=0
      rw [sum_map]
      change (∑i∈supp x.val,(T.equivFin.symm i).val)=0
      simpa only [Prod.snd_sum,Prod.snd_zero] using congrArg Prod.snd z

private theorem weight_flip {n:ℕ} (x:Cube n) :
    (supp (x+(fun _=>1))).card=n-(supp x).card := by
  have e:supp (x+(fun _=>1))=(supp x)ᶜ := by
    ext i
    rcases (show ∀a:F,a=0 ∨ a=1 from by decide) (x i) with h|h <;>
      simp [supp,h,show (1:F)+1=0 by decide]
  rw [e,card_compl,Fintype.card_fin]

private theorem complement {n:ℕ} (C:Submodule F (Cube n)) (ones:(fun _=>(1:F))∈C)
    (dist:∀x:C,x≠0 → 8≤(supp x.val).card) (x:C) (ne:x.val≠(fun _=>1)) :
    (supp x.val).card+8≤n := by
  let O:C:=⟨_,ones⟩
  have nz:x+O≠0 := by
    intro h
    exact ne (congrArg Subtype.val (add_right_cancel (h.trans (ZModModule.add_self O).symm)))
  have high:=dist (x+O) nz
  change 8≤(supp (x.val+(fun _=>1))).card at high
  rw [weight_flip] at high
  omega

private theorem no_fourteen {T:Finset V} (size:T.card=14)
    (free:∀U⊆T,U.card=4 ∨ U.card=6 → syndrome U≠0) : syndrome T≠0 := by
  intro z
  obtain ⟨C,number,ones,_,dist,_⟩:=relation_code T (by omega) free z
  let O:C:=⟨_,ones⟩
  have sub : (univ:Finset C)⊆{0,O} := by
    intro x _
    by_cases zero:x=0
    · simp [zero]
    by_cases all:x=O
    · simp [all]
    have other:x.val≠(fun _=>1) := fun h=>all (Subtype.ext h)
    have lo:=dist x zero
    have hi:=complement C ones dist x other
    omega
  have small:= (card_le_card sub).trans (card_le_two ..)
  rw [card_univ] at small
  rw [show 2^(T.card-12)=4 by rw [size]; decide] at number
  omega
private theorem antipodal_bound {n:ℕ} (pos:0<n) (C:Submodule F (Cube n))
    (ones:(fun _=>(1:F))∈C) (u:ℤ)
    (bound:∀x:C,x≠0 → x.val≠(fun _=>1) → ((n:ℤ)-2*(supp x.val).card)^2≤u) :
    (n:ℤ)*Fintype.card C ≤ 2*(n:ℤ)^2+((Fintype.card C:ℤ)-2)*u := by
  classical
  let O:C:=⟨_,ones⟩
  have no:O≠0 := by
    intro h
    have e:=congrArg (fun x:C => x.val ⟨0,pos⟩) h
    exact (one_ne_zero (α:=F)) e
  let R:=(univ:Finset C).erase 0
  let S:=R.erase O
  have mem:O∈R := mem_erase.mpr ⟨no,mem_univ _⟩
  have sz₁:=card_erase_add_one (mem_univ (0:C))
  have sz₂:=card_erase_add_one mem
  have sizes:S.card+2=Fintype.card C := by
    change R.card+1=_ at sz₁
    rw [card_univ] at sz₁
    change S.card+1=R.card at sz₂
    omega
  have sz : (S.card:ℤ)+2=Fintype.card C := by exact_mod_cast sizes
  let f (x:C) : ℤ:=((n:ℤ)-2*(supp x.val).card)^2
  have atZero:f 0=(n:ℤ)^2 := by
    simp [f,supp]
  have atOne:f O=(n:ℤ)^2 := by
    simp [f,O,supp];ring
  have a:=sum_erase_add univ f (mem_univ (0:C))
  have b:=sum_erase_add R f mem
  change ∑x∈R,f x+f 0=∑x:C,f x at a
  change ∑x∈S,f x+f O=∑x∈R,f x at b
  rw [atZero] at a
  rw [atOne] at b
  have major:(∑x∈S,f x)≤∑_x∈S,u := by
    apply sum_le_sum
    intro x hx
    obtain ⟨diff,inR⟩:=mem_erase.mp hx
    exact bound x (mem_erase.mp inR).1 (fun h=>diff (Subtype.ext h))
  simp only [sum_const,nsmul_eq_mul] at major
  have moment:=Green51Hadamard.weight_second_moment C
  change _≤∑x:C,f x at moment
  nlinarith [congrArg (fun z:ℤ=>z*u) sz]

/-- A set avoiding zero sums on four and six labels cannot itself be a
zero-sum set of size fourteen, eighteen, twenty or twenty-two in eleven dimensions. -/
theorem forbidden {T:Finset V} (size:T.card=14 ∨ T.card=18 ∨ T.card=20 ∨ T.card=22)
    (free:∀U⊆T,U.card=4 ∨ U.card=6 → syndrome U≠0) :
    syndrome T≠0 := by
  rcases size with four|size
  · exact no_fourteen four free
  intro sum
  obtain ⟨C,number,ones,even,dist,subsets⟩:=relation_code T (by omega) free sum
  have skip (x:C) : (supp x.val).card≠14 := by
    intro w
    obtain ⟨U,sub,sz,zero⟩:=subsets x
    exact no_fourteen (sz.trans w) (fun R r => free R (r.trans sub)) zero
  have cap (x:C) (non:x≠0) (ne:x.val≠(fun _=>1)) :
      ((T.card:ℤ)-2*(supp x.val).card)^2≤(if T.card=20 then 16 else 4) := by
    have lo:=dist x non
    have hi:=complement C ones dist x ne
    have ev:=even x
    have skip1:=skip x
    let O:C:=⟨_,ones⟩
    have skip2:=skip (x+O)
    change (supp (x.val+(fun _=>1))).card≠14 at skip2
    rw [weight_flip] at skip2
    generalize hw:(supp x.val).card=w at *
    rcases size with n|n|n
    · simp only [n] at hi ⊢
      have cases:w=8 ∨ w=10:=by omega
      rcases cases with rfl|rfl <;> decide
    · simp only [n] at hi ⊢
      have cases:w=8 ∨ w=10 ∨ w=12:=by omega
      rcases cases with rfl|rfl|rfl <;> decide
    · simp only [n] at hi skip2 ⊢
      have cases:w=10 ∨ w=12:=by omega
      rcases cases with rfl|rfl <;> decide
  have total:=antipodal_bound (by omega) C ones _ cap
  generalize hc:Fintype.card C=m at total number
  rcases size with n|n|n <;> rw [n] at number total <;> norm_num at total number <;> omega

/-- The sum of twenty-three labels is the unique extra label preserving
linear three-space avoidance. -/
theorem extension {A:Finset V} (size:A.card=23) (avoid:¬FlatAt A 0) :
    syndrome A∉A ∧ ¬FlatAt (insert (syndrome A) A) 0 ∧
    ∀v:V,v∉A → ¬FlatAt (insert v A) 0 → v=syndrome A := by
  classical
  let p:=syndrome A
  have free (U:Finset V) (sub:U⊆A) (sz:U.card=4 ∨ U.card=6) : syndrome U≠0 := fun z=>
    avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨U,sub,sz,z⟩))
  have missing (U:Finset V) (sub:U⊆A) (sz:U.card=1 ∨ U.card=3 ∨ U.card=5) : syndrome U≠p := by
    intro eq
    have count: (A\U).card=A.card-U.card := card_sdiff_of_subset sub
    have avoidSum:=forbidden (T:=A\U) (by omega)
      (fun R r=>free R (r.trans sdiff_subset))
    have total:=sum_sdiff sub (f:=id)
    change syndrome (A\U)+syndrome U=p at total
    rw [eq] at total
    exact avoidSum (add_right_cancel (total.trans (zero_add p).symm))
  have fresh:p∉A := fun hp=>missing {p} (singleton_subset_iff.mpr hp) (by simp)
    (by simp [syndrome])
  have count:(insert p A).card=24 := by rw [card_insert_of_notMem fresh,size]
  refine ⟨fresh,?_,?_⟩
  · intro hasFlat
    obtain ⟨T,sub,sz,total⟩:=(Green51SparseDimensions.linear_three_iff (insert p A) (by omega)).mp
      ((flat_zero _).mp hasFlat)
    by_cases hit:p∈T
    · have ua:T.erase p⊆A := by
        intro x hx
        exact (mem_insert.mp (sub (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1
      have cs:=card_erase_add_one hit
      have sum:=T.add_sum_erase id hit
      change p+syndrome (T.erase p)=syndrome T at sum
      exact missing (T.erase p) ua (by omega)
        (add_left_cancel (sum.trans (total.trans (ZModModule.add_self p).symm)))
    · have ta:T⊆A := by
        intro x hx
        exact (mem_insert.mp (sub hx)).resolve_left (fun h=>hit (h ▸ hx))
      exact free T ta sz total
  · intro v nv good
    have total:=full_sum (A:=insert v A) (by rw [card_insert_of_notMem nv,size]) good
    change (∑x∈insert v A,x)=0 at total
    rw [sum_insert nv] at total
    exact add_right_cancel (total.trans (ZModModule.add_self (syndrome A)).symm)

end Green51MissingLabel

#print axioms Green51MissingLabel.forbidden
#print axioms Green51MissingLabel.extension
