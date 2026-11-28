import Green51ShortenedColumns
import Mathlib.InformationTheory.Hamming

/-! # Binary linear codes of length 26 and minimum distance eight

A weight-ten word bounds the dimension by puncturing on its support. In the
remaining case the code is doubly even, and duality excludes dimension 13.
The last step removes the assumption that every word has even weight. -/

open Finset Green50Downsets Green50Sharp
open scoped Classical
namespace Green51TwelveResidual
local notation "F" => ZMod 2

private theorem residual_weight {n:ℕ} (x u:Cube n) :
    (supp x).card+(supp (x+u)).card=(supp u).card+2*(supp x\supp u).card := by
  have a:=Green51AffineMatchings.weight_sum x u
  have b:=card_sdiff_add_card_inter (supp x) (supp u)
  omega

/-- If a word has no decomposition into two nonzero words with disjoint
supports, its outside restriction has a one-dimensional kernel. -/
theorem residual_rank {n:ℕ} (C:Submodule F (Cube n)) (u:C) (nz:u≠0)
    (indecomp:∀x:C,x≠0 → x≠u → supp x.val⊆supp u.val → False) :
    let T:Finset (Fin n):=(supp u.val)ᶜ
    let R:C →ₗ[F] (T→F):=LinearMap.pi fun i:T=>(LinearMap.proj i.val).comp C.subtype
    Module.finrank F R.ker=1 := by
  classical
  dsimp only
  let T:Finset (Fin n):=(supp u.val)ᶜ
  let R:C→ₗ[F] (T→F):=LinearMap.pi fun i:T=>(LinearMap.proj i.val).comp C.subtype
  change Module.finrank F R.ker=1
  have inc (x:R.ker) : supp x.val.val⊆supp u.val := by
    intro i hi
    by_contra off
    have val:=congrFun (show R x.val=0 from x.property) (⟨i,mem_compl.mpr off⟩:T)
    exact (mem_filter.mp hi).2 val
  have ru:R u=0 := by
    funext i
    change u.val i.val=0
    simpa [T,supp] using i.property
  let U:R.ker:=⟨u,ru⟩
  have set:(univ:Finset R.ker)={0,U} := by
    ext x;simp only [mem_univ,mem_insert,mem_singleton,true_iff]
    by_contra! h
    exact indecomp x.val (fun w=>h.1 (Subtype.ext w)) (fun w=>h.2 (Subtype.ext w)) (inc x)
  have num:=Module.card_eq_pow_finrank (K:=F) (V:=R.ker)
  rw [←card_univ,set,card_pair (by intro h;exact nz (congrArg Subtype.val h).symm),ZMod.card] at num
  exact Nat.pow_right_injective (by decide : 2≤2) (show 2^Module.finrank F R.ker=2^1 from num.symm)

/-- A weight-fourteen word at redundancy at most thirteen forces a word of
weight ten in an even distance-eight code with two outside positions. -/
theorem fourteen_forces_ten {n:ℕ} (C:Submodule F (Cube n)) (large:16≤n)
    (rank:n-13≤Module.finrank F C) (dist:∀x:C,x≠0 → 8≤(supp x.val).card)
    (even:∀x:C,2∣(supp x.val).card) (u:C) (w:(supp u.val).card=14) :
    ∃x:C,(supp x.val).card=10 := by
  classical
  by_contra! noten
  have nz:u≠0:=fun z=>by simp [z,supp] at w
  have trivial:=residual_rank C u nz (by
    intro x nx ne sub
    have ny:x+u≠0:=fun eq=>ne (add_right_cancel (eq.trans (ZModModule.add_self u).symm))
    have a:=dist x nx
    have b:=dist (x+u) ny
    have sum:=residual_weight x.val u.val
    rw [sdiff_eq_empty_iff_subset.mpr sub,card_empty,w] at sum
    change 8≤(supp (x.val+u.val)).card at b
    omega)
  let T:Finset (Fin n):=(supp u.val)ᶜ
  let R:C→ₗ[F] (T→F):=LinearMap.pi fun i:T=>(LinearMap.proj i.val).comp C.subtype
  change Module.finrank F R.ker=1 at trivial
  have count:T.card=n-14:=by dsimp [T];rw [card_compl,Fintype.card_fin,w]
  have dim:Module.finrank F (T→F)=n-14:=by simpa using count
  have eq:=R.finrank_range_add_finrank_ker
  have upto:=Submodule.finrank_le R.range
  rw [dim] at upto
  have full:R.range=⊤:=Submodule.eq_top_of_finrank_eq (by rw [dim];omega)
  obtain ⟨S,st,ss⟩:=exists_subset_card_eq (s:=T) (show 2≤T.card by omega)
  obtain ⟨x,hx⟩:=LinearMap.range_eq_top.mp full (fun i:T=>if i.val∈S then 1 else 0)
  have outside:supp x.val\supp u.val=S:=by
    ext i
    by_cases t:i∈T
    · have e:=congrFun hx (⟨i,t⟩:T)
      change x.val i=(if i∈S then 1 else 0) at e
      have no:i∉supp u.val:=mem_compl.mp t
      have uz:u.val i=0:=by simpa [supp] using no
      simp [supp,e,uz]
    · have yes:i∈supp u.val:=by simpa [T] using t
      have no:i∉S:=fun h=>t (st h)
      simp [yes,no]
  have sum:=residual_weight x.val u.val
  rw [w,outside,ss] at sum
  have nx:x≠0:=by
    intro z
    have ex:supp x.val=∅:=by simp [z,supp]
    rw [ex,empty_sdiff] at outside
    simp [←outside] at ss
  have ny:x+u≠0:=by
    intro z
    have e:x=u:=add_right_cancel (z.trans (ZModModule.add_self u).symm)
    rw [e,sdiff_self] at outside
    simp [←outside] at ss
  have a:=dist x nx
  have b:=dist (x+u) ny
  have ea:=even x
  have eb:=even (x+u)
  have da:=noten x
  have db:=noten (x+u)
  change 8≤(supp (x.val+u.val)).card at b
  change 2∣(supp (x.val+u.val)).card at eb
  change (supp (x.val+u.val)).card≠10 at db
  omega
/-- Above weight fourteen the outside restriction must kill another
independent word. This splits the original support between two nonzero words. -/
theorem split_large {n:ℕ} (C:Submodule F (Cube n)) (rank:n-13≤Module.finrank F C)
    (u:C) (large:14<(supp u.val).card) :
    ∃ x y:C,x≠0 ∧ y≠0 ∧ (supp x.val).card+(supp y.val).card=(supp u.val).card := by
  classical
  have nz:u≠0:=fun z=>by simp [z,supp] at large
  by_contra! absent
  have trivial:=residual_rank C u nz (by
    intro x nx ne sub
    have ny:x+u≠0:=fun eq=>ne (add_right_cancel (eq.trans (ZModModule.add_self u).symm))
    apply absent x (x+u) nx ny
    have eq:=residual_weight x.val u.val
    change (supp x.val).card+(supp (x.val+u.val)).card=(supp u.val).card
    simpa only [sdiff_eq_empty_iff_subset.mpr sub,card_empty,mul_zero,add_zero] using eq)
  let T:Finset (Fin n):=(supp u.val)ᶜ
  let R:C→ₗ[F] (T→F):=LinearMap.pi fun i:T=>(LinearMap.proj i.val).comp C.subtype
  change Module.finrank F R.ker=1 at trivial
  have add:=R.finrank_range_add_finrank_ker
  have up:=Submodule.finrank_le R.range
  have dim:Module.finrank F (T→F)=n-(supp u.val).card:=by simp [T]
  have bound: (supp u.val).card≤n := (supp u.val).card_le_univ.trans_eq (by simp)
  rw [dim] at up
  omega

/-- For even distance-eight codes of length at most 26 and redundancy
at most 13, exclusion of weight ten forces all weights to be multiples of four. -/
theorem four_of_no_ten {n:ℕ} (C:Submodule F (Cube n)) (lo:16≤n) (hi:n≤26)
    (rank:n-13≤Module.finrank F C) (dist:∀x:C,x≠0 → 8≤(supp x.val).card)
    (even:∀x:C,2∣(supp x.val).card) (ten:∀x:C,(supp x.val).card≠10) :
    ∀x:C,4∣(supp x.val).card := by
  have fourteen (u:C):(supp u.val).card≠14:=fun w=>by
    obtain ⟨x,h⟩:=fourteen_forces_ten C lo rank dist even u w
    exact ten x h
  have split (u:C) (big:14<(supp u.val).card) := split_large C rank u big
  have eighteen (u:C):(supp u.val).card≠18:=by
    intro w
    obtain ⟨x,y,hx,hy,eq⟩:=split u (by omega)
    have dx:=dist x hx;have dy:=dist y hy;have ex:=even x;have ey:=even y
    have tx:=ten x;have ty:=ten y;omega
  have twentytwo (u:C):(supp u.val).card≠22:=by
    intro w
    obtain ⟨x,y,hx,hy,eq⟩:=split u (by omega)
    have dx:=dist x hx;have dy:=dist y hy;have ex:=even x;have ey:=even y
    have tx:=ten x;have ty:=ten y;have fx:=fourteen x;have fy:=fourteen y;omega
  have twentysix (u:C):(supp u.val).card≠26:=by
    intro w
    obtain ⟨x,y,hx,hy,eq⟩:=split u (by omega)
    have dx:=dist x hx;have dy:=dist y hy;have ex:=even x;have ey:=even y
    have tx:=ten x;have ty:=ten y;have fx:=fourteen x;have fy:=fourteen y
    have ax:=eighteen x;have ay:=eighteen y;omega
  intro x
  by_cases z:x=0
  · simp [z,supp]
  have d:=dist x z
  have e:=even x;have t:=ten x;have f:=fourteen x;have a:=eighteen x;have b:=twentytwo x;have c:=twentysix x
  have bound: (supp x.val).card≤n := (supp x.val).card_le_univ.trans_eq (by simp)
  omega

private theorem unit_packing {I:Type*} [Fintype I] [DecidableEq I] (D:Submodule F (I→F))
    (dist:∀x:D,x≠0 → 3≤hammingNorm x.val) :
    Nat.card D*(Fintype.card I+1)≤2^Fintype.card I := by
  classical
  rw [Nat.card_eq_fintype_card]
  let err : Option I → I→F := fun o=>o.elim 0 (fun i=>Pi.single i 1)
  have near (x:I→F) (o:Option I) : hammingDist x (x+err o)≤1 := by
    rw [hammingDist_eq_hammingNorm,neg_add_cancel_left]
    cases o with
    | none => simp [err]
    | some i =>
      have eq:(univ.filter fun j=>(Pi.single i (1:F):I→F) j≠0)={i} := by ext; simp [Pi.single_apply]
      change (univ.filter fun j=>(Pi.single i (1:F):I→F) j≠0).card≤1
      rw [eq,card_singleton]
  have inj:Function.Injective err:=by
    intro a b eq
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some i => simpa [err] using congrFun eq i
    | some i =>
      cases b with
      | none => simpa [err] using congrFun eq i
      | some j =>
        by_contra ne
        have ij:i≠j:=fun e=>ne (congrArg some e)
        simpa [err,Pi.single_apply,ij] using congrFun eq i
  let f:D×Option I→I→F:=fun a=>a.1.val+err a.2
  have fi:Function.Injective f:=by
    rintro ⟨x,a⟩ ⟨y,b⟩ eq
    change x.val+err a=y.val+err b at eq
    have same:x=y:=by
      by_contra ne
      have nz:-x+y≠0:=fun e=>ne (neg_add_eq_zero.mp e)
      have lower:=dist _ nz
      have upper:=hammingDist_triangle x.val (x.val+err a) y.val
      rw [hammingDist_comm (x.val+err a) y.val,eq] at upper
      have a':=near x.val a;rw [eq] at a'
      have b':=near y.val b
      rw [hammingDist_eq_hammingNorm x.val y.val] at upper
      change 3≤hammingNorm (-x.val+y.val) at lower
      omega
    subst y
    exact Prod.ext rfl (inj (add_left_cancel eq))
  simpa [Fintype.card_prod,Fintype.card_option,Fintype.card_fun,ZMod.card] using Fintype.card_le_of_injective f fi

/-- Restriction off a short codeword preserves all but one dimension and leaves
a code of minimum distance at least three, to which the Hamming bound applies. -/
theorem short_packing {n d k : ℕ} (C : Submodule F (Cube n))
    (dist : ∀x:C,x≠0 → d≤(supp x.val).card) (u:C) (w:(supp u.val).card=k)
    (non : 0<k) (short : k+5≤2*d) :
    2^(Module.finrank F C-1)*(n-k+1)≤2^(n-k) := by
  classical
  have nz:u≠0:=fun e=>by simp [e,supp] at w;omega
  let T:Finset (Fin n):=(supp u.val)ᶜ
  let R:C→ₗ[F] (T→F):=LinearMap.pi fun i:T=>(LinearMap.proj i.val).comp C.subtype
  have count:T.card=n-k:=by dsimp [T];rw [card_compl,Fintype.card_fin,w]
  have ru:R u=0:=by funext i;change u.val i.val=0;simpa [T,supp] using i.property
  have ker:Module.finrank F R.ker=1:=residual_rank C u nz (by
    intro x nx ne sub
    have ny:x+u≠0:=fun eq=>ne (add_right_cancel (eq.trans (ZModModule.add_self u).symm))
    have a:=dist x nx
    have b:=dist (x+u) ny
    have sum:=residual_weight x.val u.val
    rw [sdiff_eq_empty_iff_subset.mpr sub,card_empty,w] at sum
    change d≤(supp (x.val+u.val)).card at b
    omega)
  have outside (x:C) : hammingNorm (R x)=(supp x.val\supp u.val).card:=by
    apply card_bij fun i _=>i.val
    · intro i hi
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩,mem_compl.mp i.property⟩
    · intro i _ j _ eq;exact Subtype.ext eq
    · intro j hj
      obtain ⟨hit,miss⟩:=mem_sdiff.mp hj
      exact ⟨⟨j,mem_compl.mpr miss⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hit).2⟩,rfl⟩
  have bound:=unit_packing R.range (by
    rintro ⟨_,⟨x,rfl⟩⟩ ne
    have nz':R x≠0:=fun eq=>ne (Subtype.ext eq)
    have nx:x≠0:=fun z=>nz' (by rw [z,map_zero])
    have ny:x+u≠0:=fun eq=>nz' (by rwa [add_right_cancel (eq.trans (ZModModule.add_self u).symm)])
    have a:=dist x nx
    have b:=dist (x+u) ny
    change d≤(supp (x.val+u.val)).card at b
    have sum:=residual_weight x.val u.val
    rw [←outside x,w] at sum
    change 3≤hammingNorm (R x)
    omega)
  have dim:=R.finrank_range_add_finrank_ker
  rw [ker] at dim
  rw [Module.natCard_eq_pow_finrank (K:=F),Nat.card_zmod,
    show Module.finrank F R.range=Module.finrank F C-1 by omega,Fintype.card_coe,count] at bound
  exact bound

/-- A ten-word leaves a single-error-correcting code on the outside
coordinates, with dimension one less than the original code. -/
theorem ten_packing {n:ℕ} (C:Submodule F (Cube n))
    (dist:∀x:C,x≠0 → 8≤(supp x.val).card) (u:C) (w:(supp u.val).card=10) :
    2^(Module.finrank F C-1)*(n-10+1)≤2^(n-10) :=
  short_packing C dist u w (by decide) (by decide)

/-- An even binary code of length 26 and minimum distance eight has
dimension at most twelve. -/
theorem twenty_six (C:Submodule F (Cube 26)) (dist:∀x:C,x≠0 → 8≤(supp x.val).card)
    (even:∀x:C,2∣(supp x.val).card) : Module.finrank F C≤12 := by
  classical
  by_contra! large
  have rank:26-13≤Module.finrank F C:=by omega
  have mult:=four_of_no_ten C (by decide) (by decide) rank dist even (by
    intro x w
    have h:=ten_packing C dist x w
    have exp:2^12≤2^(Module.finrank F C-1):=Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at h exp
    omega)
  let I:Cube 26:=fun _=>1
  have wi:(supp I).card=26 := by simp [I,supp]
  have dual:I∈Green51WeightTransform.dualWords C:=by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro c
    have term (i:Fin 26) : I i*c.val i=if i∈supp c.val then (1:F) else 0 := by
      rcases (show ∀ a:F,a=0 ∨ a=1 by decide) (c.val i) with e|e <;> simp [I,supp,e]
    rw [dotProduct]
    simp only [term,sum_boole,filter_mem_eq_inter,univ_inter]
    exact (ZMod.natCast_eq_zero_iff ..).mpr (even c)
  have absent:I∉C:=fun h=>by
    have m:=mult (⟨I,h⟩:C)
    change 4∣(supp I).card at m
    rw [wi] at m;omega
  let E:=univ.map (⟨Subtype.val,Subtype.val_injective⟩:C ↪ Cube 26)
  have inc:E⊆Green51WeightTransform.dualWords C:=by
    intro x hx
    obtain ⟨c,_,rfl⟩:=mem_map.mp hx
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro y
    apply (Green51ShortenedColumns.weight_mod_four c.val y.val (mult y)).mp
    change (supp (c+y).val).card%4=(supp c.val).card%4
    exact (Nat.mod_eq_zero_of_dvd (mult _)).trans (Nat.mod_eq_zero_of_dvd (mult _)).symm
  have strict:E⊂Green51WeightTransform.dualWords C:=lt_of_le_of_ne inc (fun eq=>by
    have h:I∈E:=eq ▸ dual
    obtain ⟨c,_,e⟩:=mem_map.mp h
    exact absent (e ▸ c.property))
  have inequality:E.card<(Green51WeightTransform.dualWords C).card:=card_lt_card strict
  rw [card_map,card_univ] at inequality
  have prod:=Green51WeightTransform.macwilliams C (1:ℤ)
  have term (c:C) : ((1:ℤ)+1)^(26-(supp c.val).card)*(1-1)^(supp c.val).card=
      if c=0 then (2:ℤ)^26 else 0 := by
    by_cases z:c=0
    · simp [z,supp]
    · have d:=dist c z
      simp [z,show (supp c.val).card≠0 by omega]
  simp_rw [term] at prod
  have total:(Fintype.card C:ℤ)*(Green51WeightTransform.dualWords C).card=2^26:=by simpa using prod
  have card:=Module.card_eq_pow_finrank (K:=F) (V:=C)
  rw [ZMod.card] at card
  have min:8192≤Fintype.card C:=by rw [card];exact Nat.pow_le_pow_right (by decide : 0<2) large
  have min' : (8192:ℤ)≤Fintype.card C:=by exact_mod_cast min
  have greater : (Fintype.card C:ℤ)<(Green51WeightTransform.dualWords C).card:=by exact_mod_cast inequality
  nlinarith

end Green51TwelveResidual
#print axioms Green51TwelveResidual.fourteen_forces_ten

#print axioms Green51TwelveResidual.four_of_no_ten

#print axioms Green51TwelveResidual.twenty_six

namespace Green51TwelveResidual
open Green51ShortenedColumns
local notation "F" => ZMod 2

/-- Replacing one coordinate by the parity of the others turns any binary
linear code of even minimum distance at least two into an even code with
the same dimension and the same lower bound on distance. -/
theorem even_replacement {n d:ℕ} (i:Fin n) (C:Submodule F (Cube n)) (lo:2≤d) (de:2∣d)
    (dist:∀x:C,x≠0 → d≤(supp x.val).card) :
    ∃D:Submodule F (Cube n),Module.finrank F D=Module.finrank F C ∧
      (∀y:D,2∣(supp y.val).card) ∧ (∀y:D,y≠0 → d≤(supp y.val).card) := by
  classical
  let S:Cube n→ₗ[F] F:= ∑j:Fin n,LinearMap.proj j
  have ev (x:Cube n) : S x=∑j,x j:=by simp [S,LinearMap.sum_apply]
  have bits (x:Cube n):S x=((supp x).card:F) := by
    have t (j:Fin n):x j=if j∈supp x then (1:F) else 0:=by
      rcases (show ∀a:F,a=0 ∨ a=1 by decide) (x j) with e|e <;> simp [e,supp]
    rw [ev];simp only [t,sum_boole,filter_mem_eq_inter,univ_inter]
  let Q:Cube n→ₗ[F] Cube n:=LinearMap.pi fun j=>if j=i then LinearMap.proj j+S else LinearMap.proj j
  have eval (x:Cube n):Q x=x+Pi.single i (S x):=by
    funext j;by_cases h:j=i <;> simp [Q,h]
  have even (x:Cube n):2∣(supp (Q x)).card:=by
    apply (ZMod.natCast_eq_zero_iff ..).mp;rw [←bits,eval,map_add,ev (Pi.single i (S x))]
    simp [Pi.single_apply,ZModModule.add_self]
  have loss (x:Cube n):(supp x).card≤(supp (Q x)).card+1:=by
    have sub:supp x⊆insert i (supp (Q x)):=by
      intro j hj;by_cases h:j=i
      · exact h ▸ mem_insert_self ..
      · apply mem_insert_of_mem;simpa [eval,supp,Pi.single_apply,h] using hj
    exact (card_le_card sub).trans (card_insert_le ..)
  let L:=Q.comp C.subtype
  have inj:Function.Injective L:=by
    apply (injective_iff_map_eq_zero L).mpr
    intro x z;by_contra ne
    have d':=dist x ne
    have h:=loss x.val
    change Q x.val=0 at z
    rw [z] at h
    rw [show (supp (0:Cube n)).card=0 by simp [supp]] at h
    omega
  refine ⟨L.range,L.finrank_range_of_inj inj,?_,?_⟩
  · rintro ⟨_,⟨x,rfl⟩⟩;exact even _
  · rintro ⟨_,⟨x,rfl⟩⟩ nz
    have nx:x≠0:=fun eq=>nz (Subtype.ext ((congrArg L eq).trans (map_zero L)))
    have a:=dist x nx;have b:=loss x.val;have c:=even x.val
    change d≤(supp (Q x.val)).card
    omega

/-- Every binary linear code of length 26 and minimum distance at least
eight has dimension at most twelve, with arbitrary word parities. -/
theorem no_26_13_8 (C:Submodule F (Cube 26)) (dist:∀x:C,x≠0 → 8≤(supp x.val).card) :
    Module.finrank F C≤12 := by
  obtain ⟨D,same,even,d⟩:=even_replacement (0:Fin 26) C (by decide : 2≤8) (by decide) dist
  exact same ▸ twenty_six D d even
end Green51TwelveResidual
#print axioms Green51TwelveResidual.no_26_13_8

#print axioms Green51TwelveResidual.residual_rank
#print axioms Green51TwelveResidual.split_large
#print axioms Green51TwelveResidual.ten_packing
#print axioms Green51TwelveResidual.even_replacement

#print axioms Green51TwelveResidual.short_packing
