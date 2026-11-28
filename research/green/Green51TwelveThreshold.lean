import Green51TwelveCodes

/-! # The linear three-space threshold in twelve binary dimensions -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open scoped Classical Pointwise

namespace Green51TwelveThreshold
open Green51TwelveResidual
local notation "F" => ZMod 2
local notation "V" => Cube 12

/-- Any 26 points in twelve binary dimensions force a linear three-space
in their double. -/
theorem twenty_six_labels {A:Finset V} (sz:A.card=26) : FlatAt A 0 := by
  by_contra avoid
  have free:∀T⊆A,T.card=4 ∨ T.card=6 → (∑a∈T,a)≠0:=fun T sub size z=>
    avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,size,z⟩))
  obtain ⟨P,_,parity,kernel,_⟩:=Green51SparseDimensions.even_pair_columns A free
  have no_code {n:ℕ} (n26:n=26) (C:Submodule F (Cube n)) (dist:∀x:C,x≠0 → 8≤(supp x.val).card)
      (even:∀x:C,2∣(supp x.val).card) : Module.finrank F C≤12:=by
    subst n;exact Green51TwelveResidual.twenty_six C dist even
  have d:=no_code sz P.ker (by
    intro x nx; by_contra! small
    have even:=parity x.val x.property
    exact nx (Subtype.ext (kernel x.val (by omega) x.property))) (fun x=>parity x.val x.property)
  have add:=P.finrank_range_add_finrank_ker
  have up:=Submodule.finrank_le P.range
  rw [show Module.finrank F (F×V)=13 by simp [Cube,Module.finrank_prod]] at up
  rw [show Module.finrank F (Cube A.card)=26 by simp [Cube,sz]] at add
  omega

private def extend (x:Cube 11) : V := Fin.cons 0 x
private def apex : V := Fin.cons 1 0
private def embedding : Cube 11 ↪ V := ⟨extend,fun x y h=>by
  funext i;exact congrFun h i.succ⟩

private theorem cone (B:Finset (Cube 11)) (large:5≤B.card) (avoid:¬FlatAt B 0) :
    let A:=insert apex (B.map embedding)
    A.card=B.card+1 ∧ ¬FlatAt A 0 := by
  classical
  have zero (x:Cube 11) : (embedding x) 0=0:=rfl
  have one : apex 0=1:=rfl
  have new:apex∉B.map embedding:=by
    intro h;obtain ⟨x,_,eq⟩:=mem_map.mp h
    exact zero_ne_one ((zero x).symm.trans ((congrFun eq 0).trans one))
  let A:=insert apex (B.map embedding)
  have size:A.card=B.card+1:=by rw [show A=insert apex (B.map embedding) from rfl,card_insert_of_notMem new,card_map]
  refine ⟨size,?_⟩
  intro bad
  obtain ⟨S,sub,sz,sum⟩:=(Green51SparseDimensions.linear_three_iff A (by omega)).mp ((flat_zero A).mp bad)
  have outside:apex∉S:=by
    intro hit
    have rem:S.erase apex⊆B.map embedding:=by
      intro x hx;exact (mem_insert.mp (sub (mem_erase.mp hx).2)).resolve_left (mem_erase.mp hx).1
    have vanish:∑x∈S.erase apex,x 0=0:=sum_eq_zero fun x hx=>by
      obtain ⟨b,_,rfl⟩:=mem_map.mp (rem hx);exact zero _
    have all:=congrFun sum 0
    rw [Finset.sum_apply] at all
    have slice:=(S.add_sum_erase (fun x=>x 0) hit)
    rw [one,vanish,add_zero,all] at slice
    exact one_ne_zero slice
  have inside:S⊆B.map embedding:=fun x hx=>(mem_insert.mp (sub hx)).resolve_left fun e=>outside (e ▸ hx)
  let T:=B.filter fun x=>embedding x∈S
  have back:T.map embedding=S:=by
    ext x
    constructor
    · intro h;obtain ⟨b,hb,rfl⟩:=mem_map.mp h;exact (mem_filter.mp hb).2
    · intro h;obtain ⟨b,hb,rfl⟩:=mem_map.mp (inside h);exact mem_map.mpr ⟨b,mem_filter.mpr ⟨hb,h⟩,rfl⟩
  have card:T.card=S.card:=(card_map embedding).symm.trans (congrArg card back)
  have z:(∑x∈T,x)=0:=by
    funext i
    have eq:=congrFun sum i.succ
    rw [←back,Finset.sum_apply,Finset.sum_map] at eq
    rw [Finset.sum_apply]
    change (∑x∈T,x i)=(0:F)
    exact eq
  exact avoid ((flat_zero B).mpr ((Green51SparseDimensions.linear_three_iff B large).mpr
    ⟨T,filter_subset ..,by omega,z⟩))

/-- The linear three-space threshold in twelve binary dimensions is 26. -/
theorem linear_iff (k:ℕ) : (∀A:Finset V,k≤A.card → FlatAt A 0) ↔ 26≤k := by
  constructor
  · intro h;by_contra! small
    have b:=Green51GolayWitnesses.sizes.1
    obtain ⟨n,no⟩:=cone Green51GolayWitnesses.full (by omega) Green51GolayWitnesses.no_linear
    exact no (h _ (by omega))
  · intro enough A large
    obtain ⟨B,sub,sz⟩:=exists_subset_card_eq (enough.trans large)
    obtain ⟨W,d,inside⟩:=twenty_six_labels sz
    exact ⟨W,d,fun x hx=>add_subset_add sub sub (inside hx)⟩
end Green51TwelveThreshold
#print axioms Green51TwelveThreshold.linear_iff

#print axioms Green51TwelveThreshold.twenty_six_labels

namespace Green51CodeCriterion
local notation "F" => ZMod 2

/-- A code correcting three errors supplies distinct parity-check columns.
Adjoining zero to those columns yields a set whose double avoids a linear
three-space whenever there are at least five labels. -/
theorem labels_from_code {n d : ℕ} (large : 4 ≤ n) (C : Submodule F (Cube n))
    (rank : n ≤ Module.finrank F C + d)
    (dist : ∀ x : C, x ≠ 0 → 7 ≤ (supp x.val).card) :
    ∃ A : Finset (Cube d), A.card = n + 1 ∧ ¬FlatAt A 0 := by
  classical
  have dim := C.finrank_quotient_add_finrank
  rw [show Module.finrank F (Cube n) = n by simp [Cube]] at dim
  have room : Module.finrank F (Cube n ⧸ C) ≤ Module.finrank F (Cube d) := by
    rw [show Module.finrank F (Cube d) = d by simp [Cube]]
    omega
  obtain ⟨f, injective⟩ := finrank_le_iff_exists_linearMap.mp room
  let col (i : Fin n) := f (C.mkQ (Pi.single i (1:F)))
  have independent (S : Finset (Fin n)) (lo : 0 < S.card) (hi : S.card ≤ 6) :
      (∑ i ∈ S, col i) ≠ 0 := by
    intro zero
    let v : Cube n := ∑ i ∈ S, Pi.single i 1
    have eval (j : Fin n) : v j = if j ∈ S then 1 else 0 := by
      simp [v,Finset.sum_apply,Pi.single_apply]
    have support : supp v = S := by ext i; simp [supp,eval]
    have hv : v ∈ C := by
      apply (Submodule.Quotient.mk_eq_zero C).mp
      apply (injective.eq_iff' (map_zero f)).mp
      change f (C.mkQ (∑ i ∈ S, Pi.single i (1:F))) = 0
      rw [map_sum,map_sum]
      exact zero
    have nonzero : (⟨v,hv⟩:C) ≠ 0 := by
      intro z
      have eq := congrArg Subtype.val z
      change v = 0 at eq
      have empty : S = ∅ := support.symm.trans (by simp [eq,supp])
      simp [empty] at lo
    have bound := dist ⟨v,hv⟩ nonzero
    change 7 ≤ (supp v).card at bound
    rw [support] at bound
    omega
  have nz (i : Fin n) : col i ≠ 0 := by
    simpa using independent {i} (by simp) (by simp)
  have ci : Function.Injective col := by
    intro i j eq
    by_contra ne
    have h := independent {i,j} (by simp [ne]) (by simp [ne])
    exact h (by simp [ne,eq,ZModModule.add_self])
  let emb : Fin n ↪ Cube d := ⟨col,ci⟩
  let A := insert 0 (univ.map emb)
  have nozero : 0 ∉ univ.map emb := by
    rintro h; obtain ⟨i,_,e⟩ := mem_map.mp h; exact nz i e
  have size : A.card = n+1 := by simp [A,card_insert_of_notMem nozero]
  refine ⟨A,size,?_⟩
  intro flat
  obtain ⟨T,sub,sz,total⟩ := (Green51SparseDimensions.linear_three_iff A (by omega)).mp
    ((flat_zero A).mp flat)
  let S := univ.filter fun i => col i ∈ T
  have back : S.map emb = T.erase 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hx
      exact mem_erase.mpr ⟨nz i,(mem_filter.mp hi).2⟩
    · intro hx
      have inside := sub (mem_erase.mp hx).2
      obtain ⟨i,_,rfl⟩ := mem_map.mp ((mem_insert.mp inside).resolve_left (mem_erase.mp hx).1)
      exact mem_map.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,(mem_erase.mp hx).2⟩,rfl⟩
  have count : S.card = (T.erase 0).card := (card_map emb).symm.trans (congrArg card back)
  have hi := card_le_card (erase_subset (0:Cube d) T)
  have lo := pred_card_le_card_erase (s:=T) (a:=(0:Cube d))
  have same : (∑ i ∈ S,col i) = ∑ a ∈ T.erase 0,a := by rw [←back,sum_map];rfl
  apply independent S (by omega) (by omega)
  rw [same]
  by_cases z : (0:Cube d) ∈ T
  · have h := sum_erase_add (s:=T) (fun x => x) z
    simpa [total] using h
  · rwa [erase_eq_of_notMem z]

/-- Puncturing a binary code in one position preserves dimension at
distance at least two, and reduces the distance lower bound by at most one. -/
theorem puncture {n b : ℕ} (C : Submodule F (Cube (n+1))) (pos : 0 < b)
    (distance : ∀ x : C, x ≠ 0 → b+1 ≤ (supp x.val).card) :
    ∃ D : Submodule F (Cube n), Module.finrank F D = Module.finrank F C ∧
      ∀ y : D, y ≠ 0 → b ≤ (supp y.val).card := by
  classical
  let p : C →ₗ[F] Cube n := LinearMap.pi fun i : Fin n => (LinearMap.proj i.succ).comp C.subtype
  have loss (x : C) : (supp x.val).card ≤ (supp (p x)).card + 1 := by
    simp only [supp,card_filter]
    rw [Fin.sum_univ_succ]
    change (if x.val 0 ≠ 0 then 1 else 0) + (∑ i : Fin n, if x.val i.succ ≠ 0 then 1 else 0) ≤
      (∑ i : Fin n, if x.val i.succ ≠ 0 then 1 else 0) + 1
    split <;> omega
  have inj : Function.Injective p := by
    apply (injective_iff_map_eq_zero p).mpr
    intro x hx
    by_contra ne
    have h := loss x
    have d := distance x ne
    rw [hx,show supp (0 : Cube n) = ∅ by simp [supp],card_empty] at h
    omega
  refine ⟨p.range,p.finrank_range_of_inj inj,?_⟩
  rintro ⟨_,⟨x,rfl⟩⟩ nz
  have nx : x ≠ 0 := fun e => nz (Subtype.ext ((congrArg p e).trans (map_zero p)))
  have h := loss x
  have d := distance x nx
  change b ≤ (supp (p x)).card
  omega

/-- In every dimension and at every size at least five, the existence
of a set avoiding a linear three-space is equivalent to the existence of a
binary triple-error-correcting code on one fewer coordinate. -/
theorem avoiding_iff_code {n d : ℕ} (large : 4 ≤ n) :
    (∃ A : Finset (Cube d), A.card = n+1 ∧ ¬FlatAt A 0) ↔
    ∃ C : Submodule F (Cube n), n ≤ Module.finrank F C + d ∧
      ∀ x : C, x ≠ 0 → 7 ≤ (supp x.val).card := by
  constructor
  · rintro ⟨A,sz,avoid⟩
    have free : ∀ T ⊆ A, T.card = 4 ∨ T.card = 6 → (∑ a ∈ T,a) ≠ 0 := fun T sub size sum =>
      avoid ((flat_zero A).mpr ((Green51SparseDimensions.linear_three_iff A (by omega)).mpr ⟨T,sub,size,sum⟩))
    obtain ⟨P,_,even,kernel,_⟩ := Green51SparseDimensions.even_pair_columns A free
    have dist (x : P.ker) (nz : x ≠ 0) : 8 ≤ (supp x.val).card := by
      have e := even x.val x.property
      by_contra! h
      exact nz (Subtype.ext (kernel x.val (by omega) x.property))
    have h := P.finrank_range_add_finrank_ker
    have up := Submodule.finrank_le P.range
    rw [show Module.finrank F (Cube A.card) = n+1 by simp [Cube,sz]] at h
    rw [show Module.finrank F (F × Cube d) = 1+d by simp [Cube,Module.finrank_prod]] at up
    have lower : n ≤ Module.finrank F P.ker + d := by omega
    have shrink {k : ℕ} (hk : k = n+1) (D : Submodule F (Cube k))
        (bound : n ≤ Module.finrank F D + d)
        (minWeight : ∀ x : D, x ≠ 0 → 8 ≤ (supp x.val).card) :
        ∃ C : Submodule F (Cube n), n ≤ Module.finrank F C + d ∧
          ∀ x : C, x ≠ 0 → 7 ≤ (supp x.val).card := by
      subst k
      obtain ⟨C,dim,c⟩ := puncture D (by decide : 0 < 7) minWeight
      exact ⟨C,dim ▸ bound,c⟩
    exact shrink sz P.ker lower dist
  · rintro ⟨C,rank,dist⟩
    exact labels_from_code large C rank dist
end Green51CodeCriterion

#print axioms Green51CodeCriterion.labels_from_code
#print axioms Green51CodeCriterion.puncture
#print axioms Green51CodeCriterion.avoiding_iff_code
