import Green51SeventeenBound

/-! # Projections of shortened doubly even codes -/

open Finset Green50Downsets Green50Sharp
open scoped Classical Pointwise
namespace Green51ResidualPacking
local notation "F" => ZMod 2

/-- A distance-eight, doubly even binary code of length at least seventeen
and dimension at least the length less twelve prescribes arbitrary entries
on any set of positions leaving at least seventeen unchanged. -/
theorem projection {n:ℕ} (hn:17≤n) (C:Submodule F (Cube n))
    (rank:n-12≤Module.finrank F C)
    (dist:∀x:C,x≠0 → 8≤(supp x.val).card) (four:∀x:C,4∣(supp x.val).card) :
    Module.finrank F C=n-12 ∧ ∀T:Finset (Fin n),T.card≤n-17 →
      ∀y:T→F,∃x:C,∀i:T,x.val i.val=y i := by
  classical
  have exactSize (T:Finset (Fin n)) (sz:T.card=n-17) :
      Module.finrank F C=n-12 ∧ ∀y:T→F,∃x:C,∀i:T,x.val i.val=y i := by
    let R:C →ₗ[F] (T→F):=LinearMap.pi fun i:T => (LinearMap.proj i.val).comp C.subtype
    let U:Finset (Fin n):=Tᶜ
    have us:U.card=17 := by dsimp [U];rw [card_compl,Fintype.card_fin,sz];omega
    let e:Fin 17 ≃ U := ((U.equivFin).trans (finCongr us)).symm
    let f:R.ker →ₗ[F] Cube 17:=LinearMap.pi fun i:Fin 17 =>
      ((LinearMap.proj (e i).val).comp C.subtype).comp R.ker.subtype
    have vanish (x:R.ker) (i:Fin n) (hi:i∈T) : x.val.val i=0 :=
      congrFun (show R x.val=0 from x.property) (⟨i,hi⟩:T)
    have inj:Function.Injective f := by
      intro x y eq
      apply Subtype.ext;apply Subtype.ext;funext i
      by_cases h:i∈T
      · rw [vanish x i h,vanish y i h]
      · obtain ⟨j,hj⟩:=e.surjective (⟨i,mem_compl.mpr h⟩:U)
        have q:=congrFun eq j
        change x.val.val (e j).val=y.val.val (e j).val at q
        simpa [hj] using q
    have wt (x:R.ker) : (supp (f x)).card=(supp x.val.val).card := by
      apply card_bij (fun j _ => (e j).val)
      · intro j hj;exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hj).2⟩
      · intro i _ j _ eq;exact e.injective (Subtype.ext eq)
      · intro i hi
        have outside:i∉T:=fun hit=>(mem_filter.mp hi).2 (vanish x i hit)
        obtain ⟨j,hj⟩:=e.surjective (⟨i,mem_compl.mpr outside⟩:U)
        refine ⟨j,mem_filter.mpr ⟨mem_univ _,?_⟩,congrArg Subtype.val hj⟩
        change x.val.val (e j).val≠0
        simpa only [hj] using (mem_filter.mp hi).2
    have low:=seventeen f.range (by
      rintro ⟨_,⟨x,rfl⟩⟩ nz
      rw [wt]
      apply dist
      intro zero
      have zero':x=0:=Subtype.ext zero
      apply nz
      apply Subtype.ext
      simp [zero']) (by rintro ⟨_,⟨x,rfl⟩⟩;rw [wt];exact four x.val)
    rw [LinearMap.finrank_range_of_inj inj] at low
    have add:=R.finrank_range_add_finrank_ker
    have up:=Submodule.finrank_le R.range
    have dim:Module.finrank F (T→F)=T.card:=by simp
    rw [dim] at up
    have full:R.range=⊤:=Submodule.eq_top_of_finrank_eq (by omega)
    refine ⟨by omega,?_⟩
    intro y
    obtain ⟨x,hx⟩:=LinearMap.range_eq_top.mp full y
    exact ⟨x,congrFun hx⟩
  obtain ⟨U,_,su⟩:=exists_subset_card_eq (s:=(univ:Finset (Fin n)))
    (show n-17≤univ.card by simp)
  refine ⟨(exactSize U su).1,?_⟩
  intro T ts y
  obtain ⟨S,inc,_,ss⟩:=exists_subsuperset_card_eq (subset_univ T) ts
    (show n-17≤(univ:Finset (Fin n)).card by simp)
  let z (s:S):F:=if h:s.val∈T then y ⟨s.val,h⟩ else 0
  obtain ⟨x,hx⟩:=(exactSize S ss).2 z
  exact ⟨x,fun i=>by simpa [z,i.property] using hx (⟨i.val,inc i.property⟩:S)⟩

end Green51ResidualPacking
#print axioms Green51ResidualPacking.projection
