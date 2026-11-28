import Green51CoreOccupancy

/-! # Multiplicities of the three exterior cosets for a twenty-one-point candidate -/

open Finset Green50Downsets Green50Sharp Green51TenDimensions
open Green51SimplexSection Green51SimplexFibres Green51CoreOccupancy
open scoped Classical Pointwise
namespace Green51ExteriorFibres
local notation "F" => ZMod 2
local notation "V" => Cube 12

theorem quotient_card (L:Cube 10 →ₗ[F] V) (inj:Function.Injective L) [Fintype (V ⧸ L.range)] :
    Fintype.card (V ⧸ L.range)=4 := by
  let Q := V ⧸ L.range
  have rank := L.range.finrank_quotient_add_finrank
  have codim : Module.finrank F Q=2 := by
    change Module.finrank F (V ⧸ L.range)=2
    rw [L.finrank_range_of_inj inj,show Module.finrank F V=12 by simp [Cube],
      show Module.finrank F (Cube 10)=10 by simp [Cube]] at rank;omega
  rw [Module.card_eq_pow_finrank (K:=F),codim,ZMod.card]
  rfl

theorem fibre_counts {A:Finset V} (L:Cube 10 →ₗ[F] V) (inj:Function.Injective L)
    (t:V) (inc:core L t⊆A) (size:A.card=21) (avoid:¬∃p,FlatAt A p) :
    ∀q:V ⧸ L.range,q≠L.range.mkQ t →
      ((A\core L t).filter (fun x=>L.range.mkQ x=q)).card=2 := by
  classical
  let Q := V ⧸ L.range
  let _ : Fintype Q := Fintype.ofFinite _
  let f := L.range.mkQ
  let E := A\core L t
  let fibre (q:Q) := E.filter (fun x=>f x=q)
  have four := quotient_card L inj
  have coreCard : (core L t).card=15 := by
    rw [core,card_image_of_injective _ (fun _ _ h => inj (add_right_cancel h)),model_card]
  have six : E.card=6 := by dsimp [E];rw [card_sdiff_of_subset inc,size,coreCard]
  have inA {x} (h:x∈E) : x∈A := (mem_sdiff.mp h).1
  have outside {x} (h:x∈E) : x∉core L t := (mem_sdiff.mp h).2
  have miss {x} (h:x∈E) : f x≠f t := fun eq=> outside h ((exact_fibre L inj t inc avoid (inA h)).mp eq)
  have same {x y:V} (eq:f x=f y) : x+y∈L.range := by
    apply (Submodule.Quotient.mk_eq_zero L.range).mp
    change f (x+y)=0;rw [map_add,eq,ZModModule.add_self]
  have maxTwo (q:Q) : (fibre q).card≤2 := by
    by_contra! many
    obtain ⟨B,sub,three⟩ := exists_subset_card_eq (show 3≤(fibre q).card by omega)
    have bE {x} (h:x∈B) : x∈E := (mem_filter.mp (sub h)).1
    have tag {x} (h:x∈B) : f x=q := (mem_filter.mp (sub h)).2
    have bDiff := fun x (hx:x∈B) y (hy:y∈B) => same ((tag hx).trans (tag hy).symm)
    have outB : Disjoint B (core L t) := disjoint_left.mpr fun _ hx=>outside (bE hx)
    have controls {x y:V} (he:x∈E) (hf:y∈E) (ne:x≠y) (eq:f x=f y) : x∈B := by
      let C : Finset V := {x,y}
      have cE : C⊆E := by
        intro z hz;rcases mem_insert.mp hz with rfl|k;exact he;simpa only [mem_singleton.mp k] using hf
      have iden (z) (hz:z∈C) : f z=f y := by
        rcases mem_insert.mp hz with rfl|k;exact eq;rw [mem_singleton.mp k]
      have all := triangle_controls L inj t inc (by omega) avoid (fun _ h => inA (bE h))
        (fun _ h=>inA (cE h)) three (show C.card=2 by simp [C,ne]) outB
        (disjoint_left.mpr fun _ h => outside (cE h)) bDiff
        (fun v hv w hw=>same ((iden v hv).trans (iden w hw).symm))
      exact all (show x∈C by simp [C])
    let R := E\B
    obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by omega)
    have qne:q≠f t := tag hb ▸ miss (bE hb)
    let S : Finset Q := (univ.erase (f t)).erase q
    have small : S.card=2 := by
      dsimp [S];rw [card_erase_of_mem (by simp [qne]),card_erase_of_mem (mem_univ _),card_univ,four]
    have maps : R.image f⊆S := by
      intro z hz;obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      have ⟨he,nb⟩ := mem_sdiff.mp hx
      have nq:f x≠q := fun eq => nb (controls he (bE hb) (fun same=>nb (same ▸ hb)) (eq.trans (tag hb).symm))
      exact mem_erase.mpr ⟨nq,mem_erase.mpr ⟨miss he,mem_univ _⟩⟩
    have inject : Set.InjOn f ↑R := by
      intro x hx y hy eq
      by_contra ne
      exact (mem_sdiff.mp hx).2 (controls (mem_sdiff.mp hx).1 (mem_sdiff.mp hy).1 ne eq)
    have cnt := card_le_card maps
    rw [card_image_of_injOn inject,small] at cnt
    have rsize : R.card=3 := by dsimp [R]; rw [card_sdiff_of_subset (fun _ h=>bE h),six,three]
    omega
  let S : Finset Q := univ.erase (f t)
  have sc:S.card=3 := by dsimp [S];rw [card_erase_of_mem (mem_univ _),card_univ,four]
  have total : E.card=∑q∈S,(fibre q).card :=
    card_eq_sum_card_fiberwise (f:=f) (fun x hx=>mem_erase.mpr ⟨miss hx,mem_univ _⟩)
  intro q non
  change (fibre q).card=2
  have inS : q∈S := mem_erase.mpr ⟨non,mem_univ _⟩
  have er := card_erase_add_one (s:=S) inS
  have other := sum_le_sum (s:=S.erase q) (fun i _=> maxTwo i)
  have split := sum_erase_add (s:=S) (f:=fun i=>(fibre i).card) inS
  simp only [sum_const,nsmul_eq_mul] at other
  have erased : (S.erase q).card=2 := by omega
  rw [erased] at other
  have bound:=maxTwo q
  omega

end Green51ExteriorFibres
#print axioms Green51ExteriorFibres.quotient_card
#print axioms Green51ExteriorFibres.fibre_counts
