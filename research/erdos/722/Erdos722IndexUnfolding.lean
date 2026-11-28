import Erdos722UnfoldingCharts
import Erdos722QuartetCovers
import Mathlib.Data.ZMod.Basic

/-!
# From repeated blocks to an ordinary Steiner design

Following Brouwer's unfolding of an indexed design, number the copies
through each pair by field elements. The affine charts give unique
blocks across distinct fibers. An ordinary design fills each fiber.
-/

namespace Erdos722.PairUnfolding
open Finset
variable {K : Type*} [Field K]

abbrev Copies {v : ℕ} (k : ℕ) (w : Finset (Fin v) → ℕ) :=
  (B : ↥((univ : Finset (Fin v)).powersetCard k)) × Fin (w B.val)

def base {v k : ℕ} {w : Finset (Fin v) → ℕ} (b : Copies k w) := b.1.val

theorem base_size {v k : ℕ} {w : Finset (Fin v) → ℕ} (b : Copies k w) : (base b).card=k :=
  (mem_powersetCard.mp b.1.property).2

/-- Number the copies containing each pair of points by field elements. -/
theorem serial_numbers [Fintype K] {v k : ℕ} (w : Finset (Fin v) → ℕ)
    (hw : ∀ e : Finset (Fin v), e.card=2 →
      (∑ B∈((univ : Finset (Fin v)).powersetCard k).filter (e ⊆ ·), w B)=Fintype.card K) :
    ∃ serial : Coord v → Copies k w → K, ∀ e d, ∃! b,
      e.val.1 ∈ base b ∧ e.val.2 ∈ base b ∧ serial e b=d := by
  classical
  let blocks := (univ : Finset (Fin v)).powersetCard k
  let pairs (e : Coord v) : Finset (Fin v) := {e.val.1,e.val.2}
  let groups (e : Coord v) := blocks.filter (pairs e ⊆ ·)
  let eligible (e : Coord v) := {b : Copies k w // e.val.1∈base b ∧ e.val.2∈base b}
  have count (e : Coord v) : Fintype.card (eligible e) = Fintype.card K := by
    let eqv : eligible e ≃ (B : groups e) × Fin (w B.val) := {
      toFun := fun b => ⟨⟨b.val.1.val,mem_filter.mpr ⟨b.val.1.property,by
        simpa [pairs,base,insert_subset_iff] using b.property⟩⟩,b.val.2⟩
      invFun := fun b => ⟨⟨⟨b.1.val,(mem_filter.mp b.1.property).1⟩,b.2⟩,by
        simpa [base,pairs,insert_subset_iff] using (mem_filter.mp b.1.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Fintype.card_congr eqv,Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Finset.sum_coe_sort]
    exact hw (pairs e) (by simp [pairs,e.property.ne])
  let label (e : Coord v) := Fintype.equivOfCardEq (count e)
  let serial (e : Coord v) (b : Copies k w) :=
    if h : e.val.1∈base b ∧ e.val.2∈base b then label e (⟨b,h⟩ : eligible e) else 0
  refine ⟨serial,?_⟩
  intro e d
  let b := (label e).symm d
  refine ⟨b.val,⟨b.property.1,b.property.2,?_⟩,?_⟩
  · simp only [serial,dif_pos b.property]
    exact (label e).apply_symm_apply d
  · rintro c ⟨h₁,h₂,hc⟩
    have hg : e.val.1∈base c ∧ e.val.2∈base c := ⟨h₁,h₂⟩
    simp only [serial,dif_pos hg] at hc
    exact congrArg Subtype.val ((label e).injective (hc.trans ((label e).apply_symm_apply d).symm))

#print axioms serial_numbers

/-- Blocks between distinct fibers of the unfolded design. -/
theorem between_blocks [Fintype K] {v k : ℕ} (w : Finset (Fin v) → ℕ)
    (hw : ∀ e : Finset (Fin v), e.card=2 →
      (∑ B∈((univ : Finset (Fin v)).powersetCard k).filter (e ⊆ ·), w B)=Fintype.card K)
    (f : Fin v → K) (hf : Function.Injective f) (hn : ∀ i, f i≠0) :
    ∃ H : Set (Finset (Fin v × (Coord v → K))),
      (∀ B∈H, B.card=k) ∧
      (∀ B∈H, ∀ x∈B, ∀ y∈B, x≠y → x.1≠y.1) ∧
      ∀ x y : Fin v × (Coord v → K), x.1≠y.1 → ∃! B, B∈H ∧ x∈B ∧ y∈B := by
  classical
  obtain ⟨serial,hs⟩ := serial_numbers w hw
  let point (z : Copies k w × Params v K) : Fin v ↪ Fin v × (Coord v → K) :=
    ⟨fun i => (i,chart (slope f i) (offset serial z.1 i) z.2),fun _ _ h => congrArg Prod.fst h⟩
  let block (z : Copies k w × Params v K) := (base z.1).map (point z)
  let H := Set.range block
  have mem (z) (x : Fin v × (Coord v → K)) : x∈block z ↔
      x.1∈base z.1 ∧ chart (slope f x.1) (offset serial z.1 x.1) z.2=x.2 := by
    constructor
    · rintro h
      obtain ⟨i,hi,rfl⟩ := mem_map.mp h
      exact ⟨hi,rfl⟩
    · rintro ⟨h₁,h₂⟩
      exact mem_map.mpr ⟨x.1,h₁,Prod.ext rfl h₂⟩
  have through (x y : Fin v × (Coord v → K)) (h : x.1<y.1) : ∃! B, B∈H ∧ x∈B ∧ y∈B := by
    obtain ⟨z,⟨hx,hy,hX,hY⟩,hu⟩ := repeat_through f hf hn base serial hs h x.2 y.2
    refine ⟨block z,⟨⟨z,rfl⟩,(mem z x).mpr ⟨hx,hX⟩,(mem z y).mpr ⟨hy,hY⟩⟩,?_⟩
    rintro _ ⟨⟨b,rfl⟩,hx',hy'⟩
    obtain ⟨h₁,h₂⟩ := (mem b x).mp hx'
    obtain ⟨h₃,h₄⟩ := (mem b y).mp hy'
    exact congrArg block (hu b ⟨h₁,h₃,h₂,h₄⟩)
  refine ⟨H,?_,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    exact (card_map ..).trans (base_size z.1)
  · rintro _ ⟨z,rfl⟩ x hx y hy hne he
    apply hne
    apply Prod.ext he
    rw [← ((mem z x).mp hx).2,← ((mem z y).mp hy).2,he]
  · intro x y hxy
    rcases lt_or_gt_of_ne hxy with h|h
    · exact through x y h
    · obtain ⟨B,⟨hB,hy,hx⟩,hu⟩ := through y x h
      exact ⟨B,⟨hB,hx,hy⟩,fun C hc => hu C ⟨hc.1,hc.2.2,hc.2.1⟩⟩

#print axioms between_blocks
end Erdos722.PairUnfolding

namespace Erdos722.PairUnfolding
open Finset Erdos722.Quartet

/-- A repeated design of prime index and a design inside a fiber give an
ordinary pair design. The new order is v times a power of that prime. -/
theorem lift_at_prime {v k q : ℕ} (hq : q.Prime) (hvq : v<q) (w : Finset (Fin v) → ℕ)
    (hw : ∀ e : Finset (Fin v), e.card=2 → (∑ B∈((univ : Finset (Fin v)).powersetCard k).filter
      (e ⊆ ·), w B)=q) (inside : Has (·=k) (q^Fintype.card (Coord v))) :
    Has (·=k) (v*q^Fintype.card (Coord v)) := by
  classical
  let : Fact q.Prime := ⟨hq⟩
  let K := ZMod q
  let W := Coord v → K
  let f (i : Fin v) : K := ((i.val+1 : ℕ) : ZMod q)
  have val (i : Fin v) : (f i).val=i.val+1 := ZMod.val_natCast_of_lt (by omega)
  have hf : Function.Injective f := by
    intro i j he
    have h := congrArg ZMod.val he
    rw [val,val] at h
    exact Fin.ext (by omega)
  have hn (i : Fin v) : f i≠0 := by
    intro h
    have z := val i
    rw [h,ZMod.val_zero] at z
    omega
  obtain ⟨H,hs,hsound,hthrough⟩ := between_blocks w (by simpa [K] using hw) f hf hn
  let cross : Cover (Fin v × W) (fun x y => x.1≠y.1) (·=k) := {
    blocks := H
    size := hs
    sound := hsound
    through := fun x y _ h => hthrough x y h }
  have hW : Fintype.card W=q^Fintype.card (Coord v) := by simp [W,K]
  rw [← hW] at inside
  let fiber (i : Fin v) : {x : Fin v × W // x.1=i} ≃ W := {
    toFun := fun x => x.val.2
    invFun := fun t => ⟨(i,t),rfl⟩
    left_inv := by rintro ⟨⟨j,t⟩,rfl⟩; rfl
    right_inv := fun _ => rfl }
  let C := Cover.fillFibers Prod.fst cross (fun i =>
    inside.some.relabel ((Fintype.equivFin W).symm.trans (fiber i).symm))
  have hc : Fintype.card (Fin v × W)=v*q^Fintype.card (Coord v) := by rw [Fintype.card_prod,Fintype.card_fin,hW]
  exact ⟨C.relabel ((Fintype.equivFin _).trans (finCongr hc))⟩

#print axioms lift_at_prime
end Erdos722.PairUnfolding
