import Erdos722EventualArrays
import Erdos722QuartetDeletion

/-!
# Truncating an orthogonal array

Keep every symbol in the ordinary columns and an initial segment in column
zero. Every remaining pair in distinct columns still determines its row.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet Erdos722.Quartet.Transversal Finset

private def retained {t : ℕ} (r : ℕ) (v : Fin t) : Finset (Fin r) :=
  if h : v.val < r then {⟨v.val,h⟩} else ∅

private theorem retained_mem {t r : ℕ} (hr : r ≤ t) (v : Fin t) (l : Fin r) :
    l ∈ retained r v ↔ v=Fin.castLE hr l := by
  dsimp [retained]
  split_ifs with h
  · simp only [mem_singleton,Fin.ext_iff,Fin.val_castLE]
    exact eq_comm
  · simp only [notMem_empty,false_iff,Fin.ext_iff,Fin.val_castLE]
    omega

private theorem retained_size {t r : ℕ} (v : Fin t) :
    (retained r v).card=1 ∨ ((retained r v).card=0 ∧ r<t) := by
  dsimp [retained]
  split_ifs <;> simp_all
  omega

/-- The missing block size is only needed when the last column is shortened. -/
theorem array_truncate {s t r a : ℕ} {S : ℕ → Prop} (A : ArrayAt (s+1) t)
    (hr : r≤t) (ha : a≤1) (hsmall : r<t → S s) (hbig : S (s+1))
    (hT : Has S (t+a)) (hR : Has S (r+a)) : Has S (s*t+r+a) := by
  classical
  let V := Point s (Fin t) (Fin r)
  let symbol : V → Fin t := Sum.elim Prod.snd (Fin.castLE hr)
  let idx (x : V) := (finSuccEquiv s).symm (column x)
  let row (f : Fin (s+1) → Fin t) : Fin s ↪ Fin s × Fin t :=
    ⟨fun i => (i,f i.succ),fun _ _ h => congrArg Prod.fst h⟩
  let L (f : {f // f∈A.some.rows}) := (univ.map (row f.val)).disjSum (retained r (f.val 0))
  have mem (f x) : x ∈ L f ↔ f.val (idx x)=symbol x := by
    rcases x with ⟨i,x⟩ | l
    · simp only [L,inl_mem_disjSum,mem_map,mem_univ,true_and]
      change (∃ j : Fin s, (j,f.val j.succ)=(i,x)) ↔ _
      simp [idx,column,symbol]
    · simpa [L,idx,column,symbol] using retained_mem hr (f.val 0) l
  have C : Cover V (fun x y => column x ≠ column y) S := by
    apply Cover.ofLines L
    · intro f
      rcases retained_size (r:=r) (f.val 0) with h | ⟨h,ht⟩
      · simpa [L,h] using hbig
      · simpa [L,h] using hsmall ht
    · intro f x hx y hy hxy he
      have hi : idx x=idx y := congrArg (finSuccEquiv s).symm he
      have hx' := (mem f x).mp hx
      have hy' := (mem f y).mp hy
      rw [hi] at hx'
      have hv := hx'.symm.trans hy'
      apply hxy
      rcases x with ⟨i,x⟩ | x <;> rcases y with ⟨j,y⟩ | y <;> simp_all [symbol,column]
    · intro x y _ hxy
      obtain ⟨f,⟨hf,hx,hy⟩,hu⟩ := A.some.through (idx x) (idx y)
        (fun e => hxy ((finSuccEquiv s).symm.injective e)) (symbol x) (symbol y)
      exact ⟨⟨f,hf⟩,⟨(mem _ _).mpr hx,(mem _ _).mpr hy⟩,
        fun g hg => Subtype.ext (hu g.val ⟨g.property,(mem _ _).mp hg.1,(mem _ _).mp hg.2⟩)⟩
  rcases (by omega : a=0 ∨ a=1) with rfl | rfl
  · apply (Cover.fillFibers column C _).has (by simp [Point])
    intro i
    cases i with
    | none => exact (hR.realize (Fintype.card_fin r)).relabel lastFiber
    | some i => exact (hT.realize (Fintype.card_fin t)).relabel (finiteFiber i)
  · apply (Cover.adjoin column C _).has (by simp [Point])
    intro i
    cases i with
    | none => exact (hR.realize (V:=Option (Fin r)) (by simp)).relabel (Equiv.optionCongr lastFiber)
    | some i => exact (hT.realize (V:=Option (Fin t)) (by simp)).relabel (Equiv.optionCongr (finiteFiber i))

theorem array_fill {k t a : ℕ} {S : ℕ → Prop} (hk : 0<k)
    (A : ArrayAt k t) (hS : S k) (ha : a≤1) (ht : Has S (t+a)) : Has S (k*t+a) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simpa [Nat.succ_mul] using array_truncate A (r:=t) le_rfl ha (by omega) hS ht ht

#print axioms array_truncate
#print axioms array_fill
end Erdos722.PairDesign
