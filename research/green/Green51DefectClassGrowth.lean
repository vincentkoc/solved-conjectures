import Green51StableDefectPartitions
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.Finsupp.Multiset

/-! # Binomial bounds for the stable number of affine classes -/

namespace Green51FrameIsomorphisms
open Finset Green53ParityThreshold Green51MissingMasks Green51Hyperplane
open scoped Classical

def plainWeight (t : Parts) : ℕ := t.1+t.2.1+t.2.2.1+t.2.2.2

private def tupleEquiv (h : ℕ) :
    {t : Parts // plainWeight t≤h} ≃ {f : Fin 5 → ℕ // ∑ i,f i=h} where
  toFun t := ⟨![t.val.1,t.val.2.1,t.val.2.2.1,t.val.2.2.2,h-plainWeight t.val],by
    have enough := t.property
    simp [Fin.sum_univ_succ,plainWeight] at *
    omega⟩
  invFun f := ⟨⟨f.val 0,f.val 1,f.val 2,f.val 3⟩,by
    have eq := f.property
    simp [Fin.sum_univ_succ] at eq
    dsimp [plainWeight];omega⟩
  left_inv := by rintro ⟨⟨a,b,c,d⟩,h⟩; rfl
  right_inv f := by
    apply Subtype.ext;funext i
    fin_cases i <;> try rfl
    have eq := f.property
    simp [Fin.sum_univ_succ] at eq
    change h-(f.val 0+f.val 1+f.val 2+f.val 3)=f.val 4
    omega

theorem plain_card (h : ℕ) : Nat.card {t : Parts // plainWeight t≤h}=(h+4).choose 4 := by
  let e : {f : Fin 5 →₀ ℕ // f.sum (fun _ => id)=h} ≃ {f : Fin 5 → ℕ // ∑ i,f i=h} :=
    Finsupp.equivFunOnFinite.subtypeEquiv (fun f => by
      change (f.sum (fun _ => id)=h) ↔ (∑ i,f i)=h
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)];rfl)
  rw [Nat.card_congr ((tupleEquiv h).trans (e.symm.trans (Sym.equivNatSum (Fin 5) h).symm)),
    Sym.natCard_sym_eq_choose,Nat.card_fin,show 5+h-1=h+4 by omega,Nat.choose_symm_add]

abbrev Residues := Fin 3 × Fin 2 × Fin 4 × Fin 6

private def divide (t : Parts) : Parts × Residues :=
  (⟨t.1/3,t.2.1/2,t.2.2.1/4,t.2.2.2/6⟩,⟨t.1%3,by omega⟩,⟨t.2.1%2,by omega⟩,
    ⟨t.2.2.1%4,by omega⟩,⟨t.2.2.2%6,by omega⟩)

private def expand (t : Parts) (r : Residues) : Parts :=
  ⟨3*t.1+r.1.val,2*t.2.1+r.2.1.val,4*t.2.2.1+r.2.2.1.val,6*t.2.2.2+r.2.2.2.val⟩

private theorem divide_expand (t : Parts) (r : Residues) : divide (expand t r)=(t,r) := by
  rcases r with ⟨⟨i,hi⟩,⟨j,hj⟩,⟨k,hk⟩,⟨l,hl⟩⟩
  rcases t with ⟨a,b,c,d⟩
  simp [divide,expand,Nat.add_mod,Nat.mul_add_div]; omega

private theorem expand_divide (t : Parts) : expand (divide t).1 (divide t).2=t := by
  rcases t with ⟨a,b,c,d⟩
  dsimp [divide,expand]
  congr <;> omega

theorem stable_count {g h : ℕ} (enough : h≤g) :
    (profileTable g (4*g-h)).card=Nat.card {t : Parts // weight t≤h} := by
  let f (t : {t : Parts // weight t≤h}) : ↥(profileTable g (4*g-h)) :=
    ⟨_,mem_profileTable.mpr ((stable_parts enough).mpr ⟨t.val,t.property,rfl⟩)⟩
  have bij : Function.Bijective f := by
    refine ⟨fun t u eq => Subtype.ext (fromParts_injective g h (congrArg Subtype.val eq)),?_⟩
    intro p
    obtain ⟨t,w,eq⟩ := (stable_parts enough).mp (mem_profileTable.mp p.property)
    exact ⟨⟨t,w⟩,Subtype.ext eq⟩
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr (Equiv.ofBijective f bij).symm

private instance plain_finite (h : ℕ) : Finite {t : Parts // plainWeight t≤h} :=
  Nat.finite_of_card_ne_zero (by rw [plain_card];exact (Nat.choose_pos (by omega)).ne')

private instance weighted_finite (h : ℕ) : Finite {t : Parts // weight t≤h} :=
  Finite.of_injective (fun t : {t : Parts // weight t≤h} =>
    (⟨t.val,by have eq := t.property;dsimp [plainWeight,weight] at *;omega⟩ : {t : Parts // plainWeight t≤h}))
    (fun _ _ eq => Subtype.ext (congrArg (fun z : {t : Parts // plainWeight t≤h} => z.val) eq))

/-- Boxes of 144 residue vectors bound the stable class count between two ordinary simplex counts. -/
theorem defect_bounds {g h : ℕ} (enough : h≤g) :
    (h+4).choose 4 ≤ 144*(profileTable g (4*g-h)).card ∧
      144*(profileTable g (4*g-h)).card ≤ (h+15).choose 4 := by
  rw [stable_count enough]
  let W := {t : Parts // weight t≤h}
  have cardR : Nat.card Residues=144 := by simp [Residues]
  let f (t : {t : Parts // plainWeight t≤h}) : W × Residues :=
    (⟨(divide t.val).1,by have eq := t.property;dsimp [divide,weight,plainWeight] at *;omega⟩,(divide t.val).2)
  let e (w : W × Residues) : {t : Parts // plainWeight t≤h+11} :=
    ⟨expand w.1.val w.2,by
      have ht := w.1.property
      have ha := w.2.1.isLt
      have hb := w.2.2.1.isLt
      have hc := w.2.2.2.1.isLt
      have hd := w.2.2.2.2.isLt
      dsimp [expand,weight,plainWeight] at *;omega⟩
  have injf : Function.Injective f := by
    intro a b eq
    have eq' : divide a.val=divide b.val :=
      congrArg (fun z : W × Residues => (z.1.val,z.2)) eq
    apply Subtype.ext
    exact (expand_divide a.val).symm.trans ((congrArg (fun z : Parts×Residues => expand z.1 z.2) eq').trans (expand_divide b.val))
  have inje : Function.Injective e := by
    intro a b eq
    have eq' := congrArg (fun z : {t : Parts // plainWeight t≤h+11} => divide z.val) eq
    change divide (expand a.1.val a.2)=divide (expand b.1.val b.2) at eq'
    rw [divide_expand,divide_expand] at eq'
    exact Prod.ext (Subtype.ext (congrArg Prod.fst eq')) (congrArg (fun z : Parts × Residues => z.2) eq')
  have l := Nat.card_le_card_of_injective f injf
  have u := Nat.card_le_card_of_injective e inje
  rw [plain_card,Nat.card_prod,cardR] at l
  rw [plain_card,Nat.card_prod,cardR] at u
  exact ⟨by simpa only [W,Nat.mul_comm 144 _] using l,by simpa only [W,Nat.mul_comm 144 _] using u⟩

end Green51FrameIsomorphisms
#print axioms Green51FrameIsomorphisms.plain_card
#print axioms Green51FrameIsomorphisms.stable_count

#print axioms Green51FrameIsomorphisms.defect_bounds
