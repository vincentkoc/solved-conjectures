import Green50HammingDensity
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.CharP.Two
/-!
# Sparse sumset obstructions from binary BCH parity checks

A linear image that is injective on short binary relations preserves the
parallelograms needed to lift affine flats in a Hamming ball.
-/

open Finset
open scoped Pointwise
namespace Green50BCH
variable {K : Type*} [Field K] [CharP K 2]

/-- Odd-power coordinates in a binary BCH parity-check column. -/
def column (t : ℕ) (x : K) (i : Fin t) := x^(2*i.val+1)

private theorem all_moments {n t : ℕ} (v : Fin n → K)
    (h : ∀ i : Fin t, ∑ j : Fin n, v j ^ (2*i.val+1) = 0) :
    ∀ e : ℕ, 0<e → e≤2*t → ∑ j : Fin n, v j ^ e = 0 := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih =>
    intro hp he
    by_cases ho : e%2=1
    · simpa only [show 2*(e/2)+1=e by omega] using h ⟨e/2,by omega⟩
    · have hs := ih (e/2) (by omega) (by omega) (by omega)
      have sq := CharTwo.sum_sq (univ : Finset (Fin n)) (fun j => v j ^ (e/2))
      rw [hs,zero_pow (by decide : 2 ≠ 0)] at sq
      simpa only [←pow_mul,show e/2*2=e by omega] using sq.symm

/-- The odd-power columns of a binary BCH parity-check matrix have no nonempty
zero sum of at most twice their number of coordinates. -/
theorem column_girth {n t : ℕ} (hn : 0<n) (hnt : n≤2*t) (v : Fin n → K)
    (inj : Function.Injective v) (nz : ∀ i, v i ≠ 0) : (∑ j : Fin n, column t (v j)) ≠ 0 := by
  intro hz
  have h (i : Fin t) : ∑ j : Fin n, v j ^ (2*i.val+1) = 0 := by
    simpa [column,Finset.sum_apply] using congrFun hz i
  have all := all_moments v h
  have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero inj (fun i => by
    simpa only [pow_succ',Nat.succ_eq_add_one] using all (i.val+1) (by omega) (by omega))
  exact nz ⟨0,hn⟩ (congrFun hv _)

open Green50Sharp Green50Downsets
local notation "F₂" => ZMod 2
variable [Algebra F₂ K]

private theorem syndrome_kernel {N t : ℕ} (v : Fin N → K)
    (hv : Function.Injective v) (hn : ∀ j, v j ≠ 0) (z : Cube N)
    (hw : (supp z).card ≤ 2*t)
    (hz : Fintype.linearCombination F₂ (fun j => column t (v j)) z = 0) : z=0 := by
  classical
  let S := supp z
  by_contra hne
  have hs : S.Nonempty := by
    by_contra! h
    apply hne
    funext j
    by_contra! hn
    have : j∈S := mem_filter.mpr ⟨mem_univ _,hn⟩
    simp [h] at this
  let f (i : Fin S.card) := v ((S.equivFin.symm i).val)
  have inj : Function.Injective f := hv.comp (Subtype.val_injective.comp S.equivFin.symm.injective)
  have nz (i : Fin S.card) := hn ((S.equivFin.symm i).val)
  have g := column_girth (t:=t) (card_pos.mpr hs) hw f inj nz
  apply g
  calc
    ∑ j, column t (f j) = ∑ x : S, column t (v x.val) :=
      S.equivFin.symm.sum_comp (fun x : S => column t (v x.val))
    _ = ∑ x ∈ S, column t (v x) := sum_coe_sort S (fun x => column t (v x))
    _ = ∑ x ∈ S, z x • column t (v x) := by
      apply sum_congr rfl
      intro x hx
      have hn : z x ≠ 0 := (mem_filter.mp hx).2
      rcases (show ∀ a:F₂,a=0 ∨ a=1 from by decide) (z x) with h|h
      · exact (hn h).elim
      · rw [h,one_smul]
    _ = ∑ x, z x • column t (v x) := sum_subset (subset_univ _) (by
      intro x _ hx
      have h : z x = 0 := by by_contra! he; exact hx (mem_filter.mpr ⟨mem_univ _,he⟩)
      rw [h,zero_smul])
    _ = 0 := hz

private theorem twice {E : Type*} [AddCommGroup E] [Module F₂ E] (x:E) : x+x=0 := by
  rw [←two_smul F₂ x,show (2:F₂)=0 by decide,zero_smul]

/-- Below a quarter of the shortest nonzero kernel weight, every affine flat
in the image of a Hamming ball lifts to an affine flat in the ball. -/
theorem sparse_image_flat {G : Type*} [AddCommGroup G] [Module F₂ G] [DecidableEq G]
    {N r : ℕ} (P : Cube N →ₗ[F₂] G)
    (hk : ∀ z, (supp z).card ≤ 4*r → P z=0 → z=0)
    (W : Submodule F₂ G) (t : G)
    (h : t +ᵥ (W : Set G) ⊆ ↑((ball N r).image P)) :
    Module.finrank F₂ W ≤ r := by
  classical
  have ex (x : W) : ∃ y ∈ ball N r, P y = t + x.val := by
    have ht : t+x.val ∈ t +ᵥ (W : Set G) := ⟨x.val,x.property,rfl⟩
    exact mem_image.mp (h ht)
  choose f hf hP using ex
  let lift (x : W) := f x+f 0
  have hmap (x y : W) : lift (x+y)=lift x+lift y := by
    let z := (f (x+y)+f 0)+(f x+f y)
    have hz : z ∈ (4:ℕ) • ball N r := by
      rw [show (4:ℕ)=2+2 by decide,add_nsmul,two_nsmul]
      exact add_mem_add (add_mem_add (hf _) (hf _)) (add_mem_add (hf _) (hf _))
    have hzero : P z=0 := by
      simp only [z,map_add,hP,Submodule.coe_add,Submodule.coe_zero,add_zero]
      calc
        _ = ((t+t)+(t+t))+((x.val+x.val)+(y.val+y.val)) := by abel
        _ = 0 := by simp [twice]
    have flat := hk z (weight_of_mem_sum hz) hzero
    have e := congrArg (fun a => a+(f x+f y)) flat
    change ((f (x+y)+f 0)+(f x+f y))+(f x+f y) = 0+(f x+f y) at e
    rw [add_assoc (f (x+y)+f 0),twice,add_zero,zero_add] at e
    change f (x+y)+f 0=(f x+f 0)+(f y+f 0)
    rw [e]
    calc
      _ = (f x+f y)+(f 0+f 0) := by rw [twice,add_zero]
      _ = _ := by abel
  let L : W →ₗ[F₂] Cube N :=
    { toFun := lift
      map_add' := hmap
      map_smul' := by
        intro c x
        rcases (show ∀ c:F₂, c=0 ∨ c=1 from by decide) c with rfl|rfl <;> simp [lift,twice] }
  have left (x : W) : P (L x) = x.val := by
    change P (f x+f 0)=x.val
    rw [map_add,hP,hP,Submodule.coe_zero,add_zero,add_right_comm,twice,zero_add]
  have inj : Function.Injective L := fun _ _ eq => Subtype.ext (by simpa only [left] using congrArg P eq)
  obtain ⟨p,hp,hd⟩ := max_weight L.range (f 0)
  obtain ⟨_,⟨x,rfl⟩,rfl⟩ := hp
  have id : f 0 +ᵥ L x = f x := by
    change f 0 + (f x+f 0) = f x
    rw [add_left_comm,twice,add_zero]
  change Module.finrank F₂ L.range ≤ (supp (f 0 +ᵥ L x)).card at hd
  rw [id] at hd
  have dim := L.finrank_range_of_inj inj
  rw [dim] at hd
  exact hd.trans (mem_filter.mp (hf x)).2

/-- For every positive r,m an explicit image of a binary radius-one ball has 2^m
points in dimension 2rm, and every affine flat in its r-fold sum has dimension at most r. -/
theorem sparse_cube_examples (r m : ℕ) (hr : 0 < r) (hm : 0 < m) :
    ∃ A : Finset (Cube (2*r*m)), A.card=2^m ∧
      ∀ (W : Submodule F₂ (Cube (2*r*m))) (x : Cube (2*r*m)),
        x +ᵥ (W : Set (Cube (2*r*m))) ⊆ ↑(r • A) → Module.finrank F₂ W ≤ r := by
  classical
  let K := GaloisField 2 m
  let : Fintype K := Fintype.ofFinite K
  let N := Fintype.card Kˣ
  let v (i : Fin N) : K := ((Fintype.equivFin Kˣ).symm i).val
  have hv : Function.Injective v := Units.val_injective.comp (Fintype.equivFin Kˣ).symm.injective
  have hn (i : Fin N) : v i ≠ 0 := Units.ne_zero _
  let e : (Fin (2*r) → K) ≃ₗ[F₂] Cube (2*r*m) := LinearEquiv.ofFinrankEq _ _ (by
    rw [Module.finrank_pi_fintype,Module.finrank_pi,Fintype.card_fin]
    simp [K,GaloisField.finrank _ hm.ne'])
  let P := e.toLinearMap.comp (Fintype.linearCombination F₂ (fun i => column (2*r) (v i)))
  have kernel (z : Cube N) (hw : (supp z).card ≤ 4*r) (hz : P z = 0) : z = 0 := by
    apply syndrome_kernel v hv hn z (t:=2*r) (by omega)
    exact e.injective (hz.trans e.map_zero.symm)
  let A := (ball N 1).image P
  refine ⟨A,?_,?_⟩
  · change ((ball N 1).image P).card=_
    rw [(card_image_iff.mpr (show Set.InjOn P ↑(ball N 1) from by
      intro x hx y hy eq
      have small := weight_of_mem_sum (show x+y∈(2:ℕ) • ball N 1 by
        rw [two_nsmul]; exact add_mem_add hx hy)
      have z := kernel (x+y) (by omega) (by rw [map_add,eq,twice])
      exact (add_right_cancel (z.trans (twice y).symm) : x=y)))]
    rw [Green50HammingDensity.ball_count]
    have card : Fintype.card K = 2^m := by rw [←Nat.card_eq_fintype_card]; exact GaloisField.card 2 m hm.ne'
    have pos := Fintype.card_pos (α:=K)
    have hu : N = Fintype.card K - 1 := Fintype.card_units K
    calc
      _ = N + 1 := by simp [sum_range_succ,Nat.add_comm]
      _ = 2^m := by omega
  · intro W x hW
    apply sparse_image_flat P kernel W x
    have incl : r • A ⊆ (ball N r).image P := by
      change r • (ball N 1).image P ⊆ _
      rw [←image_nsmul]
      apply image_subset_image
      intro z hz
      exact mem_filter.mpr ⟨mem_univ _,by simpa using weight_of_mem_sum hz⟩
    exact hW.trans incl

/-- These witnesses force (2r−1)C ≥ 2r for an all-dimensions r-fold Green bound. -/
theorem bch_coefficient_bound (r : ℕ) (hr : 0 < r) (C : ℝ)
    (h : ∀ n (A : Finset (Cube n)), A.Nonempty →
      ∃ (W : Submodule F₂ (Cube n)) (v : Cube n), v +ᵥ (W : Set (Cube n)) ⊆ ↑(r • A) ∧
        (n:ℝ)-C*Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W) :
    (2*(r:ℝ)-1)*C ≥ 2*r := by
  by_contra! hbad
  let δ : ℝ := 2*r-(2*r-1)*C
  have pos : 0<δ := sub_pos.mpr hbad
  obtain ⟨b,hb⟩ := exists_nat_gt ((r:ℝ)/δ)
  let m := b+1
  have hm : 0 < m := Nat.zero_lt_succ _
  obtain ⟨A,hA,hflat⟩ := sparse_cube_examples r m hr hm
  have ne : A.Nonempty := card_pos.mp (by rw [hA]; positivity)
  obtain ⟨W,x,hW,hd⟩ := h _ A ne
  have hw := hflat W x hW
  have dens : (A.dens:ℝ) = (2:ℝ)^m/2^(2*r*m) := by simp [Finset.dens,hA,Cube,Fintype.card_pi]
  have log : Real.logb 2 (1/(A.dens:ℝ)) = (2*(r:ℝ)-1)*m := by
    rw [dens,one_div_div,Real.logb_div (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    push_cast
    ring
  rw [log] at hd
  push_cast at hd
  have hwr : (Module.finrank F₂ W:ℝ) ≤ r := by exact_mod_cast hw
  have bm : (b:ℝ) < m := by dsimp [m]; push_cast; linarith
  have big := (div_lt_iff₀ pos).mp (hb.trans bm)
  dsimp [δ] at big
  nlinarith only [big,hd,hwr]

/-- Any universal coefficient in the pinned tenfold assertion is at least 20/19. -/
theorem tenfold_requires_twenty_nineteenths (C : ℝ)
    (h : ∀ n (A : Finset (Cube n)), A.Nonempty →
      ∃ (W : Submodule F₂ (Cube n)) (v : Cube n), v +ᵥ (W : Set (Cube n)) ⊆ ↑((10:ℕ) • A) ∧
        (n:ℝ)-C*Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W) : 20/19 ≤ C := by
  have h' := bch_coefficient_bound 10 (by decide) C h
  norm_num at h'
  linarith

end Green50BCH

#print axioms Green50BCH.column_girth
#print axioms Green50BCH.sparse_image_flat
#print axioms Green50BCH.sparse_cube_examples
#print axioms Green50BCH.bch_coefficient_bound
#print axioms Green50BCH.tenfold_requires_twenty_nineteenths
