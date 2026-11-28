import Green53ParityBlocks
import Green53ParityBlockDirections

/-! # Anti-concentration for a row of threshold weights on an affine parity slice -/

open Finset Green53ParityThreshold Green53Threshold
open scoped Classical Pointwise
namespace Green53ParityBlocks

/-- Number of heavy coordinates sufficient for a row's failure probability to be at most 1/(2r). -/
def heavyCount (s r c : ℕ) := (8*(4*r*(c+1))^2)*(2*s+1)

private def translate {J V : Type*} [AddCommGroup V] [Module F V]
    (Q : (J → F) →ₗ[F] V) (anchor d : J → F) (zero : Q d=0) :
    Equiv.Perm {x : J → F // Q x=Q anchor} where
  toFun x := ⟨x.val+d,by simp [x.property,zero]⟩
  invFun x := ⟨x.val-d,by simp [x.property,zero]⟩
  left_inv _ := Subtype.ext (add_sub_cancel_right _ _)
  right_inv _ := Subtype.ext (sub_add_cancel _ _)

/-- On any nonempty affine parity slice, enough heavy weights force a small
fraction in the interval, uniformly in the center and in all other weights. -/
theorem slice_window {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : (J → F) →ₗ[F] V) (anchor : J → F) (a : J → ℝ) (b δ : ℝ) (r c : ℕ)
    (hr : 0 < r) (pos : 0 < δ) (S : Finset J) (h : heavyCount (Module.finrank F V) r c ≤ S.card)
    (large : ∀ j∈S,δ≤|a j|) :
    2*r*(univ.filter (fun x : {x : J → F // Q x=Q anchor} =>
      |b+∑ j,a j*spin (x.val j)|≤c*δ)).card ≤ Fintype.card {x : J → F // Q x=Q anchor} := by
  classical
  let m := 8*(4*r*(c+1))^2
  let G := {x : J → F // Q x=Q anchor}
  obtain ⟨D,piv⟩ := heavy_crossings Q S m h
  let mask (x : J → F) : ℕ := if |b+∑ j,a j*spin (x j)|≤c*δ then 1 else 0
  let f (x : G) (l t : Fin m → Bool) := mask (x.val+moves D.left l+moves D.right t)
  let W := ∑ x : G, mask x.val
  have same (l t : Fin m → Bool) : ∑ x : G,f x l t=W := by
    let d := moves D.left l+moves D.right t
    have dz : Q d=0 := by
      dsimp [d]; rw [map_add,moves_kernel Q D.left (fun i => (piv i).2.1),
        moves_kernel Q D.right (fun i => (piv i).2.2),zero_add]
    let e := translate Q anchor d dz
    calc
      _ = ∑ x : G,mask (e x).val := sum_congr rfl (fun x _ => by
        change mask (x.val+moves D.left l+moves D.right t)=mask (x.val+(moves D.left l+moves D.right t))
        rw [add_assoc])
      _ = _ := Equiv.sum_comp e (fun x : G => mask x.val)
  have row (x : G) : 2*r*(∑ l, ∑ t, f x l t) ≤ 2^m*2^m := by
    obtain ⟨offset,B,C,mag,eq⟩ := crossing_row D x.val a b
    have big i : δ ≤ |C i| := by rw [mag]; exact large _ (piv i).1
    have lim := two_sign_window hr (m:=m) (c:=c) rfl offset B C pos big
    simp only [card_filter] at lim
    simpa only [f,mask,eq] using lim
  have total : (2^m*2^m)*(2*r*W) ≤ (2^m*2^m)*Fintype.card G := calc
    _ = 2*r*(∑ l,∑ t,∑ x : G, f x l t) := by simp_rw [same]; simp; ring
    _ = ∑ x : G,2*r*(∑ l,∑ t,f x l t) := by
      rw [←mul_sum]
      congr 1
      calc
        _ = ∑ l,∑ x : G,∑ t,f x l t := sum_congr rfl (fun _ _ => sum_comm)
        _ = _ := sum_comm
    _ ≤ ∑ _x : G,2^m*2^m := sum_le_sum (fun x _ => row x)
    _ = _ := by simp; ring
  have endBound := Nat.le_of_mul_le_mul_left total (by positivity)
  simpa only [W,mask,card_filter,G] using endBound
/-- Choose one feasible signing with simultaneous margins using a number of
coordinates polynomial in the row count and the number of parity checks. -/
theorem polynomial_slice_margins {J V : Type*} [Fintype J] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : (J → F) →ₗ[F] V) (anchor : J → F) (r c : ℕ)
    (A : Fin r → J → ℝ) (b : Fin r → ℝ) :
    ∃ (t : Finset J) (x : J → F), t.card ≤ r*heavyCount (Module.finrank F V) r c ∧
      Q x=Q anchor ∧ ∀ i j,j∉t → (c:ℝ)*|A i j| ≤ |b i+∑ k∈t,A i k*spin (x k)| := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl|hr
  · exact ⟨∅,anchor,by simp,rfl,fun i => i.elim0⟩
  let h := heavyCount (Module.finrank F V) r c
  let G := {x : J → F // Q x=Q anchor}
  by_cases enough : h ≤ Fintype.card J
  · choose top part card order using fun i => largest (fun j => |A i j|) (univ : Finset J) h
    have len (i : Fin r) : (top i).card=h := by rw [card i,card_univ]; exact min_eq_left enough
    let t := univ.biUnion top
    have sub (i : Fin r) : top i⊆t := subset_biUnion_of_mem top (mem_univ i)
    have tc : t.card ≤ r*h := by
      calc _ ≤ _ := card_biUnion_le
           _ = _ := by simp [len]
    let U := univ\t
    choose M nonneg cap attained using fun i => row_cap U (A i)
    let a i (j : J) := if j∈t then A i j else 0
    let bad (i : Fin r) := univ.filter (fun x : G =>
      0 < M i ∧ |b i+∑ j,a i j*spin (x.val j)|≤c*M i)
    have each i : 2*r*(bad i).card ≤ Fintype.card G := by
      by_cases pos : 0 < M i
      · rcases attained i with h0|⟨j,hj,eq⟩
        · linarith
        have heavy l (hl : l∈top i) : M i ≤ |a i l| := by
          have no : j∉top i := fun p => (mem_sdiff.mp hj).2 (sub i p)
          simpa [a,sub i hl,eq] using order i l hl j (mem_univ _) no
        have lim := slice_window Q anchor (a i) (b i) (M i) r c hr pos (top i) (len i).ge heavy
        simpa only [bad,pos,true_and,G] using lim
      · simp [bad,pos]
    have doubles : 2*r*(univ.biUnion bad).card ≤ r*Fintype.card G := calc
      _ ≤ 2*r*(∑ i,(bad i).card) := Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ i,2*r*(bad i).card := mul_sum _ _ _
      _ ≤ ∑ _i : Fin r,Fintype.card G := sum_le_sum (fun i _ => each i)
      _ = _ := by simp
    have bound : 2*(univ.biUnion bad).card ≤ Fintype.card G := by
      apply Nat.le_of_mul_le_mul_left _ hr
      simpa only [mul_left_comm,mul_assoc] using doubles
    have gn : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨⟨anchor,rfl⟩⟩
    have count : (univ.biUnion bad).card < (univ : Finset G).card := by rw [card_univ]; omega
    obtain ⟨x,hx⟩ := exists_mem_notMem_of_card_lt_card count
    refine ⟨t,x.val,tc,x.property,?_⟩
    intro i j hj
    have hj' : j∈U := mem_sdiff.mpr ⟨mem_univ j,hj⟩
    by_cases pos : 0 < M i
    · have hi : x∉bad i := fun p => hx.2 (mem_biUnion.mpr ⟨i,mem_univ _,p⟩)
      have ref : (c:ℝ)*M i < |b i+∑ l,a i l*spin (x.val l)| := by simpa [bad,pos] using hi
      have eq : (∑ l,a i l*spin (x.val l))=∑ l∈t,A i l*spin (x.val l) := by simp [a,ite_mul,sum_ite_mem]
      rw [eq] at ref
      exact (mul_le_mul_of_nonneg_left (cap i j hj') (Nat.cast_nonneg c)).trans ref.le
    · have zero := (cap i j hj').trans (not_lt.mp pos)
      rw [abs_nonpos_iff.mp zero,abs_zero,mul_zero]; exact abs_nonneg _
  · refine ⟨univ,anchor,?_,rfl,by simp⟩
    rw [card_univ]
    exact (not_le.mp enough).le.trans (Nat.le_mul_of_pos_left _ hr)

open Green52Complements in
/-- Joint polynomial bound for any real readout of threshold tests on an affine parity map. -/
theorem polynomial_parity_subspace {n N r : ℕ} {C : Type*}
    (E : Cube n →ₗ[F] Cube N) (h : Cube N) (A : Fin r → Fin N → ℝ) (b : Fin r → ℝ)
    (colour : (Fin r → Bool) → C) :
    let s := Module.finrank F (Cube N ⧸ E.range)
    ∃ (i : C) (W : Submodule F (Cube n)),
      n ≤ Module.finrank F W + 512*(2*s+1)*r^3*(r+s+1)^2 ∧
      (W : Set _) ⊆ {x | colour (readings A b (fun j => spin ((E x+h) j)))=i} +
        {x | colour (readings A b (fun j => spin ((E x+h) j)))=i} := by
  let s := Module.finrank F (Cube N ⧸ E.range)
  obtain ⟨t,x,card,hx,mg⟩ := polynomial_slice_margins E.range.mkQ h r (2*r+2*s+1) A b
  obtain ⟨y,cover⟩ := slice_of_margin E.range.mkQ h A b t x hx mg
  obtain ⟨i,W,dim,sub⟩ := subspace_of_coordinates E h A b colour t y cover
  refine ⟨i,W,dim.trans (Nat.add_le_add_left (card.trans_eq ?_) _),sub⟩
  dsimp [heavyCount,s]; ring

open Green52Complements in
/-- Explicit polynomial codimension in the original affine-subspace conclusion. -/
theorem polynomial_parity_partition (r s n k : ℕ) (as : Fin k → Set (Cube n))
    (_cover : (⋃ i, as i)=Set.univ) (_disjoint : Pairwise (fun i j => Disjoint (as i) (as j)))
    (tests : ∃ (N : ℕ) (E : Cube n →ₗ[F] Cube N) (h : Cube N)
      (A : Fin r → Fin N → ℝ) (b : Fin r → ℝ) (colour : (Fin r → Bool) → Fin k),
      Module.finrank F (Cube N ⧸ E.range) ≤ s ∧
      ∀ i, as i={x | colour (readings A b (fun j => spin ((E x+h) j)))=i}) :
    ∃ i, Flat n (512*(2*s+1)*r^3*(r+s+1)^2) (as i) := by
  obtain ⟨N,E,h,A,b,colour,rank,classes⟩ := tests
  obtain ⟨i,W,dim,sub⟩ := polynomial_parity_subspace E h A b colour
  refine ⟨i,W.toAffineSubspace,?_,?_⟩
  · rw [classes]; exact sub
  · rw [Submodule.toAffineSubspace_direction]
    refine dim.trans ?_
    gcongr

open Green52Complements in
/-- It suffices that the threshold description hold on one affine chart. -/
theorem polynomial_chart {n m d N r : ℕ} {C : Type*} (f : Cube n → C) (x₀ : Cube n)
    (L : Cube m →ₗ[F] Cube n) (inj : Function.Injective L) (chart : n ≤ m+d)
    (E : Cube m →ₗ[F] Cube N) (h : Cube N) (A : Fin r → Fin N → ℝ) (b : Fin r → ℝ)
    (colour : (Fin r → Bool) → C)
    (agree : ∀ u, f (x₀+L u)=colour (readings A b (fun j => spin ((E u+h) j)))) :
    let s := Module.finrank F (Cube N ⧸ E.range)
    ∃ (i : C) (W : Submodule F (Cube n)),
      n ≤ Module.finrank F W + d+512*(2*s+1)*r^3*(r+s+1)^2 ∧
      (W : Set _) ⊆ {x | f x=i} + {x | f x=i} := by
  classical
  obtain ⟨i,U,dim,sub⟩ := polynomial_parity_subspace E h A b colour
  refine ⟨i,U.map L,?_,?_⟩
  · have eq := (Submodule.equivMapOfInjective L inj U).finrank_eq
    omega
  · rintro _ ⟨z,hz,rfl⟩
    obtain ⟨u,hu,v,hv,eq⟩ := sub hz
    refine ⟨x₀+L u,(agree u).trans hu,x₀+L v,(agree v).trans hv,?_⟩
    have cancel : x₀+x₀=0 := by ext j; exact (by decide : ∀ a : F,a+a=0) (x₀ j)
    rw [←eq,map_add]
    calc (x₀+L u)+(x₀+L v) = x₀+x₀+(L u+L v) := by abel
         _ = _ := by rw [cancel,zero_add]

open Green52Complements in
/-- Both weights and readout may depend arbitrarily on d parity bits. -/
theorem parity_controlled_thresholds {n r d : ℕ} {C : Type*}
    (P : Cube n →ₗ[F] Cube d) (B : Cube n ≃ₗ[F] Cube n)
    (A : Cube d → Fin r → Fin n → ℝ) (b : Cube d → Fin r → ℝ)
    (colour : Cube d → (Fin r → Bool) → C) :
    let f (x : Cube n) := colour (P x) (readings (A (P x)) (b (P x)) (fun j => spin (B x j)))
    ∃ (i : C) (W : Submodule F (Cube n)),
      n ≤ Module.finrank F W + d+512*(2*d+1)*r^3*(r+d+1)^2 ∧
      (W : Set _) ⊆ {x | f x=i} + {x | f x=i} := by
  classical
  let H := P.ker
  let m := Module.finrank F H
  let e : H ≃ₗ[F] Cube m := (Module.finBasis F H).equivFun
  let L := H.subtype.comp e.symm.toLinearMap
  let E := B.toLinearMap.comp L
  have inj : Function.Injective L := H.subtype_injective.comp e.symm.injective
  have ndim : Module.finrank F (Cube n)=n := by simp [Cube]
  have ddim : Module.finrank F (Cube d)=d := by simp [Cube]
  have mdim : Module.finrank F (Cube m)=m := by simp [Cube]
  have chart : n ≤ m+d := by
    have eq := P.finrank_range_add_finrank_ker
    have cap := P.range.finrank_le
    change Module.finrank F P.range + m=Module.finrank F (Cube n) at eq
    rw [ndim] at eq
    rw [ddim] at cap
    omega
  have rank : Module.finrank F (Cube n ⧸ E.range) ≤ d := by
    have eq := E.range.finrank_quotient_add_finrank
    have full := LinearMap.finrank_range_of_inj (f:=E) (B.injective.comp inj)
    rw [full,mdim,ndim] at eq
    omega
  let f (x : Cube n) := colour (P x) (readings (A (P x)) (b (P x)) (fun j => spin (B x j)))
  have agree (u : Cube m) :
      f (0+L u)=colour 0 (readings (A 0) (b 0) (fun j => spin ((E u+0) j))) := by
    have zero : P (L u)=0 := LinearMap.mem_ker.mp (e.symm u).property
    simp only [f,zero_add,zero,add_zero]; rfl
  obtain ⟨i,W,dim,sub⟩ := polynomial_chart f 0 L inj chart E 0 (A 0) (b 0) (colour 0) agree
  refine ⟨i,W,dim.trans ?_,sub⟩
  gcongr

end Green53ParityBlocks
#print axioms Green53ParityBlocks.slice_window
#print axioms Green53ParityBlocks.polynomial_slice_margins
#print axioms Green53ParityBlocks.polynomial_parity_subspace
#print axioms Green53ParityBlocks.polynomial_parity_partition
#print axioms Green53ParityBlocks.polynomial_chart
#print axioms Green53ParityBlocks.parity_controlled_thresholds
