import Green50HammingDensity

/-!
# Sparse random images with no large affine flat in their iterated sums

Count linear maps whose images of a binary Hamming ball cover an affine flat.
A separate estimate for singleton targets keeps enough distinct generator images.
-/

open Finset
open scoped Pointwise
namespace Green50RandomImages
open Green50Downsets Green50Sharp
local notation "F₂" => ZMod 2

private def evaluations {M n t : ℕ} (z : Fin t → Cube M) :
    (Cube M →ₗ[F₂] Cube n) →ₗ[F₂] (Fin t → Cube n) :=
  LinearMap.pi fun i => LinearMap.applyₗ (R:=F₂) (z i)

private theorem evaluations_surj {M n t : ℕ} (z : Fin t → Cube M) (hi : LinearIndependent F₂ z) :
    Function.Surjective (evaluations (n:=n) z) := by
  classical
  let L := Fintype.linearCombination F₂ z
  obtain ⟨g,hg⟩ := L.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hi.fintypeLinearCombination_injective)
  intro y
  let Y := Fintype.linearCombination F₂ y
  refine ⟨Y.comp g,funext fun i => ?_⟩
  have e := LinearMap.congr_fun hg (Pi.single i (1:F₂))
  change g (Fintype.linearCombination F₂ z (Pi.single i 1)) = _ at e
  simp only [Fintype.linearCombination_apply_single,one_smul,LinearMap.id_apply] at e
  change Fintype.linearCombination F₂ y (g (z i)) = y i
  rw [e,Fintype.linearCombination_apply_single,one_smul]
private def letters {M : ℕ} (s : Finset (Fin M)) : Finset (Cube M) :=
  insert 0 (s.image fun j => Pi.single j (1:F₂))

private theorem words {M r : ℕ} (s : Finset (Fin M)) (x : Cube M) (hs : supp x ⊆ s)
    (hw : (supp x).card ≤ r) : x ∈ r • letters s := by
  classical
  induction r generalizing x with
  | zero =>
    have h0 : supp x=∅ := card_eq_zero.mp (by omega)
    have hx : x=0 := by
      funext j
      by_contra! hn
      have : j∈supp x := mem_filter.mpr ⟨mem_univ _,hn⟩
      simp [h0] at this
    simp [hx]
  | succ r ih =>
    rw [succ_nsmul]
    by_cases hle : (supp x).card ≤ r
    · have h := add_mem_add (ih x hs hle) (show (0:Cube M)∈letters s from mem_insert_self ..)
      simpa using h
    · obtain ⟨j,hj⟩ := card_pos.mp (show 0<(supp x).card by omega)
      have h1 : x j=1 := by
        have hn : x j ≠ 0 := (mem_filter.mp hj).2
        rcases (show ∀ u:F₂, u=0 ∨ u=1 from by decide) (x j) with h|h
        · exact (hn h).elim
        · exact h
      let y := Function.update x j 0
      have he : supp y = (supp x).erase j := by
        ext k
        by_cases hk : k=j <;> simp [supp,y,hk,Function.update_of_ne]
      have hy : y ∈ r • letters s := ih y (he ▸ (erase_subset j _).trans hs) (by
        rw [he,card_erase_of_mem hj]; omega)
      have hj' : Pi.single j (1:F₂) ∈ letters s := mem_insert_of_mem (mem_image_of_mem _ (hs hj))
      have id : y + Pi.single j (1:F₂) = x := by
        funext k
        by_cases hk : k=j <;> simp [y,hk,h1,Function.update_of_ne,Pi.single_eq_of_ne]
      exact id ▸ add_mem_add hy hj'

private theorem small_alphabet {M : ℕ} (s : Finset (Fin M)) (r : ℕ) :
    (r • letters s).card ≤ (s.card+1)^r := by
  have hc : (letters s).card ≤ s.card+1 :=
    (card_insert_le ..).trans (by have h := card_image_le (s:=s) (f:=fun j => Pi.single j (1:F₂)); omega)
  induction r with
  | zero => simp
  | succ r ih =>
    rw [succ_nsmul,pow_succ]
    exact (card_add_le ..).trans (Nat.mul_le_mul ih hc)

private theorem evaluation_count {M n t : ℕ} (z : Fin t → Cube M) (hi : LinearIndependent F₂ z)
    (F : Finset (Cube n)) :
    Nat.card {P : Cube M →ₗ[F₂] Cube n // ∀ i, P (z i) ∈ F} * (2^n)^t =
    F.card^t * Nat.card (Cube M →ₗ[F₂] Cube n) := by
  classical
  let : Fintype (Cube M →ₗ[F₂] Cube n) := Fintype.ofInjective
    (fun p : Cube M →ₗ[F₂] Cube n => (p : Cube M → Cube n)) DFunLike.coe_injective
  let E := evaluations (n:=n) z
  choose g hg using evaluations_surj (n:=n) z hi
  let σ (f : Fin t → F) := g (fun i => (f i).val)
  let target := {P : Cube M →ₗ[F₂] Cube n // ∀ i, P (z i) ∈ F}
  let key (p : target) (i : Fin t) : F := ⟨p.val (z i),p.property i⟩
  let bij : target ≃ (Fin t → F) × E.ker :=
    { toFun := fun p => (key p,⟨p.val-σ (key p),LinearMap.mem_ker.mpr (by
        rw [map_sub]; exact sub_eq_zero.mpr (hg _).symm)⟩)
      invFun := fun p => ⟨p.2.val+σ p.1,by
        intro i
        have e := congrFun (show E (p.2.val+σ p.1) = fun j => (p.1 j).val by
          rw [map_add,LinearMap.mem_ker.mp p.2.property,zero_add]; exact hg _) i
        change (p.2.val+σ p.1) (z i) ∈ F
        rw [show (p.2.val+σ p.1) (z i)=(p.1 i).val from e]
        exact (p.1 i).property⟩
      left_inv := fun p => Subtype.ext (sub_add_cancel _ _)
      right_inv := by
        rintro ⟨f,b⟩
        have e : E (b.val+σ f) = fun i => (f i).val := by
          rw [map_add,LinearMap.mem_ker.mp b.property,zero_add]; exact hg _
        apply Prod.ext
        · exact funext fun i => Subtype.ext (congrFun e i)
        · apply Subtype.ext
          change (b.val+σ f)-σ _ = b.val
          have inside (i : Fin t) : (b.val+σ f) (z i) ∈ F := by
            rw [show (b.val+σ f) (z i) = (f i).val from congrFun e i]
            exact (f i).property
          have he : key ⟨b.val+σ f,inside⟩ = f := funext fun i => Subtype.ext (congrFun e i)
          rw [he,add_sub_cancel_right] }
  have count := Nat.card_congr bij
  have d := E.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (evaluations_surj z hi),finrank_top] at d
  have sizes : Nat.card (Cube M →ₗ[F₂] Cube n) = Nat.card E.ker * (2^n)^t := by
    simp only [Nat.card_eq_fintype_card]
    rw [Module.card_eq_pow_finrank (K:=F₂) (V:=Cube M →ₗ[F₂] Cube n),
      Module.card_eq_pow_finrank (K:=F₂) (V:=E.ker),←d,pow_add,ZMod.card]
    simp [Cube,Module.finrank_pi_fintype,←pow_mul,Nat.mul_comm]
  change Nat.card target * _ = _
  rw [count,Nat.card_prod,sizes]
  simp [Nat.card_eq_fintype_card,Fintype.card_pi,Nat.mul_assoc]

private theorem sparse_independent {M r : ℕ} (S : Finset (Cube M))
    (hw : ∀ z∈S, (supp z).card ≤ r) (t : ℕ) (h : (r*t+1)^r < S.card) :
    ∃ z : Fin t → Cube M, LinearIndependent F₂ z ∧ ∀ i, z i ∈ S := by
  classical
  induction t with
  | zero => exact ⟨Fin.elim0,linearIndependent_empty_type,fun i => i.elim0⟩
  | succ t ih =>
    have cost : (r*t+1)^r ≤ (r*(t+1)+1)^r := by
      apply Nat.pow_le_pow_left; rw [Nat.mul_succ]; omega
    obtain ⟨z,hi,hz⟩ := ih (cost.trans_lt h)
    let R := univ.biUnion fun i => supp (z i)
    have size : R.card ≤ r*t := calc
      _ ≤ ∑ i : Fin t, (supp (z i)).card := card_biUnion_le
      _ ≤ ∑ _i : Fin t, r := sum_le_sum fun i _ => hw _ (hz i)
      _ = _ := by simp [Nat.mul_comm]
    have outside : ∃ x∈S, ¬supp x⊆R := by
      by_contra! hall
      have inc : S⊆r • letters R := fun x hx => words _ _ (hall x hx) (hw _ hx)
      have le := (card_le_card inc).trans (small_alphabet R r)
      have last : (R.card+1)^r ≤ (r*t+1)^r := Nat.pow_le_pow_left (by omega) _
      exact (h.not_ge ((le.trans last).trans cost))
    obtain ⟨x,hx,hs⟩ := outside
    obtain ⟨j,hj,hjR⟩ := Finset.not_subset.mp hs
    have hnot : x ∉ Submodule.span F₂ (Set.range z) := by
      let L : Cube M →ₗ[F₂] F₂ := LinearMap.proj j
      have inc : Submodule.span F₂ (Set.range z) ≤ L.ker := Submodule.span_le.mpr (by
        rintro _ ⟨i,rfl⟩
        apply LinearMap.mem_ker.mpr
        change z i j=0
        by_contra! hn
        exact hjR (mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hn⟩⟩))
      exact fun e => (mem_filter.mp hj).2 (LinearMap.mem_ker.mp (inc e))
    exact ⟨Fin.cons x z,linearIndependent_finCons.mpr ⟨hi,hnot⟩,Fin.cases hx hz⟩

/-- The number of linear maps sending a linearly independent tuple into a fixed finite set. -/
private theorem count_filtered {M n t : ℕ} [Fintype (Cube M →ₗ[F₂] Cube n)]
    (z : Fin t → Cube M) (hi : LinearIndependent F₂ z) (F : Finset (Cube n)) :
    (univ.filter (fun P : Cube M →ₗ[F₂] Cube n => ∀ i, P (z i) ∈ F)).card * (2^n)^t =
      F.card^t * Fintype.card (Cube M →ₗ[F₂] Cube n) := by
  classical
  simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype] using evaluation_count z hi F

private theorem sparse_flat_union {M n k t r : ℕ} [Fintype (Cube M →ₗ[F₂] Cube n)]
    (flats : (Fin (k+1) → Cube n) → Finset (Cube n))
    (sizes : ∀ b, (flats b).card ≤ 2^k) :
    ∃ bad : Finset (Cube M →ₗ[F₂] Cube n),
      bad.card * (2^n)^t ≤ (2^n)^(k+1)*(M+1)^(r*t)*(2^k)^t*Fintype.card (Cube M →ₗ[F₂] Cube n) ∧
      ∀ P∉bad, ∀ b, ((univ.filter fun z : Cube M => (supp z).card ≤ r ∧ P z∈flats b).card ≤ (r*t+1)^r) := by
  classical
  let X := r • letters (univ : Finset (Fin M))
  let Z := {z : Fin t → X // LinearIndependent F₂ (fun i => (z i).val)}
  let params := (Fin (k+1) → Cube n) × Z
  let hit (p : params) := univ.filter fun L : Cube M →ₗ[F₂] Cube n => ∀ i, L ((p.2.val i).val) ∈ flats p.1
  let bad := univ.biUnion hit
  have ix : Fintype.card Z ≤ (M+1)^(r*t) := calc
    _ ≤ Fintype.card (Fin t → X) := Fintype.card_le_of_injective _ Subtype.val_injective
    _ = X.card^t := by simp [Fintype.card_pi]
    _ ≤ ((M+1)^r)^t := Nat.pow_le_pow_left (by simpa [X] using small_alphabet (univ : Finset (Fin M)) r) _
    _ = _ := (pow_mul ..).symm
  have par : Fintype.card params ≤ (2^n)^(k+1)*(M+1)^(r*t) := by
    simp only [params,Fintype.card_prod,Fintype.card_pi,Fintype.card_fin,Cube,ZMod.card,Finset.prod_const,card_univ]
    exact Nat.mul_le_mul_left _ ix
  let total := Fintype.card (Cube M →ₗ[F₂] Cube n)
  have one (p : params) : (hit p).card*(2^n)^t ≤ (2^k)^t * total := by
    rw [show (hit p).card*(2^n)^t=(flats p.1).card^t*total from count_filtered _ p.2.property _]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (sizes _) _)
  refine ⟨bad,?_,?_⟩
  · calc
      bad.card * (2^n)^t ≤ (∑ p : params, (hit p).card)*(2^n)^t := Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p : params, (hit p).card*(2^n)^t := sum_mul ..
      _ ≤ ∑ _p : params, (2^k)^t*total := sum_le_sum fun i _ => one i
      _ = Fintype.card params*((2^k)^t*total) := by simp
      _ ≤ _ := by dsimp [total]; grw [par]; simp [Nat.mul_assoc]
  · intro P hp b
    let S := univ.filter fun z : Cube M => (supp z).card ≤ r ∧ P z∈flats b
    by_contra! h
    obtain ⟨z,hi,hz⟩ := sparse_independent S (fun x hx => (mem_filter.mp hx).2.1) t h
    let v (i : Fin t) : X := ⟨z i,words _ _ (subset_univ _) ((mem_filter.mp (hz i)).2.1)⟩
    exact hp (mem_biUnion.mpr ⟨(b,⟨v,hi⟩),mem_univ _,mem_filter.mpr ⟨mem_univ _,fun i => (mem_filter.mp (hz i)).2.2⟩⟩)

private def flatSet {n k : ℕ} (b : Fin (k+1) → Cube n) : Finset (Cube n) := by
  classical
  exact univ.image fun u : Cube k => b 0 + Fintype.linearCombination F₂ (fun j => b j.succ) u

private theorem flatSet_card {n k : ℕ} (b : Fin (k+1) → Cube n) : (flatSet b).card ≤ 2^k := by
  classical
  apply (card_image_le ..).trans
  simp [Cube,Fintype.card_pi]

private theorem flat_param {n k : ℕ} (W : Submodule F₂ (Cube n)) (x : Cube n)
    (h : k ≤ Module.finrank F₂ W) :
    ∃ b : Fin (k+1) → Cube n, (flatSet b).card=2^k ∧
      (↑(flatSet b) : Set (Cube n)) ⊆ x +ᵥ (W : Set (Cube n)) := by
  classical
  have dim : Module.finrank F₂ (Cube k) ≤ Module.finrank F₂ W := by simpa [Cube] using h
  obtain ⟨L,hi⟩ := (finrank_le_iff_exists_linearMap (R:=F₂)).mp dim
  let F := W.subtype.comp L
  let b : Fin (k+1) → Cube n := Fin.cons x (fun j : Fin k => F (Pi.single j (1:F₂)))
  have eq (u : Cube k) : Fintype.linearCombination F₂ (fun j => b j.succ) u = F u := by
    have id : u = ∑ j, u j • Pi.single j (1:F₂) := by
      funext i
      simp [Finset.sum_apply,Pi.single_apply,Pi.smul_apply]
    change ∑ j, u j • F (Pi.single j 1) = F u
    conv_rhs => rw [id,map_sum]
    simp
  refine ⟨b,?_,?_⟩
  · rw [flatSet,card_image_of_injective _ (fun u v hu => hi (Subtype.ext (show F u=F v by
      simpa only [eq,add_right_inj] using hu)))]
    simp [Cube,Fintype.card_pi]
  · intro y hy
    obtain ⟨u,_,rfl⟩ := mem_image.mp hy
    exact (eq u).symm ▸ (show x + F u ∈ x +ᵥ (W:Set (Cube n)) from ⟨(L u).val,(L u).property,rfl⟩)

/-- Finite counting criterion for a large set whose r-fold sum avoids every k-flat. -/
theorem finite_witness (M n k t r a : ℕ) (hcard : 3*a ≤ M+1) (hspan : (r*t+1)^r < 2^k)
    (hsmall : 2*(M+1)^2 < 2^n)
    (hlarge : 2*((2^n)^(k+1)*(M+1)^(r*t)*(2^k)^t) < (2^n)^t) :
    ∃ A : Finset (Cube n), A.card=a ∧ ∀ (W : Submodule F₂ (Cube n)) (x : Cube n),
      x +ᵥ (W:Set (Cube n)) ⊆ ↑(r • A) → Module.finrank F₂ W < k := by
  classical
  let : Fintype (Cube M →ₗ[F₂] Cube n) := Fintype.ofInjective
    (fun p : Cube M →ₗ[F₂] Cube n => (p : Cube M → Cube n)) DFunLike.coe_injective
  let total := Fintype.card (Cube M →ₗ[F₂] Cube n)
  have hp : 0<total := Fintype.card_pos
  obtain ⟨big,hbig,bound⟩ := sparse_flat_union (M:=M) (t:=t) (r:=r) (flatSet (n:=n) (k:=k)) flatSet_card
  obtain ⟨little,hlit,fibs⟩ := sparse_flat_union (M:=M) (k:=0) (t:=2) (r:=1)
    (fun b : Fin (0+1) → Cube n => {b 0}) (by simp)
  have half {B S D : ℕ} (h : B*D ≤ S*total) (h' : 2*S < D) : 2*B < total := by
    have le : (2*B)*D ≤ (2*S)*total := by nlinarith only [h]
    have lt := Nat.mul_lt_mul_of_pos_right h' hp
    exact Nat.lt_of_mul_lt_mul_right (le.trans_lt (by simpa only [Nat.mul_comm D total] using lt))
  have hB := half hbig hlarge
  have hL : 2*little.card < total := by
    have hh : little.card*((2^n)*(2^n)) ≤ (M+1)^2*total*(2^n) := by
      simpa [pow_two,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hlit
    have le : little.card*(2^n) ≤ (M+1)^2*total := by
      rw [←Nat.mul_assoc] at hh
      exact Nat.le_of_mul_le_mul_right hh (by positivity)
    exact half le hsmall
  have small := card_union_le big little
  obtain ⟨P,_,hP⟩ := exists_mem_notMem_of_card_lt_card (s:=big∪little)
    (t:=(univ:Finset (Cube M →ₗ[F₂] Cube n))) (by rw [card_univ]; change _ < total; omega)
  have hnb : P ∉ big := fun h => hP (mem_union_left _ h)
  have hnl : P ∉ little := fun h => hP (mem_union_right _ h)
  let X := (ball M 1).image P
  have hc : (ball M 1).card = M+1 := by rw [Green50HammingDensity.ball_count]; simp [sum_range_succ,Nat.add_comm]
  have size : M+1 ≤ 3*X.card := calc
    _ = ∑ y ∈ X, ((ball M 1).filter (fun z => P z=y)).card := hc.symm.trans (card_eq_sum_card_image P _)
    _ ≤ ∑ _y ∈ X, 3 := by
      apply sum_le_sum
      intro y _
      have hh := fibs P hnl (fun _ => y)
      simpa [ball,Finset.filter_filter] using hh
    _ = _ := by simp [Nat.mul_comm]
  obtain ⟨A,hAX,ha⟩ := exists_subset_card_eq (show a ≤ X.card by omega)
  refine ⟨A,ha,?_⟩
  intro W x hW
  by_contra! hdim
  obtain ⟨b,bc,bsub⟩ := flat_param W x hdim
  let S := univ.filter fun z : Cube M => (supp z).card ≤ r ∧ P z∈flatSet b
  have inc : flatSet b ⊆ S.image P := by
    intro y hy
    have hit := nsmul_subset_nsmul_left (n:=r) hAX (hW (bsub hy))
    change y ∈ r • (ball M 1).image P at hit
    rw [←image_nsmul] at hit
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hit
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_univ _,by simpa using weight_of_mem_sum hz,hy⟩,rfl⟩
  have small := ((card_le_card inc).trans card_image_le).trans (bound P hnb b)
  exact hspan.not_ge (bc ▸ small)

private theorem power_gap (a r : ℕ) : ∃ k : ℕ, (a*(k+1)+1)^r < 2^k := by
  let L := 2*(a+r+6)
  have sq (j : ℕ) : (j+4)*(j+4) ≤ 2^(j+4) := by
    induction j with
    | zero => decide
    | succ j ih =>
      calc
        _ ≤ 2*((j+4)*(j+4)) := by nlinarith
        _ ≤ 2*2^(j+4) := Nat.mul_le_mul_left _ ih
        _ = _ := by rw [show j+1+4=j+4+1 by omega,pow_succ]; ring
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hs : L*L ≤ 2^L := by simpa only [Nat.sub_add_cancel hL] using sq (L-4)
  let k := 2^L
  have ke : k+1 ≤ 2^(L+1) := by
    rw [pow_succ]
    have pos : 0<k := by dsimp [k]; positivity
    change k+1 ≤ k*2
    omega
  have ha : a+1 ≤ 2^(a+1) := Nat.le_of_lt (Nat.lt_two_pow_self)
  have base : a*(k+1)+1 ≤ 2^((a+1)+(L+1)) := calc
    _ ≤ (a+1)*(k+1) := by nlinarith
    _ ≤ 2^(a+1)*2^(L+1) := Nat.mul_le_mul ha ke
    _ = _ := (pow_add ..).symm
  have small : ((a+1)+(L+1))*r < k := calc
    _ ≤ (2*L)*r := Nat.mul_le_mul_right _ (by dsimp [L]; omega)
    _ = (2*r)*L := by ring
    _ < L*L := Nat.mul_lt_mul_of_pos_right (by dsimp [L]; omega) (by omega)
    _ ≤ k := hs
  exact ⟨k,(Nat.pow_le_pow_left base r).trans_lt (by rw [←pow_mul]; exact Nat.pow_lt_pow_right (by decide) small)⟩

/-- At every sufficiently large scale in a fixed progression, the r-fold sum can exclude every flat of a fixed
dimension, even with generator count close to the r-th root of the ambient order. -/
theorem sparse_examples (r b : ℕ) (hr : 2 ≤ r) :
    ∃ k S₀ : ℕ, ∀ s ≥ S₀, ∃ A : Finset (Cube ((r*b+1)*s)),
      A.card=2^(b*s) ∧ ∀ (W : Submodule F₂ (Cube ((r*b+1)*s))) (x : Cube ((r*b+1)*s)),
        x +ᵥ (W:Set (Cube ((r*b+1)*s))) ⊆ ↑(r • A) → Module.finrank F₂ W < k := by
  obtain ⟨k,hk⟩ := power_gap (r*(r*b+2)) r
  let t := (r*b+2)*(k+1)
  have knob : (r*t+1)^r < 2^k := by simpa only [t,Nat.mul_assoc] using hk
  refine ⟨k,6+(2*r+k)*t,?_⟩
  intro s hs₀
  let m := b*s
  let n := (r*b+1)*s
  let M := 2^(m+2)-1
  have hp : 0 < (2:ℕ)^(m+2) := by positivity
  have Msize : M+1=2^(m+2) := Nat.sub_add_cancel (by omega)
  have hdim : 1+2*(m+2) < n := by
    have hs : 6 ≤ s := by omega
    have hh := Nat.mul_le_mul_right m hr
    change 1 + 2*(b*s+2) < (r*b+1)*s
    dsimp [m] at hh
    rw [Nat.add_mul,one_mul,Nat.mul_assoc]
    omega
  have grow : 1+n*(k+1)+(m+2)*(r*t)+k*t < n*t := by
    have edge : 1+(2*r+k)*t < s*(k+1) := calc
      _ < s := by omega
      _ ≤ s*(k+1) := Nat.le_mul_of_pos_right _ (by omega)
    have balance : n*t = n*(k+1)+(m+2)*(r*t)+k*t + s*(k+1) - (2*r+k)*t := by
      dsimp [n,m,t]; exact Nat.eq_sub_of_add_eq (by ring)
    omega
  refine finite_witness M n k t r (2^m) ?_ knob ?_ ?_
  · rw [Msize,pow_add]; norm_num; omega
  · rw [Msize,←pow_mul,show 2*((2:ℕ)^((m+2)*2))=2^(1+(m+2)*2) by rw [pow_add,pow_one]]
    apply Nat.pow_lt_pow_right (by decide)
    omega
  · rw [Msize,←pow_mul,←pow_mul,←pow_mul,←pow_mul]
    convert Nat.pow_lt_pow_right (by decide : (1:ℕ)<2) grow using 1
    simp only [pow_add,pow_one]
    ring

/-- A universal r-fold coefficient satisfies (r−1)C ≥ r for every r ≥ 2. -/
theorem coefficient_bound (r : ℕ) (hr : 2 ≤ r) (C : ℝ)
    (h : ∀ n (A : Finset (Cube n)), A.Nonempty →
      ∃ (W : Submodule F₂ (Cube n)) (v : Cube n), v +ᵥ (W : Set (Cube n)) ⊆ ↑(r • A) ∧
        (n:ℝ)-C*Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W) :
    (r:ℝ) ≤ (r-1)*C := by
  by_contra! hbad
  let δ : ℝ := r-(r-1)*C
  have hd : 0<δ := sub_pos.mpr hbad
  obtain ⟨b,hb⟩ := exists_nat_gt ((C-1)/δ)
  have hb' := (div_lt_iff₀ hd).mp hb
  let ε : ℝ := (r*b+1)-C*((r*b+1)-b)
  have he : 0<ε := by dsimp [δ] at hb'; dsimp [ε]; nlinarith only [hb']
  obtain ⟨k,S₀,ex⟩ := sparse_examples r b hr
  obtain ⟨N,hN⟩ := exists_nat_gt ((k:ℝ)/ε)
  let s := max N S₀
  obtain ⟨A,hA,flat⟩ := ex s (le_max_right ..)
  have hs : N ≤ s := le_max_left ..
  have hbnd := (div_lt_iff₀ he).mp (hN.trans_le (show (N:ℝ) ≤ s by exact_mod_cast hs))
  have ne : A.Nonempty := card_pos.mp (by rw [hA]; positivity)
  obtain ⟨W,x,hW,hdim⟩ := h _ A ne
  have dim := flat W x hW
  have dens : (A.dens:ℝ) = (2:ℝ)^(b*s)/2^((r*b+1)*s) := by simp [Finset.dens,hA,Cube,Fintype.card_pi]
  have lg : Real.logb 2 (1/(A.dens:ℝ)) = (((r:ℝ)*b+1)-b)*s := by
    rw [dens,one_div_div,Real.logb_div (by positivity) (by positivity),Real.logb_pow,Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    push_cast
    ring
  rw [lg] at hdim
  push_cast at hdim
  have hwr : (Module.finrank F₂ W:ℝ) < k := by exact_mod_cast dim
  dsimp [ε] at hbnd
  nlinarith only [hbnd,hdim,hwr]

/-- Any admissible coefficient in Green's tenfold statement is at least 10/9. -/
theorem tenfold_requires_ten_ninths (C : ℝ)
    (h : ∀ n (A : Finset (Cube n)), A.Nonempty →
      ∃ (W : Submodule F₂ (Cube n)) (v : Cube n), v +ᵥ (W : Set (Cube n)) ⊆ ↑((10:ℕ) • A) ∧
        (n:ℝ)-C*Real.logb 2 (1/(A.dens:ℝ)) ≤ Module.finrank F₂ W) : 10/9 ≤ C := by
  have h' := coefficient_bound 10 (by decide) C h
  norm_num at h'
  linarith

end Green50RandomImages

#print axioms Green50RandomImages.finite_witness
#print axioms Green50RandomImages.sparse_examples
#print axioms Green50RandomImages.coefficient_bound
#print axioms Green50RandomImages.tenfold_requires_ten_ninths
