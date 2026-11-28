import CunninghamGapPeriod

/-! The resultant controlling collisions between the two prefixes at gap h+2. -/

namespace CunninghamChain.GapMean

open Finset BatemanHornConjecture

def determinant (i j h : ℕ) := 2^(i+j)*h + 2^i + 2^j

def exceptionalProduct (k l h : ℕ) :=
  ∏ i ∈ range k, ∏ j ∈ range l, determinant i j h

theorem exceptional_pos (k l h : ℕ) : 0 < exceptionalProduct k l h := by
  apply prod_pos; intro i _
  apply prod_pos; intro j _
  unfold determinant
  positivity

theorem exceptional_le (k l h : ℕ) :
    exceptionalProduct k l h ≤ (2^(k+l)*(h+2))^(k*l) := by
  unfold exceptionalProduct
  rw [pow_mul]
  calc
    _ ≤ ∏ _i ∈ range k, ∏ _j ∈ range l, 2^(k+l)*(h+2) := by
      apply prod_le_prod'; intro i hi; apply prod_le_prod'; intro j hj
      have ii := mem_range.mp hi
      have jj := mem_range.mp hj
      have f (t) (ht : t≤k+l) : 2^t≤2^(k+l) := Nat.pow_le_pow_right (by decide) ht
      unfold determinant
      calc
        _ ≤ 2^(k+l)*h+2^(k+l)+2^(k+l) := Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_right h (f _ (by omega))) (f _ (by omega))) (f _ (by omega))
        _ = _ := by ring
    _ = _ := by simp only [prod_const,card_range,←pow_mul]; rw [Nat.mul_comm l k]

private lemma excluded {s : ℤ} {k q : ℕ} [NeZero q] (x : ZMod q) (hx : x∉accepted s k q) :
    ∃ i<k, (2:ZMod q)^i*x+(s:ZMod q)*(2^i-1)=0 := by
  classical
  have failed : ¬∀ f∈chainForms s k, (f.map (Int.castRingHom (ZMod q))).eval x ≠0 := by
    simpa [accepted] using hx
  push Not at failed
  obtain ⟨g,mg,zero⟩ := failed
  change g∈(range k).image (form s) at mg
  obtain ⟨i,hi,rfl⟩ := mem_image.mp mg
  exact ⟨i,mem_range.mp hi,by simpa [form] using zero⟩

private lemma collision_dvd {k l q h : ℕ} [Fact q.Prime] (z : ZMod q)
    (left : z ∉ accepted 1 k q) (right : z+(h+2:ℕ) ∉ accepted (-1) l q) :
    q ∣ exceptionalProduct k l h := by
  obtain ⟨i,hi,h₁⟩ := excluded z left
  obtain ⟨j,hj,h₂⟩ := excluded _ right
  push_cast at h₁ h₂
  have dv : q ∣ determinant i j h := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    unfold determinant
    push_cast
    rw [pow_add]
    linear_combination (2:ZMod q)^i*h₂-(2:ZMod q)^j*h₁
  exact dv.trans ((dvd_prod_of_mem (fun j => determinant i j h) (mem_range.mpr hj)).trans
    (dvd_prod_of_mem (fun i => ∏ j ∈ range l, determinant i j h) (mem_range.mpr hi)))

theorem stable_roots {k q : ℕ} [Fact q.Prime] (hq : 2<q) (big : 2^k<q) :
    OmegaP (chainForms 1 k) q=k := by
  rw [chainForms_omega_odd k q hq,min_eq_left]
  by_contra! lt
  let d := orderOf (2:ZMod q)
  have two : (2:ZMod q)≠0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) hq)
  have dp : 0<d := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q-1,by omega,ZMod.pow_card_sub_one_eq_one two⟩)
  have hc : ((2^d:ℕ):ZMod q)=((1:ℕ):ZMod q) := by push_cast; exact pow_orderOf_eq_one _
  have mod := (ZMod.natCast_eq_natCast_iff ..).mp hc
  have lb : 2^d<q := (Nat.pow_le_pow_right (by decide) lt.le).trans_lt big
  change 2^d%q=1%q at mod
  rw [Nat.mod_eq_of_lt lb,Nat.mod_eq_of_lt (by omega : 1<q)] at mod
  exact (one_lt_pow₀ (by decide : 1<(2:ℕ)) dp.ne').ne' mod

/-- Above the internal collision primes the excess in the number of allowed
residues is exactly the common-root count. Each such prime divides the resultant. -/
theorem pairCount_excess {k l q : ℕ} [Fact q.Prime] (hq : 2<q) (big : 2^(k+l)<q) (h : ℕ) :
    ∃ c≤k+l, (c≠0 → q∣exceptionalProduct k l h) ∧
      pairCount (accepted 1 k q) (accepted (-1) l q) (h+2:ℕ) + (k+l) = q+c := by
  classical
  let A := accepted 1 k q
  let B := accepted (-1) l q
  let C := B.map (Equiv.addRight (-(h+2:ℕ):ZMod q)).toEmbedding
  have mem (x : ZMod q) : x∈C ↔ x+(h+2:ℕ)∈B := by
    simp only [C,mem_map,Equiv.toEmbedding_apply]
    change (∃ z∈B, z + -((h+2:ℕ):ZMod q) = x) ↔ _
    constructor
    · rintro ⟨z,hz,rfl⟩; simpa only [neg_add_cancel_right] using hz
    · intro hx; exact ⟨_,hx,by abel⟩
  have pair : pairCount A B (h+2:ℕ)=(A∩C).card := by
    unfold pairCount
    congr 1; ext z; simp [mem]
  have ca := accepted_card 1 k q
  rw [stable_roots hq ((Nat.pow_le_pow_right (by decide) (Nat.le_add_right k l)).trans_lt big)] at ca
  have cb := accepted_card (-1) l q
  rw [←chainForms_omega_neg 1,stable_roots hq ((Nat.pow_le_pow_right (by decide) (Nat.le_add_left l k)).trans_lt big)] at cb
  have cc : C.card=B.card := card_map _
  let S := (A∪C)ᶜ
  have union := card_union_add_card_inter A C
  have all := card_add_card_compl (A∪C)
  have single := card_add_card_compl A
  simp only [ZMod.card] at all single
  change A.card+k=q at ca
  change B.card+l=q at cb
  have csmall : S.card≤Aᶜ.card := card_le_card (by intro z hz; exact mem_compl.mpr (fun ha => (mem_compl.mp hz) (mem_union_left _ ha)))
  refine ⟨S.card,by omega,?_,?_⟩
  · intro non
    obtain ⟨z,hz⟩ := card_pos.mp (Nat.pos_of_ne_zero non)
    have H : z∉A ∧ z∉C := by simpa [S] using hz
    exact collision_dvd z H.1 (fun e => H.2 ((mem z).mpr e))
  · change pairCount A B _ + _ = _
    rw [pair]
    dsimp only [S]
    omega

#print axioms stable_roots
#print axioms exceptional_pos
#print axioms exceptional_le
#print axioms pairCount_excess

end CunninghamChain.GapMean
