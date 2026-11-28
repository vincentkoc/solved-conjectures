import Mathlib

/-! Force composite affine values while preserving admissibility of a tuple of seed translates. -/

namespace CunninghamChain.SeedClusters

/-- At a large enough prime a prescribed affine root can avoid all seed translates. -/
theorem forbidden_root {q a c : ℕ} (hq : q.Prime) (ha : 0<a) (aq : a<q) (cq : c<q)
    (A : Finset ℕ) (small : ∀ j∈A, a*j<q) (distinct : ∀ j∈A, a*j≠c) :
    ∃ r : ℕ, q ∣ a*r+c ∧ ∀ j∈A, ¬ q ∣ r+j := by
  let : Fact q.Prime := ⟨hq⟩
  have unit : (a:ZMod q) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff a q).not.mpr (Nat.not_dvd_of_pos_of_lt ha aq)
  obtain ⟨r,hr⟩ := ZMod.natCast_zmod_surjective (-(c:ZMod q)/(a:ZMod q))
  have zero : (a:ZMod q)*r+c=0 := by rw [hr]; field_simp; ring
  refine ⟨r,(ZMod.natCast_eq_zero_iff ..).mp (by push_cast;exact zero),?_⟩
  intro j hj dv
  have other := (ZMod.natCast_eq_zero_iff ..).mpr dv
  push_cast at other
  have eq : ((a*j:ℕ):ZMod q)=c := by
    push_cast
    linear_combination (a:ZMod q)*other-zero
  exact distinct j hj (((ZMod.natCast_eq_natCast_iff ..).mp eq).eq_of_lt_of_lt (small j hj) cq)

open Finset

/-- Keep an admissible tuple of translates while forcing composite values
at every affine form that is nonproportional to each of those translates. -/
theorem affine_mask {ι : Type*} [Encodable ι] (A : Finset ℕ) (F : Finset ι) (a c : ι → ℕ)
    (adm : ∀ p : ℕ, p.Prime → ∃ r, ∀ j∈A, ¬p ∣ r+j)
    (pos : ∀ i∈F, 0<a i) (distinct : ∀ i∈F, ∀ j∈A, a i*j ≠ c i) :
    ∃ W B : ℕ, 0<W ∧ 2≤B ∧
      (∀ n i, i∈F → ¬(a i*(W*n+B)+c i).Prime) ∧
      ∀ p : ℕ, p.Prime → ∃ n, ∀ j∈A, ¬p ∣ W*n+B+j := by
  classical
  let D := 2 + F.sup a + F.sup c + F.sup a * A.sup id
  let q (i : ι) := Nat.nth Nat.Prime (D+Encodable.encode i)
  have pr (i : ι) : (q i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have inj : Function.Injective q := fun _ _ h => Encodable.encode_injective (Nat.add_left_cancel ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h))
  have big (i : ι) : D ≤ q i :=
    (Nat.le_add_right ..).trans ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le _)
  have roots (i : ι) (hi : i∈F) : ∃ r : ℕ, q i ∣ a i*r+c i ∧ ∀ j∈A, ¬q i ∣ r+j := by
    have ai := le_sup (f:=a) hi
    have ci := le_sup (f:=c) hi
    have qi := big i
    dsimp only [D] at qi
    apply forbidden_root (pr i) (pos i hi) (by omega) (by omega) _ _ (distinct i hi)
    intro j hj
    have jj : j≤A.sup id := le_sup (f:=id) hj
    have := Nat.mul_le_mul ai jj
    omega
  let r (i : ι) := if h : i∈F then (roots i h).choose else 0
  have hr (i : ι) (hi : i∈F) : q i ∣ a i*r i+c i ∧ ∀ j∈A, ¬q i ∣ r i+j := by
    simpa only [r,dif_pos hi] using (roots i hi).choose_spec
  let b := Nat.chineseRemainderOfFinset r q F (fun i _ => (pr i).ne_zero)
    (fun i _ j _ h => (Nat.coprime_primes (pr i) (pr j)).mpr (inj.ne h))
  let W := ∏ i∈F, q i
  let B := b.val+2*W
  have wp : 0<W := prod_pos fun i _ => (pr i).pos
  have dv (i : ι) (hi : i∈F) : q i ∣ W := dvd_prod_of_mem q hi
  have cls (i : ι) (n : ℕ) (hi : i∈F) : ((W*n+B:ℕ):ZMod (q i))=r i := by
    have w0 := (ZMod.natCast_eq_zero_iff ..).mpr (dv i hi)
    have hb := (ZMod.natCast_eq_natCast_iff ..).mpr (b.property i hi)
    simp [B,w0,hb]
  refine ⟨W,B,wp,by dsimp only [B];omega,?_,?_⟩
  · intro n i hi prime
    have h := (ZMod.natCast_eq_zero_iff ..).mpr (hr i hi).1
    have z : (q i) ∣ a i*(W*n+B)+c i := by
      apply (ZMod.natCast_eq_zero_iff ..).mp
      push_cast at h ⊢
      have e := cls i n hi
      push_cast at e
      rwa [e]
    have eq := (Nat.prime_dvd_prime_iff_eq (pr i) prime).mp z
    have lt := Nat.le_of_dvd wp (dv i hi)
    have mul := Nat.le_mul_of_pos_left (W*n+B) (pos i hi)
    dsimp only [B] at mul eq
    omega
  · intro p pp
    let : Fact p.Prime := ⟨pp⟩
    by_cases bad : p∣W
    · obtain ⟨i,hi,d⟩ := (pp.prime.dvd_finsetProd_iff q).mp bad
      obtain rfl := (Nat.prime_dvd_prime_iff_eq pp (pr i)).mp d
      refine ⟨0,fun j hj shared => (hr i hi).2 j hj ?_⟩
      have e := cls i 0 hi
      have z := (ZMod.natCast_eq_zero_iff ..).mpr shared
      apply (ZMod.natCast_eq_zero_iff ..).mp
      rw [Nat.cast_add] at z ⊢
      rwa [e] at z
    · obtain ⟨v,hv⟩ := adm p pp
      have unit := (ZMod.natCast_eq_zero_iff W p).not.mpr bad
      obtain ⟨n,hn⟩ := ZMod.natCast_zmod_surjective (((v:ZMod p)-(B:ZMod p))/(W:ZMod p))
      have e : ((W*n+B:ℕ):ZMod p)=v := by push_cast;rw [hn];field_simp;ring
      refine ⟨n,fun j hj shared => hv j hj ?_⟩
      have z := (ZMod.natCast_eq_zero_iff ..).mpr shared
      apply (ZMod.natCast_eq_zero_iff ..).mp
      rw [Nat.cast_add] at z ⊢
      rwa [e] at z

#print axioms affine_mask

#print axioms forbidden_root
end CunninghamChain.SeedClusters
