import ThetaPrimitiveSpectrum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-! An odd primitive character detects every odd prime-power precision. -/
namespace Arxiv.«2501.03234».ThetaPrimePowerDigit
open DirichletCharacter

private lemma odd_separates {q : ℕ} [NeZero q] (hneg : (-1:ZMod q) ≠ 1)
    {u : (ZMod q)ˣ} (hu : u ≠ 1) :
    ∃ χ : DirichletCharacter ℂ q, χ.Odd ∧ χ (u : ZMod q) ≠ 1 := by
  have hval : (u:ZMod q)≠1 := fun h => hu (Units.ext h)
  obtain ⟨α,ha⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hneg
  obtain ⟨β,hb⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hval
  have hao : α.Odd := α.even_or_odd.resolve_left ha
  by_cases hau : α (u:ZMod q)=1
  · rcases β.even_or_odd with he | ho
    · exact ⟨α*β,by change α (-1)*β (-1)= -1; rw [hao,he,mul_one],
          by simpa [MulChar.mul_apply,hau] using hb⟩
    · exact ⟨β,ho,hb⟩
  · exact ⟨α,hao,hau⟩

private lemma totient_step {p : ℕ} (hp : p.Prime) (hodd : p≠2) (k : ℕ) :
    (p^k).totient < (p^(k+1)).totient := by
  have h3 := hp.two_le
  cases k with
  | zero => simp [Nat.totient_prime hp]; omega
  | succ n =>
    rw [Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
    exact Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self n))
      (by omega)

theorem exists_primitive_odd {p : ℕ} (hp : p.Prime) (hodd : p≠2) (k : ℕ) :
    ∃ χ : DirichletCharacter ℂ (p^(k+1)), χ.IsPrimitive ∧ χ.Odd := by
  let q := p^(k+1)
  let d := p^k
  let : NeZero q := ⟨(pow_pos hp.pos _).ne'⟩
  let : NeZero d := ⟨(pow_pos hp.pos _).ne'⟩
  have hd : d∣q := pow_dvd_pow p (Nat.le_succ _)
  have hsize := totient_step hp hodd k
  have hmap : ¬Function.Injective (ZMod.unitsMap hd) := by
    intro hi
    have hle := Fintype.card_le_of_injective _ hi
    rw [ZMod.card_units_eq_totient,ZMod.card_units_eq_totient] at hle
    exact hsize.not_ge hle
  obtain ⟨x,y,hxy,hne⟩ : ∃ x y, ZMod.unitsMap hd x=ZMod.unitsMap hd y ∧ x≠y := by
    by_contra hn
    apply hmap
    intro a b hab
    by_contra hnab
    exact hn ⟨a,b,hab,hnab⟩
  let u := x/y
  have hu : u≠1 := div_ne_one.mpr hne
  have hker : ZMod.unitsMap hd u=1 := by simp [u,hxy]
  have hq : 2<q := by
    have hle : p^1≤p^(k+1) := Nat.pow_le_pow_right hp.pos (by omega)
    rw [pow_one] at hle
    have := hp.two_le
    dsimp [q]; omega
  have hneg : (-1:ZMod q)≠1 := by
    intro he
    have htwo : (2:ZMod q)=0 := by linear_combination -he
    have hdiv : q∣2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by exact_mod_cast htwo)
    exact (Nat.le_of_dvd (by decide) hdiv).not_gt hq
  obtain ⟨χ,ho,hu'⟩ := odd_separates hneg hu
  refine ⟨χ,?_,ho⟩
  have hnf : ¬χ.FactorsThrough d := by
    intro hf
    have H := (factorsThrough_iff_ker_unitsMap hd).mp hf (show u∈(ZMod.unitsMap hd).ker from hker)
    exact hu' (congrArg (fun z : ℂˣ => (z:ℂ)) (show χ.toUnitHom u=1 from H))
  have hnd : ¬χ.conductor∣d := fun h => hnf ((mem_conductorSet_iff_conductor_dvd χ hd).mpr h)
  obtain ⟨j,hj,he⟩ := (Nat.dvd_prime_pow hp).mp χ.conductor_dvd_level
  have hj' : j=k+1 := by
    by_contra hh
    exact hnd (he ▸ pow_dvd_pow p (by omega))
  exact he.trans (congrArg (p^·) hj')

#print axioms exists_primitive_odd
end Arxiv.«2501.03234».ThetaPrimePowerDigit
