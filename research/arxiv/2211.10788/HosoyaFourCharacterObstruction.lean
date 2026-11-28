import HosoyaIndependentSignClasses
import HosoyaReducedClassMass
import HosoyaEvenDiagonalSeparation

/-! Four independent square classes for excluding an even lower value. -/

namespace Arxiv.«2211.10788».PrimeObstruction
open Finset CunninghamChain.PrimeMass Filter Topology

private lemma nonsquare_multiple {b : ℤ} (hb : ¬IsSquare b.natAbs)
    (d : ℤ) (hc : b.natAbs.Coprime d.natAbs) : ¬IsSquare (b*d) := by
  rintro ⟨v,hv⟩
  have he := congrArg Int.natAbs hv
  simp only [Int.natAbs_mul] at he
  have hu : IsUnit (gcd b.natAbs d.natAbs) := by
    change IsUnit (Nat.gcd b.natAbs d.natAbs)
    rw [show Nat.gcd b.natAbs d.natAbs=1 from hc]; exact isUnit_one
  obtain ⟨z,hz⟩ := exists_eq_pow_of_mul_eq_pow hu (show b.natAbs*d.natAbs=v.natAbs^2 by simpa [pow_two] using he)
  exact hb ⟨z,by simpa [pow_two] using hz⟩

private lemma four_periods (b : ℤ) : ∀ a∈[b,11,-5,-1], 4*a.natAbs ∣ 220*b.natAbs := by
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl
  · exact ⟨55,by ring⟩
  · exact dvd_mul_of_dvd_left (by decide) _
  · exact dvd_mul_of_dvd_left (by decide) _
  · exact dvd_mul_of_dvd_left (by decide) _

private lemma four_independent (b : ℤ) (hb : ¬IsSquare b.natAbs) (hc : b.natAbs.Coprime 55) :
    independentProducts (220*b.natAbs) [b,11,-5,-1] := by
  have bterm (d : ℤ) (hd : d.natAbs ∣ 55) :
      ¬IsSquare (b*d) ∧ 4*(b*d).natAbs ∣ 220*b.natAbs := by
    refine ⟨nonsquare_multiple hb d (Nat.Coprime.of_dvd_right hd hc),?_⟩
    obtain ⟨k,hk⟩ := hd
    refine ⟨k,?_⟩
    rw [Int.natAbs_mul,show 220=4*55 by decide,hk]; ring
  have fixed (d : ℤ) (hn : ¬IsSquare d) (hd : 4*d.natAbs ∣ 220) :
      ¬IsSquare d ∧ 4*d.natAbs ∣ 220*b.natAbs := ⟨hn,dvd_mul_of_dvd_left hd _⟩
  have b0 := bterm 1 (by decide)
  rw [mul_one] at b0
  simp only [independentProducts,nonsquareProducts,mul_assoc]
  exact ⟨⟨⟨⟨b0,bterm _ (by decide)⟩,bterm _ (by decide),bterm _ (by decide)⟩,
    ⟨bterm _ (by decide),bterm _ (by decide)⟩,bterm _ (by decide),bterm _ (by decide)⟩,
    ⟨⟨fixed _ (by norm_num) (by decide),fixed _ (by norm_num) (by decide)⟩,
      fixed _ (by norm_num) (by decide),fixed _ (by norm_num) (by decide)⟩,
    ⟨fixed _ (by norm_num) (by decide),fixed _ (by norm_num) (by decide)⟩,
    fixed _ (by norm_num) (by decide),trivial⟩

/-- A nonsquare absolute discriminant prime to 55 imposes a fourth independent sign
in addition to those of −1, 5 and 11. -/
theorem four_sign_prime_mass (b : ℤ) (hb : ¬IsSquare b.natAbs) (hc : b.natAbs.Coprime 55) :
    ∃ P : Set ℕ, Tendsto (fun x : ℝ => (x-1)*mass P x) (𝓝[>] 1) (𝓝 (1/16:ℝ)) ∧
      ∀ p∈P, p.Prime → ¬IsSquare (b:ZMod p) ∧ ¬IsSquare (11:ZMod p) ∧
        IsSquare (5:ZMod p) ∧ ¬IsSquare (-1:ZMod p) := by
  let M := 220*b.natAbs
  have hpM : 0<M := Nat.mul_pos (by decide) (Nat.pos_of_ne_zero (by
    intro h; exact hb (h ▸ IsSquare.zero)))
  let : NeZero M := ⟨hpM.ne'⟩
  let K : List ℤ := [b,11,-5,-1]
  let S := allNegativeClasses M K
  have hcard := card_all_negative K (four_independent b hb hc) (four_periods b)
  change 16*S.card=M.totient at hcard
  refine ⟨represented S,?_,?_⟩
  · have hm := mass_represented S
    have hpos : (0:ℝ)<M.totient := by exact_mod_cast Nat.totient_pos.mpr hpM
    have heq : (16:ℝ)*S.card=M.totient := by exact_mod_cast hcard
    have hrat : (S.card:ℝ)/M.totient=1/16 := by field_simp; linarith
    simpa only [hrat] using hm
  · rintro p ⟨u,hu,he⟩ hp
    let : Fact p.Prime := ⟨hp⟩
    have hpC := (ZMod.isUnit_iff_coprime p M).mp (he ▸ u.isUnit)
    have eu : u=ZMod.unitOfCoprime p hpC := Units.ext (he.symm.trans (ZMod.coe_unitOfCoprime ..).symm)
    have signs (a : ℤ) (ha : a∈K) : jacobiSym a p = -1 := by
      have h := (mem_filter.mp hu).2 a ha
      simpa [eu,symbol_at_unit (four_periods b a ha) hpC] using h
    have neg (a : ℤ) (ha : a∈K) : ¬IsSquare (a:ZMod p) :=
      ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp (signs a ha)
    have h5 : IsSquare (5:ZMod p) := by
      by_contra hn
      have h₅ : jacobiSym 5 p = -1 := ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mpr (by simpa using hn)
      have h1 := signs (-1) (by simp [K])
      have hneg := signs (-5) (by simp [K])
      rw [show (-5:ℤ)=(-1)*5 by decide,jacobiSym.mul_left,h1,h₅] at hneg
      norm_num at hneg
    exact ⟨neg b (by simp [K]),by simpa using neg 11 (by simp [K]),h5,
      by simpa using neg (-1) (by simp [K])⟩

#print axioms four_sign_prime_mass

end Arxiv.«2211.10788».PrimeObstruction
