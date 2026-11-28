import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Units with prescribed inverse on the prime-to-`a` part of a modulus. -/
namespace Arxiv.«2501.03234».ThetaCompatibleUnits
noncomputable section

theorem unit_lift {a m : ℕ} (ha : a.Prime) (hm : 0<m) :
    ∃ n<m, n.Coprime m ∧ ∀ d, d∣m → ¬a∣d → (n:ZMod d)*(a:ZMod d)=1 := by
  let k := ordCompl[a] m
  have hc : a.Coprime k := Nat.coprime_ordCompl ha hm.ne'
  have hvk : (a+k).Coprime k := Nat.coprime_add_self_left.mpr hc
  have hva : (a+k).Coprime a := by
    rw [add_comm, Nat.coprime_add_self_left]; exact hc.symm
  have hv : (a+k).Coprime m := by
    rw [←Nat.ordProj_mul_ordCompl_eq_self m a]
    exact (hva.pow_right _).mul_right hvk
  let u := ZMod.unitOfCoprime (a+k) hv
  let : NeZero m := ⟨hm.ne'⟩
  let n := ((u⁻¹ : (ZMod m)ˣ) : ZMod m).val
  refine ⟨n,ZMod.val_lt _,ZMod.val_coe_unit_coprime _,?_⟩
  intro d hdm had
  have hk : d∣k := Nat.dvd_ordCompl_of_dvd_not_dvd hdm had
  have hn : (n:ZMod m)*(↑(a+k:ℕ):ZMod m)=1 := by
    change (↑((u⁻¹ : (ZMod m)ˣ):ZMod m).val : ZMod m)*_=1
    rw [ZMod.natCast_zmod_val,←ZMod.coe_unitOfCoprime (a+k) hv]
    exact u.inv_mul
  have he := congrArg (ZMod.castHom hdm (ZMod d)) hn
  simpa only [map_mul,map_add,map_natCast,map_one,Nat.cast_add,(ZMod.natCast_eq_zero_iff _ _).mpr hk,add_zero] using he

theorem compatible {q r : ℕ} (hq : 0<q) (hr : r<q) (hc : r.Coprime q) (A : ℕ) :
    ∃ a>max A q, a.Prime ∧ ∀ m, 0<m → q∣m →
      ∃ n<m, n.Coprime m ∧ n%q=r ∧ ∀ d, d∣m → ¬a∣d → (n:ZMod d)⁻¹=(a:ZMod d) := by
  let : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime r hc
  obtain ⟨a,ha,hap,har⟩ := Nat.forall_exists_prime_gt_and_eq_mod (u⁻¹.isUnit) (max A q)
  refine ⟨a,ha,hap,?_⟩
  intro m hm hqm
  obtain ⟨n,hn,hnc,H⟩ := unit_lift hap hm
  have haq : ¬a∣q := Nat.not_dvd_of_pos_of_lt hq ((le_max_right A q).trans_lt ha)
  have he := H q hqm haq
  rw [har] at he
  have hh := congrArg (fun x : ZMod q => x*(u:ZMod q)) he
  have heq : (n:ZMod q)=(r:ZMod q) := by
    rw [mul_assoc, u.inv_mul, mul_one, one_mul] at hh
    exact hh
  exact ⟨n,hn,hnc,((ZMod.natCast_eq_natCast_iff' _ _ _).mp heq).trans (Nat.mod_eq_of_lt hr),
    fun d hd had => ZMod.inv_eq_of_mul_eq_one _ _ _ (H d hd had)⟩

end
end Arxiv.«2501.03234».ThetaCompatibleUnits

#print axioms Arxiv.«2501.03234».ThetaCompatibleUnits.compatible
