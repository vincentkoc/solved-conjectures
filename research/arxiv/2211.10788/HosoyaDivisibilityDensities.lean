import HosoyaExactGcdDensityApproximation
import HosoyaPrimeParameterClasses

/-! Each divisibility condition used by the gcd inclusion-exclusion occupies
one residue class or none. Its period combines the progression, divisor and return rank. -/

namespace Arxiv.«2211.10788».IndexDivisors
open Finset Filter Topology

def multipleFiber (m a h n : ℕ) : Prop :=
  n ≡ a [MOD m] ∧ h ∣ n ∧ h ∣ lucasFibonacciSum n
instance (m a h n : ℕ) : Decidable (multipleFiber m a h n) := by unfold multipleFiber; infer_instance

noncomputable def jointPeriod (m h : ℕ) := m.lcm (h.lcm (returnRank h))

lemma rank_pos_all {h : ℕ} (hh : 0 < h) : 0<returnRank h := by
  let : NeZero h := ⟨hh.ne'⟩
  simpa [returnRank,hh.ne'] using (rank_properties h 1).1

lemma jointPeriod_pos {m h : ℕ} (hm : 0 < m) (hh : 0 < h) : 0<jointPeriod m h :=
  Nat.lcm_pos hm (Nat.lcm_pos hh (rank_pos_all hh))

private lemma joint_modEq {i j k l : ℕ} :
    i ≡ j [MOD k.lcm l] ↔ i ≡ j [MOD k] ∧ i ≡ j [MOD l] := by
  have f {x y : ℕ} (h : x≤y) :
      x ≡ y [MOD k.lcm l] ↔ x ≡ y [MOD k] ∧ x ≡ y [MOD l] := by
    simp only [Nat.modEq_iff_dvd' h,Nat.lcm_dvd_iff]
  rcases le_total i j with le|le
  · exact f le
  · exact ⟨fun h => ⟨((f le).mp h.symm).1.symm,((f le).mp h.symm).2.symm⟩,
      fun h => ((f le).mpr ⟨h.1.symm,h.2.symm⟩).symm⟩

theorem multipleFiber_class {m a h t : ℕ} (hh : 0 < h) (hit : multipleFiber m a h t) (n : ℕ) :
    multipleFiber m a h n ↔ n ≡ t [MOD jointPeriod m h] := by
  let : NeZero h := ⟨hh.ne'⟩
  obtain ⟨cl,div,upper⟩ := hit
  have up : h ∣ lucasFibonacciSum n ↔ n ≡ t [MOD returnRank h] := by
    simpa [returnRank,hh.ne'] using
      (upper_divisor_parameter_class (m:=h) (r:=0) (d:=1) (s:=t) (by simpa using upper) n)
  rw [jointPeriod,joint_modEq,joint_modEq]
  constructor
  · rintro ⟨x,y,z⟩
    exact ⟨x.trans cl.symm,y.modEq_zero_nat.trans div.zero_modEq_nat,up.mp z⟩
  · rintro ⟨x,y,z⟩
    exact ⟨x.trans cl,Nat.modEq_zero_iff_dvd.mp (y.trans div.modEq_zero_nat),up.mpr z⟩

private lemma multiple_periodic {m a h : ℕ} (hh : 0 < h) :
    Function.Periodic (multipleFiber m a h) (jointPeriod m h) := by
  intro n
  apply propext
  have eq : n+jointPeriod m h ≡ n [MOD jointPeriod m h] := by simp [Nat.ModEq]
  exact ⟨fun hit => (multipleFiber_class hh hit n).mpr eq.symm,
    fun hit => (multipleFiber_class hh hit _).mpr eq⟩

noncomputable def intersectionMass (m a h : ℕ) : ℝ :=
  periodMean (multipleFiber m a h) (jointPeriod m h)

theorem intersection_limit {m a h : ℕ} (hm : 0 < m) (hh : 0 < h) :
    Tendsto (sampleFreq (multipleFiber m a h)) atTop (𝓝 (intersectionMass m a h)) :=
  periodic_freq_tendsto (jointPeriod_pos hm hh) (multiple_periodic hh)

/-- A single finite search determines the signed series' local density coefficient. -/
theorem intersectionMass_eq {m a h : ℕ} (hh : 0 < h) :
    intersectionMass m a h =
      if ((range (jointPeriod m h)).filter (multipleFiber m a h)).Nonempty
      then 1/(jointPeriod m h:ℝ) else 0 := by
  let D := jointPeriod m h
  let S := (range D).filter (multipleFiber m a h)
  change periodMean (multipleFiber m a h) D=if S.Nonempty then _ else _
  rw [periodMean,Nat.count_eq_card_filter_range]
  by_cases ne : S.Nonempty
  · obtain ⟨t,ht⟩ := ne
    have singleton : S={t} := by
      ext n
      rw [mem_singleton]
      constructor
      · intro hn
        obtain ⟨nt,nh⟩ := mem_filter.mp hn
        obtain ⟨tt,th⟩ := mem_filter.mp ht
        have eq := (multipleFiber_class hh th n).mp nh
        change n%D=t%D at eq
        rwa [Nat.mod_eq_of_lt (mem_range.mp nt),Nat.mod_eq_of_lt (mem_range.mp tt)] at eq
      · rintro rfl
        exact ht
    change (S.card:ℝ)/D=_
    rw [if_pos (show S.Nonempty from ⟨t,ht⟩),singleton,card_singleton,Nat.cast_one]
  · change (S.card:ℝ)/D=_
    rw [if_neg ne,not_nonempty_iff_eq_empty.mp ne]
    simp

#print axioms multipleFiber_class
#print axioms intersection_limit
#print axioms intersectionMass_eq

end Arxiv.«2211.10788».IndexDivisors
