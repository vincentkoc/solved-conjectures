import HosoyaDyadicLucasNumbers
import Mathlib.Data.Fintype.Pigeonhole

/-! Pairwise coprime detectors from disjoint pairs of consecutive dyadic Lucas indices. -/

namespace Arxiv.«2211.10788».ProgressionClosure

private lemma coprime_ordered (d : ℕ) (y : ℤ) {i j : ℕ} (hlt : i<j) :
    (oddLucas (radius d y i)).Coprime (oddLucas (radius d y j)) := by
  apply Nat.coprime_of_dvd'
  intro p hp hpi hpj
  exfalso
  have p2 : p ≠ 2 := by rintro rfl; exact odd_layer d y i hpi
  have hn : (2 : ZMod p) ≠ 0 := by
    intro h
    have e : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact p2 (le_antisymm (Nat.le_of_dvd (by decide) e) hp.two_le)
  let A (s : ℕ) : ZMod p := lucas (radius d y s)
  have zᵢ : A i=0 := (ZMod.natCast_eq_zero_iff ..).mpr (hpi.trans (oddLucas_dvd _))
  have zⱼ : A j=0 := (ZMod.natCast_eq_zero_iff ..).mpr (hpj.trans (oddLucas_dvd _))
  have step (s : ℕ) : A (s+1) = (A s)^2-2 := by
    apply eq_sub_of_add_eq
    dsimp [A]
    rw [radius_succ]
    simpa using congrArg (fun n : ℕ => (n:ZMod p)) (lucas_double (radius_even d y s))
  have later (t : ℕ) : A (i+t+1)= -2 ∨ A (i+t+1)=2 := by
    induction t with
    | zero => left; simp [step,zᵢ]
    | succ t ih =>
      right
      rw [show i+t.succ+1 = (i+t+1)+1 by omega,step]
      rcases ih with e | e <;> rw [e] <;> ring
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le (show i+1 ≤ j by omega)
  have e : A (i+t+1)=0 := by simpa only [show i+t+1=j by omega] using zⱼ
  rcases later t with he|he
  · rw [e] at he
    exact hn (neg_eq_zero.mp he.symm)
  · exact hn (he.symm.trans e)

/-- The odd parts at distinct dyadic levels are coprime. -/
theorem odd_layers_coprime (d : ℕ) (y : ℤ) {i j : ℕ} (hne : i≠j) :
    (oddLucas (radius d y i)).Coprime (oddLucas (radius d y j)) := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact coprime_ordered d y h
  · exact (coprime_ordered d y h).symm

/-- Each detector uses two successive levels. Different detectors use disjoint level pairs. -/
def detector (d : ℕ) (y : ℤ) (e : ℕ) : ℕ :=
  oddLucas (radius d y (2*e)) * oddLucas (radius d y (2*e+1))

theorem detectors_coprime (d : ℕ) (y : ℤ) :
    Pairwise (fun i j => (detector d y i).Coprime (detector d y j)) := by
  intro i j h
  unfold detector
  rw [Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right,Nat.coprime_mul_iff_right]
  exact ⟨⟨odd_layers_coprime d y (by omega),odd_layers_coprime d y (by omega)⟩,
    ⟨odd_layers_coprime d y (by omega),odd_layers_coprime d y (by omega)⟩⟩

/-- Among the first ω(B)+1 detectors, one avoids every prime dividing B. -/
theorem exists_coprime_detector (d : ℕ) (y : ℤ) {B : ℕ} (hB : 0 < B) :
    ∃ e ≤ B.primeFactors.card, (detector d y e).Coprime B := by
  by_contra! none
  let I := Fin (B.primeFactors.card+1)
  choose p prime hdvd hdiv using fun i : I =>
    Nat.Prime.not_coprime_iff_dvd.mp (none i.val (by have := i.isLt; omega))
  let f (i : I) : {q : ℕ // q ∈ B.primeFactors} :=
    ⟨p i,Nat.mem_primeFactors.mpr ⟨prime i,hdiv i,hB.ne'⟩⟩
  obtain ⟨i,j,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp [I])
  have hij : p i=p j := congrArg Subtype.val eq
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p i,prime i,hdvd i,hij ▸ hdvd j⟩
    (detectors_coprime d y (fun h => ne (Fin.ext h)))

#print axioms odd_layers_coprime
#print axioms detectors_coprime
#print axioms exists_coprime_detector

end Arxiv.«2211.10788».ProgressionClosure
