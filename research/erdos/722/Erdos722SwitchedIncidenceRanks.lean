import Erdos722BinaryIncidenceRank
import Erdos722BinaryDoubleSymmetry
import Erdos722AffineSignatureDual

/-! # The two exact binary incidence ranks of the switched affine systems -/

namespace Erdos722.QuadSwitch
open Finset Equiv Function
open scoped Classical
noncomputable section
variable {V : Type*} [DecidableEq V] [Fintype V] {H : Finset (Finset V)}

theorem coboundary_zero_iso (hH : H.IsBlockDesign 3 4) {s : H → Bool} (cs : Coboundary s) :
    Isomorphic (doubling hH s) (doubling hH (fun _ => false)) := by
  classical
  obtain ⟨u,hu⟩ := cs
  let f (x : V) := decide (u x=1)
  have point (x : V) : bitValue (f x)=u x :=
    (show ∀ a : ZMod 2, bitValue (decide (a=1))=a by decide) _
  refine ⟨fibrePerm (Equiv.refl V) f,(maps_doubling_iff hH s _ _ _).mpr fun i => ⟨i,by simp,?_⟩⟩
  rw [← hu i,show bitValue ∘ f=u from funext point,CharTwo.add_self_eq_zero]
  rfl

def nongaugeChecks [Nonempty V] (hH : H.IsBlockDesign 3 4) (s : H → Bool) (ng : ¬Coboundary s) :
    Checks H ≃ Checks (doubling hH s) := by
  let F (p : Checks H) : Checks (doubling hH s) :=
    ⟨liftCheck p.val 0,(check_lift_iff ..).mpr fun i => by simp [p.prop i.val i.prop]⟩
  apply Equiv.ofBijective F
  constructor
  · intro u v he
    apply Subtype.ext
    funext x
    have ev := congrArg (fun w : Checks (doubling hH s) => w.val (x,false)) he
    simpa [F,liftCheck] using ev
  · rintro ⟨g,hg⟩
    obtain ⟨u,c,rfl,hs⟩ := (check_decomposition hH s g).mp hg
    have zero : c=0 := by
      by_contra hn
      have one : c=1 := (show ∀ a : ZMod 2, a≠0 → a=1 by decide) c hn
      exact ng ⟨u,fun i => by simpa [one] using hs i⟩
    subst c
    exact ⟨⟨u,fun B hB => by simpa using hs ⟨B,hB⟩⟩,rfl⟩

theorem binary_rank_iff_checks (m j : ℕ) (hj : j≤2^m) (D : Finset (Finset (Fin (2^m)))) :
    (binaryIncidence D).rank=2^m-j ↔ Nat.card (Checks D)=2^j := by
  rw [checks_card_rank,Fintype.card_fin]
  have bound := (binaryIncidence D).rank_le_card_width
  rw [Fintype.card_fin] at bound
  constructor
  · intro h
    exact congrArg (fun a : ℕ => 2^a) (by omega)
  · intro h
    have := Nat.pow_right_injective (by decide : 2≤2) h
    omega

theorem binaryDouble_check_count (d : ℕ) (s : (binaryBase d).val → Bool) :
    Nat.card (Checks (binaryDouble d s))=if Coboundary s then 2^(d+2) else 2^(d+1) := by
  classical
  rw [binaryDouble,Nat.card_congr (checkRelabel _ _)]
  by_cases cs : Coboundary s
  · rw [if_pos cs]
    obtain ⟨e,he⟩ := coboundary_zero_iso (binaryBase d).prop cs
    have eq := Nat.card_congr (checkRelabel e (doubling (binaryBase d).prop s))
    rw [he] at eq
    rw [← eq,← Nat.card_congr (zeroCheckEquiv (binaryBase d).prop),Nat.card_prod,binaryBase_checks]
    simp [Nat.card_eq_fintype_card,pow_succ]
  · rw [if_neg cs,← Nat.card_congr (nongaugeChecks (binaryBase d).prop s cs),binaryBase_checks]

theorem binaryDouble_next_rank (d : ℕ) (s : (binaryBase d).val → Bool) :
    (binaryIncidence (binaryDouble d s)).rank=2^(d+1)-(d+1) ↔ ¬Coboundary s := by
  classical
  rw [binary_rank_iff_checks _ _ (Nat.le_of_lt Nat.lt_two_pow_self),binaryDouble_check_count]
  split_ifs with hs
  · simp [hs,show (2:ℕ)^(d+2)≠2^(d+1) by
      intro eq; have := Nat.pow_right_injective (by decide : 2≤2) eq; omega]
  · simp [hs]

#print axioms coboundary_zero_iso
#print axioms nongaugeChecks
#print axioms binary_rank_iff_checks
#print axioms binaryDouble_check_count
#print axioms binaryDouble_next_rank
end
end Erdos722.QuadSwitch
