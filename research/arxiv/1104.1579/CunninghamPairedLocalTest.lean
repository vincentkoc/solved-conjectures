import CunninghamPairedBoundaryRoots
import CunninghamPairedGaps

/-! A finite local criterion and two independently forced composite stops. -/

namespace CunninghamChain.PairedRough
open Finset

/-- The plus chain starts at x and the minus chain at x+h. -/
def avoids (h k l q : ℕ) (x : ZMod q) : Prop :=
  (∀ i < k, (2:ZMod q)^i*(x+1) ≠ 1) ∧
  (∀ j < l, (2:ZMod q)^j*(x+h-1) ≠ -1)

def localTest (h k l : ℕ) : Prop := ∀ q ∈ (k+l).primesLE, ∃ x : ZMod q, avoids h k l q x

def site (k l : ℕ) : Fin (k+l) → Bool × ℕ :=
  Fin.append (fun i : Fin k => (true,i.val)) (fun j : Fin l => (false,j.val))

def slopes (k l : ℕ) (z : Fin (k+l)) := 2^(site k l z).2

def constants (h k l : ℕ) (z : Fin (k+l)) := base h (site k l z).1 (site k l z).2

lemma sites_iff {k l : ℕ} (P : Bool → ℕ → Prop) :
    (∀ z, P (site k l z).1 (site k l z).2) ↔ (∀ i < k, P true i) ∧ (∀ j < l, P false j) := by
  constructor
  · intro all
    exact ⟨fun i hi => by simpa only [site,Fin.append_left,Fin.append_right] using all ((⟨i,hi⟩ : Fin k).castAdd l),
      fun j hj => by simpa only [site,Fin.append_left,Fin.append_right] using all (Fin.natAdd k (⟨j,hj⟩ : Fin l))⟩
  · rintro ⟨left,right⟩ z
    refine Fin.addCases (fun i => ?_) (fun j => ?_) z
    · simpa [site] using left i i.isLt
    · simpa [site] using right j j.isLt

lemma avoids_iff (h k l q : ℕ) (x : ZMod q) :
    avoids h k l q x ↔ ∀ z, residue q (slopes k l z) (constants h k l z) x ≠ 0 := by
  rw [show (∀ z, residue q (slopes k l z) (constants h k l z) x ≠ 0) ↔ _ from
    sites_iff (k:=k) (l:=l) (fun b i => residue q (2^i) (base h b i) x ≠ 0)]
  simp only [avoids,residue_site,if_true,Bool.false_eq_true,if_false,ne_eq,sub_eq_zero,
    add_eq_zero_iff_eq_neg]

lemma avoids_unit {h k l q : ℕ} (hp : q.Prime) (hk : 0 < k) {x : ZMod q}
    (ok : avoids h k l q x) : IsUnit x := by
  let : Fact q.Prime := ⟨hp⟩
  apply isUnit_iff_ne_zero.mpr
  rintro rfl
  exact ok.1 0 hk (by simp)

/-- There are at most k+l forbidden seed residues at each odd prime. -/
theorem localTest_iff_all {h k l : ℕ} (hk : 0 < k) (hl : 0 < l) :
    localTest h k l ↔ ∀ q, q.Prime → ∃ x : ZMod q, avoids h k l q x := by
  classical
  refine ⟨?_,fun all q hq => all q (Nat.prime_of_mem_primesLE hq)⟩
  intro localOK q hp
  by_cases small : q≤k+l
  · exact localOK q (Nat.mem_primesLE.mpr ⟨small,hp⟩)
  let : Fact q.Prime := ⟨hp⟩
  let roots := univ.image fun z : Fin (k+l) =>
    (2:ZMod q)-(constants h k l z : ZMod q)/(slopes k l z : ZMod q)
  have card : roots.card ≤ k+l := card_image_le.trans_eq (by simp)
  obtain ⟨x,hx⟩ : ∃ x : ZMod q, x∉roots := by
    by_contra! all
    rw [show roots=univ from eq_univ_of_forall all,card_univ,ZMod.card] at card
    omega
  refine ⟨x,(avoids_iff ..).mpr (fun z bad => hx (mem_image.mpr ⟨z,mem_univ _,?_⟩))⟩
  have two : (2:ZMod q)≠0 := fun e => (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < q))
    ((ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using e))
  have unit : (slopes k l z : ZMod q)≠0 := by simp [slopes,two]
  unfold residue at bad
  field_simp [unit]
  linear_combination -bad

#print axioms localTest_iff_all

private lemma gap_ne_one {h k l : ℕ} (hk : 0 < k) (hl : 0 < l) (ok : localTest h k l) : h≠1 := by
  rintro rfl
  obtain ⟨x,hx⟩ := (localTest_iff_all hk hl).mp ok 2 Nat.prime_two
  have a := hx.1 0 hk
  have b := hx.2 0 hl
  fin_cases x <;> revert a b <;> decide

/-- Choose the two stopping primes before specifying a roughness cutoff.
The small-prime residue assignment avoids the whole prefix at every prime. -/
theorem stop_classes {h k l : ℕ} (hk : 0 < k) (hl : 0 < l) (ok : localTest h k l) :
    ∃ Q R : ℕ, Q.Prime ∧ R.Prime ∧ Q<R ∧ ∃ x : (q : ℕ) → ZMod q,
      (∀ q, q.Prime → avoids h k l q (x q)) ∧
      residue Q (2^k) (base h true k) (x Q)=0 ∧ residue R (2^l) (base h false l) (x R)=0 := by
  have gap := gap_ne_one hk hl ok
  have distinct (b : Bool) {N : ℕ} (pos : 0 < N) (oklen : N=if b then k else l) :
      ∀ z, slopes k l z * base h b N ≠ 2^N * constants h k l z := by
    apply (sites_iff (k:=k) (l:=l) (fun e i => 2^i*base h b N ≠ 2^N*base h e i)).mpr
    constructor
    · exact fun i hi => terminal_distinct gap b true pos (fun eq => by simpa [eq,oklen] using hi)
    · exact fun i hi => terminal_distinct gap b false pos (fun eq => by simpa [eq,oklen] using hi)
  obtain ⟨Q,_,hQ,u,hitQ,safeQ⟩ := separate_terminal _ _ _ _ 2 (pow_pos (by decide) k) (distinct true hk rfl)
  obtain ⟨R,hQR,hR,v,hitR,safeR⟩ := separate_terminal _ _ _ _ Q (pow_pos (by decide) l) (distinct false hl rfl)
  have chooseAt (q : ℕ) : ∃ w : ZMod q, (q.Prime → avoids h k l q w) ∧
      (q=Q → residue q (2^k) (base h true k) w=0) ∧ (q=R → residue q (2^l) (base h false l) w=0) := by
    by_cases e : q=Q
    · subst q
      exact ⟨u,fun _ => (avoids_iff ..).mpr safeQ,fun _ => hitQ,fun hh => (hQR.ne hh).elim⟩
    by_cases f : q=R
    · subst q
      exact ⟨v,fun _ => (avoids_iff ..).mpr safeR,fun hh => (e hh).elim,fun _ => hitR⟩
    by_cases hp : q.Prime
    · obtain ⟨w,hw⟩ := (localTest_iff_all hk hl).mp ok q hp
      exact ⟨w,fun _ => hw,fun hh => (e hh).elim,fun hh => (f hh).elim⟩
    · exact ⟨0,fun hh => (hp hh).elim,fun hh => (e hh).elim,fun hh => (f hh).elim⟩
  choose x safe hit1 hit2 using chooseAt
  exact ⟨Q,R,hQ,hR,hQR,x,safe,hit1 Q rfl,hit2 R rfl⟩

#print axioms stop_classes

#print axioms sites_iff
#print axioms avoids_iff
#print axioms avoids_unit

end CunninghamChain.PairedRough
