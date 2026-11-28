import CunninghamGeometricWindow
import CunninghamSquarefreeLocalFactors

/-! Gaps between sites avoiding a finite collection of prime divisors. -/

namespace CunninghamChain.OrbitCover
open Finset SquarefreeSeeds

theorem two_order_pos {q : ℕ} (hq : q.Prime) (odd : 2<q) : 0 < orderOf (2:ZMod q) := by
  let : Fact q.Prime := ⟨hq⟩
  have nz : (2:ZMod q)≠0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff 2 q).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide) odd)
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr
    ⟨q-1,by omega,ZMod.pow_card_sub_one_eq_one nz⟩)

private lemma local_equation (b : Bool) {p q : ℕ} (pp : 0<p) (hq : q.Prime) (odd : 2<q) :
    ∃ v : ℂ × ℂ, v.1≠0 ∧ ∀ j : ℕ, v.1^j=v.2 ↔ q∣term b p j := by
  classical
  by_cases used : ∃ a : ℕ, q∣term b p a
  · obtain ⟨a,hit⟩ := used
    let : Fact q.Prime := ⟨hq⟩
    let d := orderOf (2:ZMod q)
    have dp : 0<d := two_order_pos hq odd
    let z := Complex.exp (2*Real.pi*Complex.I/d)
    have prim : IsPrimitiveRoot z d := Complex.isPrimitiveRoot_exp d dp.ne'
    have fin : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨d,dp,prim.pow_eq_one⟩
    refine ⟨(z,z^a),Complex.exp_ne_zero _,?_⟩
    intro j
    change z^j=z^a ↔ _
    rw [fin.pow_eq_pow_iff_modEq,←prim.eq_orderOf]
    exact (SquarefreeDensity.term_dvd_at_iff b odd pp hit j).symm
  · refine ⟨(1,0),one_ne_zero,?_⟩
    intro j
    simp [show ¬q∣term b p j from fun h => used ⟨j,h⟩]

/-- Once one site escapes a set of k odd primes, every block of 2^k
sites contains another site escaping all k primes, for either sign. -/
theorem escape_every_block (b : Bool) {p : ℕ} (pp : 0<p) (S : Finset ℕ)
    (prime : ∀ q∈S,q.Prime ∧ 2<q) {u : ℕ} (miss : ∀ q∈S, ¬q∣term b p u) (s : ℕ) :
    ∃ j<2^S.card, ∀ q∈S, ¬q∣term b p (s+j) := by
  classical
  have data (q : ℕ) : ∃ v : ℂ × ℂ, v.1≠0 ∧
      (q∈S → ∀ j : ℕ, v.1^j=v.2 ↔ q∣term b p j) := by
    by_cases h : q∈S
    · obtain ⟨v,nz,eq⟩ := local_equation b pp (prime q h).1 (prime q h).2
      exact ⟨v,nz,fun _ => eq⟩
    · exact ⟨(1,0),one_ne_zero,fun h' => (h h').elim⟩
  choose v nz eq using data
  let L := S.toList.map v
  have non : ∀ x∈L,x.1≠0 := by
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact nz q
  have zero : ∀ x∈L,x.1^u≠x.2 := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact (eq q (Finset.mem_toList.mp hq) u).not.mpr (miss q (Finset.mem_toList.mp hq))
  obtain ⟨j,bound,free⟩ := product_escape_in_block L non zero s
  refine ⟨j,by simpa [L] using bound,?_⟩
  intro q hq
  exact (eq q hq _).not.mp (free (v q) (List.mem_map.mpr ⟨q,Finset.mem_toList.mpr hq,rfl⟩))

def Covers (b : Bool) (p : ℕ) (S : Finset ℕ) : Prop := ∀ j : ℕ, 0<j → ∃ q∈S,q∣term b p j

/-- An odd prime that the cover cannot do without has small order for 2. -/
theorem indispensable_order (b : Bool) {p q : ℕ} (pp : 0<p) (S : Finset ℕ)
    (prime : ∀ l∈S,l.Prime ∧ 2<l) (mem : q∈S) (cover : Covers b p S)
    (needed : ¬Covers b p (S.erase q)) : orderOf (2:ZMod q)≤2^(S.card-1) := by
  classical
  unfold Covers at needed
  push Not at needed
  obtain ⟨u,up,miss⟩ := needed
  obtain ⟨t,ht,divide⟩ := cover u up
  have isq : t=q := by
    by_contra ne
    exact miss t (mem_erase.mpr ⟨ne,ht⟩) divide
  subst t
  let : Fact q.Prime := ⟨(prime q mem).1⟩
  obtain ⟨j,bound,free⟩ := escape_every_block b pp (S.erase q)
    (fun t h => prime t (mem_of_mem_erase h)) miss (u+1)
  obtain ⟨l,hl,hit⟩ := cover (u+1+j) (by omega)
  have eq : l=q := by
    by_contra ne
    exact free l (mem_erase.mpr ⟨ne,hl⟩) hit
  subst l
  have ap := (SquarefreeDensity.term_dvd_at_iff b (prime q mem).2 pp divide _).mp hit
  have ap' : j+1 ≡ 0 [MOD orderOf (2:ZMod q)] := Nat.ModEq.add_left_cancel' u
    (by simpa only [Nat.add_zero,show u+(j+1)=u+1+j by omega] using ap)
  have lo := Nat.le_of_dvd (Nat.succ_pos j) (Nat.modEq_zero_iff_dvd.mp ap')
  rw [Finset.card_erase_of_mem mem] at bound
  omega

#print axioms escape_every_block
#print axioms indispensable_order

end CunninghamChain.OrbitCover
