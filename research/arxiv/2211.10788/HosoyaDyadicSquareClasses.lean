import LucasFibonacciSquareValues
import LucasFibonacciIsolatedDivisors

/-! Counting the sites of a fixed square class on either Hosoya diagonal. -/

namespace Arxiv.«2211.10788».HosoyaSquareClasses

open Finset HosoyaNeighbor
open scoped Classical

/-- At every scale a sign-reversing prime has Fibonacci rank exactly 4·2^r. -/
theorem signed_prime_of_exact_rank (r : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p%4=3 ∧
      (∀ j, p ∣ Nat.fib j ↔ 4*2^r ∣ j) ∧
      ∀ s : HosoyaNeighbor, ∀ a m,
        (s.value (a+(4*2^r)*m) : ZMod p) = (-1)^m * (s.value a : ZMod p) := by
  obtain ⟨p,hp,h4,hs⟩ := dyadic_sign_prime r
  let : Fact p.Prime := ⟨hp⟩
  let D := 4*2^r
  let b := 2*2^r
  have hDb : D=2*b := by dsimp [D,b]; ring
  have hpow : D=2^(r+2) := by dsimp [D]; ring
  have hbpow : b=2^(r+1) := by dsimp [b]; ring
  have hf := hs (fun n => (Nat.fib n : ℤ)) (fun n => by exact_mod_cast @Nat.fib_add_two n)
  have hF : (Nat.fib D : ZMod p)=0 := by simpa [D] using hf 0 1
  have hF' : (Nat.fib (2*b+1) : ZMod p) = -1 := by
    simpa [← hDb,D,Nat.add_comm] using hf 1 1
  have hnot : ¬p ∣ Nat.fib b := by
    intro hh
    rw [Nat.fib_two_mul_add_one] at hF'
    push_cast at hF'
    rw [(ZMod.natCast_eq_zero_iff ..).mpr hh] at hF'
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (y:=1) one_ne_zero (by simpa using hF') h4
  have hdiv := (ZMod.natCast_eq_zero_iff ..).mp hF
  refine ⟨p,hp,h4,?_,?_⟩
  · intro j
    change p ∣ Nat.fib j ↔ D ∣ j
    refine ⟨fun hj => ?_,fun h => hdiv.trans (Nat.fib_dvd _ _ h)⟩
    have hg : p ∣ Nat.fib (D.gcd j) := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd hdiv hj
    have hd := Nat.gcd_dvd_left D j
    rw [hpow] at hd
    obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    by_cases h : i=r+2
    · have hg' := Nat.gcd_dvd_right D j
      simpa [hpow,h,he] using hg'
    · exfalso
      apply hnot
      apply hg.trans (Nat.fib_dvd ..)
      rw [hpow,he,hbpow]
      exact pow_dvd_pow 2 (by omega)
  · intro s a m
    have h := hs (fun n => (s.value n : ℤ)) (fun n => by exact_mod_cast (s.value_step n).trans (Nat.add_comm ..)) a m
    simpa using h

#print axioms signed_prime_of_exact_rank

private theorem congruent_zeros {p D : ℕ} [NeZero p]
    (h : ∀ j, p ∣ Nat.fib j ↔ D ∣ j) (s : HosoyaNeighbor) {i j : ℕ}
    (hi : p ∣ s.value i) (hj : p ∣ s.value j) : i ≡ j [MOD D] := by
  have ordered {a b : ℕ} (hle : a ≤ b) (ha : p ∣ s.value a) (hb : p ∣ s.value b) :
      a ≡ b [MOD D] := by
    apply (Nat.modEq_iff_dvd' hle).mpr
    apply (h _).mp
    exact s.supportBounds.common ha (show p ∣ s.value (a+(b-a)) by simpa [Nat.add_sub_of_le hle] using hb)
  rcases le_total i j with hh | hh
  · exact ordered hh hi hj
  · exact (ordered hh hj hi).symm

private theorem zero_at_split {p D : ℕ} (hp : p.Prime) (h4 : p%4=3) (f : ℕ → ℕ)
    (hs : ∀ a m, (f (a+D*m) : ZMod p)=(-1)^m*(f a : ZMod p)) {d i j : ℕ}
    (hi : ∃ u, f i=d*u^2) (hj : ∃ v, f j=d*v^2)
    (hij : i ≡ j [MOD D]) (hdiff : ¬ i ≡ j [MOD 2*D]) : p ∣ f i := by
  let : Fact p.Prime := ⟨hp⟩
  have ordered {a b u v : ℕ} (hle : a ≤ b) (ha : f a=d*u^2) (hb : f b=d*v^2)
      (hc : a ≡ b [MOD D]) (hn : ¬a ≡ b [MOD 2*D]) : p ∣ f a ∧ p ∣ f b := by
    obtain ⟨m,hm⟩ := (Nat.modEq_iff_dvd' hle).mp hc
    have he : a+D*m=b := by omega
    have ho : Odd m := by
      rcases Nat.even_or_odd m with ⟨v,hv⟩ | hodd
      · exfalso
        exact hn ((Nat.modEq_iff_dvd' hle).mpr ⟨v,by rw [hm,hv]; ring⟩)
      · exact hodd
    have hz := hs a m
    rw [he,ho.neg_one_pow,neg_one_mul] at hz
    have ha0 : (f a : ZMod p)=0 := by
      by_contra hne
      rw [ha] at hne
      push_cast at hne
      obtain ⟨hd,hu⟩ := mul_ne_zero_iff.mp hne
      have hu' : (u:ZMod p)≠0 := by intro he; simp [he] at hu
      rw [ha,hb] at hz
      push_cast at hz
      have hq : (v:ZMod p)^2 = -(u:ZMod p)^2 := by
        apply mul_left_cancel₀ hd
        simpa using hz
      exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hu' hq h4
    exact ⟨(ZMod.natCast_eq_zero_iff ..).mp ha0,
      (ZMod.natCast_eq_zero_iff ..).mp (by simpa [ha0] using hz)⟩
  obtain ⟨u,hu⟩ := hi
  obtain ⟨v,hv⟩ := hj
  rcases le_total i j with h | h
  · exact (ordered h hu hv hij hdiff).1
  · exact (ordered h hv hu hij.symm (fun h => hdiff h.symm)).2

/-- At most one residue modulo 4·2^r can contain square multiples of d in both
its lifts modulo 8·2^r, uniformly in the multiplier d. -/
theorem unique_splitting_class (s : HosoyaNeighbor) (d r : ℕ) :
    ∀ a b c e : ℕ, (∀ n ∈ ({a,b,c,e}:Finset ℕ), ∃ u, s.value n=d*u^2) →
      a ≡ b [MOD 4*2^r] → ¬ a ≡ b [MOD 2*(4*2^r)] →
      c ≡ e [MOD 4*2^r] → ¬ c ≡ e [MOD 2*(4*2^r)] →
      a ≡ c [MOD 4*2^r] := by
  obtain ⟨p,hp,h4,hr,hs⟩ := signed_prime_of_exact_rank r
  let : NeZero p := ⟨hp.ne_zero⟩
  intro a b c e h ha hab hc hce
  apply congruent_zeros hr s
  · exact zero_at_split hp h4 _ (hs s) (h a (by simp)) (h b (by simp)) ha hab
  · exact zero_at_split hp h4 _ (hs s) (h c (by simp)) (h e (by simp)) hc hce

#print axioms unique_splitting_class

private theorem residues_step (s : HosoyaNeighbor) (d r : ℕ) (T : Finset ℕ)
    (hT : ∀ n ∈ T, ∃ u, s.value n=d*u^2) :
    (T.image (fun n => n%(2*(4*2^r)))).card ≤ (T.image (fun n => n%(4*2^r))).card+1 := by
  classical
  let D := 4*2^r
  let A := T.image (fun n => n%(2*D))
  let B := T.image (fun n => n%D)
  let f := fun x : ℕ => x%D
  change A.card ≤ B.card+1
  have hD : 0<D := by dsimp [D]; positivity
  have red (n : ℕ) : f (n%(2*D))=n%D := Nat.mod_mod_of_dvd _ (dvd_mul_left ..)
  have hmap : Set.MapsTo f (A:Set ℕ) (B:Set ℕ) := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := mem_image.mp (show x∈A from hx)
    exact mem_image.mpr ⟨n,hn,(red n).symm⟩
  have hlift {x : ℕ} (hx : x∈A) : x=f x ∨ x=f x+D := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    let z := n%(2*D)
    have hz : z < 2*D := Nat.mod_lt _ (by omega)
    change z=z%D ∨ z=z%D+D
    by_cases hz' : z<D
    · left; rw [Nat.mod_eq_of_lt hz']
    · right
      have he : z%D=(z-D)%D := Nat.mod_eq_sub_mod (by omega)
      rw [he,Nat.mod_eq_of_lt (show z-D<D by omega)]
      omega
  have hsplit {a b c e : ℕ} (ha : a∈A) (hb : b∈A) (hc : c∈A) (he : e∈A)
      (hab : f a=f b) (hab' : a≠b) (hce : f c=f e) (hce' : c≠e) : f a=f c := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hb
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hc
    obtain ⟨l,hl,rfl⟩ := mem_image.mp he
    simp only [red] at hab hce ⊢
    apply unique_splitting_class s d r i j k l _ hab hab' hce hce'
    intro n hn
    apply hT
    simp only [mem_insert,mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> assumption
  by_cases hinj : Set.InjOn f (A : Set ℕ)
  · exact (card_le_card_of_injOn f hmap hinj).trans (by omega)
  · obtain ⟨a,ha,b,hb,hab,hab'⟩ : ∃ a ∈ A, ∃ b ∈ A, f a=f b ∧ a≠b := by
      by_contra! h
      apply hinj
      intro x hx y hy he
      exact h x hx y hy he
    have hleft : Set.InjOn f (A.erase a : Set ℕ) := by
      intro x hx y hy hxy
      obtain ⟨hxa,hx'⟩ := mem_erase.mp (show x∈A.erase a from hx)
      obtain ⟨hya,hy'⟩ := mem_erase.mp (show y∈A.erase a from hy)
      by_contra hne
      have he := hsplit ha hb hx' hy' hab hab' hxy hne
      have hx₁ := hlift hx'
      have hy₁ := hlift hy'
      have ha₁ := hlift ha
      omega
    have hle := card_le_card_of_injOn f (fun x hx => hmap (erase_subset _ _ hx)) hleft
    rw [card_erase_of_mem ha] at hle
    omega

/-- In every interval of 4·2^r consecutive indices, at most 4+r terms on either
diagonal equal d times a square. The bound is uniform in the multiplier and start. -/
theorem square_class_block_bound (s : HosoyaNeighbor) (d a r : ℕ) :
    ((Ico a (a+4*2^r)).filter (fun n => ∃ u, s.value n=d*u^2)).card ≤ 4+r := by
  classical
  let T := (Ico a (a+4*2^r)).filter fun n => ∃ u, s.value n=d*u^2
  have hT : ∀ n ∈ T, ∃ u, s.value n=d*u^2 := fun n hn => (mem_filter.mp hn).2
  have hb (j : ℕ) : (T.image (fun n => n%(4*2^j))).card ≤ 4+j := by
    induction j with
    | zero =>
      have hh : T.image (fun n => n%(4*2^0)) ⊆ range 4 := by
        intro k hk
        obtain ⟨n,_,rfl⟩ := mem_image.mp hk
        simpa using (Nat.mod_lt n (by decide : 0<4))
      simpa using card_le_card hh
    | succ j ih =>
      have hh := residues_step s d j T hT
      rw [show 4*2^(j+1) = 2*(4*2^j) by ring]
      omega
  have hinj : Set.InjOn (fun n => n%(4*2^r)) (T : Set ℕ) := by
    intro n hn m hm he
    obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp (mem_filter.mp (show n∈T from hn)).1
    obtain ⟨hm₁,hm₂⟩ := mem_Ico.mp (mem_filter.mp (show m∈T from hm)).1
    apply (show n ≡ m [MOD 4*2^r] from he).eq_of_abs_lt
    let D := 4*2^r
    change n < a+D at hn₂
    change m < a+D at hm₂
    change |(m:ℤ)-(n:ℤ)| < (D:ℕ)
    rw [abs_lt]; omega
  have h := hb r
  rwa [card_image_of_injOn hinj] at h

#print axioms square_class_block_bound

end Arxiv.«2211.10788».HosoyaSquareClasses
