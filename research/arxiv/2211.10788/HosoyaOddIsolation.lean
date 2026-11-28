import HosoyaDyadicSquareClasses
import FormalConjecturesForMathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Primorial

/-! Prime divisors of odd multiplicity exclusive to sites in windows on both Hosoya diagonals. -/

namespace Arxiv.«2211.10788».HosoyaSquareClasses

open Finset Filter HosoyaNeighbor
open scoped Classical Topology

/-- An odd-multiplicity divisor above Y that is absent from all other sites on
either diagonal within H steps. The counter n starts at physical index two. -/
def HasIsolatedOddPrime (s : HosoyaNeighbor) (n H Y : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Y<p ∧ Odd ((s.value n).factorization p) ∧
    ∀ t m, s≠t ∨ n≠m → Nat.dist n m ≤ H → ¬p ∣ t.value m

private theorem pos_value (s : HosoyaNeighbor) (n : ℕ) : 0 < s.value n := by
  have hh := s.supportBounds.lower n
  by_contra! he
  rw [Nat.eq_zero_of_le_zero he] at hh
  have := Nat.one_le_two_pow (n:=n)
  omega

private theorem squarefree_part_rep {y : ℕ} (hy : y≠0) :
    ∃ u : ℕ, y = y.squarefreePart*u^2 := by
  refine ⟨∏ p ∈ y.primeFactors, p ^ (y.factorization p/2),?_⟩
  rw [Nat.squarefreePart,Finsupp.prod,Nat.support_factorization,← Finset.prod_pow,← Finset.prod_mul_distrib]
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hy]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul,← pow_add]
  congr 1
  omega

private def cost (H Y : ℕ) := primorial Y * shiftDetProduct H

private theorem cost_pos (H Y : ℕ) : 0 < cost H Y :=
  Nat.mul_pos (primorial_pos _) (shiftDetProduct_pos _)

private theorem cost_le (H Y : ℕ) : cost H Y ≤ 2^(2*Y+4*(H+1)*(H+10)) := by
  calc cost H Y ≤ 4^Y * 2^((H+1)*(4*(H+10))) :=
        Nat.mul_le_mul (primorial_le_four_pow _) (shiftDetProduct_le _)
       _ = _ := by
         rw [pow_add,pow_mul (2:ℕ) 2 Y,show (2:ℕ)^2=4 by decide,
           show (H+1)*(4*(H+10))=4*(H+1)*(H+10) by ring]

private theorem class_dvd_cost {s : HosoyaNeighbor} {n H Y : ℕ} (h : ¬HasIsolatedOddPrime s n H Y) :
    (s.value n).squarefreePart ∣ cost H Y := by
  let y := s.value n
  change y.squarefreePart ∣ cost H Y
  rw [← Nat.prod_primeFactors_of_squarefree (Nat.squarefree_squarefreePart y)]
  apply (Nat.prod_primeFactors_dvd_iff (cost_pos H Y).ne').mpr
  intro p hp
  obtain ⟨hpr,hd,_⟩ := Nat.mem_primeFactors.mp hp
  refine Nat.mem_primeFactors.mpr ⟨hpr,?_,(cost_pos H Y).ne'⟩
  by_cases small : p ≤ Y
  · exact dvd_mul_of_dvd_left (hpr.dvd_primorial_iff.mpr small) _
  have hodd : Odd (y.factorization p) := by
    have he := hpr.factorization_pos_of_dvd y.squarefreePart_ne_zero hd
    rw [Nat.squarefreePart_factorization _ hpr] at he
    exact Nat.odd_iff.mpr (by omega)
  have hex : ∃ t m, (s≠t ∨ n≠m) ∧ Nat.dist n m ≤ H ∧ p ∣ t.value m := by
    by_contra! hh
    exact h ⟨p,hpr,by omega,hodd,hh⟩
  obtain ⟨t,m,hne,hgap,hdiv⟩ := hex
  exact dvd_mul_of_dvd_right
    (dvd_shiftDetProduct_of_shared hne hgap (hd.trans (Nat.squarefreePart_dvd y)) hdiv) _

/-- Exceptional sites in an arbitrary translated block. The divisor count is
independent of the block's starting index. -/
theorem odd_divisor_exception_bound (s : HosoyaNeighbor) (a r H Y : ℕ) :
    ((Ico a (a+4*2^r)).filter (fun n => ¬HasIsolatedOddPrime s n H Y)).card ≤
      (primorial Y * shiftDetProduct H).divisors.card * (4+r) := by
  let T (d : ℕ) := (Ico a (a+4*2^r)).filter (fun n => ∃ u, s.value n=d*u^2)
  let M := cost H Y
  have hs : (Ico a (a+4*2^r)).filter (fun n => ¬HasIsolatedOddPrime s n H Y) ⊆ M.divisors.biUnion T := by
    intro n hn
    obtain ⟨hn,hh⟩ := mem_filter.mp hn
    apply mem_biUnion.mpr
    refine ⟨(s.value n).squarefreePart,Nat.mem_divisors.mpr ⟨class_dvd_cost hh,(cost_pos H Y).ne'⟩,?_⟩
    exact mem_filter.mpr ⟨hn,squarefree_part_rep (pos_value s n).ne'⟩
  calc _ ≤ (M.divisors.biUnion T).card := card_le_card hs
       _ ≤ ∑ d ∈ M.divisors, (T d).card := card_biUnion_le
       _ ≤ ∑ _ ∈ M.divisors, (4+r) := sum_le_sum (fun d _ => square_class_block_bound s d a r)
       _ = _ := by simp [M,cost]

#print axioms odd_divisor_exception_bound

/-- Every site in the forward window on both sides has its own odd-multiplicity
prime above Y, exclusive even against comparison sites outside that forward window
and within H steps of the chosen site. -/
def GoodWindow (n H Y : ℕ) : Prop :=
  ∀ s : HosoyaNeighbor, ∀ j ≤ H, HasIsolatedOddPrime s (n+j) H Y

/-- Any nonempty selection from a good window has nonsquare product. -/
theorem nonsquare_of_good_window {n H Y : ℕ} (hg : GoodWindow n H Y)
    (T : Finset (HosoyaNeighbor × ℕ)) (hT : T.Nonempty)
    (hr : ∀ u ∈ T, n ≤ u.2 ∧ u.2 ≤ n+H) : ¬IsSquare (∏ u ∈ T, u.1.value u.2) := by
  obtain ⟨⟨s,i⟩,ha⟩ := hT
  obtain ⟨hi,hi'⟩ := hr _ ha
  change n ≤ i at hi
  change i ≤ n+H at hi'
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨p,hp,_,hf,hisol⟩ := hg s j (by omega)
  let f (u : HosoyaNeighbor × ℕ) := u.1.value u.2
  let W := (T.erase (s,n+j)).prod f
  have hw : ¬p ∣ W := hp.prime.not_dvd_finsetProd fun u hu => by
    obtain ⟨hne,hu⟩ := mem_erase.mp hu
    obtain ⟨hm,hm'⟩ := hr _ hu
    apply hisol u.1 u.2
    · by_contra! heq
      exact hne (Prod.ext heq.1.symm heq.2.symm)
    · simp only [Nat.dist]; omega
  have hwpos : W ≠ 0 := fun h => hw (h ▸ dvd_zero _)
  have he := T.mul_prod_erase f ha
  change s.value (n+j)*W=T.prod f at he
  rintro ⟨b,hb⟩
  change T.prod f=b*b at hb
  have hh := congrArg (fun z : ℕ => z.factorization p) (he.trans hb)
  rw [← pow_two,Nat.factorization_pow,Nat.factorization_mul (pos_value ..).ne' hwpos] at hh
  simp [Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd hw] at hh
  obtain ⟨v,hv⟩ := hf
  omega

/-- Uniform count of starting indices whose forward window fails to supply one
exclusive odd-multiplicity prime per site on both sides. -/
theorem window_exception_bound (a r H Y : ℕ) :
    ((Ico a (a+4*2^r)).filter (fun n => ¬GoodWindow n H Y)).card ≤
      2*(H+1)*(primorial Y * shiftDetProduct H).divisors.card*(4+r) := by
  let B := Ico a (a+4*2^r)
  let E (s : HosoyaNeighbor) (j : ℕ) := B.filter fun n => ¬HasIsolatedOddPrime s (n+j) H Y
  let K := (cost H Y).divisors.card*(4+r)
  have hb (s : HosoyaNeighbor) (j : ℕ) : (E s j).card ≤ K := by
    let V := (Ico (a+j) (a+j+4*2^r)).filter (fun m => ¬HasIsolatedOddPrime s m H Y)
    apply le_trans _ (odd_divisor_exception_bound s (a+j) r H Y)
    apply card_le_card_of_injOn (fun n : ℕ => n+j) (t:=V)
    · intro n hn
      obtain ⟨hn,hp⟩ := mem_filter.mp (show n∈E s j from hn)
      obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hn
      change n+j ∈ V
      exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,hp⟩
    · intro x _ y _ h; simpa using h
  let V (j : ℕ) := E .upper j ∪ E .lower j
  have hV (j : ℕ) : (V j).card ≤ K+K :=
    (card_union_le _ _).trans (Nat.add_le_add (hb .upper j) (hb .lower j))
  have hsub : B.filter (fun n => ¬GoodWindow n H Y) ⊆ (range (H+1)).biUnion V := by
    intro n hn
    obtain ⟨hn,h⟩ := mem_filter.mp hn
    unfold GoodWindow at h
    push Not at h
    obtain ⟨s,j,hj,hs⟩ := h
    apply mem_biUnion.mpr
    refine ⟨j,mem_range.mpr (by omega),?_⟩
    cases s with
    | upper => exact mem_union_left _ (mem_filter.mpr ⟨hn,hs⟩)
    | lower => exact mem_union_right _ (mem_filter.mpr ⟨hn,hs⟩)
  calc _ ≤ ((range (H+1)).biUnion V).card := card_le_card hsub
       _ ≤ ∑ j ∈ range (H+1), (V j).card := card_biUnion_le
       _ ≤ ∑ _ ∈ range (H+1), (K+K) := sum_le_sum (fun j _ => hV j)
       _ = _ := by simp [K,cost]; ring

#print axioms nonsquare_of_good_window
#print axioms window_exception_bound

private theorem prefactor_bound {r : ℕ} (hr : 25600 ≤ r) : r+4 ≤ 2^(r/16) := by
  have grows (m : ℕ) (hm : 10 ≤ m) : 16*(m+1)+4 ≤ 2^m := by
    induction m, hm using Nat.le_induction with
    | base => decide
    | succ m hm ih =>
      rw [pow_succ]
      omega
  have hh := grows (r/16) (by omega)
  omega

private theorem dyadic_exception_sqrt (a r : ℕ) (hr : 25600 ≤ r) :
    ((Ico a (a+4*2^r)).filter (fun n => ¬GoodWindow n (r.sqrt/16) (r/16))).card ≤
      2^(r/2) := by
  let H := r.sqrt/16
  let Y := r/16
  let M := cost H Y
  have hM : 0<M := cost_pos H Y
  have hdiv : M.divisors.card ≤ M := by
    have hsub : M.divisors ⊆ Icc 1 M := by
      intro d hd
      exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hM (Nat.mem_divisors.mp hd).1⟩
    simpa using card_le_card hsub
  have hroot : 160 ≤ r.sqrt := Nat.le_sqrt.mpr (by simpa using hr)
  have hspan : 64*((H+1)*(H+10)) ≤ r := by
    calc
      64*((H+1)*(H+10)) ≤ (8*(H+10))^2 := by
        rw [show (8*(H+10))^2 = 64*((H+10)*(H+10)) by ring]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ r.sqrt^2 := Nat.pow_le_pow_left (by dsimp [H]; omega) 2
      _ ≤ r := Nat.sqrt_le' r
  have hbound : 1+Y+(2*Y+4*(H+1)*(H+10))+Y ≤ r/2 := by
    have hy : 16*Y ≤ r := by dsimp [Y]; omega
    have h₁ : 16*(4*(H+1)*(H+10)) ≤ r := by nlinarith only [hspan]
    omega
  have h1 : H+1 ≤ 2^Y := by
    apply le_trans _ (prefactor_bound hr)
    have := Nat.sqrt_le_self r
    dsimp [H]; omega
  have h2 : M.divisors.card ≤ 2^(2*Y+4*(H+1)*(H+10)) := hdiv.trans (cost_le H Y)
  apply (window_exception_bound a r H Y).trans
  calc 2*(H+1)*M.divisors.card*(4+r) ≤
         2*(2^Y)*2^(2*Y+4*(H+1)*(H+10))*2^Y := by
           apply Nat.mul_le_mul _ (by simpa [Y,Nat.add_comm] using prefactor_bound hr)
           exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) h2
       _ = 2^(1+Y+(2*Y+4*(H+1)*(H+10))+Y) := by simp [pow_add]
       _ ≤ _ := Nat.pow_le_pow_right (by decide) hbound

/-- Write r=floor(log₂ N). Once r≥25600, at most sqrt(N) starts in *any*
interval of length N fail to have exclusive odd-multiplicity primes larger
than floor(r/16) at all sites of their two-diagonal window of width floor(sqrt(r)/16). -/
theorem moving_windows_sparse (a N : ℕ) (hN : 25600 ≤ Nat.log 2 N) :
    let r := Nat.log 2 N
    (((Ico a (a+N)).filter (fun n => ¬GoodWindow n (r.sqrt/16) (r/16))).card)^2 ≤ N := by
  let r := Nat.log 2 N
  change (((Ico a (a+N)).filter (fun n => ¬GoodWindow n (r.sqrt/16) (r/16))).card)^2 ≤ N
  have hN' : N≠0 := by intro h; simp [h] at hN
  have hlen : N ≤ 4*2^r := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1<2) N
    change N < 2^(r+1) at hh
    rw [pow_succ] at hh
    omega
  have hs : (Ico a (a+N)).filter (fun n => ¬GoodWindow n (r.sqrt/16) (r/16)) ⊆
      (Ico a (a+4*2^r)).filter (fun n => ¬GoodWindow n (r.sqrt/16) (r/16)) := by
    intro n hn
    obtain ⟨hi,h⟩ := mem_filter.mp hn
    obtain ⟨ha,hb⟩ := mem_Ico.mp hi
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨ha,by omega⟩,h⟩
  have hb := (card_le_card hs).trans (dyadic_exception_sqrt a r hN)
  apply (Nat.pow_le_pow_left hb 2).trans
  rw [← pow_mul]
  exact (Nat.pow_le_pow_right (by decide) (by omega : r/2*2 ≤ r)).trans (Nat.pow_log_le_self 2 hN')

#print axioms moving_windows_sparse

end Arxiv.«2211.10788».HosoyaSquareClasses
