import CunninghamFiniteCoverSearch
import Mathlib.NumberTheory.LucasPrimality

/-! Lucas certificates for the large primes in the bounded Cunningham cover search. -/

namespace CunninghamChain.OrbitCover.Certificate

theorem member_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) (L : List ℕ)
    (primes : ∀ x∈L,x.Prime) (div : q∣L.prod) : q∈L := by
  induction L with
  | nil => exact (hq.not_dvd_one (by simpa using div)).elim
  | cons x xs ih =>
    rcases hq.dvd_mul.mp (by simpa only [List.prod_cons] using div) with h|h
    · rcases (Nat.dvd_prime (primes _ (by simp))).mp h with unit|eq
      · exact (hq.ne_one unit).elim
      · simp [eq]
    · exact List.mem_cons_of_mem _ (ih (fun t ht => primes _ (List.mem_cons_of_mem _ ht)) h)

private theorem binary_pow {G : Type*} [Monoid G] (a : G) (n : ℕ) : npowBinRec n a=a^n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ,pow_succ,ih]

/-- The factors of p−1 may repeat. Only a small set of generator tests is needed. -/
private theorem certify {p a : ℕ} (L : List ℕ) (factors : L.prod=p-1)
    (prime : ∀ q∈L,q.Prime)
    (one : npowBinRec (p-1) (a:ZMod p)=1)
    (full : ∀ q∈L,npowBinRec ((p-1)/q) (a:ZMod p)≠1) : p.Prime := by
  apply lucas_primality p (a:ZMod p) (by rwa [binary_pow] at one)
  intro q hq hdiv
  rw [← binary_pow]
  exact full q (member_of_prime_dvd_prod hq L prime (factors ▸ hdiv))

private def trialPrime (p : ℕ) : Bool :=
  decide (2≤p) && (List.range (p.sqrt+1)).all (fun m => decide (m<2 ∨ ¬m∣p))

private theorem trial_prime {p : ℕ} (ok : trialPrime p=true) : p.Prime := by
  simp only [trialPrime,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  refine Nat.prime_def_le_sqrt.mpr ⟨ok.1,fun m lo hi => ?_⟩
  exact (ok.2 m (List.mem_range.mpr (by omega))).resolve_left (by omega)

private def valid (p a : ℕ) (L : List ℕ) : Bool :=
  decide (L.prod=p-1) && L.all trialPrime &&
  decide (npowBinRec (p-1) (a:ZMod p)=1) &&
  L.all (fun q => decide (npowBinRec ((p-1)/q) (a:ZMod p)≠1))

private theorem valid_prime {p a : ℕ} {L : List ℕ} (ok : valid p a L=true) : p.Prime := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  obtain ⟨⟨⟨prod,pr⟩,one⟩,full⟩ := ok
  exact certify L prod (fun q h => trial_prime (pr q h)) one full

private structure Row where
  seed : ℕ
  generator : ℕ
  factors : List ℕ
  firstEscape : ℕ
  secondEscape : ℕ

-- Each row supplies a Lucas witness, the factors of seed−1 with
-- multiplicity, and one escaping positive site for each sign.
private def rows : List Row := [
  ⟨3, 2, [2], 65, 63⟩,
  ⟨5, 2, [2, 2], 5, 62⟩,
  ⟨7, 3, [2, 3], 64, 5⟩,
  ⟨11, 2, [2, 5], 4, 12⟩,
  ⟨13, 2, [2, 2, 3], 8, 4⟩,
  ⟨17, 3, [2, 2, 2, 2], 6, 60⟩,
  ⟨19, 2, [2, 3, 3], 6, 5⟩,
  ⟨23, 5, [2, 11], 3, 4⟩,
  ⟨29, 2, [2, 2, 7], 3, 4⟩,
  ⟨31, 3, [2, 3, 5], 62, 8⟩,
  ⟨37, 2, [2, 2, 3, 3], 4, 4⟩,
  ⟨41, 6, [2, 2, 2, 5], 1, 10⟩,
  ⟨43, 3, [2, 3, 7], 12, 6⟩,
  ⟨47, 5, [2, 23], 2, 8⟩,
  ⟨53, 2, [2, 2, 13], 1, 6⟩,
  ⟨59, 2, [2, 29], 2, 4⟩,
  ⟨61, 2, [2, 2, 3, 5], 4, 7⟩,
  ⟨71, 7, [2, 5, 7], 4, 2⟩,
  ⟨73, 5, [2, 2, 2, 3, 3], 32, 3⟩,
  ⟨79, 3, [2, 3, 13], 4, 2⟩,
  ⟨89, 3, [2, 2, 2, 11], 1, 2⟩,
  ⟨97, 5, [2, 2, 2, 2, 2, 3], 4, 1⟩,
  ⟨103, 5, [2, 3, 17], 4, 2⟩,
  ⟨109, 6, [2, 2, 3, 3, 3], 2, 2⟩,
  ⟨113, 3, [2, 2, 2, 2, 7], 1, 2⟩,
  ⟨127, 3, [2, 3, 3, 7], 60, 3⟩,
  ⟨151, 6, [2, 3, 5, 5], 2, 3⟩,
  ⟨157, 5, [2, 2, 3, 13], 6, 1⟩,
  ⟨223, 3, [2, 3, 37], 4, 3⟩,
  ⟨233, 3, [2, 2, 2, 29], 1, 2⟩,
  ⟨241, 7, [2, 2, 2, 2, 3, 5], 2, 5⟩,
  ⟨251, 6, [2, 5, 5, 5], 1, 4⟩,
  ⟨257, 3, [2, 2, 2, 2, 2, 2, 2, 2], 2, 56⟩,
  ⟨331, 3, [2, 3, 5, 11], 2, 1⟩,
  ⟨337, 10, [2, 2, 2, 2, 3, 7], 4, 3⟩,
  ⟨397, 5, [2, 2, 3, 3, 11], 4, 3⟩,
  ⟨431, 7, [2, 5, 43], 1, 2⟩,
  ⟨601, 7, [2, 2, 2, 3, 5, 5], 4, 1⟩,
  ⟨631, 3, [2, 3, 3, 5, 7], 4, 2⟩,
  ⟨641, 3, [2, 2, 2, 2, 2, 2, 2, 5], 1, 6⟩,
  ⟨673, 5, [2, 2, 2, 2, 2, 3, 7], 36, 2⟩,
  ⟨683, 5, [2, 11, 31], 1, 2⟩,
  ⟨881, 3, [2, 2, 2, 2, 5, 11], 2, 4⟩,
  ⟨1103, 5, [2, 19, 29], 1, 2⟩,
  ⟨1321, 13, [2, 2, 2, 3, 5, 11], 8, 2⟩,
  ⟨1613, 3, [2, 2, 13, 31], 3, 2⟩,
  ⟨1801, 11, [2, 2, 2, 3, 3, 5, 5], 2, 3⟩,
  ⟨2089, 7, [2, 2, 2, 3, 3, 29], 6, 1⟩,
  ⟨2113, 5, [2, 2, 2, 2, 2, 2, 3, 11], 4, 7⟩,
  ⟨2143, 3, [2, 3, 3, 7, 17], 4, 3⟩,
  ⟨2351, 13, [2, 5, 5, 47], 1, 6⟩,
  ⟨2731, 3, [2, 3, 5, 7, 13], 4, 2⟩,
  ⟨3191, 11, [2, 5, 11, 29], 4, 6⟩,
  ⟨4051, 10, [2, 3, 3, 3, 3, 5, 5], 6, 1⟩,
  ⟨4513, 7, [2, 2, 2, 2, 2, 3, 47], 4, 2⟩,
  ⟨5419, 3, [2, 3, 3, 7, 43], 4, 1⟩,
  ⟨6361, 19, [2, 2, 2, 3, 5, 53], 2, 1⟩,
  ⟨8191, 17, [2, 3, 3, 5, 7, 13], 54, 1⟩,
  ⟨9719, 17, [2, 43, 113], 8, 2⟩,
  ⟨11119, 3, [2, 3, 17, 109], 6, 4⟩,
  ⟨13367, 5, [2, 41, 163], 3, 8⟩,
  ⟨23311, 3, [2, 3, 3, 5, 7, 37], 6, 2⟩,
  ⟨32377, 5, [2, 2, 2, 3, 19, 71], 2, 3⟩,
  ⟨43691, 6, [2, 5, 17, 257], 1, 2⟩,
  ⟨61681, 29, [2, 2, 2, 2, 3, 5, 257], 8, 5⟩,
  ⟨65537, 3, [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], 2, 48⟩,
  ⟨69431, 13, [2, 5, 53, 131], 1, 2⟩,
  ⟨87211, 13, [2, 3, 3, 3, 5, 17, 19], 2, 3⟩,
  ⟨92737, 5, [2, 2, 2, 2, 2, 2, 3, 3, 7, 23], 6, 8⟩,
  ⟨121369, 7, [2, 2, 2, 3, 13, 389], 2, 4⟩,
  ⟨122921, 3, [2, 2, 2, 5, 7, 439], 9, 4⟩,
  ⟨131071, 3, [2, 3, 5, 17, 257], 50, 2⟩,
  ⟨174763, 17, [2, 3, 3, 7, 19, 73], 4, 10⟩,
  ⟨178481, 3, [2, 2, 2, 2, 5, 23, 97], 1, 6⟩,
  ⟨179951, 7, [2, 5, 5, 59, 61], 1, 2⟩,
  ⟨201961, 13, [2, 2, 2, 3, 3, 3, 5, 11, 17], 10, 6⟩,
  ⟨262657, 5, [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 19], 2, 1⟩,
  ⟨524287, 3, [2, 3, 3, 3, 7, 19, 73], 48, 1⟩,
  ⟨599479, 6, [2, 3, 11, 31, 293], 10, 4⟩,
  ⟨649657, 5, [2, 2, 2, 3, 3, 7, 1289], 6, 3⟩,
  ⟨1212847, 5, [2, 3, 19, 10639], 4, 1⟩,
  ⟨2099863, 3, [2, 3, 3, 43, 2713], 8, 2⟩,
  ⟨2796203, 5, [2, 23, 89, 683], 1, 6⟩,
  ⟨3033169, 7, [2, 2, 2, 2, 3, 29, 2179], 4, 4⟩,
  ⟨6700417, 5, [2, 2, 2, 2, 2, 2, 2, 3, 17449], 20, 7⟩,
  ⟨13264529, 3, [2, 2, 2, 2, 31, 47, 569], 1, 2⟩,
  ⟨15790321, 19, [2, 2, 2, 2, 3, 3, 5, 7, 13, 241], 16, 4⟩,
  ⟨20394401, 3, [2, 2, 2, 2, 2, 5, 5, 13, 37, 53], 2, 10⟩,
  ⟨164511353, 3, [2, 2, 2, 41, 59, 8501], 8, 4⟩,
  ⟨616318177, 5, [2, 2, 2, 2, 2, 3, 37, 167, 1039], 8, 3⟩,
  ⟨715827883, 5, [2, 3, 7, 11, 31, 151, 331], 16, 3⟩,
  ⟨2147483647, 7, [2, 3, 3, 7, 11, 31, 151, 331], 36, 1⟩,
  ⟨3203431780337, 3, [2, 2, 2, 2, 59, 421, 8060489], 8, 12⟩,
  ⟨4432676798593, 5, [2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 7, 43, 337, 5419], 40, 4⟩,
  ⟨2305843009213693951, 37, [2, 3, 3, 5, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321], 6, 4⟩]

private def primes := rows.map Row.seed
private def B := primes.prod

set_option maxRecDepth 12000 in
private theorem valid_rows : rows.all (fun r => valid r.seed r.generator r.factors)=true := by
  decide +kernel

private theorem primes_prime (q : ℕ) (mem : q∈primes) : q.Prime := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
  exact valid_prime (List.all_eq_true.mp valid_rows r hr)

private theorem candidates_seven {q : ℕ} (hq : q∈candidates 7) : q∈primes := by
  have fac : mersenneProduct 64 ∣ B^64 := by decide +kernel
  have div : q∣mersenneProduct 64 := Nat.dvd_of_mem_primeFactors hq
  have prime := Nat.prime_of_mem_primeFactors hq
  exact member_of_prime_dvd_prod prime primes primes_prime (prime.dvd_of_dvd_pow (div.trans fac))

private def good (r : Row) : Bool :=
  decide (0<r.firstEscape ∧ (firstKindTerm r.seed r.firstEscape).Coprime B ∧
    0<r.secondEscape ∧ (secondKindTerm r.seed r.secondEscape).Coprime B)

set_option maxRecDepth 12000 in
private theorem escape_rows : rows.all good=true := by decide +kernel

private theorem escape_candidates (b : Bool) (p : ℕ) (hp : p∈primes) :
    ∃ j : ℕ, 0<j ∧ (SquarefreeSeeds.term b p j).Coprime B := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
  have h := List.all_eq_true.mp escape_rows r hr
  simp only [good,decide_eq_true_eq] at h
  cases b
  · exact ⟨r.secondEscape,h.2.2⟩
  · exact ⟨r.firstEscape,h.1,h.2.1⟩

/-- No seven primes cover every positive site of either canonical
Cunningham recurrence at any prime seed. -/
theorem seven_do_not_cover (b : Bool) {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (pr : ∀ q∈S,q.Prime) (size : S.card≤7) : ¬Covers b p S := by
  intro cover
  obtain ⟨T,ts,sub,odd,ct⟩ := reduce_cover b hp.pos S pr size cover
  have mem := seed_mem_of_cover b hp T (fun q h => ⟨pr q (ts h),odd q h⟩) ct
  obtain ⟨j,pos,free⟩ := escape_candidates b p (candidates_seven (sub mem))
  obtain ⟨q,hq,hit⟩ := ct j pos
  exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨q,pr q (ts hq),hit,List.dvd_prod (candidates_seven (sub hq))⟩ free

/-- For at most seven odd primes, each block of 2^|S| sites contains a
term avoiding all of them. The starting site is arbitrary. -/
theorem seven_escape_every_block (b : Bool) {p : ℕ} (hp : p.Prime) (S : Finset ℕ)
    (prime : ∀ q∈S,q.Prime ∧ 2<q) (size : S.card≤7) (s : ℕ) :
    ∃ j<2^S.card, ∀ q∈S, ¬q∣SquarefreeSeeds.term b p (s+j) := by
  have miss := seven_do_not_cover b hp S (fun q h => (prime q h).1) size
  unfold Covers at miss
  push Not at miss
  obtain ⟨u,_,free⟩ := miss
  exact escape_every_block b hp.pos S prime free s

#print axioms seven_escape_every_block

#print axioms seven_do_not_cover

end CunninghamChain.OrbitCover.Certificate
