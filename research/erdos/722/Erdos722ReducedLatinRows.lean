import Erdos722LatinCubeNormalization

/-! # An exhaustive row extension test for reduced Latin cubes -/

namespace Erdos722.LatinFillings
open List

/-- A row uses two bits per entry, starting at the low end. -/
def rowCode (f : Symbol → Symbol) : ℕ := (f 0).val+4*(f 1).val+16*(f 2).val+64*(f 3).val

def entry (u : ℕ) (k : Symbol) : Symbol := ⟨u / 4^k.val % 4, Nat.mod_lt _ (by decide)⟩

theorem entry_code (f : Symbol → Symbol) (k : Symbol) : entry (rowCode f) k=f k := by
  have a := (f 0).isLt
  have b := (f 1).isLt
  have c := (f 2).isLt
  have d := (f 3).isLt
  fin_cases k <;> apply Fin.ext <;> simp [entry,rowCode] <;> omega

/-- The packed words for the 24 permutations of the four symbols. -/
def latinRows : List ℕ :=
  [228,180,216,120,156,108,225,177,201,57,141,45,210,114,198,54,78,30,147,99,135,39,75,27]

theorem code_mem {f : Symbol → Symbol} (hf : Function.Injective f) : rowCode f ∈ latinRows := by
  have cert : ∀ a b c d : Symbol, a≠b → a≠c → a≠d → b≠c → b≠d → c≠d →
      a.val+4*b.val+16*c.val+64*d.val ∈ latinRows := by decide +kernel
  exact cert _ _ _ _ (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide))
    (hf.ne (by decide)) (hf.ne (by decide)) (hf.ne (by decide))

/-- Fold the two bits of each nonzero coordinate difference into its low bit. -/
def apart (u v : ℕ) := (((u ^^^ v) ||| ((u ^^^ v) >>> 1)) &&& 85) == 85

theorem apart_iff (u : ℕ) (hu : u∈latinRows) (v : ℕ) (hv : v∈latinRows) :
    apart u v = true ↔ ∀ k, entry u k ≠ entry v k := by
  have cert : ∀ x∈latinRows, ∀ y∈latinRows, apart x y = true ↔ ∀ k, entry x k ≠ entry y k := by
    decide +kernel
  exact cert _ hu _ hv

/-- The rows are ordered by the first coordinate and then by the second. -/
def layer (l : ℕ) : Symbol := ⟨(l/4)%4, Nat.mod_lt _ (by decide)⟩
def column (l : ℕ) : Symbol := ⟨l%4, Nat.mod_lt _ (by decide)⟩
def packed (q : Table) (l : ℕ) := rowCode (q (layer l) (column l))
def prefixRows (q : Table) (n : ℕ) := (List.range n).map (packed q)

theorem prefix_at (q : Table) {n l : ℕ} (h : l<n) :
    (prefixRows q n)[l]?.getD 0 = packed q l := by
  simp [prefixRows,h]

def decodeRows (s : List ℕ) : Table := fun i j k => entry (s[4*i.val+j.val]?.getD 0) k

theorem decode_prefix (q : Table) : decodeRows (prefixRows q 16)=q := by
  funext i j k
  have ij : 4*i.val+j.val<16 := by have := i.isLt; have := j.isLt; omega
  have li : layer (4*i.val+j.val)=i := by
    apply Fin.ext
    change (4*i.val+j.val)/4%4=i.val
    have := i.isLt; have := j.isLt; omega
  have cj : column (4*i.val+j.val)=j := by
    apply Fin.ext
    change (4*i.val+j.val)%4=j.val
    have := j.isLt; omega
  simp only [decodeRows,prefix_at q ij,packed,li,cj,entry_code]

/-- Test the three normalized axes and compare only rows sharing a layer or column. -/
def canAppend (n : ℕ) (s : List ℕ) (u : ℕ) : Bool :=
  (n != 0 || u == 228) &&
  (n / 4 != 0 || u % 4 == n % 4) &&
  (n % 4 != 0 || u % 4 == n / 4) &&
  (List.range n).all (fun l => !(l / 4 == n / 4 || l % 4 == n % 4) || apart (s[l]?.getD 0) u)

def extensions (n : ℕ) (s : List ℕ) :=
  (latinRows.filter (canAppend n s)).map (fun u => s++[u])

def pool : ℕ → List (List ℕ)
  | 0 => [[]]
  | n+1 => (pool n).flatMap (extensions n)

private theorem append_complete (q : Reduced) {n : ℕ} (hn : n<16) :
    canAppend n (prefixRows q.val.val n) (packed q.val.val n)=true := by
  let f := q.val.val
  have norm : Normal f := q.prop
  have latin : Latin f := q.val.prop
  have lr (l : ℕ) (hl : l<16) : (layer l).val = l/4 := by change l/4%4=l/4; omega
  have digit (l : ℕ) : packed f l % 4 = (f (layer l) (column l) 0).val := by
    have h := congrArg Fin.val (entry_code (f (layer l) (column l)) 0)
    simpa [entry,packed] using h
  change canAppend n (prefixRows f n) (packed f n)=true
  unfold canAppend
  simp only [Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,beq_iff_eq,List.all_eq_true,
    List.mem_range,Bool.not_eq_true',Bool.or_eq_false_iff]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · by_cases h : n=0
    · subst n
      right
      change rowCode (f 0 0)=228
      have eq : f 0 0=id := funext fun k => (norm k).2.2
      rw [eq]; decide
    · exact Or.inl h
  · by_cases h : n/4=0
    · right
      have z : layer n=0 := Fin.ext ((lr n hn).trans h)
      rw [digit,z,(norm (column n)).2.1]
      rfl
    · exact Or.inl h
  · by_cases h : n%4=0
    · right
      have z : column n=0 := Fin.ext h
      rw [digit,z,(norm (layer n)).1,lr _ hn]
    · exact Or.inl h
  · intro l hl
    by_cases same : l/4=n/4 ∨ l%4=n%4
    · right
      rw [prefix_at f hl]
      apply (apart_iff _ (code_mem (latin.2.2 ..)) _ (code_mem (latin.2.2 ..))).mpr
      intro k
      simp only [entry_code]
      rcases same with h|h
      · have e : layer l=layer n := Fin.ext (by simp [layer,h])
        have ne : column l≠column n := by
          intro he
          have j := congrArg Fin.val he
          change l%4=n%4 at j
          omega
        rw [e]
        exact (latin.2.1 _ _).ne ne
      · have e : column l=column n := Fin.ext h
        have ne : layer l≠layer n := by
          intro he
          have i := congrArg Fin.val he
          rw [lr l (by omega),lr n hn] at i
          omega
        rw [e]
        exact (latin.1 _ _).ne ne
    · left
      simpa using not_or.mp same

theorem prefix_mem_pool (q : Reduced) {n : ℕ} (hn : n≤16) : prefixRows q.val.val n ∈ pool n := by
  induction n with
  | zero => simp [prefixRows,pool]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨_,ih (by omega),?_⟩
    apply List.mem_map.mpr
    exact ⟨_,List.mem_filter.mpr ⟨code_mem (q.val.prop.2.2 ..),append_complete q (by omega)⟩,
      by simp [prefixRows,List.range_succ,packed]⟩

#print axioms rowCode
#print axioms entry
#print axioms entry_code
#print axioms latinRows
#print axioms code_mem
#print axioms apart
#print axioms apart_iff
#print axioms layer
#print axioms column
#print axioms packed
#print axioms prefixRows
#print axioms prefix_at
#print axioms decodeRows
#print axioms decode_prefix
#print axioms canAppend
#print axioms extensions
#print axioms pool
#print axioms prefix_mem_pool

end Erdos722.LatinFillings
