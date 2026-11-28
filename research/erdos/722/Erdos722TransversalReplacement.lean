import Erdos722LatinFibreLaws
import Erdos722BlockwiseFibreCoordinates

/-! # Replacing transversal blocks by arbitrary local completion laws -/

namespace Erdos722.LatinFillings
open Finset QuadCompletion FourPoint Function
open scoped Classical
noncomputable section

variable {I F : Type*} [DecidableEq I] [DecidableEq F]

/-- The four lifted points, including the proposed completion. -/
def packet (a b c d : I × F) : Finset (I × F) := {d,a,b,c}

abbrev Laws (S : Finset (Finset I)) (F : Type*) := (B : S) → BlockLaw B.val F

def packetTest {S : Finset (Finset I)} (L : Laws S F) (U : Finset (I × F)) (fallback : Prop) : Prop :=
  if h : U.image Prod.fst ∈ S then
    ∃ f, (L ⟨_,h⟩).accepts f ∧ ∀ v ∈ U, f v.1=v.2
  else fallback

def legal (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (a b c d : I × F) : Prop :=
  Q.complete a.1 b.1 c.1=d.1 ∧ packetTest L (packet a b c d) (P.complete a b c=d)

private theorem packet_proj (a b c d : I × F) :
    (packet a b c d).image Prod.fst=insert d.1 {a.1,b.1,c.1} := by simp [packet]

private theorem rule_reverse {V : Type*} (R : Rule V) (i j k z : V) :
    R.complete i j z=k ↔ R.complete i j k=z := by
  constructor <;> intro he <;> rw [← he,R.cancel]

omit [DecidableEq F] in
private theorem test_on {S : Finset (Finset I)} (L : Laws S F) (U : Finset (I × F)) (r : Prop)
    (B : S) (eq : U.image Prod.fst=B.val) : packetTest L U r ↔
      ∃ f, (L B).accepts f ∧ ∀ v ∈ U, f v.1=v.2 := by
  obtain ⟨B,hB⟩ := B
  change U.image Prod.fst=B at eq
  subst B
  rw [packetTest,dif_pos hB]

omit [DecidableEq F] in
private theorem test_off {S : Finset (Finset I)} (L : Laws S F) (U : Finset (I × F)) (r : Prop)
    (off : U.image Prod.fst ∉ S) : packetTest L U r ↔ r := by rw [packetTest,dif_neg off]

private theorem legal_symmetries (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)}
    (L : Laws S F) {a b c d : I × F} (h : legal Q P L a b c d) :
    legal Q P L b a c d ∧ legal Q P L a c b d ∧ legal Q P L a b d c := by
  have eq₁ : packet b a c d=packet a b c d := by ext; simp [packet,or_comm,or_left_comm]
  have eq₂ : packet a c b d=packet a b c d := by ext; simp [packet,or_comm,or_left_comm]
  have eq₃ : packet a b d c=packet a b c d := by ext; simp [packet,or_comm,or_left_comm]
  unfold legal at h ⊢
  rwa [eq₁,eq₂,eq₃,Q.swap₁ b.1 a.1 c.1,P.swap₁ b a c,Q.swap₂ a.1 c.1 b.1,P.swap₂ a c b,
    propext (rule_reverse P a b c d),propext (rule_reverse Q a.1 b.1 c.1 d.1),and_self,and_self]

private theorem pair_absent {S : Finset (Finset I)} (sizes : ∀ B∈S,B.card=4)
    (Q : Rule I) (a b : I) : baseQuad Q a a b ∉ S := by
  intro h
  have size := sizes _ h
  have pair := @card_le_two I _ b a
  have eq : baseQuad Q a a b={b,a} := by ext; simp [baseQuad,Q.repeated,or_comm]
  rw [eq] at size
  omega

private theorem distinct_triple {d a b c : I} (h : (insert d {a,b,c} : Finset I).card=4) :
    a≠b ∧ a≠c ∧ b≠c ∧ d∉({a,b,c}:Finset I) := by
  have size : ({a,b,c}:Finset I).card=3 := by
    have t := @card_le_three I _ a b c
    have u := card_insert_le d ({a,b,c}:Finset I)
    omega
  have ne (x y : I) (eq : ({a,b,c}:Finset I)={x,y}) : False := by
    have t := @card_le_two I _ x y
    rw [eq] at size
    omega
  refine ⟨fun eq => ne a c (by simp [eq]), fun eq => ne a b ?_,
    fun eq => ne a b (by simp [eq]),?_⟩
  · ext v
    simp [eq,or_comm]
  · intro inside
    rw [insert_eq_of_mem inside,size] at h
    contradiction

omit [DecidableEq F] in
private theorem matched_assignment (a b c : I × F) (ab : a.1≠b.1) (ac : a.1≠c.1) (bc : b.1≠c.1) :
    ∃ f : I → F, f a.1=a.2 ∧ f b.1=b.2 ∧ f c.1=c.2 := by
  refine ⟨fun i => if i=a.1 then a.2 else if i=b.1 then b.2 else c.2,?_⟩
  simp [ab.symm,ac.symm,bc.symm]

private theorem at_fourth {Q : Rule I} {P : Rule (I × F)} {S : Finset (Finset I)} (L : Laws S F)
    (a b c : I × F) (m : baseQuad Q a.1 b.1 c.1 ∈ S)
    (out : Q.complete a.1 b.1 c.1 ∉ ({a.1,b.1,c.1} : Finset I)) (f : I → F)
    (fa : f a.1=a.2) (fb : f b.1=b.2) (fc : f c.1=c.2) (y : F) :
    legal Q P L a b c (Q.complete a.1 b.1 c.1,y) ↔
      (L ⟨_,m⟩).accepts (update f (Q.complete a.1 b.1 c.1) y) := by
  let d := Q.complete a.1 b.1 c.1
  have eq : (packet a b c (d,y)).image Prod.fst=baseQuad Q a.1 b.1 c.1 := packet_proj ..
  have avoid : d≠a.1 ∧ d≠b.1 ∧ d≠c.1 := by simpa [d] using out
  change (_ = _ ∧ packetTest L (packet a b c (d,y)) _) ↔ (L ⟨_,m⟩).accepts (update f d y)
  rw [test_on L _ _ ⟨_,m⟩ eq]
  simp only [true_and]
  constructor
  · rintro ⟨g,hg,matchG⟩
    apply (L ⟨_,m⟩).localize _ hg
    intro i hi
    change i∈insert d {a.1,b.1,c.1} at hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · rw [update_self]
      exact matchG (d,y) (by simp [packet])
    · simpa [update,avoid.1.symm,fa] using matchG a (by simp [packet])
    · simpa [update,avoid.2.1.symm,fb] using matchG b (by simp [packet])
    · simpa [update,avoid.2.2.symm,fc] using matchG c (by simp [packet])
  · intro hg
    refine ⟨_,hg,?_⟩
    intro v hv
    simp only [packet,mem_insert,mem_singleton] at hv
    rcases hv with rfl|rfl|rfl|rfl <;> simp [update,avoid.1.symm,avoid.2.1.symm,avoid.2.2.symm,fa,fb,fc,d] at *

/-- The matching on the repeated fibres supplies the fallback. A transversal
on a selected base block supplies its own completion in each of four directions. -/
theorem unique_legal (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (sizes : ∀ B∈S,B.card=4) (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (a b c : I × F) : ∃! d, legal Q P L a b c d := by
  let z := Q.complete a.1 b.1 c.1
  by_cases m : baseQuad Q a.1 b.1 c.1 ∈ S
  · obtain ⟨ab,ac,bc,out⟩ := distinct_triple (sizes _ m)
    obtain ⟨f,fa,fb,fc⟩ := matched_assignment a b c ab ac bc
    obtain ⟨y,hy,uniq⟩ := (L ⟨_,m⟩).complete z (by simp [baseQuad,z]) f
    have eq := at_fourth (P:=P) L a b c m out f fa fb fc
    refine ⟨(z,y),(eq y).mpr hy,?_⟩
    rintro ⟨i,x⟩ hx
    have ei : z=i := hx.1
    subst i
    exact Prod.ext rfl (uniq x ((eq x).mp hx))
  · have eq (d : I × F) (hd : d.1=z) : legal Q P L a b c d ↔ P.complete a b c=d := by
      have setEq : (packet a b c d).image Prod.fst=baseQuad Q a.1 b.1 c.1 := by rw [packet_proj,hd]; rfl
      unfold legal
      rw [test_off L _ _ (fun h => m (setEq ▸ h)),hd]
      simp [z]
    have ep := proj a b c
    exact ⟨P.complete a b c,(eq _ ep).mpr rfl,fun d hd => ((eq d hd.1.symm).mp hd).symm⟩

private theorem legal_fallback (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (a b c : I × F) (proj : (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (off : baseQuad Q a.1 b.1 c.1 ∉ S) : legal Q P L a b c (P.complete a b c) := by
  refine ⟨proj.symm,?_⟩
  have h : (packet a b c (P.complete a b c)).image Prod.fst ∉ S := by
    rwa [packet_proj,proj]
  exact (test_off L _ _ h).mpr rfl

/-- Independent replacement on any collection of base blocks preserves the entire quadruple rule. -/
def patch (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (sizes : ∀ B∈S,B.card=4) (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1) :
    Rule (I × F) := by
  let existsOne := unique_legal Q P L sizes proj
  let pick (a b c) := (existsOne a b c).choose
  have hg (a b c) : legal Q P L a b c (pick a b c) := (existsOne a b c).choose_spec.1
  have only (a b c d) (hd : legal Q P L a b c d) : pick a b c=d :=
    (existsOne a b c).unique (hg ..) hd
  refine ⟨pick,fun a b c => (only b a c _ (legal_symmetries Q P L (hg a b c)).1).symm,
    fun a b c => (only a c b _ (legal_symmetries Q P L (hg a b c)).2.1).symm,?_,
    fun a b c => only a b _ _ (legal_symmetries Q P L (hg a b c)).2.2⟩
  intro a b
  have h := legal_fallback Q P L a a b (proj ..) (pair_absent sizes Q a.1 b.1)
  exact (only _ _ _ _ h).trans (P.repeated a b)

theorem patch_iff (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (sizes : ∀ B∈S,B.card=4) (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (a b c d : I × F) :
    (patch Q P L sizes proj).complete a b c=d ↔ legal Q P L a b c d := by
  let h := unique_legal Q P L sizes proj a b c
  exact ⟨fun eq => eq ▸ h.choose_spec.1,fun hd => h.unique h.choose_spec.1 hd⟩

theorem patch_outside (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (sizes : ∀ B∈S,B.card=4) (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (a b c : I × F) (off : baseQuad Q a.1 b.1 c.1 ∉ S) :
    (patch Q P L sizes proj).complete a b c=P.complete a b c :=
  (patch_iff ..).mpr (legal_fallback Q P L a b c (proj ..) off)

theorem patch_graph (Q : Rule I) (P : Rule (I × F)) {S : Finset (Finset I)} (L : Laws S F)
    (sizes : ∀ B∈S,B.card=4) (proj : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (i j k : I) (m : baseQuad Q i j k ∈ S) (f : I → F) :
    (patch Q P L sizes proj).complete (i,f i) (j,f j) (k,f k)=(Q.complete i j k,f (Q.complete i j k)) ↔
    (L ⟨_,m⟩).accepts f := by
  have out := (distinct_triple (sizes _ m)).2.2.2
  rw [patch_iff,at_fourth L _ _ _ m out f rfl rfl rfl,update_eq_self]

theorem patch_compatible [Fintype I] (Q : Rule I) (M : Matching I) (P : Rule (I × Fibre))
    (hp : Compatible Q M P) {S : Finset (Finset I)} (L : Laws S Fibre) (sizes : ∀ B∈S,B.card=4) :
    Compatible Q M (patch Q P L sizes hp.project) where
  project a b c := ((patch_iff Q P L sizes hp.project a b c _).mp rfl).1.symm
  pair i j x y z := (patch_outside Q P L sizes hp.project (i,x) (i,y) (j,z) (pair_absent sizes Q i j)).trans
    (hp.pair ..)

/-- Apply an independently chosen permutation to the symbols of every fibre. -/
def movePoint (e : I → Equiv.Perm F) (a : I × F) : I × F := (a.1,e a.1 a.2)

/-- Transport of the local predicates and of the fallback triples suffices for
transport of the patched ternary rule. -/
theorem patch_transport (Q : Rule I) (P T : Rule (I × F)) {S : Finset (Finset I)}
    (L J : Laws S F) (sizes : ∀ B∈S,B.card=4)
    (hp : ∀ a b c, (P.complete a b c).1=Q.complete a.1 b.1 c.1)
    (ht : ∀ a b c, (T.complete a b c).1=Q.complete a.1 b.1 c.1) (e : I → Equiv.Perm F)
    (localMap : ∀ B f, (L B).accepts f → (J B).accepts (fun i => e i (f i)))
    (fallback : ∀ a b c : I × F, baseQuad Q a.1 b.1 c.1 ∉ S →
      movePoint e (P.complete a b c) = T.complete (movePoint e a) (movePoint e b) (movePoint e c))
    (a b c : I × F) :
    movePoint e ((patch Q P L sizes hp).complete a b c) =
      (patch Q T J sizes ht).complete (movePoint e a) (movePoint e b) (movePoint e c) := by
  let w := (patch Q P L sizes hp).complete a b c
  have src : legal Q P L a b c w := (patch_iff Q P L sizes hp ..).mp rfl
  let B := baseQuad Q a.1 b.1 c.1
  have eq : (packet a b c w).image Prod.fst=B := by rw [packet_proj,← src.1]; rfl
  have eq' : (packet (movePoint e a) (movePoint e b) (movePoint e c) (movePoint e w)).image Prod.fst=B := by
    rw [packet_proj]
    change insert w.1 {a.1,b.1,c.1}=_
    rw [← src.1]; rfl
  apply Eq.symm
  apply (patch_iff ..).mpr
  refine ⟨src.1,?_⟩
  by_cases m : B∈S
  · obtain ⟨f,hf,mem⟩ := (test_on L _ _ ⟨B,m⟩ eq).mp src.2
    apply (test_on J _ _ ⟨B,m⟩ eq').mpr
    refine ⟨_,localMap _ _ hf,?_⟩
    intro u hu
    simp only [packet,mem_insert,mem_singleton] at hu
    have point (v : I × F) (hv : v∈packet a b c w) :
        e (movePoint e v).1 (f (movePoint e v).1)=(movePoint e v).2 := congrArg (e v.1) (mem v hv)
    rcases hu with rfl|rfl|rfl|rfl
    · exact point w (by simp [packet])
    · exact point a (by simp [packet])
    · exact point b (by simp [packet])
    · exact point c (by simp [packet])
  · have orig := (test_off L _ _ (fun h => m (eq ▸ h))).mp src.2
    apply (test_off J _ _ (fun h => m (eq' ▸ h))).mpr
    exact (fallback a b c m).symm.trans (congrArg (movePoint e) orig)

#print axioms movePoint
#print axioms patch_transport

#print axioms patch
#print axioms patch_iff
#print axioms patch_outside
#print axioms patch_graph
#print axioms patch_compatible

#print axioms packet
#print axioms Laws
#print axioms packetTest
#print axioms legal
#print axioms unique_legal
end
end Erdos722.LatinFillings
