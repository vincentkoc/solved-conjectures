import Erdos722QuartetCovers
import Erdos722QuartetDirections

/-!
# Orthogonal arrays with all constant rows

Two specified symbols in distinct columns determine exactly one row.
Arrays containing the constant rows can be composed along the blocks
of a pairwise balanced design.
-/

namespace Erdos722.PairDesign
open Erdos722.Quartet

structure DiagonalArray (I V : Type*) where
  rows : Set (I → V)
  diagonal : ∀ x, (fun _ => x) ∈ rows
  through : ∀ i j : I, i ≠ j → ∀ x y : V,
    ∃! f, f ∈ rows ∧ f i=x ∧ f j=y

namespace DiagonalArray
variable {I V W : Type*}

theorem equal_entries {A : DiagonalArray I V} {i j : I} (hij : i≠j)
    {f : I → V} (hf : f∈A.rows) (h : f i=f j) : f=fun _ => f i :=
  (A.through i j hij (f i) (f i)).unique ⟨hf,rfl,h.symm⟩ ⟨A.diagonal _,rfl,rfl⟩

def relabel (A : DiagonalArray I V) (e : V ≃ W) : DiagonalArray I W where
  rows := {f | (fun i => e.symm (f i))∈A.rows}
  diagonal x := A.diagonal (e.symm x)
  through i j hij x y := by
    obtain ⟨f,⟨hf,hi,hj⟩,hu⟩ := A.through i j hij (e.symm x) (e.symm y)
    refine ⟨fun i => e (f i),⟨?_,by simp [hi],by simp [hj]⟩,?_⟩
    · change (fun i => e.symm (e (f i)))∈A.rows
      simpa using hf
    · rintro g ⟨hg,hgi,hgj⟩
      have he := hu (fun i => e.symm (g i)) ⟨hg,congrArg e.symm hgi,congrArg e.symm hgj⟩
      exact funext fun l => e.symm.injective (by simpa using congrFun he l)

/-- An array on the alphabet of a finite ring with unit-difference directions. -/
noncomputable def ofDirections {k t : ℕ} (D : Directions k t) : DiagonalArray (Fin k) D.K where
  rows := Set.range (fun p : D.K × D.K => fun i => p.1*D.c i+p.2)
  diagonal x := ⟨(0,x),by funext; simp⟩
  through i j hij x y := by
    obtain ⟨u,hu⟩ := D.units i j hij
    obtain ⟨m,hm,unique⟩ := u.mulRight.bijective.existsUnique (x-y)
    change m*(u : D.K)=x-y at hm
    rw [hu,mul_sub] at hm
    let b := x-m*D.c i
    refine ⟨fun l => m*D.c l+b,⟨⟨(m,b),rfl⟩,by dsimp [b]; abel,by dsimp [b]; linear_combination -hm⟩,?_⟩
    rintro _ ⟨⟨⟨a,d⟩,rfl⟩,hi,hj⟩
    change a*D.c i+d=x at hi
    change a*D.c j+d=y at hj
    have ha := unique a (by change a*(u:D.K)=x-y; rw [hu,mul_sub]; linear_combination hi-hj)
    subst a
    have hd : d=b := by dsimp [b]; linear_combination hi
    subst d
    rfl

/-- Compose arrays by identifying the diagonal rows along the blocks. -/
noncomputable def glue {S : ℕ → Prop} (C : Cover V (AllPairs V) S)
    (A : (b : {B // B∈C.blocks}) → DiagonalArray I b.val) : DiagonalArray I V := by
  let emb (b : {B // B∈C.blocks}) (f : I → b.val) := fun i => (f i : V)
  let rows : Set (I → V) := {f | (∃ x, f=fun _ => x) ∨
    ∃ b, ∃ g∈(A b).rows, f=emb b g}
  refine ⟨rows,fun x => Or.inl ⟨x,rfl⟩,?_⟩
  intro i j hij x y
  by_cases hxy : x=y
  · subst y
    refine ⟨fun _ => x,⟨Or.inl ⟨x,rfl⟩,rfl,rfl⟩,?_⟩
    rintro f ⟨hf,hi,hj⟩
    rcases hf with ⟨z,rfl⟩ | ⟨b,g,hg,rfl⟩
    · exact funext fun _ => hi
    · have he : g i=g j := Subtype.ext (hi.trans hj.symm)
      have h := equal_entries hij hg he
      exact funext fun l => (congrArg Subtype.val (congrFun h l)).trans hi
  · obtain ⟨B,⟨hB,hx,hy⟩,hu⟩ := C.through x y hxy trivial
    let b : {B // B∈C.blocks} := ⟨B,hB⟩
    obtain ⟨g,⟨hg,hgi,hgj⟩,huniq⟩ := (A b).through i j hij ⟨x,hx⟩ ⟨y,hy⟩
    refine ⟨emb b g,⟨Or.inr ⟨b,g,hg,rfl⟩,congrArg Subtype.val hgi,congrArg Subtype.val hgj⟩,?_⟩
    rintro f ⟨hf,hi,hj⟩
    rcases hf with ⟨z,rfl⟩ | ⟨b',v,hv,rfl⟩
    · exact (hxy (hi.symm.trans hj)).elim
    · have hb' : b'=b := Subtype.ext (hu _ ⟨b'.property,hi ▸ (v i).property,hj ▸ (v j).property⟩)
      subst b'
      exact congrArg (emb b) (huniq v ⟨hv,Subtype.ext hi,Subtype.ext hj⟩)

end DiagonalArray
end Erdos722.PairDesign

#print axioms Erdos722.PairDesign.DiagonalArray.ofDirections
#print axioms Erdos722.PairDesign.DiagonalArray.glue
