import BooleanAntichainsKernel.MultigraphEnds
import Mathlib.Data.List.Nodup

namespace BooleanAntichainsKernel

universe u v
variable {α : Type u} {β : Type v}

/-- Walks use the actual vertex set and original edge identities. Loops
are allowed and parallel edges remain distinct constructors. -/
inductive LabelledGraphWalk (G : Graph α β) (F : Set β) :
    G.vertexSet → G.vertexSet → Type (max u v)
  | nil (x : G.vertexSet) : LabelledGraphWalk G F x x
  | cons {x y z : G.vertexSet} (e : G.edgeSet) (he : e.1 ∈ F)
      (h : G.IsLink e.1 x.1 y.1) (p : LabelledGraphWalk G F y z) : LabelledGraphWalk G F x z

namespace LabelledGraphWalk

variable {G : Graph α β} {F H : Set β} {x y z : G.vertexSet}

def edges {x y : G.vertexSet} : LabelledGraphWalk G F x y → List G.edgeSet
  | .nil _ => []
  | .cons e _ _ p => e :: p.edges

def support {x y : G.vertexSet} : LabelledGraphWalk G F x y → List G.vertexSet
  | .nil x => [x]
  | .cons _ _ _ p => x :: p.support

def length (p : LabelledGraphWalk G F x y) : ℕ := p.edges.length

/-- Edge labels as elements of the original ambient edge type. -/
def edgeLabels (p : LabelledGraphWalk G F x y) : List β := p.edges.map Subtype.val

def IsPath (p : LabelledGraphWalk G F x y) : Prop := p.support.Nodup

/-- A nonempty closed trail whose only repeated vertex is its endpoint.
In a multigraph this includes loops and two distinct parallel edges. -/
def IsCycle (p : LabelledGraphWalk G F x x) : Prop :=
  p.edges.Nodup ∧ p.edges ≠ [] ∧ p.support.tail.Nodup

@[simp] theorem edges_nil (x : G.vertexSet) : (nil x : LabelledGraphWalk G F x x).edges = [] := rfl
@[simp] theorem support_nil (x : G.vertexSet) : (nil x : LabelledGraphWalk G F x x).support = [x] := rfl
@[simp] theorem edges_cons (e : G.edgeSet) (he : e.1 ∈ F) (h : G.IsLink e.1 x.1 y.1)
    (p : LabelledGraphWalk G F y z) : (cons e he h p).edges = e :: p.edges := rfl
@[simp] theorem support_cons (e : G.edgeSet) (he : e.1 ∈ F) (h : G.IsLink e.1 x.1 y.1)
    (p : LabelledGraphWalk G F y z) : (cons e he h p).support = x :: p.support := rfl

theorem edgeLabels_nodup_iff (p : LabelledGraphWalk G F x y) :
    p.edgeLabels.Nodup ↔ p.edges.Nodup := List.nodup_map_iff Subtype.val_injective

theorem edges_mem (p : LabelledGraphWalk G F x y) : ∀ e ∈ p.edges, e.1 ∈ F := by
  induction p with
  | nil => simp
  | cons e he h p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact he
    · exact ih f hf

/-- Inclusion of edge sets changes only membership certificates. -/
def mono (hFH : F ⊆ H) {x y : G.vertexSet} : LabelledGraphWalk G F x y → LabelledGraphWalk G H x y
  | .nil x => .nil x
  | .cons e he h p => .cons e (hFH he) h (p.mono hFH)

@[simp] theorem edges_mono (hFH : F ⊆ H) (p : LabelledGraphWalk G F x y) :
    (p.mono hFH).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons e he h p ih => simp only [mono, edges, ih]

@[simp] theorem support_mono (hFH : F ⊆ H) (p : LabelledGraphWalk G F x y) :
    (p.mono hFH).support = p.support := by
  induction p with
  | nil => rfl
  | cons e he h p ih => simp only [mono, support, ih]

theorem isCycle_mono (hFH : F ⊆ H) (p : LabelledGraphWalk G F x x) :
    (p.mono hFH).IsCycle ↔ p.IsCycle := by simp only [IsCycle, edges_mono, support_mono]

def append {x y z : G.vertexSet} :
    LabelledGraphWalk G F x y → LabelledGraphWalk G F y z → LabelledGraphWalk G F x z
  | .nil _, q => q
  | .cons e he h p, q => .cons e he h (p.append q)

@[simp] theorem edges_append (p : LabelledGraphWalk G F x y) (q : LabelledGraphWalk G F y z) :
    (p.append q).edges = p.edges ++ q.edges := by
  induction p with
  | nil => rfl
  | cons e he h p ih => simp only [append, edges, List.cons_append, ih]

end LabelledGraphWalk

/-- The actual edge subsets containing no labelled multigraph cycle.
The ground condition does not admit ghost edges outside G.edgeSet. -/
def GraphEdgeForest (G : Graph α β) (F : Set β) : Prop :=
  F ⊆ G.edgeSet ∧ ∀ x (p : LabelledGraphWalk G F x x), ¬p.IsCycle

theorem GraphEdgeForest.mono {G : Graph α β} {F H : Set β}
    (hH : GraphEdgeForest G H) (hFH : F ⊆ H) : GraphEdgeForest G F := by
  refine ⟨hFH.trans hH.1, ?_⟩
  intro x p hp
  exact hH.2 x (p.mono hFH) ((p.isCycle_mono hFH).mpr hp)

theorem graphEdgeForest_empty (G : Graph α β) : GraphEdgeForest G ∅ := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro x p
  cases p with
  | nil => simp [LabelledGraphWalk.IsCycle]
  | cons e he h p => exact (Set.notMem_empty e.1 he).elim

end BooleanAntichainsKernel
