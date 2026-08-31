import BooleanAntichainsKernel.UniformAllFormula

namespace BooleanAntichainsKernel

open Finset

/-- A constructive decision procedure for the literal arithmetic constraints. -/
instance uniformProfileValidDecidable (n r k b : ℕ) (p : Fin k → ℕ) :
    Decidable (UniformProfileValid n r k b p) := by
  unfold UniformProfileValid
  infer_instance

def uniformProfileTerm (n k b : ℕ) (p : Fin k → ℕ) : ℕ :=
  (n - b).factorial / ((n - b - ∑ i, p i).factorial * ∏ i, (p i).factorial)

abbrev BoundedUniformProfile (n r k b : ℕ) :=
  {q : Fin k → Fin (n + 1) // UniformProfileValid n r k b (fun i ↦ (q i).1)}

instance (n r k b : ℕ) : Fintype (BoundedUniformProfile n r k b) := Subtype.fintype _

/-- Exact conversion of the paper's natural profiles to bounded codes. -/
def uniformProfileEquivBounded (n r k b : ℕ) :
    UniformAdmissibleProfile n r k b ≃ BoundedUniformProfile n r k b where
  toFun p := ⟨uniformProfileBoundedCode p, p.2⟩
  invFun q := ⟨fun i ↦ (q.1 i).1, q.2⟩
  left_inv _ := Subtype.ext (funext fun _ ↦ rfl)
  right_inv _ := Subtype.ext (funext fun _ ↦ Fin.ext rfl)

def uniformBoundedProfileSum (n r k b : ℕ) : ℕ :=
  ∑ q : Fin k → Fin (n + 1),
    if UniformProfileValid n r k b (fun i ↦ (q i).1) then
      uniformProfileTerm n k b (fun i ↦ (q i).1) else 0

def uniformBoundedEnumerator (n r k : ℕ) : ℕ :=
  (∑ b ∈ Finset.range r, n.choose b * uniformBoundedProfileSum n r k b) / k.factorial

theorem uniformAdmissibleProfile_sum_eq_bounded (n r k b : ℕ) :
    (∑ p : UniformAdmissibleProfile n r k b, uniformProfileTerm n k b p.1) =
      uniformBoundedProfileSum n r k b := by
  calc
    _ = ∑ q : BoundedUniformProfile n r k b,
        uniformProfileTerm n k b (fun i ↦ (q.1 i).1) :=
      Fintype.sum_equiv (uniformProfileEquivBounded n r k b) _ _ (fun _ ↦ rfl)
    _ = ∑ q ∈ (Finset.univ : Finset (Fin k → Fin (n + 1))).filter
        (fun q ↦ UniformProfileValid n r k b (fun i ↦ (q i).1)),
        uniformProfileTerm n k b (fun i ↦ (q i).1) :=
      (Finset.sum_subtype
        (p := fun q : Fin k → Fin (n + 1) ↦ UniformProfileValid n r k b (fun i ↦ (q i).1))
        (F := (inferInstance : Fintype (BoundedUniformProfile n r k b)))
        ((Finset.univ : Finset (Fin k → Fin (n + 1))).filter
          (fun q ↦ UniformProfileValid n r k b (fun i ↦ (q i).1)))
        (fun _ ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
        (fun q ↦ uniformProfileTerm n k b (fun i ↦ (q i).1))).symm
    _ = uniformBoundedProfileSum n r k b := by
      simp only [uniformBoundedProfileSum, Finset.sum_filter]

/-- Numerical evaluation consumes a proved transport of the exact full
formula. It does not replay the external Python examples. -/
theorem uniform_count_eq_bounded (n r k : ℕ) (hr : r ≤ n) (hk : 2 ≤ k) :
    Fintype.card (BooleanAntichain k (MatroidFlat (uniformOn (Set.univ : Set (Fin n)) r))) =
      uniformBoundedEnumerator n r k := by
  rw [uniform_all_size_formula n r k hr hk]
  unfold uniformBoundedEnumerator
  apply congrArg (fun z : ℕ ↦ z / k.factorial)
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (fun z : ℕ ↦ n.choose b * z)
  exact uniformAdmissibleProfile_sum_eq_bounded n r k b

end BooleanAntichainsKernel
