import linear_algebra
import utils

namespace linear_map

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E →ₗ[K] E)

def iterate (n : ℕ) : E →ₗ[K] E :=
{ to_fun := λ x, f^[n] x,
  map_add' := 
  begin
    induction n with n hn,
    { simp },
    { simp [hn] }
  end,
  map_smul' := 
  begin
    induction n with n hn,
    { simp },
    { simp [hn] }
  end }
-- try to simplify by grouping proofs

lemma iterate_succ_apply (n : ℕ) (x : E) : f.iterate (n+1) x = (f.iterate n (f x)) :=
  function.iterate_succ_apply f n x

lemma iterate_succ_apply' (n : ℕ) (x : E) : f.iterate (n+1) x = f (f.iterate n x) :=
  function.iterate_succ_apply' f n x

lemma iterate_add_apply (m n : ℕ) (x : E) : f.iterate (m+n) x = f.iterate m (f.iterate n x) :=
  function.iterate_add_apply f m n x

lemma iterate_add_apply' (m n : ℕ) (x : E) : f.iterate (m+n) x = f.iterate n (f.iterate m x) :=
  add_comm n m ▸ function.iterate_add_apply f n m x

lemma iterate_succ (n : ℕ) : f.iterate (n+1) = (f.iterate n).comp f :=
  ext (f.iterate_succ_apply n)

lemma iterate_succ' (n : ℕ) : f.iterate (n+1) = f.comp (f.iterate n) :=
  ext (f.iterate_succ_apply' n)

def ker_it (n : ℕ) := (f.iterate n).ker

lemma mem_ker_it_succ_iff (n : ℕ) (x : E) : x ∈ f.ker_it (n+1) ↔ f x ∈ f.ker_it n :=
by rw [ker_it, mem_ker, ker_it, mem_ker, iterate_succ_apply]

def range_it (n : ℕ) := (f.iterate n).range

lemma range_it_succ_eq' (n : ℕ) : f.range_it (n+1) = (f.range_it n).map f :=
by rw [range_it, range_it, range, range, iterate_succ', submodule.map_comp]

lemma range_it_succ_eq (n : ℕ) : f.range_it (n+1) = f.range.map (f.iterate n) :=
by rw [range_it, range, range, iterate_succ, submodule.map_comp]

lemma ker_it_mono : monotone f.ker_it :=
monotone_of_monotone_nat
begin
  intros n x hx,
  rw [ker_it, mem_ker] at ⊢ hx,
  simp [hx, iterate_succ_apply']
end

lemma range_it_antimono : ∀ ⦃x y⦄, x ≤ y → f.range_it y ≤ f.range_it x :=
antimono_of_antimono_nat (λ n x ⟨x', _, hx'⟩, ⟨f x', trivial, hx'⟩)

lemma q1_1 {m : ℕ} (hm : f.range_it (m+1) = f.range_it m) : ∀ p, f.range_it (m+p) = f.range_it m
| 0 := rfl
| (p+1) := le_antisymm (f.range_it_antimono $ le_add_right $ le_refl m)
  begin
    intros x hx,
    rwa [← hm, range_it_succ_eq', ← q1_1 p, ← range_it_succ_eq'] at hx
  end

lemma q1_2 {m : ℕ} (hm : f.ker_it (m+1) = f.ker_it m) : ∀ p, f.ker_it (m+p) = f.ker_it m
| 0 := rfl
| (p+1) := le_antisymm
  begin
    intros x hx,
    rwa [← add_assoc, mem_ker_it_succ_iff, q1_2 p, ← mem_ker_it_succ_iff, hm] at hx,
  end
  (f.ker_it_mono $ le_add_right $ le_refl m)

lemma q1_1' {m n : ℕ} (hm : f.range_it (m+1) = f.range_it m) (hmn : m ≤ n) : 
  f.range_it n = f.range_it m :=
begin
  convert f.q1_1 hm (n-m),
  rw nat.add_sub_cancel' hmn
end

lemma q1_2' {m n : ℕ} (hm : f.ker_it (m+1) = f.ker_it m) (hmn : m ≤ n) : 
  f.ker_it n = f.ker_it m :=
begin
  convert f.q1_2 hm (n-m),
  rw nat.add_sub_cancel' hmn
end

end linear_map