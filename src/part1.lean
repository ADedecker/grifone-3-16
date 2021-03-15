import linear_algebra
import utils

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E →ₗ[K] E)

def linear_map.iterate (n : ℕ) : E →ₗ[K] E :=
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

lemma linear_map.iterate_succ (n : ℕ) (x : E) : f.iterate (n+1) x = (f.iterate n (f x)) :=
  function.iterate_succ_apply f n x

lemma linear_map.iterate_succ' (n : ℕ) (x : E) : f.iterate (n+1) x = f (f.iterate n x) :=
  function.iterate_succ_apply' f n x

def linear_map.ker_it (n : ℕ) := (f.iterate n).ker

def linear_map.range_it (n : ℕ) := (f.iterate n).range

lemma ker_it_mono : monotone f.ker_it :=
monotone_of_monotone_nat
begin
  intros n x hx,
  rw [linear_map.ker_it, linear_map.mem_ker] at ⊢ hx,
  simp [hx, linear_map.iterate_succ']
end

lemma range_it_antimono : ∀ ⦃x y⦄, x ≤ y → f.range_it y ≤ f.range_it x :=
antimono_of_antimono_nat (λ n x ⟨x', _, hx'⟩, ⟨f x', trivial, hx'⟩)