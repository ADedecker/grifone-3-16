lemma antimono_of_antimono_nat {α : Type*} [preorder α] {f : ℕ → α} 
  (hf : ∀n, f (n + 1) ≤ f n) :
  ∀ ⦃x y⦄, x ≤ y → f y ≤ f x | n m h :=
begin
  induction h,
  { refl },
  { transitivity, exact hf _, assumption }
end