import order.directed

lemma antimono_of_antimono_nat {α : Type*} [preorder α] {f : ℕ → α} 
  (hf : ∀n, f (n + 1) ≤ f n) :
  ∀ ⦃x y⦄, x ≤ y → f y ≤ f x | n m h :=
begin
  induction h,
  { refl },
  { transitivity, exact hf _, assumption }
end

lemma directed_le_of_monotone {α ι : Type*} [preorder α] [linear_order ι] {f : ι → α} 
  (hf : monotone f) : directed (≤) f :=
λ i j, ⟨max i j, hf (le_max_left i j), hf (le_max_right i j)⟩