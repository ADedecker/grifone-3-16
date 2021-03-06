import part1

open_locale classical

namespace linear_map

variables {E K : Type*} [field K] [add_comm_group E] [vector_space K E] (f : E ââ[K] E)

local notation `k` := f.ker_it
local notation `j` := f.range_it
local notation `ð` := f.ker_it_supr
local notation `ð` := f.range_it_infi
local notation `r` := f.range_char
local notation `s` := f.ker_char

def range_it_infi := â¨ (n : â), j n

def ker_it_supr := â¨ (n : â), k n

def has_finite_range_char := â m, j (m+1) = j m

def has_finite_ker_char := â m, k (m+1) = k m

noncomputable def range_char := if h : f.has_finite_range_char then nat.find h else 0

noncomputable def ker_char := if h : f.has_finite_ker_char then nat.find h else 0

lemma range_char_spec (hf : f.has_finite_range_char) : 
  j (r + 1) = j r :=
begin
  simp only [range_char, hf, dif_pos],
  exact nat.find_spec hf
end

lemma ker_char_spec (hf : f.has_finite_ker_char) : 
  k (s + 1) = k s :=
begin
  simp only [ker_char, hf, dif_pos],
  exact nat.find_spec hf
end

lemma ker_it_supr_stable : â x â ð, f x â ð :=
begin
  intro x,
  simp [ker_it_supr, submodule.mem_supr_of_directed _ (directed_le_of_monotone f.ker_it_mono)],
  intros i hi,
  use i,
  rw [ker_it, mem_ker] at â¢ hi, 
  rw [â pow_succ_apply', pow_succ_apply, hi, f.map_zero]
end

lemma range_it_infi_stable : â x â ð, f x â ð :=
begin
  intro x,
  simp [range_it_infi, submodule.mem_infi],
  intros hx i,
  rcases hx i with â¨x', -, rflâ©,
  rw [â pow_succ_apply, pow_succ_apply'],
  exact mem_range_self _ _
end

section q2_1

variables (hr : has_finite_range_char f)

include hr

lemma range_it_infi_eq_range_it_range_char : ð = j r :=
le_antisymm (infi_le _ _)
begin
  intros x hx,
  refine (submodule.mem_infi _).mpr (Î» i, _),
  by_cases h : i â¤ r,
  { exact f.range_it_antimono h hx },
  { rwa f.q1_1' (f.range_char_spec hr) (le_of_not_le h) }
end

lemma q2_1_a : submodule.map f ð â¤ ð :=
begin
  rw [f.range_it_infi_eq_range_it_range_char hr, â range_it_succ_eq', f.range_char_spec hr],
  exact le_refl _
end

lemma q2_1_b : ð â k r = â¤ :=
begin
  rw eq_top_iff,
  rintro x -,
  rw submodule.mem_sup,
  obtain â¨x', -, hx'â© : (f^r) x â j (r + r),
  { convert (f^r).mem_range_self x using 1,
    exact f.q1_1 (f.range_char_spec hr) _ },
  rw f.pow_add_apply at hx',
  refine â¨(f^r) x', _, x - (f^r) x', _, by abelâ©,
  { rw f.range_it_infi_eq_range_it_range_char hr,
    exact (f^r).mem_range_self x' },
  { rw [ker_it, mem_ker, map_sub, hx', sub_self] }
end

end q2_1

section q2_2

variables (hs : has_finite_ker_char f)

include hs

lemma ker_it_supr_eq_ker_it_ker_char : ð = k s :=
le_antisymm
begin
  intros x hx,
  rw [ker_it_supr, submodule.mem_supr_of_directed _ (directed_le_of_monotone f.ker_it_mono)] at hx,
  rcases hx with â¨i, hxâ©,
  by_cases h : i â¤ s,
  { exact f.ker_it_mono h hx },
  { rwa â f.q1_2' (f.ker_char_spec hs) (le_of_not_le h) }
end
(le_supr _ _)

lemma q2_2_a : (f.restrict f.ker_it_supr_stable)^s = 0 :=
begin
  ext â¨x, hxâ©,
  rw pow_restrict_comm,
  rw f.ker_it_supr_eq_ker_it_ker_char hs at hx,
  exact hx
end

lemma q2_2_b : function.injective (f.restrict f.range_it_infi_stable) :=
begin
  rw [â ker_eq_bot, eq_bot_iff],
  rintros â¨x, hxâ©,-- hxf,
  rw [ker_restrict, submodule.mem_bot, submodule.mk_eq_zero],
  rintro (hxf : f x = 0),
  rw [range_it_infi, submodule.mem_infi] at hx,
  rcases hx s with â¨x', -, rflâ©,
  have : x' â k (s+1) := by rwa [â pow_succ_apply] at hxf,
  rwa f.ker_char_spec hs at this
end 

--lemma q2_2_b : function.injective (f.restrict f.range_it_infi_stable) :=
--suffices h : (f.restrict f.range_it_infi_stable).ker â¤ â¥,
--  by rwa [â ker_eq_bot, eq_bot_iff],
--assume â¨x, (hx : x â ð)â©,
--suffices h : f x = 0 â x = 0,
--  by rw [ker_restrict, submodule.mem_bot, submodule.mk_eq_zero]; exact h,
--assume (hfx : f x = 0),
--have hxâ : â i, x â j i,
--  by rwa [â submodule.mem_infi],
--have hxâ : x â j s,
--  from hxâ s,
--let â¨x', _, (hx' : (f^s) x' = x)â© := hxâ in
--have hx'â : (f^(s+1)) x' = 0,
--  by rwa [pow_succ_apply, hx'],
--have hx'â : x' â k s,
--  by rwa â f.ker_char_spec hs,
--show x = 0,
--  by rwa â hx'

lemma q2_2_c : j s â ð = â¥ :=
begin
  rw [eq_bot_iff, f.ker_it_supr_eq_ker_it_ker_char hs],
  rintros x â¨â¨x', -, rflâ©, hxâ©,
  have : x' â k (s+s),
  { rw [ker_it, mem_ker, pow_add_apply],
    exact hx },
  rw f.q1_2 (f.ker_char_spec hs) s at this,
  rwa [submodule.mem_bot]
end

--lemma q2_2_c : j s â ð = â¥ :=
--suffices h : j s â ð â¤ â¥,
--  by rwa eq_bot_iff,
--assume x â¨â¨x', _, (hx' : (f^s) x' = x)â© , (hx : x â ð)â©,
--suffices h : x = 0,
--  by rwa submodule.mem_bot,
--have hxâ : x â k s,
--  by rwa â f.ker_it_supr_eq_ker_it_ker_char hs,
--have hx'â : (f^s) x' â k s,
--  by rwa hx',
--have hx'â : x' â k (s+s),
--  by rw [ker_it, mem_ker, pow_add_apply]; exact hx'â,
--have hx'â : x' â k s,
--  by rwa â f.q1_2 (f.ker_char_spec hs) s,
--have hx'â : (f^s) x' = 0,
--  from hx'â,
--show x = 0, 
--  by rwa â hx'

end q2_2

end linear_map