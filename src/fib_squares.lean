import luc_double_squares

lemma prod_pos (a b n: ℕ ) (h: n=a*b) (h2: 0<n) : 0<b:=
begin
    by_contra, push_neg at a_1, interval_cases b, rw mul_zero at h, rw h at h2, linarith
end

lemma product_ineq (a b n: ℕ ) (h: 2≤ a) (h3: 0 <n): n=a*b → b <n ∧ 0<b:=
begin
    intro h2, rw nat.succ_le_iff at h, rw h2, nth_rewrite_lhs 0 ← one_mul b,
    have h1:=prod_pos a b n h2 h3,
    have h2:= mul_lt_mul h (le_refl b) h1 (zero_le a), split, assumption'
end

lemma coprime_squares_factors (a b n: ℕ ) (h: a*b=n^2) (h1: nat.coprime a b) (h2: 0 <n): ∃ (r : ℕ), a=r^2:=
begin
    revert b, revert a, revert h2, apply nat.strong_induction_on n,
    {intros m hd h0 a b h h1, cases lt_or_le a 2,
    {interval_cases a, {use 0, ring}, {use 1, ring}},
    {cases nat.exists_prime_and_dvd h_1 with p h3, cases h3.2 with x h4,
    have h5: p ∣ a*b, {use x*b, rw h4,  rw mul_assoc}, rw h at h5,
    have h6:= nat.prime.dvd_of_dvd_pow h3.1 h5,  
    have h7:= nat.pow_dvd_pow_of_dvd h6 2, rw ← h at h7,
    have h9: ¬ p ∣ b, {by_contra, 
    have i1: 2 ≤  nat.gcd a b, {apply le_trans (nat.prime.two_le h3.1), apply nat.le_of_dvd (nat.gcd_pos_of_pos_left b (show 0<a, by linarith)), apply nat.dvd_gcd h3.2 a_1},
    have h1': nat.gcd a b=1, {exact h1}, rw h1' at i1, linarith},
    have h10: (p^2).coprime b, {apply nat.coprime.symm, exact nat.prime.coprime_pow_of_not_dvd h3.1 h9},
    have h11:= nat.coprime.dvd_of_dvd_mul_right h10 h7, cases h11 with y h11, cases h6 with z h6, rw h6 at h, rw h11 at h, rw nat.mul_pow at h,
    have h12: p^2>0, apply nat.pow_pos, apply gt_of_ge_of_gt (nat.prime.two_le h3.1) (show 2>0, by linarith), rw mul_assoc at h, rw nat.mul_right_inj h12 at h,
    have h13:= product_ineq p z (m) (nat.prime.two_le h3.1) h0 h6, rw h11 at h1,
    have h14:= hd z h13.1 h13.2 y b h (nat.coprime.coprime_mul_left h1), cases h14 with r h14, use p*r, rw h11, rw h14, rw nat.mul_pow}} 
end

lemma squares_factors ( a b n:ℕ) (h: a*b=n^2) (h1: 0<n) : ∃ (r s: ℕ ), a=(nat.gcd a b)*r^2 ∧ b = (nat.gcd a b)*s^2:=
begin
    cases nat.eq_zero_or_pos (nat.gcd a b) with g0 g0,
    {simp [nat.eq_zero_of_gcd_eq_zero_right g0] at *, rw nat.pow_two at h, rw eq_comm at h, rw nat.mul_eq_zero at h, rw (or_self (n=0)) at h, rw h at h1, linarith},
    {rcases nat.exists_coprime g0 with ⟨ x, y ,g3, g1, g2 ⟩, rw g1 at h, nth_rewrite 1 g2 at h,
    have g4: (nat.gcd a b)^2 ∣ n^2, {use x*y, rw ← h, ring},
    rw nat.pow_dvd_pow_iff (show 0<2, by linarith) at g4, cases g4 with s g4, rw mul_comm at h, rw ← mul_assoc at h, nth_rewrite 1 mul_assoc at h, nth_rewrite 2 mul_comm at h, 
    repeat {rw mul_assoc at h}, rw ← pow_two at h, rw ← mul_assoc at h, rw g4 at h,rw nat.mul_pow at h, repeat {rw nat.pow_eq_pow at h}, rw mul_comm at h,
    have g5:= mul_pos g0 g0, rw ← nat.pow_two at g5, rw nat.mul_right_inj g5 at h,
    have g6:= coprime_squares_factors y x s h g3.symm (prod_pos (nat.gcd a b) s n g4 h1), cases g6 with r g6, rw mul_comm at h,
    have g7:= coprime_squares_factors x y s h g3 (prod_pos (nat.gcd a b) s n g4 h1), cases g7 with s g7, rw g6 at g2, rw g7 at g1, rw mul_comm at g2, rw mul_comm at g1, use s, use r, cc}
end

theorem fib_squares (n k: ℕ ) (h: fib n =k^2) : n=0 ∨ n=1 ∨ n=2 ∨ n=12:=
begin
    cases res_mod_4' n with h0 h1', cases div_algo n 2 with  w h1, rw h0 at h1, rw add_zero at h1, swap,
    {cases div_algo n 4 with s h2',cases h1' with h1 h_1, 
    {cases nat_case_bash s 0 with g2 g3, swap, 
    {cases g3 with q g3, rw add_zero q at g3, cases decomp_pow_3 s (show s>0, by linarith) with r g4, rcases g4 with ⟨ u, g4, g5 ⟩, rw add_comm at h2',
    have g6:=double_not_zero_mod3 u g5, 
    have g7:=fun_gen_add 1 u n s q r (n%4) (luc(2*u)) (fib) h2' g3 g4 (mod_fib (2*1*u) g6), repeat{rw mul_one at g7},
    rw h at g7, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at g7, apply_fun (λ (a: zmod (luc(2*u))), (a- fib(n%4))) at g7,
    have H: (k^2 : zmod (luc(2*u))) = -fib(n%4), {simp at g7, exact g7},
    rw h1 at H, rw [show fib 1 =1, from rfl] at H, simp at H, 
    have g10:= non_res_3_mod_4 _ _ (luc_pos (2*u)) H, rw luc_mod_4 (2*u) g6 at g10, contradiction},
    {simp * at *}},

    {have h2: n=4*(s+1)-1, 
        {rw add_comm at h2', rw h2', rw h_1, rw mul_add, rw mul_one, rw nat.add_sub_assoc (show 1 ≤ 4, by linarith), rw add_comm},
    cases decomp_pow_3 (s+1) (show s+1>0, by linarith) with r g4, rcases g4 with ⟨ u, g4, g5 ⟩,
    have g6:=double_not_zero_mod3 u g5, 
    have g7:= fun_gen_add 1 u (4*u-1 + 2*2*(s+1)) (s+1) s r (4*u-1) (luc(2*u)) (fib) (show 4*u-1+2*2*(s+1) = 4*u-1+2*2*(s+1), from rfl) (show s+1=s+1, from rfl) g4 (mod_fib (2*u) g6),
    have g8:= mod_fib (2*u) g6 (4*(s+1)-1),
    have i1: 1 ≤ 2*(2*u), 
        {have h2: 1 ≤ u, {by_contra, push_neg at a, interval_cases u, linarith},
        ring, apply le_trans (show 1 ≤ 4*1, by linarith), linarith},
    have g9:= mod_fib_sub (2*u) (1) (g6.1) (g6.2) (i1), 
    rw (show (-1 :ℤ )^(1+1) = 1, by ring) at g9, rw one_mul at g9, norm_cast at g9, rw (show 2*(2*u)=4*u, by ring) at *,
    have g10: 4*(s+1)-1+4*u = 4*u -1+2*2*(s+1), {rw (show 2*2 =4, from rfl), rw add_sub_add _ _ _ (i1) (show 1 ≤ 4*(s+1), by linarith)}, rw g10 at g8,
    have g11:= nat.dvd_add g8 g9, rw add_assoc at g11, nth_rewrite 1 ← add_assoc at g11, nth_rewrite 4 add_comm at g11, repeat {rw ← add_assoc at g11}, rw add_assoc at g11, rw nat.dvd_add_right g7 at g11,
    rw h2 at h, rw h at g11, rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at g11, apply_fun (λ (a: zmod (luc(2*u))), (a- fib (1))) at g11,
    have H: (↑ k^2 : zmod (luc((2*u)))) = -fib(1), {simp at g11, simp, rw ← g11}, rw (show fib 1 =1, from rfl) at H, simp at H,
    have g12:= non_res_3_mod_4 _ _ (luc_pos(2*u)) H, rw luc_mod_4 (2*u) g6 at g12, contradiction}},

    {rw h1 at h, rw fib_2k w at h,cases nat_case_bash k 0, swap,
    {cases classical.em (w%3=0),
    {rw ← nat.dvd_iff_mod_eq_zero at h_2, cases h_2 with x h_2, rw h_2 at h, cases h_1 with s h_1, rw add_zero s at h_1, cases squares_factors _ _ _ h (show 0 <k, by linarith) with b h3, rcases h3 with ⟨ a, h3, h4⟩, rw fib_luc_gcd x at *,
    have h5:= luc_double_square (3*x) _ h4, rw h_2 at h1, cases h5 with h51 h52,
    {rw h51 at h1, rw mul_zero at h1, left, assumption},
    {rw h52 at h1, repeat{right}, rw h1, ring}},
    {cases h_1 with s h1', rw add_zero (s) at h1', cases squares_factors _ _ _ h (show 0 <k, by linarith) with b h3, rcases h3 with ⟨ a, h3, h4⟩, rw fib_luc_gcd_2 w h_2 at *, rw one_mul at h4,
    have h5:= luc_square w _ h4, cases h5 with h51 h52, 
    {rw h51 at h1, rw mul_one at h1, cc },
    {rw h52 at h_2, rw (show 3%3 =0, from rfl) at h_2, contradiction}}},
    {rw le_zero_iff_eq at h_1, rw h_1 at h, rw (show 0^2=0, from rfl) at h, rw nat.mul_eq_zero at h, cases h with hx hy,
    {cases nat_case_bash w 0, 
    {rw le_zero_iff_eq at h, rw h at h1, rw h1, simp},
    {cases h with k h, rw add_zero k at h, rw h at hx,
    have i1:= fib_pos k, linarith}},
    have i2:= luc_pos w, linarith}}
end