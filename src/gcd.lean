import data.nat.modeq
import recursions

lemma div_algo (a b: ℕ ): ∃ (q : ℕ) , a=b*q+(a%b) :=
begin
    have t1: b ∣ a-(a%b), apply nat.dvd_sub_mod,
    cases t1 with x y, use x, rw ← y, 
    apply int.coe_nat_inj, push_cast, rw int.coe_nat_sub (nat.mod_le a b), ring,
end

lemma fib_pos : ∀ m: ℕ, fib(m+1) >0:=
begin
    apply nat.two_step_induction,
    {simp},
    {simp},
    {intros, simp,linarith}
end

lemma luc_pos : ∀ m: ℕ, luc(m) >0:=
begin
    apply nat.two_step_induction,
    {simp},
    {simp},
    {intros, rw luc_add, linarith}
end

lemma gcd_add (a b c: ℕ  ) (h: a = b +c): nat.gcd a b = nat.gcd b c:=
begin
    cases nat.gcd_dvd b c,
    have h1: nat.gcd b c ∣ b + c, 
    {apply dvd_add, exact left, exact right}, 
    rw ← h at h1,
    have h2: nat.gcd b c ∣ nat.gcd a b,
    {rw nat.dvd_gcd_iff, split, exact h1, exact left},
    clear left, clear right,
    cases nat.gcd_dvd a b,
    have h3: (nat.gcd a b :ℤ ) ∣  (a - b :ℤ) ,
    {apply dvd_sub, norm_cast, exact left, norm_cast, exact right},
    nth_rewrite 1 h at h3, 
    have h4: nat.gcd a b ∣ nat.gcd b c,
    {rw nat.dvd_gcd_iff, split,
    {exact right},
    {simp at h3, norm_cast at h3, assumption}},
    apply nat.dvd_antisymm h4 h2,
end

lemma fib_coprime (m: ℕ ) : nat.gcd (fib(m+1)) (fib(m+2)) = 1:=
begin
    induction m with d hd,
    {ring},
    nth_rewrite 1 fib_add, rw  nat.gcd_comm, rw gcd_add, 
    {rw nat.gcd_comm, exact hd},
    {simp}
end

lemma fib_even (m : ℕ) : fib (3*m) %2 =0 ∧  fib (3*m +1) % 2 =1  ∧ fib (3*m+2)%2=1 :=
begin
    induction m with d hd,
    {simp, ring},
    {cases hd with h1 h2, cases h2 with h2 h3,
    have g1:fib (3*d+3)%2=0,
    {rw fib_add, rw nat.add_mod, simp * at *},
    have g2: fib(3*d+4)%2=1,
    {rw fib_add, rw nat.add_mod, rw g1, rw h3, ring},
    have g3: fib(3*d+5)%2=1,
    {rw fib_add, rw nat.add_mod, rw g2, rw g1, ring},
    repeat{rw nat.succ_eq_add_one}, ring, cc}
end 


lemma fib_luc_gcd_div_2 (m: ℕ ) : nat.gcd (fib(m+2)) (luc(m+2)) =nat.gcd (fib(m+2)) 2:=
begin
    have h1: nat.gcd (fib(m+2)) (luc(m+2)) =nat.gcd (fib(m+2)) (2 * fib(m+1)),
    {rw  fib_luc_rec, rw fib_add, rw nat.gcd_comm, rw gcd_add, simp, ring},
    rw h1, apply nat.coprime.gcd_mul_right_cancel_right, apply fib_coprime
end

lemma fib_luc_gcd (m: ℕ ) : nat.gcd (fib(3*m)) (luc(3*m)) = 2  :=
begin
    cases nat_case_bash m 0, interval_cases m, 
    {cases h with h h2, rw [show h+0+1 =h+1, from rfl] at h2, rw h2, rw mul_add, rw [show 3*1 = 1+2, by ring], rw fib_luc_gcd_div_2,
    rw [show 3*h+1+2 = 3*(h+1), by ring], 
    rw ← nat.gcd_eq_right_iff_dvd, rw nat.dvd_iff_mod_eq_zero,  simp[fib_even]},
    {ring},
end 

lemma fib_luc_gcd_2 (m : ℕ) (h: m%3 ≠ 0): nat.gcd (fib(m)) (luc(m))=1 :=
begin
    cases nat_case_bash m 1, interval_cases m, 
    {cases h_1 with u h1, rw h1, rw fib_luc_gcd_div_2, rw nat.gcd_comm, rw ← nat.coprime,  rw nat.prime.coprime_iff_not_dvd nat.prime_two,
    by_contra, 
    have h2 := nat.mod_eq_zero_of_dvd a, have h3:= nat.mod_lt m (show 3>0, by linarith), 
    have h4:= div_algo m 3, cases h4 with d h4, have h5:=fib_even d, interval_cases m%3, 
    {rw h_1 at h4, rw ← h1 at h2, rw h4 at h2, cc},
    {rw h_1 at h4, rw ← h1 at h2, rw h4 at h2, cc}},
    {simp at h, exfalso, exact h},
    {simp}
end