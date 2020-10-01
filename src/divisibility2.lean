import divisibility1
import data.nat.prime
import data.int.gcd
import data.nat.modeq
import data.int.modeq
import data.zmod.basic

lemma int_dvd_cancel ( a b c: ℤ ) (h: int.gcd a b =1): a ∣ b*c → a ∣ c:=
begin
    intro h1, rw ← int.nat_abs_dvd_abs_iff at *, rw int.nat_abs_mul at h1, apply nat.coprime.dvd_of_dvd_mul_left, apply h, assumption,
end

lemma luc_cancel_2 (k: ℕ ) (b: ℤ) (x: 2 ∣ k)  (x1: k%3 ≠ 0 ): (luc (k): ℤ ) ∣ 2* b → (luc k :ℤ) ∣ b:=
begin
    have h1: nat.coprime (luc k) 2,
    {apply nat.coprime.symm, rw nat.prime.coprime_iff_not_dvd, 
        {rw nat.dvd_iff_mod_eq_zero, rw luc_even, assumption},
        {exact nat.prime_two}},
    {apply int_dvd_cancel, assumption}
end

lemma fib_2k (k: ℕ ): fib(2*k) = fib k * luc k:=
begin
    have h1: 2* fib (2*k) = 2*(fib k * luc k),
    {rw [show 2*k =k+k, by ring], rw fib_luc1, ring}, 
    {linarith}
end

lemma even_or_odd (n: ℕ ): ∃ (w: ℕ ), n=2*w ∨ n=2*w+1:=
begin
    induction n with d hd,
    {use 0, simp},
    {cases hd with w hd, cases hd with hx hy,
    {use w, right, simp *},
    {use (w+1), left, rw hy, ring}}
end

lemma neg_1_pow_even (k: ℕ ) (h: 2 ∣ k): (-1: ℤ )^k=1:=
begin
    cases h with u v, rw v, rw pow_mul, simp
end

lemma neg_1_pow_odd (u: ℕ ) : (-1: ℤ )^(2*u+1)=-1:=
begin
    rw pow_add, rw neg_1_pow_even, 
    {ring}, 
    {use u}
end

lemma luc_2k (k: ℕ )(h: 2 ∣ k) : (luc k)^2 = luc(2*k)+2:=
begin
    apply int.coe_nat_inj, push_cast, rw ← fib_luc3, rw neg_1_pow_even _ h, ring
end

lemma mod_luc (k: ℕ ) (h: 2 ∣ k ∧ (k%3) ≠ 0) : ∀ (m: ℕ), luc(k) ∣ luc(m+2*k) + luc(m):=
begin
    intro m, cases h with hx hy, rw ← int.coe_nat_dvd, apply luc_cancel_2 _ _ hx hy, norm_cast,
    rw mul_add, rw fib_luc2 m (2*k), nth_rewrite 3 mul_comm, rw add_assoc, rw ← add_mul,
    rw fib_2k, rw ← luc_2k _ hx, rw nat.pow_two, rw ← mul_assoc, nth_rewrite 3 mul_comm, rw ← mul_assoc, rw ← add_mul, simp
end

lemma mod_luc_sub (k m: ℕ ) (h1 : 2 ∣ k) (h2: (k%3)≠ 0) (h3: 2*k ≥ m):(luc k:ℤ ) ∣ (luc (2*k-m) + (-1: ℤ)^m * luc m:ℤ ):=
begin
    have h4: (luc k:ℤ ) ∣ 2*(luc (2*k-m) + (-1: ℤ)^m * luc m:ℤ ),
        {rw mul_add, rw fib_luc2_sub (2*k-m) m, rw nat.sub_add_cancel h3, rw fib_2k, rw add_assoc, nth_rewrite 7 mul_comm, 
        nth_rewrite 3 mul_assoc, nth_rewrite 3 mul_assoc, rw ← mul_add, nth_rewrite 5 mul_comm, rw ← mul_add,
        norm_cast, rw ← luc_2k k h1,rw nat.pow_two, push_cast, use ((-1:ℤ)^(m+1)*5*fib k * fib m + (-1: ℤ )^m * luc m * luc k),ring},
    apply luc_cancel_2 _ _ h1 h2 h4
end

lemma mod_fun_gen (a k r s v: ℕ ) (f: ℕ → ℕ ) (h0: s≥ 1)(h: ∀ (m:ℕ ), (a: ℤ)  ∣ f(m+k) + (-1: ℤ )^r*f(m) ) :  (a: ℤ ) ∣ f(v+s*k) + (-1: ℤ )^(s*(r+1)-1)* f(v):=
begin
    have h3: ∃ (u:ℕ ), s=u+1, 
    {use s-1, omega},
    cases h3 with u h3, rw h3, clear h0 h3 s, induction u with s hs,
    {simp * at *},
    {have h5:= h (v+(s+1)*k),
    have h6:= dvd_mul_of_dvd_right (hs) ((-1)^(r+1)), 
    have h7:= dvd_add h5 h6, 
    rw nat.succ_eq_add_one, cases h7 with x h8, use x, rw ← h8, rw add_mul, rw one_mul, 
    rw eq_comm, rw add_assoc, conv_lhs{congr, skip, rw pow_add _ r 1, ring}, rw mul_assoc, rw ← pow_add, rw neg_eq_neg_one_mul, rw mul_left_comm, 
    have h9: (-1:ℤ ) ^ ((s + 2) * (r + 1) -1) = (-1:ℤ ) * (-1) ^ ((s + 1) * (r + 1) - 1 + r),
        {nth_rewrite_rhs 0 [show (-1:ℤ ) = (-1)^1, from rfl], rw ← pow_add, 
        have h10: (s + 2) * (r + 1) - 1 = 1 + ((s + 1) * (r + 1) - 1 + r), 
            {apply int.coe_nat_inj, rw [show 2=1+1, from rfl], repeat {rw add_mul}, rw one_mul,push_cast, simp, ring},
        rw h10}, 
    rw h9,nth_rewrite 1 mul_comm,  rw add_assoc}
end

lemma mod_fib (k: ℕ ) (h: 2 ∣ k ∧ (k%3) ≠ 0) : ∀ (m:ℕ), luc(k) ∣ fib(m+2*k) + fib(m):=
begin
    intro m, cases h with hx hy, rw ← int.coe_nat_dvd, apply luc_cancel_2 _ _ hx hy, norm_cast,
    rw mul_add, rw fib_luc1 m (2*k), nth_rewrite 3 mul_comm, rw add_assoc, rw mul_comm k 2,
    rw fib_2k, nth_rewrite 1 add_comm, rw mul_comm, rw ← add_assoc, rw ← add_mul, rw ← luc_2k _ hx, rw nat.pow_two, use (luc k * fib m + luc m * (fib k)), ring
end

lemma mod_fib_sub (k m: ℕ ) (h1 : 2 ∣ k) (h2: (k%3)≠ 0) (h3: 2*k ≥ m):(luc k:ℤ ) ∣ (fib (2*k-m) + (-1: ℤ)^(m+1) * fib m:ℤ ):=
begin
    have h4: (luc k:ℤ ) ∣ 2*(fib (2*k-m) + (-1: ℤ)^(m+1) * fib m:ℤ ),
        {rw mul_add, rw fib_luc1_sub (2*k-m) m, rw nat.sub_add_cancel h3, rw fib_2k, rw add_assoc, nth_rewrite 6 mul_comm, 
        nth_rewrite 1 mul_assoc, nth_rewrite 2 mul_assoc, rw ← mul_add, nth_rewrite 6 mul_comm, rw ← add_mul,
        norm_cast, rw ← luc_2k k h1,rw nat.pow_two, push_cast, use ((-1:ℤ)^(m)*fib k * luc m + (-1: ℤ )^(m+1) * luc k * fib m),ring},
    apply luc_cancel_2 _ _ h1 h2 h4
end

lemma luc_mod_8 (m : ℕ ): luc (m+12)%8  =luc m %8 :=
begin
    rw [show m+12=11+m+1, by ring],  rw fib_luc_rec_2,
    rw [show fib (11+1)=144, from rfl], rw [show fib 11=89, from rfl], rw nat.add_mod, rw nat.mul_mod, 
    rw [show 144%8 =0, from rfl], nth_rewrite 1 nat.mul_mod, rw [show 89%8 =1, from rfl], simp
end

lemma luc_mod_8_gen (m:ℕ ): luc(m)%8 = luc(m%12)%8:=
begin
    cases div_algo m 12, rw h, clear h, rw add_comm, induction w with d hd,
    {simp},
    {rw nat.succ_eq_add_one, rw mul_add, rw← add_assoc, rw mul_one, rw luc_mod_8, rw hd, simp}
end