import data.nat.basic
import algebra.group_power
import algebra.ring
import tactic
import data.int.basic
import data.real.basic
import tactic.nth_rewrite.default
import data.nat.modeq
import data.nat.prime
import data.nat.sqrt
import number_theory.quadratic_reciprocity
import data.zmod.basic
import field_theory.finite
import data.nat.parity

def fib : ℕ → ℕ
| 0     := 0
| 1     := 1
| (n+2) := fib (n+1) + fib n

def luc: ℕ → ℕ
| 0 := 2
| 1 := 1
| (n+2) := luc(n+1) +luc n

@[simp] lemma fib_add ( n :  ℕ) : fib (n+2) = fib (n+1) + fib (n):= by refl
@[simp] lemma luc_add (n: ℕ ): luc (n+2) = luc (n+1) + luc n:= by refl 
@[simp] lemma fib_zero : fib 0 =0:= by refl
@[simp] lemma fib_one : fib 1 = 1:= by refl
@[simp] lemma fib_two : fib 2= 1:= by refl
@[simp] lemma luc_zero : luc 0 =2:= by refl
@[simp] lemma luc_one : luc 1 = 1:= by refl

@[simp] lemma fib_luc_rec (n: ℕ ): luc(n+1) = fib(n+2) + fib (n):=
begin
revert n,
apply nat.two_step_induction,
{simp}, 
{simp},
{intros, simp * at *, ring}
end

lemma nat_case_bash (h n : ℕ ):  h ≤ n ∨ ∃ (k: ℕ ), h=k+n:=
begin
have t1:= le_or_lt h n, cases t1 with t1 t2,
{left, assumption},
{right, use h-n, omega,}
end

lemma fib_luc1 (m n : ℕ ) : 2 * fib (m+n) = fib (m) * luc (n) + luc(m) * fib(n):=
begin
revert n, apply nat.two_step_induction,
{simp [mul_comm]},
{cases nat_case_bash m 1, interval_cases m, 
    {cases h with k h, rw h, simp, ring},
    {simp},
    {simp}},
{intros, repeat {rw nat.succ_eq_add_one at *}, rw [show m+ (n+1+1) = (m+n)+2, by ring], nth_rewrite 0 ← add_assoc at IH2, 
rw fib_add, rw mul_add, rw IH1, rw IH2, rw [show n+1+1 =n+2, from rfl], rw fib_add, rw luc_add, ring,}
end

lemma fib_luc2 (m n : ℕ ): 2* luc (m+n) = 5* fib (m) * fib (n) +luc(m) * luc(n) :=
begin
revert n, apply nat.two_step_induction,
{simp [mul_comm]},
{cases nat_case_bash m 1, interval_cases m, 
    {cases h with k h, rw h, simp, ring},
    {simp},
    {simp, ring}},
{intros, repeat {rw nat.succ_eq_add_one at *}, rw [show m+ (n+1+1) = (m+n)+2, by ring], nth_rewrite 0 ← add_assoc at IH2, 
rw luc_add, rw mul_add, rw IH1, rw IH2, rw [show n+1+1 =n+2, from rfl], rw fib_add, rw luc_add, ring,}
end

lemma fib_luc_rec_2 (m n: ℕ): luc(m+n+1) = fib(m+1)*luc(n+1) + fib(m)*luc(n):=
begin
revert n, apply nat.two_step_induction,
{simp,ring},
{cases nat_case_bash m 1, interval_cases m, 
    {cases h with k h, rw h, simp, ring},
    {simp}, 
    {simp}},
{intros, repeat {rw nat.succ_eq_add_one at *}, rw [show m+ (n+1+1) = (m+n)+2, by ring], nth_rewrite 0 ← add_assoc at IH2, 
rw luc_add, rw IH1, rw IH2, ring,}
end


lemma fib_luc3 (m: ℕ) : ((luc(2*m) + 2 * (-1: ℤ )^(m)) : ℤ )= ((luc(m))^2 : ℤ ):=
begin
cases m with d hd,
{simp, ring},

{rw nat.succ_eq_add_one, rw [show 2*(d+1)= d+(d+1)+1, by ring], rw fib_luc_rec_2,
rw fib_luc_rec d, rw pow_two, 
suffices goal:  (↑(luc (d + 2)) * ↑(fib (d + 1)) + 2 * (-1) ^ (d + 1): ℤ) = (↑(luc (d + 1)) * ↑(fib (d + 2)): ℤ),
have t1: (↑(fib (d + 1) * luc (d + 1 + 1) + fib d * (fib (d + 2) + fib d)) + 2 * (-1) ^ (d + 1):ℤ) = (↑(luc(d+2))*↑ (fib (d + 1))   + 2 * (-1) ^ (d + 1)+fib d * (fib (d + 2) + fib d): ℤ ),

apply nat.two_step_induction,
ring,
ring,
intros p q r,
rw nat.succ_eq_add_one,
rw nat.succ_eq_add_one,
clear r,
rw luc_add,
rw fib_add,
simp,
rw mul_add,
rw add_mul,
have: (-1: ℤ )^(p+1+1+1) = (-1: ℤ )^ (p+1),
rw pow_add (-1: ℤ ) (p+1) (1+1),
rw [show (-1: ℤ )^(1+1)=1, from rfl],
rw mul_one,

rw this,
clear this,
rw add_mul,
rw [show p+1+1=p+2, from rfl],
simp,
repeat{rw add_assoc},
rw q,
clear q,
simp,
rw eq_comm,
rw fib_add,
simp,
rw mul_add,
rw fib_add,
simp,
rw mul_add,
nth_rewrite 2 luc_add,
simp,
rw add_mul,
ring,
apply goal,}
end

lemma dvd_imp_leq (a b: ℕ   ) (h: b ≥ 1) : a ∣ b → a ≤ b:=
begin
    intro p,
    cases p,
    have : p_w ≥ 1,
    by_contra,
    push_neg at a_1,
    have h1: p_w =0,
    linarith,
    rw h1 at p_h,
    rw mul_zero at p_h,
    linarith,
suffices goal: a*1 ≤ a*p_w,
rw p_h,
rw mul_one at goal,
exact goal,
apply nat.mul_le_mul_left,
assumption,
end

lemma dvd_imp_eq (a b: ℕ ) (h1: a≥ 1) (h2: b ≥ 1): a∣ b ∧ b∣ a → a=b:=
begin
intro p,
cases p,
have: a ≤ b,
apply dvd_imp_leq,
exact h2,
exact p_left,

have this2: b ≤ a,
apply dvd_imp_leq,
assumption,
assumption,
linarith,
end

lemma gcd_add (a b c: ℕ  ) (h: a = b +c) (x: a >0) (y: b >0) (z: c>0): nat.gcd a b = nat.gcd b c:=
begin
cases nat.gcd_dvd b c,
have h1: nat.gcd b c ∣ b + c,
apply dvd_add,
exact left,
exact right,
rw ← h at h1,
have h2: nat.gcd b c ∣ nat.gcd a b,
rw nat.dvd_gcd_iff,
split,
exact h1,
exact left,
clear left,
clear right,

cases nat.gcd_dvd a b,
have h3: (nat.gcd a b :ℤ ) ∣  (a - b :ℤ) ,
apply dvd_sub,
norm_cast,
exact left,
norm_cast,
exact right,
nth_rewrite 1 h at h3,
simp at h3,
norm_cast at h3,

have h4: nat.gcd a b ∣ nat.gcd b c,
rw nat.dvd_gcd_iff,
split,
exact right,
exact h3,
apply dvd_imp_eq,
suffices: nat.gcd a b >0, linarith,
apply nat.gcd_pos_of_pos_right, assumption,
suffices: nat.gcd b c >0, linarith,
apply nat.gcd_pos_of_pos_right, assumption,
split,
assumption,
assumption,
end

lemma fib_pos : ∀ m: ℕ, fib(m+1) >0:=
begin
apply nat.two_step_induction,
simp,
rw [show fib 1 = 1, from rfl],
simp,
rw [show fib (1+1) = 1, from rfl],
simp,
intros p q r,
rw nat.succ_eq_add_one,
rw nat.succ_eq_add_one,
rw nat.succ_eq_add_one at r,
rw fib_add,
linarith,
end

lemma luc_pos : ∀ m: ℕ, luc(m) >0:=
begin
apply nat.two_step_induction,
simp,
rw [show luc 0 =2, from rfl],
simp,
rw [show luc 1 =1, from rfl],
simp,
intros p q r,
repeat {rw nat.succ_eq_add_one},
rw nat.succ_eq_add_one at r,
rw luc_add,
linarith,
end

lemma fib_coprime (m: ℕ ) : nat.gcd (fib(m+1)) (fib(m+2)) = 1:=
begin
induction m with d hd,
ring,
rw nat.succ_eq_add_one,
have:  fib(d+1) + fib(d+1+1) = fib(d+1+2) , rw eq_comm, rw fib_add, ring,
rw nat.gcd_comm,
rw gcd_add,
ring,
rw nat.gcd_comm,
exact hd,
ring,
rw [show d+1+2 = (d+2)+1, from rfl],
apply fib_pos,
apply fib_pos (d+1),
apply fib_pos,
end

lemma fib_even (m : ℕ) : fib (3*m) %2 =0 ∧  fib (3*m +1) % 2 =1  ∧ fib (3*m+2)%2=1 :=
begin
induction m with d hd,
simp,
split,
rw [show fib 0 = 0, from rfl],
simp,
split,
rw [show fib(1) = 1, from rfl],
ring,
rw [show fib(2) =1, from rfl],
ring,
cases hd,
cases hd_right,
split,
rw nat.succ_eq_add_one,
have t1: fib(3*(d+1)) = fib(3*d+2) + fib(3*d+1),
rw [show 3*(d+1) = (3*d + 1 )+ 2, from rfl],
rw fib_add,
rw t1,
rw nat.add_mod,
rw hd_right_left,
rw hd_right_right,
ring,
rw nat.succ_eq_add_one,
split,
rw [show 3*(d+1)+1 = 3*d +2+2, from rfl ],
rw fib_add,
rw fib_add,
rw nat.add_mod,
rw hd_right_right,
rw nat.add_mod (fib(3*d+1+1)) (fib(3*d+1)) 2,
rw hd_right_right,
rw hd_right_left,
ring,
rw fib_add,
rw [show 3*(d+1)+1 = 3*d +2+2, from rfl ],
rw [show 3*(d+1) = (3*d + 1 )+ 2, from rfl],
rw fib_add,
rw fib_add,
rw nat.add_mod,
rw nat.add_mod (fib(3*d+1+1)) (fib(3*d+1)) 2,
rw hd_right_right,
rw hd_right_left,
ring,
rw nat.add_mod (2*fib(3*d+1+1)) (fib(3*d+1)) 2,
rw hd_right_left,
ring,
nth_rewrite 0 [show 2=1+1, from rfl],
rw add_mul,
rw one_mul,
rw nat.add_mod (fib(3*d+2)) (fib(3*d+2)) 2,
rw hd_right_right,
ring,
end 


lemma fib_luc_gcd_div_2 (m: ℕ ) : nat.gcd (fib(m+2)) (luc(m+2)) =nat.gcd (fib(m+2)) 2:=
begin
have goal: nat.gcd (fib(m+2)) (luc(m+2)) =nat.gcd (fib(m+2)) (2 * fib(m+1)),
    have: luc(m+2) = fib(m+2) + 2* fib(m+1),
    rw  fib_luc_rec,
    rw fib_add,
    ring,
rw nat.gcd_comm,
rw gcd_add (luc(m+2)) (fib(m+2)) (2*fib(m+1)),
assumption,
apply luc_pos,
apply fib_pos,
have t1: fib(m+1)>0, apply fib_pos,
linarith,

rw nat.coprime.gcd_mul_right_cancel_right at goal,
assumption,
apply fib_coprime,
end

lemma fib_luc_gcd (m: ℕ ) : nat.gcd (fib(3*m)) (luc(3*m)) = 2  :=
begin
cases nat_case_bash m 1, interval_cases m, 
ring,
cases h with p q,
rw q,
rw [show 3*(p+1) = 3*p + 1 +2, from rfl],
rw fib_luc_gcd_div_2,
rw [show 3*p + 1 +2=3*(p+1) , from rfl],
have: fib (3*m) %2 =0 ∧  fib (3*m +1) % 2 =1  ∧ fib (3*m+2)%2=1,
apply fib_even,
rw q at this,
cases this,
clear this_right,

have t1: 2 ∣ fib (3*(p+1)),
rw nat.dvd_iff_mod_eq_zero,
assumption,

cases t1 with x y,
rw y,
simp,
end 

lemma fib_luc_gcd_2 (m : ℕ) (h: m%3 ≠ 0): nat.gcd (fib(m)) (luc(m))=1 :=
begin
cases zero_or_one_two m,
rw h_1 at h,
have: 0%3 =0 , refl,
exfalso,
rw this at h,
apply h,
refl,
cases h_1,
rw h_1,
rw [show fib 1 =1, from rfl],
rw [show luc 1 =1, from rfl],
simp,
cases h_1 with s hy,
rw hy,
rw fib_luc_gcd_div_2,
rw ← hy,

cases res_mod_3 m,
cases h_1 with h1 h2,
exfalso,
rw h1 at h,
simp at h,
assumption,


suffices goal: (fib (m)).gcd 2 ≠  1 → false,
cc,
intro f,
have g: nat.gcd (fib (m)) 2  ≤ 2,
apply nat.gcd_le_right, simp,
have i: nat.gcd (fib (m)) 2 >0,
apply nat.gcd_pos_of_pos_right, simp,
have j: ∃ u:ℕ , u =nat.gcd (fib (m)) 2 ,
exact exists_eq,
cases j with j jy,
cases zero_or_one_two_three j,
rw jy at h_1,
linarith,
cases h_1 with f1 f2,
rw jy at f1,
rw f1 at f,
apply f,
refl,
cases f2 with f2 f3,
rw jy at f2,
have e: 2 ∣ fib (m),
cases nat.gcd_dvd (fib (m)) 2,
clear right,
rw f2 at left,
exact left,
rw nat.dvd_iff_mod_eq_zero at e,
have fib_even: fib (3*w) %2 =0 ∧  fib (3*w +1) % 2 =1  ∧ fib (3*w+2)%2=1,
apply fib_even,

cases fib_even with fib1 fib2,
cases fib2 with fib2 fib3,
cases h2 with h2 h3,
rw ← h2 at fib2,
rw fib2 at e,
contradiction,
rw ← h3 at fib3,
rw fib3 at e,
contradiction,

cases f3 with k g3,
have g4: m%3 <3,
apply nat.mod_lt,
simp,
linarith,
end 

lemma luc_even (m: ℕ ): luc(m)%2 =0  ↔ (m%3)=0:=
begin
split,
intro h,
cases res_mod_3 m,
by_contra,
cases h_1 with h1 h2,
rw h1 at a,
simp at a,
exact a,
have fib_even:fib (3*w) %2 =0 ∧  fib (3*w +1) % 2 =1  ∧ fib (3*w+2)%2=1,
apply fib_even,
cases fib_even with fib1 fib2,
cases fib2 with fib2 fib3,

cases h2 with h2 h3,
rw h2 at h,
cases nat_case_bash w 1, interval_cases w, 
simp at h,
rw [show luc 1 =1, from rfl] at h,
contradiction,

cases h_1 with k h1,
rw h1 at h,
rw fib_luc_rec at h,
rw h1 at fib3,
rw h1 at fib1,
rw nat.add_mod at h,
rw fib1 at h,
rw fib3 at h,
simp at h,
contradiction,

rw h3 at h,
rw fib_luc_rec at h,
rw fib_add at h,
ring at h,
simp at h,
ring at h,
rw fib3 at h,
contradiction,

intro h,
cases res_mod_3 m,
cases h_1 with h1 h2,
rw h1,
cases nat_case_bash w 1, interval_cases w, 
ring,
cases h_1 with k f,
rw f,
rw [show 3*(k+1) = 3*k+1+2, from rfl],
rw fib_luc_rec,
rw fib_add,
rw fib_add,
ring,
ring,
have fib_even:fib (3*k) %2 =0 ∧  fib (3*k +1) % 2 =1  ∧ fib (3*k+2)%2=1,
apply fib_even,
cases fib_even with fib1 fib2,
cases fib2 with fib2 fib3,
rw nat.add_mod,
rw fib2,
rw nat.mul_mod,
rw fib3,
ring,

cases h2 with h2 h3,
exfalso,
rw h2 at h,
rw nat.add_mod at h,
simp at h,
contradiction,
rw h3 at h,
rw nat.add_mod at h,
simp at h,
contradiction,
end

lemma div_algo (a b: ℕ ) (h2: b>0): ∃ (q : ℕ) , a=b*q+(a%b) ∧ (a%b)<b:=
begin
have: b ∣ a - a%b,
exact nat.dvd_sub_mod a,
cases this with x y,
use x,
split,
have t1: ∃ k: ℕ, k=a%b,
use a%b,
cases t1 with k t1,
rw ← t1,
rw ← t1 at y,
rw ← y,
suffices goal: (↑a : ℤ) = (↑(a-k+k): ℤ ),
apply int.coe_nat_inj,
assumption,

have: (↑a : ℤ ) = (↑a - ↑k +↑k: ℤ ), simp,
simp,

rw this,
rw add_right_cancel_iff,
rw eq_comm,
have t2: k≤ a,
rw t1,
apply nat.mod_le,
exact int.coe_nat_sub t2,

apply nat.mod_lt, 
exact h2,
end

lemma luc_mod_3_pre (k: ℕ ): luc(8*k)%3 =2 ∧ luc(8*k+1) %3 =1 ∧ luc(8*k+2) %3 =0 ∧ luc(8*k+3) %3=1 ∧ luc(8*k+4) %3 = 1 ∧ luc(8*k+5) %3=2 ∧ luc(8*k+6) %3 =0 ∧ luc(8*k+7) %3 = 2 :=
begin
induction k with d hd,
split, simp, rw [show luc 0 =2, from rfl], ring,
split, simp, rw [show luc 1 =1, from rfl], ring,
split, simp, rw [show luc 2 =3, from rfl], ring,
split, simp, rw [show luc 3 =4, from rfl], ring,
split, simp, rw [show luc 4 =7, from rfl], ring,
split, simp, rw [show luc 5 =11, from rfl], ring,
split, simp, rw [show luc 6 =18, from rfl], ring,
simp, rw [show luc 7 =29, from rfl], ring,

cases hd with h1 h2, cases h2 with h2 h3, cases h3 with h3 h4, cases h4 with h4 h5, cases h5 with h5 h6, cases h6 with h6 h7, cases h7 with h7 h8,

rw nat.succ_eq_add_one,
have h9: luc(8*d+8)%3=2,
rw [show 8*d+8 = (8*d +6)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h8, rw h7, ring,
have h10: luc(8*d+9)%3=1,
rw [show 9 = 7+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h9, rw h8, ring,
have h11: luc(8*d+10)%3=0,
rw [show 10 = 8+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h10, rw h9, ring,
have h12: luc(8*d+11)%3=1,
rw [show 11 = 9+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h10, rw h11, ring,
have h13: luc(8*d+12)%3=1,
rw [show 12 = 10+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h12, rw h11, ring,
have h14: luc(8*d+13)%3=2,
rw [show 13 = 11+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h12, rw h13, ring,
have h15: luc(8*d+14)%3=0,
rw [show 14 = 12+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h13, rw h14, ring,
have h16: luc(8*d+15)%3=2,
rw [show 15 = 13+2, from rfl], rw luc_add, ring, rw nat.add_mod, rw h14, rw h15, ring,

repeat{split, ring, assumption},
ring, assumption,
end

lemma luc_mod_3 (m: ℕ) : luc(m) %3=0 ↔ m%4=2 :=
begin

have: ∃ q: ℕ ,m=8*q+(m%8) ∧ (m%8) <8,  
apply div_algo m 8,
simp,

cases this with q r,
cases r with x y,
have hd: ∀ n: ℕ, luc(8*n)%3 =2 ∧ luc(8*n+1) %3 =1 ∧ luc(8*n+2) %3 =0 ∧ luc(8*n+3) %3=1 ∧ luc(8*n+4) %3 = 1 ∧ luc(8*n+5) %3=2 ∧ luc(8*n+6) %3 =0 ∧ luc(8*n+7) %3 = 2,
apply luc_mod_3_pre,
cases hd q with h1 h2, cases h2 with h2 h3, cases h3 with h3 h4, cases h4 with h4 h5, cases h5 with h5 h6, cases h6 with h6 h7, cases h7 with h7 h8,
have: (8*q) %4 =0,
rw ← nat.dvd_iff_mod_eq_zero,
rw [show 8*q = 4*(2*q), by ring],
split,
refl,

split,
intro u,
rw x at u,
interval_cases (m%8),
swap,
rw h at u,
simp at u,
rw h1 at u,
exfalso, 
contradiction,
swap,
rw h at u,
rw h2 at u,
exfalso, 
contradiction,
swap,
rw x,
rw h at u,
rw nat.add_mod,
rw this,
rw h,
simp,
refl,
swap,
rw h at u,
rw h4 at u,
exfalso, 
contradiction,
swap,
rw h at u,
rw h5 at u,
exfalso, 
contradiction,
swap,
rw h at u,
rw h6 at u,
exfalso, 
contradiction,
swap,
rw h at u,
rw x,
rw nat.add_mod,
rw this,
rw h,
simp, refl,
swap,
rw h at u,
rw h8 at u,
exfalso, 
contradiction,

intro u,
rw x,
interval_cases (m%8),
exfalso,
rw h at x,
simp at x,
rw x at u,
rw this at u, 
contradiction,
exfalso,
rw h at x,
rw x at u,
rw nat.add_mod at u,
rw this at u, 
simp at u,
rw [show 1%4 =1, from rfl] at u,
linarith,
rw h,
exact h3,
exfalso,
rw h at x,
rw x at u,
rw nat.add_mod at u,
rw this at u, 
simp at u,
rw [show 3%4 =3, from rfl] at u,
linarith,
exfalso,
rw h at x,
rw x at u,
rw nat.add_mod at u,
rw this at u, 
simp at u,
linarith,
exfalso,
rw h at x,
rw x at u,
rw nat.add_mod at u,
rw this at u, 
simp at u,
rw [show 5%4 =1, from rfl] at u,
linarith,
rw h,
exact h7,
exfalso,
rw h at x,
rw x at u,
rw nat.add_mod at u,
rw this at u, 
simp at u,
rw [show 7%4 =3, from rfl] at u,
linarith,
end

lemma luc_mod_4_pre (k: ℕ ): luc(6*k)%4 =2 ∧ luc (6*k+1)%4=1 ∧ luc(6*k+2)%4=3 ∧ luc(6*k+3)%4=0 ∧ luc(6*k+4)%4=3 ∧ luc(6*k+5)%4=3:=
begin
induction k with d hd,
split, simp, rw [show luc 0 =2, from rfl], ring,
split, simp, rw [show luc 1 =1, from rfl], ring,
split, simp, rw [show luc 2 =3, from rfl], ring,
split, simp, rw [show luc 3 =4, from rfl], ring,
split, simp, rw [show luc 4 =7, from rfl], ring,
simp, rw [show luc 5 =11, from rfl], ring,

cases hd with h1 h2, cases h2 with h2 h3, cases h3 with h3 h4, cases h4 with h4 h5, cases h5 with h5 h6,
rw nat.succ_eq_add_one,
have h7: luc(6*d+6)%4=2,
rw [show 6*d+6 = (6*d +4)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h6, rw h5, ring,
have h8: luc(6*d+7)%4=1,
rw [show 6*d+7 = (6*d +5)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h6, rw h7, ring,
have h9: luc(6*d+8)%4=3,
rw [show 6*d+8 = (6*d +6)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h7, rw h8, ring,
have h10: luc(6*d+9)%4=0,
rw [show 6*d+9 = (6*d +7)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h9, rw h8, ring,
have h11: luc(6*d+10)%4=3,
rw [show 6*d+10 = (6*d +8)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h9, rw h10, ring,
have h12: luc(6*d+11)%4=3,
rw [show 6*d+11 = (6*d +9)+2 , from rfl ], rw luc_add, ring, rw nat.add_mod, rw h10, rw h11, ring,

repeat {split, rw mul_add, assumption,},
rw mul_add, assumption,
end 

lemma luc_mod_4 (m: ℕ): m%6 =2 ∨ m%6 =4 →  luc (m)%4 =3 :=
begin
have: ∃ q: ℕ ,m=6*q+(m%6) ∧ (m%6) <6,  apply div_algo m 6,simp,
cases this with q x, cases x with x y,
have pre: ∀ k: ℕ, luc(6*k)%4 =2 ∧ luc (6*k+1)%4=1 ∧ luc(6*k+2)%4=3 ∧ luc(6*k+3)%4=0 ∧ luc(6*k+4)%4=3 ∧ luc(6*k+5)%4=3, exact luc_mod_4_pre,
cases pre q with h h1, cases h1 with h1 h2, cases h2 with h2 h3, cases h3 with h3 h4, cases h4 with h4 h5,
intro u,
cases u,
rw x, rw u, assumption,
rw x, rw u, assumption,
end

lemma mod_luc_pre (k b: ℕ ) (x: 2 ∣ k)  (x1: k%3 ≠ 0 ): luc (k) ∣ 2* b → luc k ∣ b:=
begin
intro h,
apply nat.coprime.dvd_of_dvd_mul_left,
have: nat.coprime (luc k) 2,
have h0: nat.gcd (luc k) 2 =1 → nat.coprime (luc k) 2, intro h, assumption,
apply h0,
by_contradiction,
have: nat.gcd (luc(k)) 2 ≠ 1, cc,
have t2: nat.gcd (luc(k)) 2 ≤ 2, apply nat.gcd_le_right, simp,
interval_cases nat.gcd(luc(k)) 2,

assumption,
swap,
have t3: nat.gcd(luc(k)) 2 >0, apply nat.gcd_pos_of_pos_right, simp,
linarith,
swap,
have t4: nat.gcd (luc(k)) 2 ∣ luc(k), apply nat.gcd_dvd_left,
rw h_1 at t4,
have t5: luc k%2 =0, apply nat.mod_eq_zero_of_dvd, assumption,
rw luc_even at t5,
contradiction,
exact h,
end

lemma mod_luc (m k: ℕ ): 2 ∣ k ∧ (k%3) ≠ 0 → luc(k) ∣ luc(m+2*k) + luc(m):=
begin
intro h,
cases h with hx hy,
apply mod_luc_pre,
assumption, assumption,

rw mul_add,
rw fib_luc2 m (2*k),
have t6: luc m * luc (2 * k) + 2 * luc m = luc m *(luc(2*k)+2), ring,
rw add_assoc,
rw t6,
have t7: 2*fib(2*k) = 2*(fib(k)*luc(k)), rw [show 2*k = k+k, by ring], rw fib_luc1, ring,
rw nat.mul_right_inj at t7,
rw t7,
have t8: luc(2*k)+2 =(luc k)*(luc k),
apply int.coe_nat_inj,
simp, ring,
rw ← fib_luc3 k,
cases hx with h x,
nth_rewrite 2 x,
simp,
rw pow_mul,
ring, simp,
rw t8,
have t10: 5 * fib m * (fib k * luc k) + luc m * (luc k * luc k) = (5* fib m*fib k +luc m * luc k)* (luc k), rw eq_comm, rw add_mul, ring, 
rw t10,
rw mul_comm,
simp,
simp,
end

lemma mod_luc2 (k n m: ℕ ) (h: 2 ∣ k) (h1: (k%3) ≠ 0): luc(k) ∣ luc(m+2*(2*n+1)*k) + luc(m):=
begin
have goal:∀ (m:ℕ), luc(k) ∣ luc(m+2*(2*n+1)*k) + luc(m),
induction n with d hd, intro h, simp, apply mod_luc, split, assumption, assumption,
rw nat.succ_eq_add_one,
intro m, 
have:  m + 2 * (2 * (d + 1) + 1) * k = m+4*k + 2*(2*d+1)*k, ring, rw this,
have t1: luc k ∣ luc (m +4*k + 2 * (2 * d + 1) * k) + luc (m+4*k), apply hd (m+4*k),
have t2: luc k ∣ luc (m+2*k + 2*k) + luc(m+2*k), apply mod_luc (m+2*k), split, assumption, assumption, ring at t2,
have t3: luc k ∣ luc (m+2*k) + luc(m), apply mod_luc, split, assumption, assumption,
have t4: luc k ∣ (luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc (m + 4 * k)) + (luc (m+4*k) +luc (m + 2 * k)), apply dvd_add, assumption, assumption,
have s1: (luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc (m + 4 * k)) + (luc (m+4*k) +luc (m + 2 * k)) = luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc (m + 4 * k) + luc (m+4*k) +luc (m + 2 * k), ring, rw s1 at t4,
have t5: luc k ∣ (luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc (m + 4 * k) + luc (m+4*k) +luc (m + 2 * k)) + (luc(m+2*k)+luc(m)), apply dvd_add, assumption, assumption,
have s2: (luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc (m + 4 * k) + luc (m+4*k) +luc (m + 2 * k)) + (luc(m+2*k)+luc(m)) =2*(luc (m + 4 * k) +luc (m + 2 * k)) + luc (m + 4 * k + 2 * (2 * d + 1) * k) +luc(m), ring,
rw s2 at t5, 
have t6: (2 * (luc (m + 4 * k) + luc (m + 2 * k)) + luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc m)%(luc k)=0, apply nat.mod_eq_zero_of_dvd, assumption,
have s3: 2 * (luc (m + 4 * k) + luc (m + 2 * k)) + luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc m = (2 * (luc (m + 4 * k) + luc (m + 2 * k))) + (luc (m + 4 * k + 2 * (2 * d + 1) * k) + luc m), ring, rw s3 at t6,
have t7: (luc (m + 4 * k) + luc (m + 2 * k))%(luc k) = 0, apply nat.mod_eq_zero_of_dvd, assumption,
rw nat.add_mod at t6, rw nat.mul_mod at t6, rw t7 at t6, simp at t6, apply nat.dvd_of_mod_eq_zero, assumption,
exact goal m,
end

lemma mod_fib (m k: ℕ ): 2 ∣ k ∧ (k%3) ≠ 0 → luc k ∣ fib (m+2*k) + fib(m):=
begin
intro h,
cases h with hx hy,
apply mod_luc_pre,
assumption, assumption,

rw mul_add,
rw fib_luc1 m (2*k),
have t6: fib m * luc (2 * k) + luc m * fib (2*k) + 2* fib m = luc m * fib (2*k) + fib m * (luc(2*k)+2), ring,
rw t6,
have t7: 2*fib(2*k) = 2*(fib(k)*luc(k)), rw [show 2*k = k+k, by ring], rw fib_luc1, ring,
rw nat.mul_right_inj at t7,
rw t7,
have t8: luc(2*k)+2 =(luc k)*(luc k),
apply int.coe_nat_inj,
simp, ring,
rw ← fib_luc3 k,
cases hx with h x,
nth_rewrite 2 x,
simp,
rw pow_mul,
ring, simp,
rw t8,
have t10: luc m * (fib k * luc k) + fib m * (luc k * luc k) = (luc m *fib k + fib m * luc k) * luc k, ring,
rw t10,
rw mul_comm,
simp,
simp,
end

lemma luc_mod_8 (m : ℕ ): luc (m+12)%8  =luc m %8 :=
begin
have: m+12 =11+m+1, ring,
rw this,
rw fib_luc_rec_2,
rw [show fib(11+1) =144, from rfl],
rw [show fib(11)=89, from rfl],
rw nat.add_mod,
rw nat.mul_mod,
rw [show 144%8 =0, from rfl],
nth_rewrite 1 nat.mul_mod,
rw [show 89%8 =1, from rfl],
simp,
end

lemma add_arrows (a b : ℕ ): a = b → (a: ℤ ) = (b: ℤ ):=
begin
exact congr_arg (λ (a : ℕ), ↑a),
end

lemma pow_neg_one (m: ℕ ): (-1: ℤ )^(m) = 1 ∨ (-1: ℤ )^m =(-1: ℤ ):=
begin
induction m with d hd,
left,
refl,
rw nat.succ_eq_add_one,
cases hd with h1 h2,
right,
rw pow_add,
rw h1,
ring,

left,
rw pow_add,
rw h2,
ring,
end


lemma add_to_both_sides (a b c :ℕ ) (h: a≥ b): a-b =c → a=c+b:=
begin    
intro h,
have: (↑ (a-b) : ℤ ) = (c: ℤ ), apply add_arrows,  exact h,
apply int.coe_nat_inj,
simp, 
rw ← this, 
have t2:  (↑(a-b) : ℤ) = (a-b :ℤ ) ,
apply int.coe_nat_sub,
assumption, 
rw t2,
ring,
end

lemma diff_of_squares_neq_2 (a b: ℕ ): a^2 +2 ≠ b^2:=
begin
by_contra,
push_neg at a_1,
have: b>a, 
by_contradiction, push_neg at a_2,
have t2: b*b ≤ a*a,
apply mul_le_mul, exact a_2, exact a_2, linarith, linarith,
ring at t2,
repeat {rw nat.pow_eq_pow at t2}, 

have t3: a^2+2 ≤ a^2,
apply le_trans, 
rw a_1, assumption,
linarith, 

have t4: b-a>0, apply nat.sub_pos_of_lt, assumption, 

have t5: ∃ k: ℕ, b-a =k, use b-a, 
cases t5 with k t5,
cases zero_or_one_two k, 
rw h at t5,
linarith, 
have t6: b=a+k, rw add_comm, apply add_to_both_sides, linarith, assumption,
rw t6 at a_1, 
ring at a_1, rw add_mul at a_1, nth_rewrite 0 [show 2=1+1, from rfl] at a_1, rw pow_add at a_1, simp at a_1, rw add_assoc at a_1, rw add_left_cancel_iff at a_1,
cases h with h1 h2,
rw h1 at a_1, simp at a_1,
have t7:(2)%2 = ((2*a+1)%2: ℕ ), exact congr_fun (congr_arg has_mod.mod a_1) 2,
rw nat.add_mod at t7,
rw nat.mul_mod at t7,
simp at t7,
contradiction,

cases h2 with w h2,
rw h2 at a_1, 
nth_rewrite 4 [show 2=1+1, from rfl] at a_1, rw ← nat.pow_eq_pow at a_1, rw pow_add (w+2) 1 1 at a_1, simp at a_1, rw add_mul at a_1, rw mul_add at a_1, rw mul_add at a_1,
linarith,
end

lemma is_contra (P:  Prop) : P ↔ (¬ P → false):=
begin
split, cc, cc,
end 

lemma flip_ineq (a b: ℕ ): a>b ↔ b<a:=
begin
exact iff.rfl,
end
lemma to_3_n_gt_n (n:ℕ ): 3^n >n :=
begin
cases nat_case_bash n 1, interval_cases n,  simp, 
cases h with x y, rw y, clear y,
induction x with d hd, simp, 
rw nat.succ_eq_add_one, 

have: 3*(d+1) < 3^(d+1+1), rw ← nat.pow_eq_pow, rw pow_add, simp, rw mul_comm, simp, assumption,
rw ← flip_ineq at this,
apply gt_trans, assumption,
rw mul_add, linarith, 
end
lemma decomp_pow_3 (n: ℕ ) (h : n>0): ∃ (k r: ℕ ), n = 3^r *k ∧ ¬ 3 ∣ k:=
begin 
have :  ∃ (r :ℕ ),3^r ∣ n ∧ ¬ 3^(r+1)∣ n,
rw is_contra ( ∃ (r : ℕ), 3 ^ r ∣ n ∧  ¬3 ^ (r + 1) ∣ n),
rw  not_exists,
intro p,
push_neg at p,
have: ∀ x: ℕ , 3 ^(x+1) ∣ n,
intro q,
induction q with d hd,
cases p 0 with p1 p2, exfalso, simp at p1, assumption, assumption,
rw nat.succ_eq_add_one, cases p (d+1) with p1 p2,  contradiction, assumption,
have t1: 3^(n+1) ∣ n, exact this n,
have t2: 3^n ∣ n,apply nat.dvd_trans, swap, assumption, rw ← nat.pow_eq_pow, rw nat.pow_add, simp, 
have: 3^n ≤ n, apply dvd_imp_leq, linarith, assumption,
have t2: n < 3^n, rw ← flip_ineq, apply to_3_n_gt_n, linarith,

cases this with r t1, cases t1 with t1 t2, cases t1 with k y, use k, use r, split, assumption,
by_contra, cases a with a b, rw b at y, rw ← mul_assoc at y, nth_rewrite 1 [show 3=3^1, from rfl] at y, rw ←  nat.pow_add at y, 
have: 3^(r+1) ∣ n, use a, assumption,
contradiction,
end


lemma zmod_exi: ∀ (q: ℕ ) [fact q.prime], (∃ y : zmod q, y^2=-1) →  q%4 ≠ 3:=
begin
    intros q r,
have: (∃ y : zmod q, y^2=-1) ↔   q%4 ≠ 3, apply @zmod.exists_pow_two_eq_neg_one_iff_mod_four_ne_three q r,
cases this, assumption,
end
lemma zmod_trans (a  p  n : ℕ ) (h: p ∣ n): (a :zmod n)^2 =-1 → (a:zmod p)^2 =-1:=
begin
intro y, cases h with x z,
have: (a :zmod n)^2  + 1 =0, rw y, ring, 
have t1: a^2 + 1 ≡ 0 [MOD n], rw ← zmod.eq_iff_modeq_nat, simp, exact this,
have t2: a^2  + 1 ≡ 0 [MOD p], rw z at t1, apply nat.modeq.modeq_of_modeq_mul_right, exact t1,
rw ← zmod.eq_iff_modeq_nat at t2,simp at t2, rw [show (-1 : zmod p) = -1+0, by ring], rw ← t2, ring,
end

lemma non_res_3_mod_4 (d a: ℕ ) (h: d>0): (a : zmod d)^2 =-1→ (d%4) ≠ 3:=
begin
apply nat.strong_induction_on d, intros n m,
cases zero_or_one_two n, intro g1, rw h_1, simp, linarith, cases h_1 with h1 h2, intro q, rw h1, rw [show 1%4 =1, from rfl], linarith,
cases h2 with k h2, intro g, 

have: ∀ (p: ℕ), nat.prime p ∧  p ∣ n → (p%4)≠ 3, intro p, intro v, cases v with g1 g2, 
have t1: ∃ y: zmod p, y^2 =-1, use a, apply zmod_trans, exact g2, assumption,
cases t1 with y hy, 
have t7:  fact p.prime, assumption,
have t6: ∀ (r: ℕ ) [fact r.prime] , (∃ y : zmod r, y ^ 2 = -1) → r % 4 ≠ 3, apply zmod_exi,
have t8: (∃ y : zmod p, y ^ 2 = -1) → p % 4 ≠ 3, apply @t6 p t7, 
apply t8, use y, exact hy,

have t9: nat.prime n ∨ ¬ nat.prime n, tauto, cases t9 with t9 t10, 
apply this n,split, assumption, have t11: n ∣ n, simp, 
have t12: ∃ q, q ∣ n ∧ 2 ≤ q ∧ q < n, apply nat.exists_dvd_of_not_prime2, linarith, assumption, cases t12 with q t12, cases t12 with t12 t13, cases t13 with t13 t14,
have t15: q%4 ≠ 3, apply m q, assumption, apply zmod_trans, assumption, assumption, 
have t16: ∃ w: ℕ, n = q*w, use t12, cases t16 with w t16,
have h1: 1 <q, linarith,
have h2: w>0, by_contra, push_neg at a_1,  have x1: w=0, linarith, rw x1 at t16, simp at t16, linarith,
have h3: w < n, rw t16, nth_rewrite 0 [show w = 1*w, by ring], apply mul_lt_mul, exact h1, linarith, assumption, linarith, 
have h4: w%4 ≠ 3, apply m w, exact h3, apply zmod_trans, use q, rw mul_comm, rw ← t16, assumption,
have h5: q%4 <4, apply nat.mod_lt, simp,
have h6: w%4 <4, apply nat.mod_lt, simp, rw t16, rw nat.mul_mod,
interval_cases q%4, interval_cases w%4, interval_cases w%4, interval_cases w%4,
repeat {rw h_1, rw h_2,simp,linarith},
rw h_1, rw h_2, simp, rw [show 1%4 =1, from rfl], linarith,
rw h_1, rw h_2, simp, rw [show 2%4 =2, from rfl], linarith,
rw h_1, rw h_2, simp, rw [show 2%4 =2, from rfl], linarith,
rw h_1, rw h_2, rw [show 2*2 = 4, from rfl], simp, linarith,
end

lemma res_mod_6 (k: ℕ ): 2 ∣ k ∧ ¬ 3 ∣ k ↔ (k%6) = 2 ∨ (k%6)=4:=
begin
split, intro h,  cases h with h1 h2,
have t3: k%2=0, apply nat.mod_eq_zero_of_dvd, assumption, 
have t2: k%3 ≠ 0, by_contra, push_neg at a, have: 3 ∣ k, apply nat.dvd_of_mod_eq_zero, exact a, contradiction,
have t1: k%6 <6, apply nat.mod_lt, simp, interval_cases (k%6),
swap, exfalso, rw [show 6=3*2, from rfl] at h, have t9: ( k % (3 * 2))%3=0%3, exact congr_fun (congr_arg has_mod.mod h) 3, rw nat.mod_mul_right_mod at t9, contradiction,
swap, exfalso, rw [show 6=2*3, from rfl] at h, have g1: ( k % (2*3))%2=1%2, exact congr_fun (congr_arg has_mod.mod h) 2, rw nat.mod_mul_right_mod at g1, rw t3 at g1, contradiction,
swap, left, assumption,
swap, exfalso, rw [show 6=3*2, from rfl] at h, have t9: ( k % (3 * 2))%3=3%3, exact congr_fun (congr_arg has_mod.mod h) 3, rw nat.mod_mul_right_mod at t9, contradiction,
swap, right, exact h,
swap, exfalso, rw [show 6=2*3, from rfl] at h, have g1: ( k % (2*3))%2=5%2, exact congr_fun (congr_arg has_mod.mod h) 2, rw nat.mod_mul_right_mod at g1, rw t3 at g1, contradiction,

intro h, cases h with h p,split, apply nat.dvd_of_mod_eq_zero, rw [show 6=2*3, from rfl] at h, have g1: ( k % (2*3))%2=2%2, exact congr_fun (congr_arg has_mod.mod h) 2, rw nat.mod_mul_right_mod at g1, rw g1, simp,
by_contra, rw [show 6=3*2, from rfl] at h, have t9: ( k % (3 * 2))%3=2%3, exact congr_fun (congr_arg has_mod.mod h) 3, rw nat.mod_mul_right_mod at t9, have: k%3 =0, apply nat.mod_eq_zero_of_dvd,  exact a, rw this at t9, contradiction,
split, apply nat.dvd_of_mod_eq_zero, rw [show 6=2*3, from rfl] at p, have g1: ( k % (2*3))%2=4%2, exact congr_fun (congr_arg has_mod.mod p) 2, rw nat.mod_mul_right_mod at g1, rw g1, ring,
by_contra, rw [show 6=3*2, from rfl] at p, have t9: ( k % (3 * 2))%3=4%3, exact congr_fun (congr_arg has_mod.mod p) 3, rw nat.mod_mul_right_mod at t9, have: k%3 =0, apply nat.mod_eq_zero_of_dvd,  exact a, rw this at t9, contradiction, 
end

theorem luc_square (n : ℕ ) (h: ∃ k : ℕ , luc n =k^2) :  n=1 ∨ n=3:=
begin
have g1: ∀ u: ℕ ,(3^u)%2 =1, intro u, induction u with x hx, simp, refl, rw nat.succ_eq_add_one, rw nat.pow_add, rw nat.mul_mod, rw hx, simp, refl,
cases h with h i,
cases even_or_odd n,
cases h_1 with k y,
rw y at i,
have: (↑ (luc(2*k)): ℤ ) = (↑ (h^2): ℤ ), 
apply add_arrows, exact i,
simp at this,
have t1: ((luc(2*k) + 2 * (-1: ℤ )^(k)) : ℤ )= ((luc(k))^2 : ℤ ), apply fib_luc3,
rw this at t1, 
have t2: ∃ g: ℕ, ↑(luc k) =(g: ℤ ), use luc k, 
cases t2 with g t2,
rw t2 at t1,
cases pow_neg_one k with h1 h2,
rw h1 at t1,
simp at t1,
norm_cast at t1,
exfalso,
have t1': h^2 +2 ≠ g^2, apply diff_of_squares_neq_2,
contradiction,
rw h2 at t1,
have t2: (h^2 : ℤ ) = (g^2 +2 : ℤ ), rw ← t1, simp,
norm_cast at t2,
exfalso,
have t2':   g^2 +2 ≠ h^2  , apply diff_of_squares_neq_2,
rw eq_comm at t2,
contradiction,
have t4: nat.gcd 3 2 =1, simp, rw nat.succ_eq_add_one, ring, 
have: ∃ q: ℕ ,n=4*q+(n%4) ∧ (n%4) <4,  apply div_algo n 4,simp,
cases this with q r,  cases r with r s, interval_cases (n%4),
rw  nat.dvd_iff_mod_eq_zero at h_1, rw [show 4=2*2, from rfl] at h_2,
have t3: (n%(2*2))%2 = 0%2, exact congr_fun (congr_arg has_mod.mod h_2) 2,
rw nat.mod_mul_left_mod at t3, rw nat.add_mod at h_1, rw t3 at h_1, simp at h_1, contradiction,
swap, rw  nat.dvd_iff_mod_eq_zero at h_1, rw [show 4=2*2, from rfl] at h_2,
have t3: (n%(2*2))%2 = 2%2, exact congr_fun (congr_arg has_mod.mod h_2) 2,
rw nat.mod_mul_left_mod at t3, rw nat.add_mod at h_1, rw t3 at h_1, simp at h_1, contradiction,

cases nat_case_bash 1 1, interval_cases q, rw h_3 at r, left, rw h_2 at r, simp at r, assumption,
cases h_3 with f h3, have s1: q >0, linarith,
rw h_2 at r, rw [show 4 =2*2, from rfl] at r,
have: ∃ (k r: ℕ ), q =3^r *k ∧ ¬ 3 ∣ k, apply decomp_pow_3 q, exact s1,
cases this with k u, cases u with u j, cases j with j l, rw j at r, rw [show 2*2*(3^u*k)= 2*3^u *(2*k), by ring] at r,
have g2: ∃ v: ℕ, 3^u =2*v+ (3^u)%2 ∧ (3^u)%2<2, apply div_algo, simp,
cases g2 with v g2, rw g1 u at g2, cases g2 with g2 g3, clear g3, rw g2 at r,
have: luc (2*k) ∣ luc (1+2*(2*v+1)*(2*k)) + luc 1, apply mod_luc2 (2*k) v 1, simp,
by_contra, push_neg at a, have: 3 ∣ 2*k, apply nat.dvd_of_mod_eq_zero, exact a,
have t2: 3 ∣ k, apply nat.coprime.dvd_of_dvd_mul_left, swap, assumption, swap, contradiction,
assumption, rw [show luc 1 =1, from rfl] at this, rw add_comm at r, rw ← r at this, rw i at this,
have t6: luc(2*k)%4 ≠ 3, apply non_res_3_mod_4,  apply luc_pos,
have r6: (h^2 + 1)%(luc(2*k))=0, apply nat.mod_eq_zero_of_dvd, assumption,
have r8: (h: zmod (luc(2*k)))^2 =(-1 : zmod (luc (2*k))), rw ←  zmod.val_cast_nat at r6, simp at r6, rw [show (-1 : zmod (luc (2*k))) = -1+0 , by ring], rw ← r6, ring, assumption,
have t7: luc(2*k)%4=3, apply luc_mod_4, have t8: (2*k) %6 <6, apply nat.mod_lt, simp, rw ← res_mod_6,split, simp, by_contra, have g2: 3 ∣ k, apply nat.coprime.dvd_of_dvd_mul_left,assumption, exact a, contradiction, contradiction,

rw h_2 at r, cases nat_case_bash q 1, interval_cases q, rw h_3 at r, right, simp at r, assumption,
cases h_3 with f h3, have s1: q >0, linarith,
rw [show 4 =2*2, from rfl] at r,
have: ∃ (k r: ℕ ), q =3^r *k ∧ ¬ 3 ∣ k, apply decomp_pow_3 q, exact s1,
cases this with k u, cases u with u j, cases j with j l, rw j at r, rw [show 2*2*(3^u*k)= 2*3^u *(2*k), by ring] at r,
have g2: ∃ v: ℕ, 3^u =2*v+ (3^u)%2 ∧ (3^u)%2<2, apply div_algo, simp,
cases g2 with v g2, rw g1 u at g2, cases g2 with g2 g3, clear g3, rw g2 at r,
have: luc (2*k) ∣ luc (3+2*(2*v+1)*(2*k)) + luc 3, apply mod_luc2 (2*k) v 3, simp,
by_contra, push_neg at a, have: 3 ∣ 2*k, apply nat.dvd_of_mod_eq_zero, exact a,
have t2: 3 ∣ k, apply nat.coprime.dvd_of_dvd_mul_left, swap, assumption, swap, contradiction,
assumption, rw [show luc 3 =4, from rfl] at this, rw add_comm at r, rw ← r at this, rw i at this,
have t7: luc(2*k)%4=3, apply luc_mod_4, have t8: (2*k) %6 <6, apply nat.mod_lt, simp, rw ← res_mod_6,split, simp, by_contra, have g2: 3 ∣ k, apply nat.coprime.dvd_of_dvd_mul_left,assumption, exact a, contradiction, 
have t6: (h^2 + 4)%(luc(2*k))=0, apply nat.mod_eq_zero_of_dvd, assumption,
have t8: (h: zmod (luc(2*k)))^2 =(-4 : zmod (luc (2*k))), rw ←  zmod.val_cast_nat at t6, simp at t6, rw [show (-4 : zmod (luc (2*k))) = -4+0 , by ring], rw ← t6, ring,
have t9: (4: zmod (luc (2*k))) * 4⁻¹ =1, rw zmod.mul_inv_eq_gcd, 
have t11: nat.gcd (4 : zmod (luc(2*k))).val (luc(2*k)) = nat.gcd (luc(2*k)) 4, nth_rewrite 1 nat.gcd_rec,  rw←  zmod.val_cast_nat, simp, rw t11, 
have t12: nat.gcd (luc(2*k)) 4 =1, rw nat.gcd_comm, simp, rw nat.succ_eq_add_one, rw [show 3+1=4, from rfl], 
rw t7, ring, rw t12, simp,
have t13: (h: zmod (luc(2*k)))^2 * 4⁻¹ = -1, rw t8, ring, rw t9, clear g1, clear i, clear h_1, clear s, 
have t14: (2 : zmod (luc(2*k)))*(2 ⁻¹) =1, rw zmod.mul_inv_eq_gcd,
have t15: nat.gcd (2 : zmod (luc(2*k))).val (luc(2*k)) = nat.gcd (luc(2*k)) 2, nth_rewrite 1 nat.gcd_rec,  rw←  zmod.val_cast_nat, simp, rw t15, 
have t16: nat.gcd (luc(2*k)) 2 =1, rw nat.gcd_comm, simp, rw nat.succ_eq_add_one, rw [show 1+1=2, from rfl], 
have t17: luc(2*k) %2 =1, rw [show 4=2*2, from rfl] at t7, 
have t18: (luc (2*k))%(2*2)%2 = 3%2, exact congr_fun (congr_arg has_mod.mod t7) 2, rw [show 3%2 =1, from rfl] at t18, rw ←  nat.mod_mul_right_mod,  assumption,
rw t17, ring, rw t16, simp, 
have g3: (4: zmod (luc(2*k))) * (2 ⁻¹ *2⁻¹) =1,  rw [show (4: zmod (luc(2*k)))* (2 ⁻¹*2 ⁻¹ ) =2*(2* 2 ⁻¹)* 2 ⁻¹ , by ring], rw t14, simp, assumption,
have g4: (2 : zmod (luc(2*k))) ⁻¹ * 2 ⁻¹ = (4) ⁻¹ ,apply inv_unique g3 t9, 
rw ← g4 at t13, rw [show (h: zmod (luc(2*k))) ^ 2 * (2⁻¹ * 2⁻¹) = (h*2 ⁻¹ )^2, by ring ] at t13,
have g5: luc(2*k)%4 ≠ 3, apply non_res_3_mod_4, apply luc_pos,
have g6: luc(2*k)>0, apply luc_pos, 
have g7: ((h:zmod (luc(2*k)))* 2⁻¹) = ↑(((h:zmod (luc(2*k)))* 2⁻¹).val), rw  @zmod.cast_val (luc(2*k)) g6 ((h:zmod (luc(2*k)))* 2⁻¹), rw g7 at t13, exact t13, 
contradiction, 
end



