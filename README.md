# Formalizing Fibonacci Squares

We formalize [Cohn's proof](https://math.la.asu.edu/~checkman/SquareFibonacci.html) that the only squares in the Fibonacci sequence is 0, 1, and 144.
Read my [paper](https://kwarc.info/teaching/CICM21WS/fmm5.pdf) or watch my [talk](https://www.youtube.com/watch?v=OCQfkhqg8Yg&ab_channel=leanprovercommunity) for more details

If you've installed [lean](https://leanprover-community.github.io/get_started.html#regular-install) then type 
```
leanproject get mhk119/fibonacci_squares
```

### Contents of src
<ul>
<li> In addition to the contents below, there are other lemmas formalized in every file that are needed later on in the proofs. </li>
<li> Preliminaries 8, 9 are not formalized due to a modification to Cohn's proof. We define Fibonacci and Lucas on naturals and for places where integers are required (Preliminaries 1, 2, 11, 12, 13) we formalized separately an addition and subtraction version. </li></ul>

| No. | File               | Contents (refer to [Cohn](https://math.la.asu.edu/~checkman/SquareFibonacci.html))             |
|-----|--------------------|----------------------|
| 1   | recursions         | preliminaries 1-3    |
| 2   | gcd                | preliminaries 4-5    |
| 3   | divisibility1      | preliminaries 6,7,10 |
| 4   | divisibility2      | preliminaries 11-13  |
| 5   | luc_squares        | theorem 1            |
| 6   | luc_double_squares | theorem 2            |
| 7   | fib_squares        | theorem 3            |
