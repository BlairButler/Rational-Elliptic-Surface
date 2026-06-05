Code devolped by Blair Butler and Andreas-Stephan Elsenhans for the paper "ARITHMETIC INFORMATION OF RATIONAL ELLIPTIC SURFACES, AND SHIODA’S RANK 68 SURFACE".
The Repositry contains 11 Files. A quick rundown:
1. RatES_for_360: Contains the 11 rational elliptic surfaces needed for the Rank 68 surface, using RatESSolve
2. AutSplit.m: Code to compute the number field and automorphism group of a sequence of polynomials
3. Example 5. y^2 = x^3 -3*t*(t^2-1)*x + (t^2-1)^2: An example of using RatESSolve on a Rational Elliptic Surface
4. Field_Matching: Code to verify that the numberfields from RatESSolve match the polynomils given in Table 1 of the paper
5. FoD-GaloisGroup-Code: Code that computes the Galois group for the polynomials for the field of definition of the degree 68 elliptic surface
6. Lemma_4.2: The code that accompanies Lemma 4.2 of the Paper
7. RatESMordellWeil: Code that just computes the generators for the MordellWeil group, plus field of definition (no galois represenation).
8. RatESSolve_Examples: Examples for RatESSolve. Essentially the same information as Example 5 above.
9. RationalES_Rank_FoDDegree_Functions: Functions to compute the rank and degree of the field of definition of a rational elliptic surface without computing the entire Galios representation.
10. Rational_SplittingFieldCode_Algo.m: The main code of the paper; algorthim 2 that is then used on the 11 rational elliptic surfaces in Theorem 4.2.
